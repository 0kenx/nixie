//! Test specification and concrete oracle, independent of CP filtering code.
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

#[derive(Clone, Debug)]
pub enum Rule {
    Distinct(Vec<usize>),
    Allowed(Vec<usize>, Vec<Vec<BigInt>>),
    Word {
        vars: Vec<usize>,
        initial: usize,
        accepting: Vec<usize>,
        edges: Vec<(usize, BigInt, usize)>,
    },
    Tour(Vec<usize>),
    Resource {
        tasks: Vec<(usize, BigInt, BigInt)>,
        capacity: BigInt,
    },
}

impl Rule {
    pub fn accepts(&self, values: &[BigInt]) -> bool {
        match self {
            Self::Distinct(vars) => vars
                .iter()
                .enumerate()
                .all(|(i, &v)| vars[..i].iter().all(|&w| values[v] != values[w])),
            Self::Allowed(vars, rows) => {
                let actual: Vec<_> = vars.iter().map(|&v| values[v].clone()).collect();
                rows.contains(&actual)
            }
            Self::Word {
                vars,
                initial,
                accepting,
                edges,
            } => {
                // Enumerate concrete runs. No partial-domain reachability or
                // support computation is shared with the implementation.
                let mut paths = vec![(0, *initial)];
                while let Some((position, state)) = paths.pop() {
                    if position == vars.len() {
                        if accepting.contains(&state) {
                            return true;
                        }
                    } else {
                        for (from, symbol, to) in edges {
                            if *from == state && *symbol == values[vars[position]] {
                                paths.push((position + 1, *to));
                            }
                        }
                    }
                }
                false
            }
            Self::Tour(vars) => {
                if vars.is_empty() {
                    return true;
                }
                // Visit every node exactly once from node zero, then return
                // to zero. No matching or partial-subtour filter is reused.
                let mut visited = vec![false; vars.len()];
                let mut node = 0;
                for _ in vars {
                    if visited[node] {
                        return false;
                    }
                    visited[node] = true;
                    let Some(next) = values[vars[node]].to_usize() else {
                        return false;
                    };
                    if next >= vars.len() {
                        return false;
                    }
                    node = next;
                }
                node == 0 && visited.iter().all(|&seen| seen)
            }
            Self::Resource { tasks, capacity } => {
                if capacity < &BigInt::zero() {
                    return false;
                }
                // With nonnegative demands, overload can first arise only
                // at a task's start. Evaluate actual usage there, without
                // mandatory parts, event aggregation, or a sweep algorithm.
                tasks.iter().all(|(at, _, _)| {
                    let time = &values[*at];
                    let load: BigInt = tasks
                        .iter()
                        .filter_map(|(start, duration, demand)| {
                            (values[*start] <= *time && *time < &values[*start] + duration)
                                .then_some(demand.clone())
                        })
                        .sum();
                    load <= *capacity
                })
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Case {
    pub family: usize,
    pub seed: u64,
    pub domains: Vec<Vec<BigInt>>,
    pub rules: Vec<Rule>,
}

impl Case {
    pub fn accepts(&self, indices: &[usize]) -> bool {
        let values: Vec<_> = indices
            .iter()
            .enumerate()
            .map(|(v, &i)| self.domains[v][i].clone())
            .collect();
        self.rules.iter().all(|r| r.accepts(&values))
    }

    pub fn assignments(&self) -> Vec<Vec<usize>> {
        // Bounded Cartesian enumeration on a heap worklist; zero variables
        // have one empty assignment, whereas any empty domain has none.
        let mut rows = vec![Vec::new()];
        for domain in &self.domains {
            rows = rows
                .into_iter()
                .flat_map(|prefix| {
                    (0..domain.len()).map(move |i| {
                        let mut row = prefix.clone();
                        row.push(i);
                        row
                    })
                })
                .collect();
        }
        rows
    }
}

// Fixed PRNG for reproducibility. This is test generation, not search policy.
pub struct Rng(u64);
impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }
    pub fn pick(&mut self, bound: usize) -> usize {
        assert!(bound > 0);
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 32) % bound as u64) as usize
    }
}

fn selected(vars: usize, rng: &mut Rng) -> Vec<usize> {
    if vars == 0 {
        return Vec::new();
    }
    let count = rng.pick(7);
    (0..count).map(|_| rng.pick(vars)).collect()
}

fn rule(family: usize, domains: &[Vec<BigInt>], rng: &mut Rng) -> Rule {
    let count = domains.len();
    let vars = selected(count, rng);
    match family {
        0 => Rule::Distinct(vars),
        1 => {
            let rows = (0..rng.pick(7))
                .map(|_| {
                    vars.iter()
                        .map(|&v| {
                            if domains[v].is_empty() || rng.pick(5) == 0 {
                                BigInt::from(-7)
                            } else {
                                domains[v][rng.pick(domains[v].len())].clone()
                            }
                        })
                        .collect()
                })
                .collect();
            Rule::Allowed(vars, rows)
        }
        2 => {
            let states = rng.pick(4) + 1;
            let initial = rng.pick(states);
            let accepting = (0..states).filter(|_| rng.pick(2) == 0).collect();
            let mut alphabet: Vec<_> = domains.iter().flatten().cloned().collect();
            alphabet.extend([BigInt::from(-7), BigInt::zero()]);
            alphabet.sort();
            alphabet.dedup();
            let edges = (0..rng.pick(15))
                .map(|_| {
                    (
                        rng.pick(states),
                        alphabet[rng.pick(alphabet.len())].clone(),
                        rng.pick(states),
                    )
                })
                .collect();
            Rule::Word {
                vars,
                initial,
                accepting,
                edges,
            }
        }
        3 => {
            let mut tour: Vec<_> = (0..count).collect();
            if count > 1 && rng.pick(5) == 0 {
                tour[1] = tour[0];
            }
            Rule::Tour(tour)
        }
        4 => {
            let wide = rng.pick(4) == 0;
            let scale = if wide {
                BigInt::from(1) << 130usize
            } else {
                BigInt::from(1)
            };
            let tasks = vars
                .into_iter()
                .map(|v| {
                    let duration = BigInt::from(rng.pick(5));
                    let demand = BigInt::from(rng.pick(4)) * &scale;
                    (v, duration, demand)
                })
                .collect();
            let capacity = (BigInt::from(rng.pick(7)) - 1) * scale;
            Rule::Resource { tasks, capacity }
        }
        _ => panic!("unknown test family"),
    }
}

pub fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for family in 0..6 {
        for seed in 0..40u64 {
            let mut rng = Rng::new(0x4350_2026_0916 ^ (family as u64 * 1009 + seed));
            let count = if family == 5 {
                3 + rng.pick(2)
            } else {
                (seed % 5) as usize
            };
            let offset = match seed % 4 {
                0 => -(BigInt::from(1) << 130usize),
                1 => BigInt::from(-2),
                2 => BigInt::zero(),
                3 => BigInt::from(1) << 130usize,
                _ => unreachable!(),
            };
            let domains: Vec<Vec<BigInt>> = (0..count)
                .map(|_| {
                    let mut domain: Vec<_> = (0..4)
                        .filter(|_| rng.pick(4) != 0)
                        .map(|v| {
                            if family == 3 {
                                BigInt::from(v)
                            } else {
                                &offset + v
                            }
                        })
                        .collect();
                    if seed % 13 == 0 && rng.pick(3) == 0 {
                        domain.clear();
                    }
                    // Reverse insertion order to exercise unsorted domains.
                    if rng.pick(2) == 0 {
                        domain.reverse();
                    }
                    domain
                })
                .collect();
            let rules = if family == 5 {
                (0..3)
                    .map(|_| rule(rng.pick(5), &domains, &mut rng))
                    .collect()
            } else {
                vec![rule(family, &domains, &mut rng)]
            };
            cases.push(Case {
                family,
                seed,
                domains,
                rules,
            });
        }
    }
    // Guarantee coverage of nondeterminism, repeated word variables, and
    // nonempty circuit solutions at the largest generated arity.
    cases.push(Case {
        family: 2,
        seed: 100,
        domains: vec![vec![0.into(), 1.into()], vec![0.into(), 1.into()]],
        rules: vec![Rule::Word {
            vars: vec![0, 1, 0],
            initial: 0,
            accepting: vec![2, 3],
            edges: vec![
                (0, 0.into(), 0),
                (0, 0.into(), 1),
                (0, 1.into(), 2),
                (1, 1.into(), 3),
                (2, 0.into(), 3),
                (3, 0.into(), 2),
            ],
        }],
    });
    cases.push(Case {
        family: 3,
        seed: 100,
        domains: vec![vec![0.into(), 1.into(), 2.into(), 3.into()]; 4],
        rules: vec![Rule::Tour(vec![0, 1, 2, 3])],
    });
    let huge: BigInt = BigInt::from(1) << 130usize;
    cases.push(Case {
        family: 3,
        seed: 101,
        domains: vec![
            vec![-&huge, 1.into(), huge.clone()],
            vec![(-1).into(), 0.into(), huge.clone()],
        ],
        rules: vec![Rule::Tour(vec![0, 1])],
    });
    cases.push(Case {
        family: 4,
        seed: 100,
        domains: vec![
            vec![0.into(), huge.clone()],
            vec![&huge - 1, huge.clone(), &huge * 2],
        ],
        rules: vec![Rule::Resource {
            tasks: vec![(0, huge.clone(), huge.clone()), (1, 1.into(), huge.clone())],
            capacity: huge,
        }],
    });
    cases
}

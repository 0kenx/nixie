use super::*;

impl CpModel {
    // Necessary conditions on partial domains; exact predicates on singletons.
    // Testing a candidate singleton yields an explained value deletion.
    pub(super) fn feasible(
        &self,
        constraint: &Constraint,
        domains: &[Vec<BigInt>],
    ) -> Option<bool> {
        Some(match constraint {
            Constraint::AllDifferent(vars) => matching(vars, domains)?,
            Constraint::Table(statement) => statement.rows().iter().any(|tuple| {
                let vars = statement.variables();
                vars.iter().enumerate().all(|(i, v)| {
                    domains[v.0].contains(&tuple[i])
                        && vars[..i]
                            .iter()
                            .enumerate()
                            .all(|(j, w)| v != w || tuple[i] == tuple[j])
                })
            }),
            Constraint::Regular(vars, initial, accepting, transitions) => {
                let mut reachable = HashSet::new();
                reachable.insert(*initial);
                for var in vars {
                    let mut next = HashSet::new();
                    for edge in transitions {
                        if reachable.contains(&edge.source) && domains[var.0].contains(&edge.symbol)
                        {
                            next.insert(edge.destination);
                        }
                    }
                    reachable = next;
                }
                accepting.iter().any(|q| reachable.contains(q))
            }
            Constraint::Circuit(vars) => {
                let n = vars.len();
                if n == 0 {
                    return Some(true);
                }
                let mut restricted = domains.to_vec();
                for (i, v) in vars.iter().enumerate() {
                    restricted[v.0]
                        .retain(|x| x.to_usize().is_some_and(|j| j < n && (n == 1 || i != j)));
                }
                if !matching(vars, &restricted)? {
                    return Some(false);
                }
                // Every cycle already forced by singleton successors must
                // cover all nodes. Iterative traversal, bounded by node count.
                for start in 0..n {
                    let mut seen = HashMap::new();
                    let mut node = start;
                    while restricted[vars[node].0].len() == 1 {
                        let step = seen.len();
                        if let Some(first) = seen.insert(node, step) {
                            if step - first < n {
                                return Some(false);
                            }
                            break;
                        }
                        let Some(next) = restricted[vars[node].0][0].to_usize() else {
                            return Some(false);
                        };
                        node = next;
                    }
                }
                true
            }
            Constraint::Cumulative(tasks, capacity) => {
                if *capacity < BigInt::zero() {
                    return Some(false);
                }
                let mut events: BTreeMap<BigInt, BigInt> = BTreeMap::new();
                for task in tasks {
                    if task.duration.is_zero() || task.demand.is_zero() {
                        continue;
                    }
                    let domain = &domains[task.start.0];
                    let (Some(earliest), Some(latest)) = (domain.iter().min(), domain.iter().max())
                    else {
                        return Some(false);
                    };
                    let end = earliest + &task.duration;
                    // Mandatory part [latest start, earliest end).
                    if *latest < end {
                        *events.entry(latest.clone()).or_default() += &task.demand;
                        *events.entry(end).or_default() -= &task.demand;
                    }
                }
                let mut load = BigInt::zero();
                for delta in events.values() {
                    load += delta;
                    if load > *capacity {
                        return Some(false);
                    }
                }
                true
            }
        })
    }
}

// Bipartite maximum matching by iterative augmenting paths. Forcing each
// candidate edge in the caller gives domain consistency (including Hall sets).
fn matching(vars: &[CpVar], domains: &[Vec<BigInt>]) -> Option<bool> {
    let mut unique = HashSet::new();
    if vars.iter().any(|v| !unique.insert(*v)) {
        return Some(false);
    }
    let mut owner: HashMap<BigInt, usize> = HashMap::new();
    let mut assigned: Vec<Option<BigInt>> = vec![None; vars.len()];
    for root in 0..vars.len() {
        let mut queue = VecDeque::from([root]);
        let mut reached = vec![false; vars.len()];
        reached[root] = true;
        let mut via: HashMap<BigInt, usize> = HashMap::new();
        let mut free = None;
        while let Some(v) = queue.pop_front() {
            for value in &domains[vars[v].0] {
                if via.contains_key(value) {
                    continue;
                }
                via.insert(value.clone(), v);
                if let Some(&w) = owner.get(value) {
                    if !reached[w] {
                        reached[w] = true;
                        queue.push_back(w);
                    }
                } else {
                    free = Some(value.clone());
                    break;
                }
            }
            if free.is_some() {
                break;
            }
        }
        let Some(mut value) = free else {
            return Some(false);
        };
        loop {
            // A missing predecessor would be corrupted bookkeeping, not
            // proof that the matching problem is infeasible.
            let &v = via.get(&value)?;
            owner.insert(value.clone(), v);
            match assigned[v].replace(value) {
                Some(previous) => value = previous,
                None => break,
            }
        }
    }
    Some(true)
}

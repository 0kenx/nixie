use super::*;
use core::cell::OnceCell;

type Bounds<'a> = Option<(&'a BigInt, &'a BigInt)>;

// One immutable callback snapshot. Both cache levels are lazy: callbacks with
// no active cumulative task, and non-cumulative globals, allocate nothing here.
// The borrowed domains cannot change while their extrema are retained. Trials
// bypass these cells, and the entire object is dropped at the callback boundary.
pub(super) struct Feasibility<'a> {
    domains: &'a [Vec<BigInt>],
    bounds: OnceCell<Vec<OnceCell<Bounds<'a>>>>,
}

impl<'a> Feasibility<'a> {
    pub(super) fn new(domains: &'a [Vec<BigInt>]) -> Self {
        Self {
            domains,
            bounds: OnceCell::new(),
        }
    }

    fn bounds(&self, var: CpVar) -> Option<Bounds<'a>> {
        let domain = self.domains.get(var.0)?;
        let cells = self
            .bounds
            .get_or_init(|| self.domains.iter().map(|_| OnceCell::new()).collect());
        let cell = cells.get(var.0)?;
        // Outer None is an invalid variable; cached inner None is an empty
        // domain. Keep the distinction between Unknown and infeasibility.
        Some(*cell.get_or_init(|| Some((domain.iter().min()?, domain.iter().max()?))))
    }

    // Borrow the singleton override for cumulative trials. Every occurrence of
    // this start variable sees the same value, including tasks with different
    // presence conditions. Other globals retain their existing implementation.
    pub(super) fn feasible_at(
        &self,
        constraint: &Constraint,
        presences: &[Option<bool>],
        var: CpVar,
        value: &BigInt,
    ) -> Option<bool> {
        match constraint {
            Constraint::Cumulative(tasks, capacity) => {
                cumulative_feasible(tasks, capacity, self, presences, Some((var, value)))
            }
            Constraint::AllDifferent(_)
            | Constraint::Table(_)
            | Constraint::Regular(..)
            | Constraint::Circuit(_) => {
                let mut candidate = self.domains.to_vec();
                *candidate.get_mut(var.0)? = vec![value.clone()];
                Feasibility::new(&candidate).feasible(constraint, presences)
            }
        }
    }

    // Discharge a trial presence after testing every start of each present
    // task against the timetable. No supported start for any one task proves
    // the trial impossible, even when that task has an empty mandatory part.
    pub(super) fn presence_feasible(
        &self,
        constraint: &Constraint,
        presences: &[Option<bool>],
    ) -> Option<bool> {
        if !self.feasible(constraint, presences)? {
            return Some(false);
        }
        if let Constraint::Cumulative(tasks, _) = constraint {
            for scheduled in tasks {
                if let Some((index, positive)) = scheduled.presence
                    && *presences.get(index)? != Some(positive)
                {
                    continue;
                }
                let var = scheduled.task.start;
                let mut supported = false;
                for start in &self.domains[var.0] {
                    if self.feasible_at(constraint, presences, var, start)? {
                        supported = true;
                        break;
                    }
                }
                if !supported {
                    return Some(false);
                }
            }
        }
        Some(true)
    }

    // Necessary conditions on partial domains; exact predicates on singletons.
    // Testing a candidate singleton yields an explained value deletion.
    pub(super) fn feasible(
        &self,
        constraint: &Constraint,
        presences: &[Option<bool>],
    ) -> Option<bool> {
        let domains = self.domains;
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
                cumulative_feasible(tasks, capacity, self, presences, None)?
            }
        })
    }
}

// Exact half-open mandatory-part sweep. A borrowed trial is an overlay, not a
// domain mutation: no candidate state or reduction can leak into another test.
fn cumulative_feasible(
    tasks: &[ScheduledTask],
    capacity: &BigInt,
    state: &Feasibility<'_>,
    presences: &[Option<bool>],
    trial: Option<(CpVar, &BigInt)>,
) -> Option<bool> {
    if *capacity < BigInt::zero() {
        return Some(false);
    }
    let mut events: BTreeMap<BigInt, BigInt> = BTreeMap::new();
    for scheduled in tasks {
        if let Some((index, positive)) = scheduled.presence
            && *presences.get(index)? != Some(positive)
        {
            continue;
        }
        let task = &scheduled.task;
        if task.duration.is_zero() || task.demand.is_zero() {
            continue;
        }
        if task.demand > *capacity {
            return Some(false);
        }
        let bounds = match trial {
            Some((var, value)) if var == task.start => Some((value, value)),
            _ => state.bounds(task.start)?,
        };
        let Some((earliest, latest)) = bounds else {
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
    Some(true)
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

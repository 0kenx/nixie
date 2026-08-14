//! Regular Expression Constraint Solver for String Theory
//!
//! This module implements solving for string constraints with regular expressions:
//! - Membership testing (str ∈ regex)
//! - Negated membership (str ∉ regex)
//! - Regex intersection and complement
//! - Length-aware regex solving
#![allow(missing_docs)] // Under development - documentation in progress

#[allow(unused_imports)]
use crate::prelude::*;

/// String variable identifier
pub type StrVar = usize;

/// Maximum nesting depth explored by the backtracking membership and
/// string-generation procedures.
///
/// These are *not* structural walks over the regex: `test_concat_recursive`
/// recurses once per remaining part **and** once per candidate split position,
/// and `test_star` once per repetition, so the depth is bounded by the regex
/// nesting depth times the subject length -- input-unbounded in both factors,
/// and exponential in the worst case. An explicit-stack rewrite would still
/// need this bound, so it is stated honestly instead: exceeding it returns
/// `Err`, never a `false` "not a member" or a `None` "no such string", either
/// of which the caller could not tell apart from a real answer.
const MAX_REGEX_SEARCH_DEPTH: usize = 256;

/// Build the error returned when [`MAX_REGEX_SEARCH_DEPTH`] is exhausted.
fn depth_budget_error(procedure: &str) -> String {
    format!(
        "{} exceeded the maximum search depth of {} \
         (the regex nesting depth times the subject length is too large); \
         the result is unknown, not negative",
        procedure, MAX_REGEX_SEARCH_DEPTH
    )
}

/// Regular expression
///
/// # Depth invariant
///
/// There is deliberately no bound on how deep a `Regex` may be: the variants
/// are public, so callers build values directly. [`Clone`] and [`PartialEq`]
/// are therefore iterative -- see their impls below -- rather than derived,
/// exactly like the [`Drop`] impl already in this file. Do **not** replace
/// any of them with a `derive`.
#[derive(Debug)]
pub enum Regex {
    /// Empty language
    Empty,
    /// Epsilon (empty string)
    Epsilon,
    /// Single character
    Char(char),
    /// Character class (set of characters)
    CharClass(FxHashSet<char>),
    /// Concatenation
    Concat(Vec<Regex>),
    /// Union (alternation)
    Union(Vec<Regex>),
    /// Kleene star
    Star(Box<Regex>),
    /// Negation (complement)
    Complement(Box<Regex>),
    /// Intersection
    Intersection(Vec<Regex>),
    /// Optional (zero or one)
    Optional(Box<Regex>),
    /// One or more
    Plus(Box<Regex>),
    /// Exact repetition
    Repeat { regex: Box<Regex>, count: usize },
    /// Range repetition
    RepeatRange {
        regex: Box<Regex>,
        min: usize,
        max: Option<usize>,
    },
}

/// String constraint
#[derive(Debug, Clone)]
pub enum StringConstraint {
    /// String matches regex
    InRegex {
        var: StrVar,
        regex: Regex,
    },
    /// String doesn't match regex
    NotInRegex {
        var: StrVar,
        regex: Regex,
    },
    /// Length constraint
    LengthEq {
        var: StrVar,
        length: usize,
    },
    LengthLe {
        var: StrVar,
        length: usize,
    },
    LengthGe {
        var: StrVar,
        length: usize,
    },
}

/// Solution for string variables
#[derive(Debug, Clone)]
pub struct StringSolution {
    /// Assignment of variables to strings
    pub assignment: FxHashMap<StrVar, String>,
}

/// Statistics for regex solver
#[derive(Debug, Clone, Default)]
pub struct RegexSolverStats {
    pub constraints_solved: u64,
    pub regex_intersections: u64,
    pub regex_complements: u64,
    pub membership_tests: u64,
    pub length_propagations: u64,
}

/// Configuration for regex solver
#[derive(Debug, Clone)]
pub struct RegexSolverConfig {
    /// Maximum string length to consider
    pub max_string_length: usize,
    /// Enable length-based pruning
    pub use_length_pruning: bool,
    /// Maximum regex size for complement
    pub max_complement_size: usize,
}

impl Default for RegexSolverConfig {
    fn default() -> Self {
        Self {
            max_string_length: 100,
            use_length_pruning: true,
            max_complement_size: 1000,
        }
    }
}

/// Regular expression constraint solver
pub struct RegexSolver {
    config: RegexSolverConfig,
    stats: RegexSolverStats,
    /// Constraints for each variable
    constraints: FxHashMap<StrVar, Vec<StringConstraint>>,
    /// Length bounds for variables
    length_bounds: FxHashMap<StrVar, (Option<usize>, Option<usize>)>,
}

impl RegexSolver {
    /// Create a new regex solver
    pub fn new(config: RegexSolverConfig) -> Self {
        Self {
            config,
            stats: RegexSolverStats::default(),
            constraints: FxHashMap::default(),
            length_bounds: FxHashMap::default(),
        }
    }

    /// Add a constraint
    pub fn add_constraint(&mut self, constraint: StringConstraint) {
        let var = match &constraint {
            StringConstraint::InRegex { var, .. } => *var,
            StringConstraint::NotInRegex { var, .. } => *var,
            StringConstraint::LengthEq { var, .. } => *var,
            StringConstraint::LengthLe { var, .. } => *var,
            StringConstraint::LengthGe { var, .. } => *var,
        };

        self.constraints.entry(var).or_default().push(constraint);
    }

    /// Solve all constraints
    pub fn solve(&mut self) -> Result<Option<StringSolution>, String> {
        self.stats.constraints_solved += 1;

        // Phase 1: Propagate length constraints
        if self.config.use_length_pruning {
            self.propagate_lengths()?;
        }

        // Phase 2: Compute regex intersection for each variable
        let combined_regexes = self.compute_combined_regexes()?;

        // Phase 3: Find satisfying strings
        let solution = self.find_satisfying_strings(&combined_regexes)?;

        Ok(solution)
    }

    /// Propagate length constraints to tighten bounds
    fn propagate_lengths(&mut self) -> Result<(), String> {
        for (&var, constraints) in &self.constraints {
            let mut lower = None;
            let mut upper = None;

            for constraint in constraints {
                match constraint {
                    StringConstraint::LengthEq { length, .. } => {
                        lower = Some(*length);
                        upper = Some(*length);
                    }
                    StringConstraint::LengthLe { length, .. } => {
                        upper = match upper {
                            Some(u) => Some(u.min(*length)),
                            None => Some(*length),
                        };
                    }
                    StringConstraint::LengthGe { length, .. } => {
                        lower = match lower {
                            Some(l) => Some(l.max(*length)),
                            None => Some(*length),
                        };
                    }
                    StringConstraint::InRegex { regex, .. } => {
                        // Compute possible lengths for regex
                        if let Some((min_len, max_len)) = self.regex_length_bounds(regex) {
                            lower = match lower {
                                Some(l) => Some(l.max(min_len)),
                                None => Some(min_len),
                            };
                            if let Some(max) = max_len {
                                upper = match upper {
                                    Some(u) => Some(u.min(max)),
                                    None => Some(max),
                                };
                            }
                        }
                    }
                    _ => {}
                }
            }

            // Check consistency
            if let (Some(l), Some(u)) = (lower, upper)
                && l > u
            {
                return Err(format!(
                    "Inconsistent length bounds for variable {}: {} > {}",
                    var, l, u
                ));
            }

            self.length_bounds.insert(var, (lower, upper));
            self.stats.length_propagations += 1;
        }

        Ok(())
    }

    /// Compute length bounds for a regex
    ///
    /// Explicit post-order stack, not recursion: the regex nests as deeply as
    /// the caller builds it, and the return type (`Option`) has no error
    /// variant -- a depth cap could only answer "no bound known" for a regex
    /// that has one, silently loosening a length constraint.
    fn regex_length_bounds(&self, regex: &Regex) -> Option<(usize, Option<usize>)> {
        let mut state = BoundsState::default();
        push_bounds_operands(regex, &mut state.tasks);
        while let Some(task) = state.tasks.pop() {
            match task {
                BoundsTask::Enter(node) => {
                    state.tasks.push(BoundsTask::Reduce(node));
                    push_bounds_operands(node, &mut state.tasks);
                }
                BoundsTask::Reduce(node) => {
                    let value = reduce_bounds(node, &mut state);
                    state.results.push(value);
                }
            }
        }
        reduce_bounds(regex, &mut state)
    }

    /// Compute combined regex for each variable
    fn compute_combined_regexes(&mut self) -> Result<FxHashMap<StrVar, Regex>, String> {
        let mut combined = FxHashMap::default();

        for (&var, constraints) in &self.constraints {
            let mut positive = Vec::new();
            let mut negative = Vec::new();

            for constraint in constraints {
                match constraint {
                    StringConstraint::InRegex { regex, .. } => {
                        positive.push(regex.clone());
                    }
                    StringConstraint::NotInRegex { regex, .. } => {
                        negative.push(regex.clone());
                    }
                    _ => {}
                }
            }

            // Intersect all positive constraints
            let mut result = if positive.is_empty() {
                Regex::Star(Box::new(Regex::CharClass(self.all_chars())))
            } else if positive.len() == 1 {
                positive[0].clone()
            } else {
                self.stats.regex_intersections += 1;
                Regex::Intersection(positive)
            };

            // Subtract negative constraints
            for neg in negative {
                self.stats.regex_complements += 1;
                result = Regex::Intersection(vec![result, Regex::Complement(Box::new(neg))]);
            }

            combined.insert(var, result);
        }

        Ok(combined)
    }

    /// Find satisfying strings for combined regexes
    fn find_satisfying_strings(
        &mut self,
        regexes: &FxHashMap<StrVar, Regex>,
    ) -> Result<Option<StringSolution>, String> {
        let mut assignment = FxHashMap::default();

        for (&var, regex) in regexes {
            // Get length bounds
            let (min_len, max_len) = self
                .length_bounds
                .get(&var)
                .copied()
                .unwrap_or((Some(0), Some(self.config.max_string_length)));

            // Generate a satisfying string
            if let Some(string) = self.generate_string(regex, min_len, max_len)? {
                assignment.insert(var, string);
            } else {
                // No satisfying string found
                return Ok(None);
            }
        }

        Ok(Some(StringSolution { assignment }))
    }

    /// Generate a string that matches the regex within length bounds
    fn generate_string(
        &self,
        regex: &Regex,
        min_len: Option<usize>,
        max_len: Option<usize>,
    ) -> Result<Option<String>, String> {
        let min = min_len.unwrap_or(0);
        let max = max_len.unwrap_or(self.config.max_string_length);

        // Try lengths from min to max
        for length in min..=max {
            if let Some(string) = self.generate_string_of_length(regex, length, 0)? {
                return Ok(Some(string));
            }
        }

        Ok(None)
    }

    /// Generate a string of specific length matching regex
    fn generate_string_of_length(
        &self,
        regex: &Regex,
        length: usize,
        depth: usize,
    ) -> Result<Option<String>, String> {
        if depth > MAX_REGEX_SEARCH_DEPTH {
            return Err(depth_budget_error("string generation"));
        }
        match regex {
            Regex::Empty => Ok(None),
            Regex::Epsilon if length == 0 => Ok(Some(String::new())),
            Regex::Epsilon => Ok(None),
            Regex::Char(c) if length == 1 => Ok(Some(c.to_string())),
            Regex::Char(_) => Ok(None),
            Regex::CharClass(chars) if length == 1 => {
                Ok(chars.iter().next().map(|c| c.to_string()))
            }
            Regex::CharClass(_) => Ok(None),
            Regex::Concat(parts) => self.generate_concat(parts, length, depth + 1),
            Regex::Union(parts) => {
                // Try each alternative
                for part in parts {
                    if let Some(s) = self.generate_string_of_length(part, length, depth + 1)? {
                        return Ok(Some(s));
                    }
                }
                Ok(None)
            }
            Regex::Star(inner) => self.generate_star(inner, length, depth + 1),
            _ => {
                // Simplified handling for other cases
                Ok(Some("a".repeat(length)))
            }
        }
    }

    /// Generate string for concatenation
    fn generate_concat(
        &self,
        parts: &[Regex],
        length: usize,
        depth: usize,
    ) -> Result<Option<String>, String> {
        // Distribute length among parts
        if parts.is_empty() {
            return Ok(if length == 0 {
                Some(String::new())
            } else {
                None
            });
        }

        // Simple strategy: try to divide length evenly
        self.generate_concat_recursive(parts, length, 0, depth)
    }

    /// Recursive helper for concatenation
    fn generate_concat_recursive(
        &self,
        parts: &[Regex],
        remaining_length: usize,
        part_idx: usize,
        depth: usize,
    ) -> Result<Option<String>, String> {
        if depth > MAX_REGEX_SEARCH_DEPTH {
            return Err(depth_budget_error("string generation"));
        }
        if part_idx >= parts.len() {
            return Ok(if remaining_length == 0 {
                Some(String::new())
            } else {
                None
            });
        }

        // Try different lengths for current part
        for len in 0..=remaining_length {
            if let Some(part_str) =
                self.generate_string_of_length(&parts[part_idx], len, depth + 1)?
                && let Some(rest_str) = self.generate_concat_recursive(
                    parts,
                    remaining_length - len,
                    part_idx + 1,
                    depth + 1,
                )?
            {
                return Ok(Some(format!("{}{}", part_str, rest_str)));
            }
        }

        Ok(None)
    }

    /// Generate string for star
    fn generate_star(
        &self,
        inner: &Regex,
        length: usize,
        depth: usize,
    ) -> Result<Option<String>, String> {
        if depth > MAX_REGEX_SEARCH_DEPTH {
            return Err(depth_budget_error("string generation"));
        }
        if length == 0 {
            return Ok(Some(String::new()));
        }

        // Get possible lengths for inner regex
        let (min_inner, _max_inner) = self.regex_length_bounds(inner).unwrap_or((1, Some(1)));

        // Try different repetition counts
        for count in 1..=(length / min_inner.max(1)) {
            let target_len = length / count;
            if let Some(inner_str) = self.generate_string_of_length(inner, target_len, depth + 1)? {
                let result = inner_str.repeat(count);
                if result.len() == length {
                    return Ok(Some(result));
                }
            }
        }

        Ok(None)
    }

    /// Test if a string matches a regex
    pub fn test_membership(&mut self, string: &str, regex: &Regex) -> Result<bool, String> {
        self.test_membership_within(string, regex, 0)
    }

    /// [`Self::test_membership`] with the remaining search budget threaded
    /// through.
    fn test_membership_within(
        &mut self,
        string: &str,
        regex: &Regex,
        depth: usize,
    ) -> Result<bool, String> {
        if depth > MAX_REGEX_SEARCH_DEPTH {
            return Err(depth_budget_error("regex membership test"));
        }
        self.stats.membership_tests += 1;

        match regex {
            Regex::Empty => Ok(false),
            Regex::Epsilon => Ok(string.is_empty()),
            // `len()` counts *bytes*: `str.len() == 1` rejected every
            // non-ASCII single character, so `あ` was not a member of the
            // regex `あ`. A regex matches characters.
            Regex::Char(c) => {
                let mut chars = string.chars();
                Ok(chars.next() == Some(*c) && chars.next().is_none())
            }
            Regex::CharClass(class) => {
                let mut chars = string.chars();
                Ok(chars.next().is_some_and(|c| class.contains(&c)) && chars.next().is_none())
            }
            Regex::Concat(parts) => self.test_concat(string, parts, depth + 1),
            Regex::Union(parts) => {
                for part in parts {
                    if self.test_membership_within(string, part, depth + 1)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Regex::Star(inner) => self.test_star(string, inner, depth + 1),
            Regex::Complement(inner) => {
                Ok(!self.test_membership_within(string, inner, depth + 1)?)
            }
            Regex::Intersection(parts) => {
                for part in parts {
                    if !self.test_membership_within(string, part, depth + 1)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            // `Optional`/`Plus`/`Repeat`/`RepeatRange` used to fall into a
            // `_ => Ok(true)` arm, i.e. every string was reported as a member
            // of them. That is not a simplification, it is a wrong answer with
            // no way for the caller to tell. They are rewritten into the
            // operators this procedure does implement.
            Regex::Optional(inner) => {
                if string.is_empty() {
                    return Ok(true);
                }
                self.test_membership_within(string, inner, depth + 1)
            }
            Regex::Plus(inner) => {
                if string.is_empty() {
                    return Ok(false);
                }
                self.test_concat(
                    string,
                    &[(**inner).clone(), Regex::Star(inner.clone())],
                    depth + 1,
                )
            }
            Regex::Repeat { regex, count } => {
                let parts = vec![(**regex).clone(); *count];
                self.test_concat(string, &parts, depth + 1)
            }
            Regex::RepeatRange { regex, min, max } => {
                let tail = match max {
                    Some(m) => {
                        let extra = m.saturating_sub(*min);
                        vec![Regex::Optional(regex.clone()); extra]
                    }
                    None => vec![Regex::Star(regex.clone())],
                };
                let mut parts = vec![(**regex).clone(); *min];
                parts.extend(tail);
                self.test_concat(string, &parts, depth + 1)
            }
        }
    }

    /// Test concatenation
    fn test_concat(&mut self, string: &str, parts: &[Regex], depth: usize) -> Result<bool, String> {
        self.test_concat_recursive(string, parts, 0, depth)
    }

    /// Recursive helper for concatenation testing
    fn test_concat_recursive(
        &mut self,
        string: &str,
        parts: &[Regex],
        part_idx: usize,
        depth: usize,
    ) -> Result<bool, String> {
        if depth > MAX_REGEX_SEARCH_DEPTH {
            return Err(depth_budget_error("regex membership test"));
        }
        if part_idx >= parts.len() {
            return Ok(string.is_empty());
        }

        // Try all possible splits.
        //
        // `split_at` panics unless the index is a UTF-8 character boundary, so
        // iterating raw byte indices made every multi-byte character in the
        // subject abort the process (release builds are `panic = "abort"`).
        // Splitting anywhere else is meaningless anyway: a regex matches
        // characters, not half a code point.
        for split_pos in 0..=string.len() {
            if !string.is_char_boundary(split_pos) {
                continue;
            }
            let (prefix, suffix) = string.split_at(split_pos);

            if self.test_membership_within(prefix, &parts[part_idx], depth + 1)?
                && self.test_concat_recursive(suffix, parts, part_idx + 1, depth + 1)?
            {
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Test star
    fn test_star(&mut self, string: &str, inner: &Regex, depth: usize) -> Result<bool, String> {
        if depth > MAX_REGEX_SEARCH_DEPTH {
            return Err(depth_budget_error("regex membership test"));
        }
        if string.is_empty() {
            return Ok(true);
        }

        // Try all possible repetitions. See `test_concat_recursive` for why
        // non-character-boundary indices are skipped rather than passed to
        // `split_at`.
        for end in 1..=string.len() {
            if !string.is_char_boundary(end) {
                continue;
            }
            let (prefix, suffix) = string.split_at(end);

            if self.test_membership_within(prefix, inner, depth + 1)?
                && self.test_star(suffix, inner, depth + 1)?
            {
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Get all characters (placeholder)
    fn all_chars(&self) -> FxHashSet<char> {
        ('a'..='z').chain('A'..='Z').chain('0'..='9').collect()
    }

    /// Get statistics
    pub fn stats(&self) -> &RegexSolverStats {
        &self.stats
    }

    /// Reset solver
    pub fn reset(&mut self) {
        self.constraints.clear();
        self.length_bounds.clear();
    }
}

/// Length bounds of one regex: `(min, max)`, `max == None` meaning unbounded.
type LengthBounds = Option<(usize, Option<usize>)>;

/// One step of the iterative [`Regex`] length-bounds fold.
enum BoundsTask<'a> {
    /// Expand a node's operands.
    Enter(&'a Regex),
    /// Combine a node's operand bounds.
    Reduce(&'a Regex),
}

/// Task stack plus the operand bounds computed so far.
#[derive(Default)]
struct BoundsState<'a> {
    /// Pending work, innermost operand on top.
    tasks: Vec<BoundsTask<'a>>,
    /// Bounds of finished operands, in evaluation order.
    results: Vec<LengthBounds>,
}

impl BoundsState<'_> {
    /// Detach the last `count` operand bounds, oldest first.
    fn take(&mut self, count: usize) -> Vec<LengthBounds> {
        let at = self.results.len().saturating_sub(count);
        self.results.split_off(at)
    }
}

/// Queue the operands whose bounds `expr` actually consumes.
///
/// `Star`, `Complement` and `Intersection` answer without looking at their
/// operands, so those operands are deliberately not queued.
fn push_bounds_operands<'a>(expr: &'a Regex, tasks: &mut Vec<BoundsTask<'a>>) {
    match expr {
        Regex::Empty
        | Regex::Epsilon
        | Regex::Char(_)
        | Regex::CharClass(_)
        | Regex::Star(_)
        | Regex::Complement(_)
        | Regex::Intersection(_) => {}
        Regex::Concat(parts) | Regex::Union(parts) => {
            tasks.extend(parts.iter().rev().map(BoundsTask::Enter));
        }
        Regex::Plus(inner) | Regex::Optional(inner) => {
            tasks.push(BoundsTask::Enter(inner));
        }
        Regex::Repeat { regex, .. } | Regex::RepeatRange { regex, .. } => {
            tasks.push(BoundsTask::Enter(regex));
        }
    }
}

/// Combine the already-computed operand bounds of one node.
fn reduce_bounds(expr: &Regex, state: &mut BoundsState<'_>) -> LengthBounds {
    match expr {
        Regex::Empty => None,
        Regex::Epsilon => Some((0, Some(0))),
        Regex::Char(_) | Regex::CharClass(_) => Some((1, Some(1))),
        Regex::Concat(parts) => {
            let mut min: usize = 0;
            let mut max = Some(0usize);

            for part_bounds in state.take(parts.len()) {
                let (part_min, part_max) = part_bounds?;
                // Overflow means the bound is not representable, which
                // is reported as "no bound known" (`None`) rather than
                // wrapped into a small – and therefore wrong – bound.
                min = min.checked_add(part_min)?;
                max = match (max, part_max) {
                    (Some(m), Some(pm)) => m.checked_add(pm),
                    _ => None,
                };
            }

            Some((min, max))
        }
        Regex::Union(parts) => {
            let bounds: Vec<_> = state.take(parts.len()).into_iter().flatten().collect();

            let min = bounds.iter().map(|(m, _)| *m).min()?;
            let max = bounds.iter().filter_map(|(_, m)| *m).max();

            Some((min, max))
        }
        Regex::Star(_) => Some((0, None)),
        Regex::Plus(_) => state.take(1).pop()?.map(|(min, _)| (min, None)),
        Regex::Optional(_) => state.take(1).pop()?.map(|(_, max)| (0, max)),
        // `{4294967295}` nested twice overflows these products; an
        // unchecked `*` wrapped (release builds have overflow checks off)
        // into a bound far smaller than the truth, which then wrongly
        // constrained the variable's length. Overflow now yields "no bound
        // known" instead.
        Regex::Repeat { count, .. } => {
            let (min, max) = state.take(1).pop()??;
            Some((
                min.checked_mul(*count)?,
                max.and_then(|m| m.checked_mul(*count)),
            ))
        }
        Regex::RepeatRange {
            min: min_rep,
            max: max_rep,
            ..
        } => {
            let (min, max) = state.take(1).pop()??;
            let min_len = min.checked_mul(*min_rep)?;
            let max_len = max_rep.and_then(|mr| max.and_then(|m| m.checked_mul(mr)));
            Some((min_len, max_len))
        }
        Regex::Complement(_) | Regex::Intersection(_) => Some((0, None)),
    }
}

/// Dismantling worklist entry for [`Regex`]'s iterative [`Drop`].
enum RegexSolverDropNode {
    /// A boxed operand.
    Boxed(Box<Regex>),
    /// A list of operands.
    List(Vec<Regex>),
}

/// Move `regex`'s operands onto `out`, leaving a childless node behind.
///
/// Operands are swapped out one field at a time: [`Regex`] implements [`Drop`],
/// so its fields cannot be moved out wholesale.
fn take_regex_solver_children(regex: &mut Regex, out: &mut Vec<RegexSolverDropNode>) {
    /// A childless stand-in, dropped immediately and never observed.
    fn placeholder() -> Box<Regex> {
        Box::new(Regex::Epsilon)
    }
    match regex {
        Regex::Empty | Regex::Epsilon | Regex::Char(_) | Regex::CharClass(_) => {}
        Regex::Concat(parts) | Regex::Union(parts) | Regex::Intersection(parts) => {
            out.push(RegexSolverDropNode::List(core::mem::take(parts)));
        }
        Regex::Star(inner)
        | Regex::Complement(inner)
        | Regex::Optional(inner)
        | Regex::Plus(inner) => {
            out.push(RegexSolverDropNode::Boxed(core::mem::replace(
                inner,
                placeholder(),
            )));
        }
        Regex::Repeat { regex, .. } | Regex::RepeatRange { regex, .. } => {
            out.push(RegexSolverDropNode::Boxed(core::mem::replace(
                regex,
                placeholder(),
            )));
        }
    }
}

impl Drop for Regex {
    /// Dismantle the operand tree iteratively.
    ///
    /// Compiler-generated drop glue recurses once per nesting level, so a
    /// regex deep enough to build is deep enough to abort the process at scope
    /// exit, after it has already been solved against successfully.
    fn drop(&mut self) {
        let mut worklist: Vec<RegexSolverDropNode> = Vec::new();
        take_regex_solver_children(self, &mut worklist);
        while let Some(node) = worklist.pop() {
            match node {
                RegexSolverDropNode::Boxed(mut inner) => {
                    take_regex_solver_children(&mut inner, &mut worklist);
                }
                RegexSolverDropNode::List(parts) => {
                    for mut part in parts {
                        take_regex_solver_children(&mut part, &mut worklist);
                    }
                }
            }
        }
    }
}

/// The shape of a node being rebuilt by the iterative [`Clone`] impl: which
/// variant it is, plus anything that is not the cloned child(ren).
enum RegexSolverCloneShape {
    /// `Concat` with the given arity.
    Concat(usize),
    /// `Union` with the given arity.
    Union(usize),
    /// `Intersection` with the given arity.
    Intersection(usize),
    /// `Star`, one child.
    Star,
    /// `Complement`, one child.
    Complement,
    /// `Optional`, one child.
    Optional,
    /// `Plus`, one child.
    Plus,
    /// `Repeat`, one child plus its exact count.
    Repeat(usize),
    /// `RepeatRange`, one child plus its bounds.
    RepeatRange(usize, Option<usize>),
}

/// Work item for the iterative [`Clone`] impl.
enum RegexSolverCloneTask<'a> {
    /// Clone this subterm.
    Visit(&'a Regex),
    /// Rebuild a node from the already-cloned children on the result stack.
    Rebuild(RegexSolverCloneShape),
}

impl Clone for Regex {
    /// Iterative clone.
    ///
    /// The derived recursive `Clone` walked the operand tree with one native
    /// call frame per nesting level -- the same hazard the [`Drop`] impl
    /// above exists to avoid, just triggered by a different standard-library
    /// entry point (`.clone()` / `#[derive(Clone)]` callers).
    fn clone(&self) -> Self {
        /// Detach the top `n` results, preserving their original order.
        fn take(results: &mut Vec<Regex>, n: usize) -> Vec<Regex> {
            let start = results.len().saturating_sub(n);
            results.split_off(start)
        }

        /// Rebuild a one-child node, or fall back to `Epsilon` if starved.
        fn one(results: &mut Vec<Regex>) -> Box<Regex> {
            let mut operand = take(results, 1);
            Box::new(operand.pop().unwrap_or(Regex::Epsilon))
        }

        let mut tasks = vec![RegexSolverCloneTask::Visit(self)];
        let mut results: Vec<Self> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                RegexSolverCloneTask::Visit(node) => match node {
                    Self::Empty => results.push(Self::Empty),
                    Self::Epsilon => results.push(Self::Epsilon),
                    Self::Char(c) => results.push(Self::Char(*c)),
                    Self::CharClass(set) => results.push(Self::CharClass(set.clone())),
                    Self::Concat(parts) => {
                        tasks.push(RegexSolverCloneTask::Rebuild(
                            RegexSolverCloneShape::Concat(parts.len()),
                        ));
                        tasks.extend(parts.iter().rev().map(RegexSolverCloneTask::Visit));
                    }
                    Self::Union(parts) => {
                        tasks.push(RegexSolverCloneTask::Rebuild(RegexSolverCloneShape::Union(
                            parts.len(),
                        )));
                        tasks.extend(parts.iter().rev().map(RegexSolverCloneTask::Visit));
                    }
                    Self::Intersection(parts) => {
                        tasks.push(RegexSolverCloneTask::Rebuild(
                            RegexSolverCloneShape::Intersection(parts.len()),
                        ));
                        tasks.extend(parts.iter().rev().map(RegexSolverCloneTask::Visit));
                    }
                    Self::Star(inner) => {
                        tasks.push(RegexSolverCloneTask::Rebuild(RegexSolverCloneShape::Star));
                        tasks.push(RegexSolverCloneTask::Visit(inner));
                    }
                    Self::Complement(inner) => {
                        tasks.push(RegexSolverCloneTask::Rebuild(
                            RegexSolverCloneShape::Complement,
                        ));
                        tasks.push(RegexSolverCloneTask::Visit(inner));
                    }
                    Self::Optional(inner) => {
                        tasks.push(RegexSolverCloneTask::Rebuild(
                            RegexSolverCloneShape::Optional,
                        ));
                        tasks.push(RegexSolverCloneTask::Visit(inner));
                    }
                    Self::Plus(inner) => {
                        tasks.push(RegexSolverCloneTask::Rebuild(RegexSolverCloneShape::Plus));
                        tasks.push(RegexSolverCloneTask::Visit(inner));
                    }
                    Self::Repeat { regex, count } => {
                        tasks.push(RegexSolverCloneTask::Rebuild(
                            RegexSolverCloneShape::Repeat(*count),
                        ));
                        tasks.push(RegexSolverCloneTask::Visit(regex));
                    }
                    Self::RepeatRange { regex, min, max } => {
                        tasks.push(RegexSolverCloneTask::Rebuild(
                            RegexSolverCloneShape::RepeatRange(*min, *max),
                        ));
                        tasks.push(RegexSolverCloneTask::Visit(regex));
                    }
                },
                RegexSolverCloneTask::Rebuild(shape) => {
                    let rebuilt = match shape {
                        RegexSolverCloneShape::Concat(n) => Self::Concat(take(&mut results, n)),
                        RegexSolverCloneShape::Union(n) => Self::Union(take(&mut results, n)),
                        RegexSolverCloneShape::Intersection(n) => {
                            Self::Intersection(take(&mut results, n))
                        }
                        RegexSolverCloneShape::Star => Self::Star(one(&mut results)),
                        RegexSolverCloneShape::Complement => Self::Complement(one(&mut results)),
                        RegexSolverCloneShape::Optional => Self::Optional(one(&mut results)),
                        RegexSolverCloneShape::Plus => Self::Plus(one(&mut results)),
                        RegexSolverCloneShape::Repeat(count) => Self::Repeat {
                            regex: one(&mut results),
                            count,
                        },
                        RegexSolverCloneShape::RepeatRange(min, max) => Self::RepeatRange {
                            regex: one(&mut results),
                            min,
                            max,
                        },
                    };
                    results.push(rebuilt);
                }
            }
        }

        results.pop().unwrap_or(Self::Epsilon)
    }
}

impl PartialEq for Regex {
    /// Iterative structural equality.
    ///
    /// The derived `PartialEq` walked both regexes with one native call frame
    /// per nesting level, mirroring the [`Clone`]/[`Drop`] hazard above. The
    /// pairs still to be compared live on the heap instead; the relation
    /// itself is unchanged. As in `InterpolantTerm`
    /// (`oxiz-proof/src/craig/term.rs`), the outer `match` is exhaustive over
    /// `self`'s variants on purpose: a new variant is a compile error here,
    /// not a silent "not equal".
    fn eq(&self, other: &Self) -> bool {
        /// Queue every positional child pair, left to right.
        fn push_all<'a>(
            worklist: &mut Vec<(&'a Regex, &'a Regex)>,
            lhs: &'a [Regex],
            rhs: &'a [Regex],
        ) {
            worklist.extend(lhs.iter().zip(rhs.iter()).rev());
        }

        let mut worklist = vec![(self, other)];

        while let Some((a, b)) = worklist.pop() {
            match a {
                Self::Empty => {
                    if !matches!(b, Self::Empty) {
                        return false;
                    }
                }
                Self::Epsilon => {
                    if !matches!(b, Self::Epsilon) {
                        return false;
                    }
                }
                Self::Char(x) => {
                    let Self::Char(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                Self::CharClass(x) => {
                    let Self::CharClass(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                Self::Concat(xs) => {
                    let Self::Concat(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Union(xs) => {
                    let Self::Union(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Intersection(xs) => {
                    let Self::Intersection(ys) = b else {
                        return false;
                    };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Star(x) => {
                    let Self::Star(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Complement(x) => {
                    let Self::Complement(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Optional(x) => {
                    let Self::Optional(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Plus(x) => {
                    let Self::Plus(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Repeat { regex: x, count: n } => {
                    let Self::Repeat { regex: y, count: m } = b else {
                        return false;
                    };
                    if n != m {
                        return false;
                    }
                    worklist.push((x, y));
                }
                Self::RepeatRange {
                    regex: x,
                    min: min1,
                    max: max1,
                } => {
                    let Self::RepeatRange {
                        regex: y,
                        min: min2,
                        max: max2,
                    } = b
                    else {
                        return false;
                    };
                    if min1 != min2 || max1 != max2 {
                        return false;
                    }
                    worklist.push((x, y));
                }
            }
        }

        true
    }
}

impl Eq for Regex {}

#[cfg(test)]
mod tests {
    use super::*;

    /// The stack the small-stack regressions below run on: a scaled-down model
    /// of an embedder's worker thread.
    ///
    /// This constant and [`DEEP_NESTING`] are scaled **together**, and only
    /// their ratio -- about 21 bytes of stack per nesting level -- decides what
    /// those tests detect. A recursive walk needs tens of bytes per frame at
    /// the very least, so it still overflows; an iterative one uses O(1) native
    /// stack, so it still returns. Never raise one without the other.
    const WORKER_STACK: usize = 1 << 17;

    /// Nesting depth paired with [`WORKER_STACK`].
    const DEEP_NESTING: usize = 12_500;

    /// Build `Optional(Optional(... Char(c) ...))` nested `depth` levels deep.
    fn nested_optionals(depth: usize, c: char) -> Regex {
        let mut regex = Regex::Char(c);
        for _ in 0..depth {
            regex = Regex::Optional(Box::new(regex));
        }
        regex
    }

    #[test]
    fn test_length_bounds_deeply_nested_small_stack() {
        // `regex_length_bounds` returns `Option`, whose `None` means "no bound
        // known" -- a depth cap would silently loosen a length constraint
        // instead of reporting a problem, so it uses an explicit stack. Run on
        // a deliberately small (128 KiB) stack: a stack overflow aborts the
        // process, so "the thread returned at all" is part of the assertion.
        // Dropping the regex afterwards exercises the iterative `Drop`.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let solver = RegexSolver::new(RegexSolverConfig::default());
                let regex = nested_optionals(DEEP_NESTING, 'a');
                assert_eq!(solver.regex_length_bounds(&regex), Some((0, Some(1))));

                let concat = Regex::Concat(vec![regex, Regex::Char('b')]);
                assert_eq!(solver.regex_length_bounds(&concat), Some((1, Some(2))));
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deeply nested regex must not overflow a 128 KiB stack");
    }

    #[test]
    fn test_length_bounds_empty_language_and_union() {
        // Semantic pins for the rewritten fold: `Empty` has no bounds and
        // poisons a concatenation, while a union skips its unbounded branches.
        let solver = RegexSolver::new(RegexSolverConfig::default());
        assert_eq!(solver.regex_length_bounds(&Regex::Empty), None);
        assert_eq!(
            solver.regex_length_bounds(&Regex::Concat(vec![Regex::Char('a'), Regex::Empty])),
            None
        );
        assert_eq!(
            solver.regex_length_bounds(&Regex::Union(vec![Regex::Empty, Regex::Empty])),
            None
        );
        assert_eq!(
            solver.regex_length_bounds(&Regex::Union(vec![
                Regex::Char('a'),
                Regex::Concat(vec![Regex::Char('a'), Regex::Char('b')]),
            ])),
            Some((1, Some(2)))
        );
    }

    #[test]
    fn test_membership_reports_exhausted_budget_as_error() {
        // The backtracking membership procedure keeps an honest search budget:
        // when it runs out it returns `Err`, never a `false` that the caller
        // could not tell apart from a genuine "not a member".
        let mut solver = RegexSolver::new(RegexSolverConfig::default());
        let deep = nested_optionals(MAX_REGEX_SEARCH_DEPTH + 10, 'a');
        let result = solver.test_membership("a", &deep);
        match result {
            Err(message) => assert!(message.contains("maximum search depth")),
            Ok(value) => panic!("expected a budget error, got Ok({})", value),
        }
    }

    #[test]
    fn test_membership_within_budget_is_still_exact() {
        // Just under the budget the answer must be the real one.
        let mut solver = RegexSolver::new(RegexSolverConfig::default());
        let shallow = nested_optionals(8, 'a');
        assert_eq!(solver.test_membership("a", &shallow), Ok(true));
        assert_eq!(solver.test_membership("b", &shallow), Ok(false));
    }

    #[test]
    fn test_deeply_nested_regex_drop_small_stack() {
        // Compiler-generated drop glue recurses once per level; the explicit
        // `Drop` dismantles the tree with a worklist instead.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let regex = Regex::Union(vec![
                    nested_optionals(DEEP_NESTING, 'a'),
                    Regex::Star(Box::new(nested_optionals(DEEP_NESTING, 'b'))),
                ]);
                drop(regex);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("dropping a deeply nested regex must not overflow a 128 KiB stack");
    }

    #[test]
    fn test_deep_clone_eq_and_drop_small_stack() {
        // The derived recursive `Clone`/`PartialEq` were the last remaining
        // native-stack walks over this type once `Drop` was made iterative;
        // both would overflow on a regex deep enough to build. Run on a
        // deliberately small (128 KiB) stack: a stack overflow aborts the
        // process, so "the thread returned at all" is part of the assertion.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let regex = nested_optionals(DEEP_NESTING, 'a');
                let cloned = regex.clone();

                assert_eq!(regex, cloned);

                drop(regex);
                drop(cloned);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle.join().expect(
            "cloning, comparing and dropping a deeply nested regex must not overflow a 128 KiB stack",
        );
    }

    #[test]
    fn test_solver_creation() {
        let config = RegexSolverConfig::default();
        let solver = RegexSolver::new(config);
        assert_eq!(solver.stats.constraints_solved, 0);
    }

    #[test]
    fn test_epsilon_membership() {
        let config = RegexSolverConfig::default();
        let mut solver = RegexSolver::new(config);

        let result = solver
            .test_membership("", &Regex::Epsilon)
            .expect("regex compilation failed");
        assert!(result);

        let result2 = solver
            .test_membership("a", &Regex::Epsilon)
            .expect("regex compilation failed");
        assert!(!result2);
    }

    #[test]
    fn test_char_membership() {
        let config = RegexSolverConfig::default();
        let mut solver = RegexSolver::new(config);

        let regex = Regex::Char('a');
        assert!(
            solver
                .test_membership("a", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            !solver
                .test_membership("b", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            !solver
                .test_membership("aa", &regex)
                .expect("regex compilation failed")
        );
    }

    #[test]
    fn test_union_membership() {
        let config = RegexSolverConfig::default();
        let mut solver = RegexSolver::new(config);

        let regex = Regex::Union(vec![Regex::Char('a'), Regex::Char('b')]);

        assert!(
            solver
                .test_membership("a", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            solver
                .test_membership("b", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            !solver
                .test_membership("c", &regex)
                .expect("regex compilation failed")
        );
    }

    #[test]
    fn test_concat_membership() {
        let config = RegexSolverConfig::default();
        let mut solver = RegexSolver::new(config);

        let regex = Regex::Concat(vec![Regex::Char('a'), Regex::Char('b')]);

        assert!(
            solver
                .test_membership("ab", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            !solver
                .test_membership("a", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            !solver
                .test_membership("ba", &regex)
                .expect("regex compilation failed")
        );
    }

    #[test]
    fn test_star_membership() {
        let config = RegexSolverConfig::default();
        let mut solver = RegexSolver::new(config);

        let regex = Regex::Star(Box::new(Regex::Char('a')));

        assert!(
            solver
                .test_membership("", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            solver
                .test_membership("a", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            solver
                .test_membership("aa", &regex)
                .expect("regex compilation failed")
        );
        assert!(
            !solver
                .test_membership("ab", &regex)
                .expect("regex compilation failed")
        );
    }

    #[test]
    fn test_length_bounds_epsilon() {
        let solver = RegexSolver::new(RegexSolverConfig::default());

        let bounds = solver.regex_length_bounds(&Regex::Epsilon);
        assert_eq!(bounds, Some((0, Some(0))));
    }

    #[test]
    fn test_length_bounds_char() {
        let solver = RegexSolver::new(RegexSolverConfig::default());

        let bounds = solver.regex_length_bounds(&Regex::Char('a'));
        assert_eq!(bounds, Some((1, Some(1))));
    }

    #[test]
    fn test_length_bounds_concat() {
        let solver = RegexSolver::new(RegexSolverConfig::default());

        let regex = Regex::Concat(vec![Regex::Char('a'), Regex::Char('b'), Regex::Char('c')]);
        let bounds = solver.regex_length_bounds(&regex);
        assert_eq!(bounds, Some((3, Some(3))));
    }

    #[test]
    fn test_length_bounds_star() {
        let solver = RegexSolver::new(RegexSolverConfig::default());

        let regex = Regex::Star(Box::new(Regex::Char('a')));
        let bounds = solver.regex_length_bounds(&regex);
        assert_eq!(bounds, Some((0, None)));
    }

    #[test]
    fn test_add_constraint() {
        let mut solver = RegexSolver::new(RegexSolverConfig::default());

        solver.add_constraint(StringConstraint::InRegex {
            var: 0,
            regex: Regex::Char('a'),
        });

        assert_eq!(solver.constraints.get(&0).map(|v| v.len()), Some(1));
    }

    #[test]
    fn test_reset() {
        let mut solver = RegexSolver::new(RegexSolverConfig::default());

        solver.add_constraint(StringConstraint::InRegex {
            var: 0,
            regex: Regex::Char('a'),
        });

        solver.reset();

        assert!(solver.constraints.is_empty());
        assert!(solver.length_bounds.is_empty());
    }
}

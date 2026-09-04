//! Regular-expression membership: AST compilation and model construction.
//!
//! This module bridges the SMT-LIB Strings regex sublanguage (parsed into
//! `RegLan`-sorted `Apply` nodes by the core parser) and the Brzozowski
//! derivative engine in `super::regex`. It provides:
//!
//! - [`compile_regex`]: turn a ground regex AST subterm (the second operand of
//!   `str.in_re`, or any `re.*` node) into a compiled [`Regex`]. Non-ground
//!   regexes (containing string variables) yield `None`, so callers can report
//!   an honest `Unknown` rather than an unsound result.
//! - [`search_word`]: given a compiled regex (typically the intersection of a
//!   variable's positive memberships and the complements of its negative
//!   memberships, together with any length bounds), decide whether the language
//!   is non-empty and, if so, return the shortest accepted word – the concrete
//!   witness used to build a satisfying string model.
//!
//! The search is a breadth-first exploration of the finite Brzozowski
//! derivative automaton over a *representative alphabet* extracted from the
//! regex: every character/range endpoint (and the code point immediately after
//! it) plus one "fresh" character outside every explicit set. That set contains
//! a representative of every derivative equivalence class, so exhausting the
//! reachable state space without reaching an accepting state is a sound proof
//! that the language is empty (used to refute unsatisfiable memberships and
//! empty intersections).

use super::regex::{Regex, RegexOp};
#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};

/// Outcome of a shortest-accepted-word search over a compiled regex.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WordSearch {
    /// A concrete accepted word (the shortest one satisfying the length bounds).
    Found(String),
    /// The language is provably empty (no accepted word exists within the
    /// requested length bounds). Sound only when the representative alphabet is
    /// complete (no opaque Unicode-class atoms).
    Empty,
    /// The search could not decide within its resource bounds (state/length
    /// cap hit, or the alphabet is incomplete). Callers must treat this as an
    /// honest `Unknown`, never as `Sat` or `Unsat`.
    Unknown,
}

/// A single membership constraint on one string variable:
/// `(positive, compiled regex, origin term)`. `positive = false` means the
/// variable must NOT be in the language.
pub type Membership = (bool, Arc<Regex>, TermId);

/// Result of trying to build a concrete value for one variable from its
/// membership (and length) constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarModel {
    /// A concrete witness string satisfying every membership and length bound.
    Assign(String),
    /// The combined language is provably empty – the memberships are jointly
    /// unsatisfiable. Carries the explaining origin terms.
    Conflict(Vec<TermId>),
    /// Undecided within the search bounds; caller must report `Unknown`.
    Undecided,
}

/// Search-resource bounds shared by the string theory's model construction.
const MAX_REGEX_STATES: usize = 4000;
const MAX_REGEX_WORD_LEN: usize = 4096;

/// Build a satisfying value for one variable from all of its memberships
/// (positive as-is, negative complemented) intersected together, subject to the
/// length window `[len_lo, len_hi]`. `extra_origins` (e.g. the length
/// constraints' origins) are appended to a conflict explanation.
pub fn solve_membership(
    memberships: &[Membership],
    len_lo: usize,
    len_hi: Option<usize>,
    extra_origins: &[TermId],
) -> VarModel {
    let parts: Vec<Arc<Regex>> = memberships
        .iter()
        .map(|(positive, regex, _origin)| {
            if *positive {
                regex.clone()
            } else {
                Regex::complement(regex.clone())
            }
        })
        .collect();
    let combined = Regex::inter(parts);
    match search_word(
        &combined,
        len_lo,
        len_hi,
        MAX_REGEX_STATES,
        MAX_REGEX_WORD_LEN,
    ) {
        WordSearch::Found(word) => VarModel::Assign(word),
        WordSearch::Empty => {
            let mut origins: Vec<TermId> = memberships.iter().map(|(_, _, o)| *o).collect();
            origins.extend_from_slice(extra_origins);
            VarModel::Conflict(origins)
        }
        WordSearch::Unknown => VarModel::Undecided,
    }
}

/// Compile a ground regex AST subterm into a [`Regex`].
///
/// Returns `None` if the subterm is not a recognised regex operator or is
/// *non-ground* (mentions a string variable, e.g. `(str.to_re x)` with `x` a
/// variable), in which case the theory must fall back to `Unknown`.
pub fn compile_regex(manager: &TermManager, term: TermId) -> Option<Arc<Regex>> {
    // The walk is an explicit post-order stack, not recursion: regex nesting
    // (`(re.* (re.* (re.++ …)))`, `re.comp`, `re.inter`, `re.diff`, `re.loop`)
    // is entirely input-controlled and this is reached from `check_sat` via the
    // `StrInRe` evaluator arm. A shared sub-regex is compiled once and reused
    // (`memo`), so a `let`-shared regex DAG cannot re-expand exponentially.
    let mut memo: FxHashMap<TermId, Arc<Regex>> = FxHashMap::default();
    let mut frames: Vec<CompileFrame> = match open_regex(manager, term)? {
        CompileOpened::Leaf(r) => {
            return Some(r);
        }
        CompileOpened::Frame(f) => vec![f],
    };
    let mut carry: Option<Arc<Regex>> = None;

    while !frames.is_empty() {
        let next = match frames.last_mut() {
            Some(top) => {
                if let Some(r) = carry.take() {
                    top.done.push(r);
                }
                top.pending.pop()
            }
            // Unreachable: the loop condition just checked non-emptiness.
            None => break,
        };
        match next {
            Some(child) => {
                if let Some(hit) = memo.get(&child) {
                    carry = Some(hit.clone());
                    continue;
                }
                match open_regex(manager, child)? {
                    CompileOpened::Leaf(r) => {
                        memo.insert(child, r.clone());
                        carry = Some(r);
                    }
                    CompileOpened::Frame(f) => frames.push(f),
                }
            }
            None => match frames.pop() {
                Some(frame) => {
                    let key = frame.term;
                    let built = frame.finish();
                    memo.insert(key, built.clone());
                    carry = Some(built);
                }
                // Unreachable for the same reason as above.
                None => break,
            },
        }
    }

    carry
}

/// How a regex operator is rebuilt once its operands are compiled.
///
/// Every variant consumes the whole operand vector, so no arm has to assert
/// that a particular operand is present.
enum CompileBuild {
    /// `re.++`
    Concat,
    /// `re.union`
    Union,
    /// `re.inter`
    Inter,
    /// `re.*`; `Regex::union` of a single operand is that operand.
    Star,
    /// `re.+`
    Plus,
    /// `re.opt`
    Opt,
    /// `re.comp`
    Comp,
    /// `re.diff a b` = `a ∩ ¬b`: the last operand is complemented.
    Diff,
    /// `re.^` / `re.loop` with the already-decoded bounds.
    Loop(u32, Option<u32>),
}

/// One pending operator of the iterative regex compilation.
struct CompileFrame {
    /// The term this frame compiles; also its memo key.
    term: TermId,
    /// How to rebuild it.
    build: CompileBuild,
    /// Operand terms still to compile, reversed so `pop` yields them in order.
    pending: Vec<TermId>,
    /// Operands compiled so far, in operand order.
    done: Vec<Arc<Regex>>,
}

impl CompileFrame {
    /// Build this operator's regex from its compiled operands.
    fn finish(self) -> Arc<Regex> {
        match self.build {
            CompileBuild::Concat => Regex::concat(self.done),
            CompileBuild::Union => Regex::union(self.done),
            CompileBuild::Inter => Regex::inter(self.done),
            CompileBuild::Star => Regex::star(Regex::union(self.done)),
            CompileBuild::Plus => Regex::plus(Regex::union(self.done)),
            CompileBuild::Opt => Regex::option(Regex::union(self.done)),
            CompileBuild::Comp => Regex::complement(Regex::union(self.done)),
            CompileBuild::Diff => {
                let mut parts = self.done;
                if let Some(last) = parts.pop() {
                    parts.push(Regex::complement(last));
                }
                Regex::inter(parts)
            }
            CompileBuild::Loop(lo, hi) => Regex::loop_bounded(Regex::union(self.done), lo, hi),
        }
    }
}

/// What compiling one regex term needs: an answer already, or its operands.
enum CompileOpened {
    /// A nullary operator or a ground literal.
    Leaf(Arc<Regex>),
    /// An operator whose regex operands must be compiled first.
    Frame(CompileFrame),
}

/// Classify one regex term. `None` means "not a recognised, ground regex
/// operator", exactly as the recursive version's `?` did.
fn open_regex(manager: &TermManager, term: TermId) -> Option<CompileOpened> {
    let kind = &manager.get(term)?.kind;
    let TermKind::Apply { func, args } = kind else {
        return None;
    };
    let name = manager.resolve_str(*func);
    let leaf = |r: Arc<Regex>| Some(CompileOpened::Leaf(r));
    let frame = |build: CompileBuild, pending: Vec<TermId>| {
        Some(CompileOpened::Frame(CompileFrame {
            term,
            build,
            pending,
            done: Vec::new(),
        }))
    };
    match name {
        "re.none" => leaf(Regex::none()),
        "re.all" => leaf(Regex::all()),
        "re.allchar" => leaf(Regex::all_char()),
        "str.to_re" => {
            let s = const_string(manager, *args.first()?)?;
            leaf(Regex::literal(&s))
        }
        "re.++" => frame(CompileBuild::Concat, args.iter().rev().copied().collect()),
        "re.union" => frame(CompileBuild::Union, args.iter().rev().copied().collect()),
        "re.inter" => frame(CompileBuild::Inter, args.iter().rev().copied().collect()),
        "re.*" => frame(CompileBuild::Star, vec![*args.first()?]),
        "re.+" => frame(CompileBuild::Plus, vec![*args.first()?]),
        "re.opt" => frame(CompileBuild::Opt, vec![*args.first()?]),
        "re.comp" => frame(CompileBuild::Comp, vec![*args.first()?]),
        "re.diff" => frame(CompileBuild::Diff, vec![*args.get(1)?, *args.first()?]),
        "re.range" => {
            // Both operands must be single-character string literals; per
            // SMT-LIB, any non-singleton literal denotes the empty language.
            let lo = const_string(manager, *args.first()?)?;
            let hi = const_string(manager, *args.get(1)?)?;
            match (single_char(&lo), single_char(&hi)) {
                (Some(l), Some(h)) => leaf(Regex::range(l, h)),
                _ => leaf(Regex::none()),
            }
        }
        "re.^" => {
            // Encoded as [Int(n), re].
            let n = const_u32(manager, *args.first()?)?;
            frame(CompileBuild::Loop(n, Some(n)), vec![*args.get(1)?])
        }
        "re.loop" => {
            // Encoded as [Int(lo), Int(hi), re].
            let lo = const_u32(manager, *args.first()?)?;
            let hi = const_u32(manager, *args.get(1)?)?;
            frame(CompileBuild::Loop(lo, Some(hi)), vec![*args.get(2)?])
        }
        _ => None,
    }
}

/// Fold a ground string subterm into its concrete value. Handles string
/// literals and constant concatenations; returns `None` for anything involving
/// a variable or a non-string-constructing operator.
///
/// Iterative: an n-ary `(str.++ …)` application folds into that many nested
/// binary `StrConcat` nodes, so the spine depth is the operand count and is
/// input-controlled. The right operand is pushed first so the pops run left to
/// right, which is the order the concatenation needs.
fn const_string(manager: &TermManager, term: TermId) -> Option<String> {
    let mut worklist = vec![term];
    let mut out = String::new();
    while let Some(current) = worklist.pop() {
        match &manager.get(current)?.kind {
            TermKind::StringLit(s) => out.push_str(s),
            TermKind::StrConcat(a, b) => {
                worklist.push(*b);
                worklist.push(*a);
            }
            _ => return None,
        }
    }
    Some(out)
}

/// Decode a ground non-negative integer constant to `u32`.
fn const_u32(manager: &TermManager, term: TermId) -> Option<u32> {
    match &manager.get(term)?.kind {
        TermKind::IntConst(n) => n.to_string().parse::<u32>().ok(),
        _ => None,
    }
}

/// The single `char` of a one-character string, else `None`.
fn single_char(s: &str) -> Option<char> {
    let mut it = s.chars();
    let c = it.next()?;
    if it.next().is_none() { Some(c) } else { None }
}

/// Search for the shortest word accepted by `regex` whose length lies in
/// `[len_lo, len_hi]` (an open upper bound when `len_hi` is `None`).
///
/// `max_states` bounds the number of distinct derivative states explored and
/// `max_len` bounds the word length considered; exceeding either yields
/// [`WordSearch::Unknown`] rather than an unsound verdict.
pub fn search_word(
    regex: &Arc<Regex>,
    len_lo: usize,
    len_hi: Option<usize>,
    max_states: usize,
    max_len: usize,
) -> WordSearch {
    let (alphabet, complete) = build_alphabet(regex);

    // When both length bounds are trivial (any length ≥ 0) a pure state-dedup
    // BFS explores the finite derivative automaton and terminates, letting us
    // soundly conclude emptiness. With an active lower/upper length bound the
    // same state may need to be revisited at different depths, so dedup on
    // (state, depth) instead and rely on the length/`max_len` cap.
    let bounded = len_lo > 0 || len_hi.is_some();
    let depth_cap = match len_hi {
        Some(h) => h.min(max_len),
        None => max_len,
    };

    let mut queue: VecDeque<(Arc<Regex>, String)> = VecDeque::new();
    let mut visited: FxHashSet<(Arc<Regex>, usize)> = FxHashSet::default();
    let mut hit_cap = false;
    queue.push_back((regex.clone(), String::new()));

    while let Some((state, word)) = queue.pop_front() {
        let depth = word.chars().count();
        let key = (state.clone(), if bounded { depth } else { 0 });
        if !visited.insert(key) {
            continue;
        }
        if visited.len() > max_states {
            return WordSearch::Unknown;
        }

        if state.is_nullable() && depth >= len_lo && len_hi.is_none_or(|h| depth <= h) {
            return WordSearch::Found(word);
        }

        // A dead (empty-language) state has no extensions.
        if state.is_empty() {
            continue;
        }
        if depth >= depth_cap {
            hit_cap = true;
            continue;
        }

        for &c in &alphabet {
            let deriv = state.derivative(c);
            if deriv.is_empty() {
                continue;
            }
            let mut next = word.clone();
            next.push(c);
            queue.push_back((deriv, next));
        }
    }

    // The queue drained without reaching an accepting state.
    if !complete || hit_cap {
        // Either the alphabet omitted some atom (opaque Unicode class) or the
        // search was truncated at the length cap, so emptiness is not proven.
        return WordSearch::Unknown;
    }
    WordSearch::Empty
}

/// Build the representative alphabet for `regex`, and report whether it is
/// *complete* (i.e. contains a representative of every derivative equivalence
/// class). Completeness is false only when an opaque `UnicodeClass` atom is
/// present, which [`compile_regex`] never produces but which could appear if a
/// regex from another source is passed in.
fn build_alphabet(regex: &Arc<Regex>) -> (Vec<char>, bool) {
    let mut endpoints: Vec<char> = Vec::new();
    let mut ranges: Vec<(char, char)> = Vec::new();
    let mut has_unicode_class = false;
    collect_atoms(regex, &mut endpoints, &mut ranges, &mut has_unicode_class);

    let explicit: FxHashSet<char> = endpoints.iter().copied().collect();

    // Representatives: every endpoint, the code point just after it (covers the
    // open interval up to the next endpoint), and one fresh char outside every
    // explicit set (covers the "matches anything else / complement" class).
    let mut candidates: Vec<char> = Vec::new();
    for &e in &endpoints {
        candidates.push(e);
        if let Some(n) = next_char(e) {
            candidates.push(n);
        }
    }
    if let Some(fresh) = pick_fresh(&explicit, &ranges) {
        candidates.push(fresh);
    }

    let mut seen: FxHashSet<char> = FxHashSet::default();
    let alphabet: Vec<char> = candidates.into_iter().filter(|c| seen.insert(*c)).collect();
    (alphabet, !has_unicode_class)
}

/// Collect every character/range atom that appears in `regex`.
///
/// Explicit stack plus a pointer-keyed visited set: the operand structure is an
/// `Arc`-shared DAG, so the recursive version re-walked every shared node once
/// per path reaching it (exponential), and it returned `()` – no channel a
/// depth limit could have used. Skipping an already-visited node is
/// unobservable: a repeat contributes only duplicate endpoints, which the
/// caller deduplicates anyway, and duplicate ranges, which only feed a
/// containment test.
fn collect_atoms(
    regex: &Arc<Regex>,
    endpoints: &mut Vec<char>,
    ranges: &mut Vec<(char, char)>,
    has_unicode_class: &mut bool,
) {
    let mut stack: Vec<Arc<Regex>> = vec![regex.clone()];
    let mut visited: FxHashSet<*const Regex> = FxHashSet::default();
    while let Some(node) = stack.pop() {
        if !visited.insert(Arc::as_ptr(&node)) {
            continue;
        }
        match &node.op {
            RegexOp::Char(c) => endpoints.push(*c),
            RegexOp::Range(lo, hi) => {
                endpoints.push(*lo);
                endpoints.push(*hi);
                ranges.push((*lo, *hi));
            }
            RegexOp::UnicodeClass(_) => *has_unicode_class = true,
            RegexOp::Concat(parts) | RegexOp::Union(parts) | RegexOp::Inter(parts) => {
                // Reversed so the pops visit operands left to right, the order
                // the recursive descent used.
                stack.extend(parts.iter().rev().cloned());
            }
            RegexOp::Complement(inner)
            | RegexOp::Star(inner)
            | RegexOp::Plus(inner)
            | RegexOp::Option(inner)
            | RegexOp::Loop(inner, _, _) => stack.push(inner.clone()),
            RegexOp::Epsilon | RegexOp::None | RegexOp::All | RegexOp::AllChar => {}
        }
    }
}

/// The code point immediately after `c`, skipping the UTF-16 surrogate gap.
fn next_char(c: char) -> Option<char> {
    let n = (c as u32).checked_add(1)?;
    let n = if n == 0xD800 { 0xE000 } else { n };
    char::from_u32(n)
}

/// Pick a character that lies in no explicit character set and no range – a
/// representative for the "matches everything / matches the complement" class.
fn pick_fresh(explicit: &FxHashSet<char>, ranges: &[(char, char)]) -> Option<char> {
    let uncovered =
        |c: char| !explicit.contains(&c) && !ranges.iter().any(|(lo, hi)| c >= *lo && c <= *hi);
    // Prefer readable ASCII for nicer witness strings.
    for &c in &['a', 'b', 'c', '0', '1', 'x', 'y', 'z', ' ', '!'] {
        if uncovered(c) {
            return Some(c);
        }
    }
    // Fall back to a linear scan of the code space (finitely many ranges, so
    // some code point is always uncovered unless the whole universe is).
    for cp in 0x20u32..=0x10_FFFF {
        if (0xD800..=0xDFFF).contains(&cp) {
            continue;
        }
        if let Some(c) = char::from_u32(cp)
            && uncovered(c)
        {
            return Some(c);
        }
    }
    None
}

/// Which `str.replace_re*` operator is being evaluated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplaceReMode {
    /// `str.replace_re`: replace the *shortest leftmost* match – including an
    /// empty one – and stop.
    First,
    /// `str.replace_re_all`: replace, left to right, every shortest
    /// **non-empty** match.
    All,
}

/// Derivative steps [`replace_re`] may take over one whole input before it
/// concedes that it cannot evaluate the term.
///
/// The scan is quadratic in the input length (one restart per start position)
/// and a single derivative can grow the regex, so an unbounded run on an
/// adversarial input would not terminate in useful time.  Exceeding the budget
/// yields `None`, which the caller turns into an honest `unknown` – never into
/// a value.
const MAX_REPLACE_RE_STEPS: usize = 1 << 20;

/// The length (in characters) of the shortest match of `regex` starting at
/// `chars[from..]`, or `None` when nothing matches there.
///
/// `min_len` is the smallest match length considered: `0` admits the empty
/// match, `1` excludes it.  The scan walks Brzozowski derivatives one
/// character at a time, so the *first* accepting state it reaches is the
/// shortest match by construction.
///
/// `budget` is decremented once per derivative step; running out is reported
/// as `Err(())` so the caller can distinguish "no match here" from "gave up".
fn shortest_match_at(
    regex: &Arc<Regex>,
    chars: &[char],
    from: usize,
    min_len: usize,
    budget: &mut usize,
) -> Result<Option<usize>, ()> {
    let mut state = regex.clone();
    if min_len == 0 && state.is_nullable() {
        return Ok(Some(0));
    }
    for (offset, &c) in chars[from..].iter().enumerate() {
        if *budget == 0 {
            return Err(());
        }
        *budget -= 1;
        state = state.derivative(c);
        // A syntactically empty language has no extension; bail out early.
        if state.is_empty() {
            return Ok(None);
        }
        let len = offset + 1;
        if len >= min_len && state.is_nullable() {
            return Ok(Some(len));
        }
    }
    Ok(None)
}

/// SMT-LIB `str.replace_re` / `str.replace_re_all`.
///
/// From the Unicode Strings theory:
///
/// * `(str.replace_re s r t)` is "the string obtained by replacing the
///   shortest leftmost match of `r` in `s`, if any, by `t`.  Note that if the
///   language of `r` contains the empty string, the result is to prepend `t`
///   to `s`" – the empty match at position 0 *is* the shortest leftmost match,
///   so no special case is needed beyond admitting length-0 matches.
/// * `(str.replace_re_all s r t)` is "the string obtained by replacing,
///   left-to-right, each shortest **non-empty** match of `r` in `s` by `t`".
///   Empty matches are excluded here – otherwise the rewrite would not
///   terminate – so a position with only an empty match simply contributes its
///   own character and the scan advances by one.
///
/// Reference: Z3 declares both operators in `seq_decl_plugin.cpp` but its
/// `seq_rewriter.cpp` folds neither (`mk_seq_replace_re*` return `BR_FAILED`),
/// so the SMT-LIB theory definition is the authority for these rules.
///
/// `None` means the internal derivative-step budget ran out; the
/// caller must report `unknown` rather than substitute a value.
#[must_use]
pub fn replace_re(
    s: &str,
    regex: &Arc<Regex>,
    replacement: &str,
    mode: ReplaceReMode,
) -> Option<String> {
    let chars: Vec<char> = s.chars().collect();
    let mut budget = MAX_REPLACE_RE_STEPS;
    let mut out = String::new();
    let mut i = 0usize;

    match mode {
        ReplaceReMode::First => {
            // `i == chars.len()` is still a candidate start position: a
            // nullable regex matches the empty string there. (It also matches
            // at position 0, so in practice the loop returns much earlier –
            // but the bound keeps the scan total.)
            while i <= chars.len() {
                if let Some(len) = shortest_match_at(regex, &chars, i, 0, &mut budget).ok()? {
                    out.push_str(replacement);
                    out.extend(chars[i + len..].iter());
                    return Some(out);
                }
                if i == chars.len() {
                    break;
                }
                out.push(chars[i]);
                i += 1;
            }
            Some(out)
        }
        ReplaceReMode::All => {
            while i < chars.len() {
                match shortest_match_at(regex, &chars, i, 1, &mut budget).ok()? {
                    Some(len) => {
                        out.push_str(replacement);
                        i += len;
                    }
                    None => {
                        out.push(chars[i]);
                        i += 1;
                    }
                }
            }
            Some(out)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_core::ast::TermManager;

    fn parse(m: &mut TermManager, src: &str) -> TermId {
        nixie_core::smtlib::parse_term(src, m).expect("parse regex term")
    }

    /// Compile the regex operand of an `str.in_re` term.
    fn compile_from_in_re(m: &TermManager, in_re: TermId) -> Option<Arc<Regex>> {
        match &m.get(in_re).expect("term").kind {
            TermKind::StrInRe(_, re) => compile_regex(m, *re),
            _ => panic!("expected str.in_re"),
        }
    }

    #[test]
    fn compile_and_match_range_star_concat() {
        let mut m = TermManager::new();
        // ".*[0-9]" – any string ending in a digit.
        let t = parse(
            &mut m,
            r#"(str.in_re s (re.++ (re.* re.allchar) (re.range "0" "9")))"#,
        );
        let re = compile_from_in_re(&m, t).expect("ground regex");
        assert!(re.matches("0"));
        assert!(re.matches("abc7"));
        assert!(!re.matches("abc"));
        assert!(!re.matches(""));
    }

    #[test]
    fn compile_union_and_to_re() {
        let mut m = TermManager::new();
        let t = parse(
            &mut m,
            r#"(str.in_re s (re.union (str.to_re "cat") (str.to_re "dog")))"#,
        );
        let re = compile_from_in_re(&m, t).expect("ground");
        assert!(re.matches("cat"));
        assert!(re.matches("dog"));
        assert!(!re.matches("cow"));
    }

    #[test]
    fn compile_power_and_loop() {
        let mut m = TermManager::new();
        let pow = parse(&mut m, r#"(str.in_re s ((_ re.^ 3) (str.to_re "ab")))"#);
        let re = compile_from_in_re(&m, pow).expect("ground");
        assert!(re.matches("ababab"));
        assert!(!re.matches("abab"));

        let lp = parse(&mut m, r#"(str.in_re s ((_ re.loop 1 2) (str.to_re "z")))"#);
        let re = compile_from_in_re(&m, lp).expect("ground");
        assert!(re.matches("z"));
        assert!(re.matches("zz"));
        assert!(!re.matches(""));
        assert!(!re.matches("zzz"));
    }

    #[test]
    fn compile_complement_and_diff() {
        let mut m = TermManager::new();
        let comp = parse(&mut m, r#"(str.in_re s (re.comp (str.to_re "no")))"#);
        let re = compile_from_in_re(&m, comp).expect("ground");
        assert!(!re.matches("no"));
        assert!(re.matches("yes"));

        let diff = parse(
            &mut m,
            r#"(str.in_re s (re.diff (re.* re.allchar) (str.to_re "bad")))"#,
        );
        let re = compile_from_in_re(&m, diff).expect("ground");
        assert!(!re.matches("bad"));
        assert!(re.matches("good"));
        assert!(re.matches(""));
    }

    #[test]
    fn non_ground_regex_is_none() {
        let mut m = TermManager::new();
        let sort = m.sorts.string_sort();
        let x = m.mk_var("x", sort);
        let re = m.mk_str_to_re(x);
        assert!(
            compile_regex(&m, re).is_none(),
            "str.to_re of a variable must be non-ground"
        );
    }

    #[test]
    fn search_finds_shortest_word() {
        // ".*[0-9]": shortest accepted word is a single digit.
        let re = Regex::concat(vec![Regex::star(Regex::all_char()), Regex::range('0', '9')]);
        match search_word(&re, 0, None, 4000, 4096) {
            WordSearch::Found(w) => {
                assert_eq!(w.chars().count(), 1);
                assert!(re.matches(&w));
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn search_detects_empty_intersection() {
        // [0-9] ∩ [a-z] is empty.
        let re = Regex::inter(vec![Regex::range('0', '9'), Regex::range('a', 'z')]);
        assert_eq!(search_word(&re, 0, None, 4000, 4096), WordSearch::Empty);
    }

    #[test]
    fn search_respects_length_lower_bound() {
        // All strings, but require length ≥ 3.
        let re = Regex::all();
        match search_word(&re, 3, None, 4000, 4096) {
            WordSearch::Found(w) => assert_eq!(w.chars().count(), 3),
            other => panic!("expected Found len 3, got {other:?}"),
        }
    }

    #[test]
    fn search_complement_shortest_is_empty_string() {
        // complement of "a": the empty string is accepted (≠ "a").
        let re = Regex::complement(Regex::literal("a"));
        assert_eq!(
            search_word(&re, 0, None, 4000, 4096),
            WordSearch::Found(String::new())
        );
    }

    /// Exact values for `str.replace_re` (shortest **leftmost** match, empty
    /// match included) and `str.replace_re_all` (every shortest **non-empty**
    /// match, left to right).
    fn first(s: &str, re: &Arc<Regex>, t: &str) -> String {
        replace_re(s, re, t, ReplaceReMode::First).expect("within the derivative budget")
    }

    fn all(s: &str, re: &Arc<Regex>, t: &str) -> String {
        replace_re(s, re, t, ReplaceReMode::All).expect("within the derivative budget")
    }

    #[test]
    fn replace_re_takes_the_leftmost_shortest_match() {
        let b = Regex::literal("b");
        assert_eq!(first("abcabc", &b, "X"), "aXcabc");
        assert_eq!(all("abcabc", &b, "X"), "aXcaXc");

        // Leftmost wins over shortest: the match at position 1 is chosen even
        // though "bc" and "b" both start there – then the shortest of those.
        let bc_or_b = Regex::union(vec![Regex::literal("bc"), Regex::literal("b")]);
        assert_eq!(first("abcabc", &bc_or_b, "X"), "aXcabc");
    }

    #[test]
    fn replace_re_handles_an_empty_matching_regex() {
        // "if the language of r contains the empty string, the result is to
        // prepend t to s" – because the empty match at position 0 *is* the
        // shortest leftmost match.
        let epsilon = Regex::literal("");
        assert_eq!(first("abc", &epsilon, "X"), "Xabc");
        assert_eq!(first("", &epsilon, "X"), "X");
        // `replace_re_all` only ever replaces non-empty matches.
        assert_eq!(all("abc", &epsilon, "X"), "abc");
        assert_eq!(all("", &epsilon, "X"), "");

        let a_star = Regex::star(Regex::literal("a"));
        assert_eq!(first("aaa", &a_star, "X"), "Xaaa");
        assert_eq!(first("", &a_star, "X"), "X");
        assert_eq!(all("aaa", &a_star, "X"), "XXX");

        // A union with `""` in it: the empty alternative is skipped by `_all`,
        // taken by the first-match form.
        let eps_or_b = Regex::union(vec![Regex::literal(""), Regex::literal("b")]);
        assert_eq!(first("abc", &eps_or_b, "X"), "Xabc");
        assert_eq!(all("abc", &eps_or_b, "X"), "aXc");
    }

    #[test]
    fn replace_re_without_a_match_is_the_identity() {
        let z = Regex::literal("z");
        assert_eq!(first("abc", &z, "X"), "abc");
        assert_eq!(all("abc", &z, "X"), "abc");
        let none = Regex::none();
        assert_eq!(first("abc", &none, "X"), "abc");
        assert_eq!(all("abc", &none, "X"), "abc");
        assert_eq!(first("", &none, "X"), "");
    }

    #[test]
    fn replace_re_non_nullable_matches_are_consumed_whole() {
        let a_plus = Regex::plus(Regex::literal("a"));
        assert_eq!(first("aaab", &a_plus, "X"), "Xaab");
        assert_eq!(all("aaab", &a_plus, "X"), "XXXb");

        // A two-character non-nullable match advances the scan by two.
        let ab = Regex::literal("ab");
        assert_eq!(all("ababc", &ab, "X"), "XXc");

        assert_eq!(all("abc", &Regex::all_char(), "X"), "XXX");
        assert_eq!(first("abc", &Regex::all(), "X"), "Xabc");
    }

    #[test]
    fn replace_re_is_code_point_aware() {
        // A non-ASCII pattern and subject: positions are counted in `char`s,
        // never in UTF-8 bytes.
        let e_acute = Regex::literal("é");
        assert_eq!(first("aéb", &e_acute, "X"), "aXb");
        assert_eq!(all("éaé", &e_acute, "X"), "XaX");
        assert_eq!(
            all("abc", &Regex::range('a', 'b'), "\u{2ffff}"),
            "\u{2ffff}\u{2ffff}c"
        );
    }
}

//! Regular Expression Engine
//!
//! Implements regular expressions with Brzozowski derivatives for efficient
//! membership testing during SMT solving.

use super::unicode::UnicodeCategory;
#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use smallvec::SmallVec;

/// Regular expression operation kinds
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RegexOp {
    /// Empty string (epsilon)
    Epsilon,
    /// Empty language (no strings)
    None,
    /// Full language (all strings)
    All,
    /// Full character set (any single character)
    AllChar,
    /// Single character literal
    Char(char),
    /// Character range [a-z]
    Range(char, char),
    /// Unicode category (e.g., \p{L} for letters)
    UnicodeClass(UnicodeCategory),
    /// Concatenation of regexes
    Concat(Vec<Arc<Regex>>),
    /// Union of regexes (alternation)
    Union(Vec<Arc<Regex>>),
    /// Intersection of regexes
    Inter(Vec<Arc<Regex>>),
    /// Complement of a regex
    Complement(Arc<Regex>),
    /// Kleene star (zero or more)
    Star(Arc<Regex>),
    /// Kleene plus (one or more)
    Plus(Arc<Regex>),
    /// Optional (zero or one)
    Option(Arc<Regex>),
    /// Bounded loop {min, max}
    Loop(Arc<Regex>, u32, Option<u32>),
}

/// A compiled regular expression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Regex {
    /// The operation
    pub op: RegexOp,
    /// Cached nullable status
    nullable: bool,
}

/// Deterministic total order over `RegexOp`, used to canonicalize the
/// operand order of `Union`/`Inter` (see [`Regex::union`]/[`Regex::inter`])
/// so that the same set of alternatives combined in a different input
/// order ends up structurally equal after sorting + `dedup`.
///
/// This used to be done via `format!("{:?}", ...).cmp(...)` on the WHOLE
/// (potentially deeply nested) regex for every comparison during the
/// sort -- correct only incidentally (derived `Debug` output happens to be
/// consistent with derived `Eq` here), but wasteful (a fresh `String`
/// allocated per comparison) and fragile (silently depends on `Debug`'s
/// output format never changing in a way that breaks the total order,
/// e.g. via a future hand-written `Debug` impl).
///
/// A `#[derive(Ord)]` on `RegexOp` itself is not available: the
/// `UnicodeClass` variant carries a `UnicodeCategory`, defined in a sibling
/// module this cluster does not own, which does not derive `Ord`. Instead,
/// `UnicodeCategory` is a plain fieldless enum, so its discriminant (via
/// `as u32`) already gives it a real total order without needing to modify
/// that module.
fn regex_op_cmp(a: &RegexOp, b: &RegexOp) -> Ordering {
    fn rank(op: &RegexOp) -> u8 {
        match op {
            RegexOp::Epsilon => 0,
            RegexOp::None => 1,
            RegexOp::All => 2,
            RegexOp::AllChar => 3,
            RegexOp::Char(_) => 4,
            RegexOp::Range(..) => 5,
            RegexOp::UnicodeClass(_) => 6,
            RegexOp::Concat(_) => 7,
            RegexOp::Union(_) => 8,
            RegexOp::Inter(_) => 9,
            RegexOp::Complement(_) => 10,
            RegexOp::Star(_) => 11,
            RegexOp::Plus(_) => 12,
            RegexOp::Option(_) => 13,
            RegexOp::Loop(..) => 14,
        }
    }

    let (ra, rb) = (rank(a), rank(b));
    if ra != rb {
        return ra.cmp(&rb);
    }

    match (a, b) {
        (RegexOp::Char(x), RegexOp::Char(y)) => x.cmp(y),
        (RegexOp::Range(x1, x2), RegexOp::Range(y1, y2)) => (x1, x2).cmp(&(y1, y2)),
        (RegexOp::UnicodeClass(x), RegexOp::UnicodeClass(y)) => (*x as u32).cmp(&(*y as u32)),
        (RegexOp::Concat(x), RegexOp::Concat(y))
        | (RegexOp::Union(x), RegexOp::Union(y))
        | (RegexOp::Inter(x), RegexOp::Inter(y)) => regex_vec_cmp(x, y),
        (RegexOp::Complement(x), RegexOp::Complement(y))
        | (RegexOp::Star(x), RegexOp::Star(y))
        | (RegexOp::Plus(x), RegexOp::Plus(y))
        | (RegexOp::Option(x), RegexOp::Option(y)) => regex_cmp(x, y),
        (RegexOp::Loop(x, xlo, xhi), RegexOp::Loop(y, ylo, yhi)) => regex_cmp(x, y)
            .then_with(|| xlo.cmp(ylo))
            .then_with(|| xhi.cmp(yhi)),
        // Same rank implies the same variant (`rank` is injective), so
        // every other combination is unreachable; fall back to `Equal`
        // rather than panicking; still a valid (if imprecise for an
        // impossible case) total order.
        _ => Ordering::Equal,
    }
}

/// Total order over `Regex`, delegating to [`regex_op_cmp`] (the cached
/// `nullable` flag is redundant with `op` and not compared).
fn regex_cmp(a: &Regex, b: &Regex) -> Ordering {
    regex_op_cmp(&a.op, &b.op)
}

/// Total order over a list of sub-regexes (`Concat`/`Union`/`Inter`
/// operands), comparing lexicographically by length then element-wise.
fn regex_vec_cmp(a: &[Arc<Regex>], b: &[Arc<Regex>]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        a.iter()
            .zip(b.iter())
            .map(|(x, y)| regex_cmp(x, y))
            .find(|o| !o.is_eq())
            .unwrap_or(Ordering::Equal)
    })
}

impl Regex {
    /// Create epsilon (empty string)
    pub fn epsilon() -> Arc<Self> {
        Arc::new(Self {
            op: RegexOp::Epsilon,
            nullable: true,
        })
    }

    /// Create empty language (no matches)
    pub fn none() -> Arc<Self> {
        Arc::new(Self {
            op: RegexOp::None,
            nullable: false,
        })
    }

    /// Create regex matching all strings
    pub fn all() -> Arc<Self> {
        Arc::new(Self {
            op: RegexOp::All,
            nullable: true,
        })
    }

    /// Create regex matching any single character
    pub fn all_char() -> Arc<Self> {
        Arc::new(Self {
            op: RegexOp::AllChar,
            nullable: false,
        })
    }

    /// Create a single character regex
    pub fn char(c: char) -> Arc<Self> {
        Arc::new(Self {
            op: RegexOp::Char(c),
            nullable: false,
        })
    }

    /// Create a character range [lo-hi]
    pub fn range(lo: char, hi: char) -> Arc<Self> {
        if lo > hi {
            return Self::none();
        }
        Arc::new(Self {
            op: RegexOp::Range(lo, hi),
            nullable: false,
        })
    }

    /// Create a string literal regex
    pub fn literal(s: &str) -> Arc<Self> {
        if s.is_empty() {
            return Self::epsilon();
        }
        let parts: Vec<Arc<Regex>> = s.chars().map(Self::char).collect();
        Self::concat(parts)
    }

    /// Create concatenation of regexes
    pub fn concat(parts: Vec<Arc<Regex>>) -> Arc<Self> {
        // Flatten nested concats and filter out epsilons
        let mut flat: Vec<Arc<Regex>> = Vec::new();
        for p in parts {
            match &p.op {
                RegexOp::Epsilon => continue,
                RegexOp::None => return Self::none(),
                RegexOp::Concat(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(p),
            }
        }
        if flat.is_empty() {
            return Self::epsilon();
        }
        if flat.len() == 1 {
            return flat
                .into_iter()
                .next()
                .expect("flat has exactly one element");
        }
        let nullable = flat.iter().all(|r| r.nullable);
        Arc::new(Self {
            op: RegexOp::Concat(flat),
            nullable,
        })
    }

    /// Create union of regexes
    pub fn union(parts: Vec<Arc<Regex>>) -> Arc<Self> {
        // Flatten nested unions and filter out nones
        let mut flat: Vec<Arc<Regex>> = Vec::new();
        for p in parts {
            match &p.op {
                RegexOp::None => continue,
                RegexOp::All => return Self::all(),
                RegexOp::Union(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(p),
            }
        }
        if flat.is_empty() {
            return Self::none();
        }
        if flat.len() == 1 {
            return flat
                .into_iter()
                .next()
                .expect("flat has exactly one element");
        }
        // Deduplicate
        flat.sort_by(|a, b| regex_op_cmp(&a.op, &b.op));
        flat.dedup();
        let nullable = flat.iter().any(|r| r.nullable);
        Arc::new(Self {
            op: RegexOp::Union(flat),
            nullable,
        })
    }

    /// Create intersection of regexes
    pub fn inter(parts: Vec<Arc<Regex>>) -> Arc<Self> {
        let mut flat: Vec<Arc<Regex>> = Vec::new();
        for p in parts {
            match &p.op {
                RegexOp::All => continue,
                RegexOp::None => return Self::none(),
                RegexOp::Inter(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(p),
            }
        }
        if flat.is_empty() {
            return Self::all();
        }
        if flat.len() == 1 {
            return flat
                .into_iter()
                .next()
                .expect("flat has exactly one element");
        }
        flat.sort_by(|a, b| regex_op_cmp(&a.op, &b.op));
        flat.dedup();
        let nullable = flat.iter().all(|r| r.nullable);
        Arc::new(Self {
            op: RegexOp::Inter(flat),
            nullable,
        })
    }

    /// Create complement of a regex
    pub fn complement(r: Arc<Regex>) -> Arc<Self> {
        match &r.op {
            RegexOp::None => Self::all(),
            RegexOp::All => Self::none(),
            RegexOp::Complement(inner) => inner.clone(),
            _ => Arc::new(Self {
                op: RegexOp::Complement(r.clone()),
                nullable: !r.nullable,
            }),
        }
    }

    /// Create Kleene star
    pub fn star(r: Arc<Regex>) -> Arc<Self> {
        match &r.op {
            RegexOp::Epsilon | RegexOp::None => Self::epsilon(),
            RegexOp::Star(_) | RegexOp::All => r,
            _ => Arc::new(Self {
                op: RegexOp::Star(r),
                nullable: true,
            }),
        }
    }

    /// Create Kleene plus
    pub fn plus(r: Arc<Regex>) -> Arc<Self> {
        match &r.op {
            RegexOp::Epsilon => Self::epsilon(),
            RegexOp::None => Self::none(),
            RegexOp::Star(_) | RegexOp::Plus(_) => r,
            _ => Arc::new(Self {
                op: RegexOp::Plus(r.clone()),
                nullable: r.nullable,
            }),
        }
    }

    /// Create optional (zero or one)
    pub fn option(r: Arc<Regex>) -> Arc<Self> {
        if r.nullable {
            return r;
        }
        match &r.op {
            RegexOp::None => Self::epsilon(),
            _ => Arc::new(Self {
                op: RegexOp::Option(r),
                nullable: true,
            }),
        }
    }

    /// Create bounded loop
    pub fn loop_bounded(r: Arc<Regex>, min: u32, max: Option<u32>) -> Arc<Self> {
        if min == 0 && max == Some(0) {
            return Self::epsilon();
        }
        if let Some(m) = max
            && m < min
        {
            return Self::none();
        }
        if matches!(r.op, RegexOp::None) && min > 0 {
            return Self::none();
        }
        if matches!(r.op, RegexOp::Epsilon) {
            return Self::epsilon();
        }
        let nullable = min == 0 || r.nullable;
        Arc::new(Self {
            op: RegexOp::Loop(r, min, max),
            nullable,
        })
    }

    /// Check if regex accepts the empty string
    #[inline]
    pub fn is_nullable(&self) -> bool {
        self.nullable
    }

    /// Check if this is the empty language
    #[inline]
    pub fn is_empty(&self) -> bool {
        matches!(self.op, RegexOp::None)
    }

    /// Check if this accepts all strings
    #[inline]
    pub fn is_all(&self) -> bool {
        matches!(self.op, RegexOp::All)
    }

    /// Compute Brzozowski derivative with respect to a character
    pub fn derivative(&self, c: char) -> Arc<Regex> {
        match &self.op {
            RegexOp::Epsilon | RegexOp::None => Self::none(),
            RegexOp::All => Self::all(),
            RegexOp::AllChar => Self::epsilon(),
            RegexOp::Char(ch) => {
                if *ch == c {
                    Self::epsilon()
                } else {
                    Self::none()
                }
            }
            RegexOp::Range(lo, hi) => {
                if c >= *lo && c <= *hi {
                    Self::epsilon()
                } else {
                    Self::none()
                }
            }
            RegexOp::UnicodeClass(cat) => {
                if cat.contains(c) {
                    Self::epsilon()
                } else {
                    Self::none()
                }
            }
            RegexOp::Concat(parts) => {
                // D(r1 r2 ... rn) = D(r1) r2 ... rn  +  (if nullable(r1)) D(r2) r3 ... rn + ...
                let mut result: Vec<Arc<Regex>> = Vec::new();
                for (i, part) in parts.iter().enumerate() {
                    let d = part.derivative(c);
                    if !d.is_empty() {
                        let mut suffix: Vec<Arc<Regex>> = vec![d];
                        suffix.extend(parts[i + 1..].iter().cloned());
                        result.push(Self::concat(suffix));
                    }
                    if !part.nullable {
                        break;
                    }
                }
                Self::union(result)
            }
            RegexOp::Union(parts) => {
                let derivs: Vec<Arc<Regex>> = parts.iter().map(|p| p.derivative(c)).collect();
                Self::union(derivs)
            }
            RegexOp::Inter(parts) => {
                let derivs: Vec<Arc<Regex>> = parts.iter().map(|p| p.derivative(c)).collect();
                Self::inter(derivs)
            }
            RegexOp::Complement(inner) => Self::complement(inner.derivative(c)),
            RegexOp::Star(inner) => {
                // D(r*) = D(r) r*
                let d = inner.derivative(c);
                Self::concat(vec![d, Arc::new(self.clone())])
            }
            RegexOp::Plus(inner) => {
                // D(r+) = D(r) r*
                let d = inner.derivative(c);
                Self::concat(vec![d, Self::star(inner.clone())])
            }
            RegexOp::Option(inner) => inner.derivative(c),
            RegexOp::Loop(inner, min, max) => {
                // D(r{m,n}) = D(r) r{max(0, m-1), n-1}
                let d = inner.derivative(c);
                let new_min = min.saturating_sub(1);
                let new_max = max.map(|m| m.saturating_sub(1));
                let rest = Self::loop_bounded(inner.clone(), new_min, new_max);
                Self::concat(vec![d, rest])
            }
        }
    }

    /// Check if a string matches this regex
    pub fn matches(&self, s: &str) -> bool {
        let mut current: Arc<Regex> = Arc::new(self.clone());
        for c in s.chars() {
            current = current.derivative(c);
            if current.is_empty() {
                return false;
            }
        }
        current.is_nullable()
    }
}

/// A regex derivative cache for efficient repeated derivative computation
#[allow(dead_code)]
#[derive(Debug, Default)]
pub struct DerivativeCache {
    /// Cache: (regex, char) -> derivative.
    ///
    /// Keyed by the actual `Regex` value (which derives `Eq`/`Hash`), not a
    /// raw pre-computed `u64` hash: using a bare hash AS the map key means
    /// any hash collision between two DIFFERENT regexes silently returns
    /// the wrong cached derivative (no equality check ever happens, since
    /// the original regex value isn't retained to check against). Keying
    /// on the value itself lets `FxHashMap`'s normal collision handling
    /// (hash bucket + `Eq` verification) do this correctly.
    cache: FxHashMap<(Regex, char), Arc<Regex>>,
}

#[allow(dead_code)]
impl DerivativeCache {
    /// Create a new derivative cache
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    /// Get or compute derivative
    pub fn derivative(&mut self, r: &Arc<Regex>, c: char) -> Arc<Regex> {
        let key = ((**r).clone(), c);

        if let Some(d) = self.cache.get(&key) {
            return d.clone();
        }

        let d = r.derivative(c);
        self.cache.insert(key, d.clone());
        d
    }

    /// Clear the cache
    pub fn clear(&mut self) {
        self.cache.clear();
    }
}

/// State in an automaton derived from a regex
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct AutomatonState {
    /// The regex representing this state
    pub regex: Arc<Regex>,
    /// State ID
    pub id: u32,
    /// Whether this is an accepting state
    pub accepting: bool,
}

/// A DFA built from a regex using derivative-based construction
#[allow(dead_code)]
#[derive(Debug)]
pub struct RegexAutomaton {
    /// All states
    states: Vec<AutomatonState>,
    /// Transition table: state_id -> [(char_range, target_state_id)]
    transitions: Vec<SmallVec<[(char, char, u32); 8]>>,
    /// Regex to state ID mapping
    regex_to_state: FxHashMap<u64, u32>,
    /// Initial state ID
    initial: u32,
    /// Derivative cache
    cache: DerivativeCache,
}

#[allow(dead_code)]
impl RegexAutomaton {
    /// Build a DFA from a regex (lazy construction)
    pub fn new(regex: Arc<Regex>) -> Self {
        let initial_accepting = regex.is_nullable();

        let mut hasher = rustc_hash::FxHasher::default();
        regex.hash(&mut hasher);
        let hash = hasher.finish();

        let mut regex_to_state = FxHashMap::default();
        regex_to_state.insert(hash, 0);

        Self {
            states: vec![AutomatonState {
                regex,
                id: 0,
                accepting: initial_accepting,
            }],
            transitions: vec![SmallVec::new()],
            regex_to_state,
            initial: 0,
            cache: DerivativeCache::new(),
        }
    }

    /// Get or create state for a regex
    fn get_or_create_state(&mut self, regex: Arc<Regex>) -> u32 {
        let mut hasher = rustc_hash::FxHasher::default();
        regex.hash(&mut hasher);
        let hash = hasher.finish();

        if let Some(&id) = self.regex_to_state.get(&hash) {
            return id;
        }

        let id = self.states.len() as u32;
        let accepting = regex.is_nullable();
        self.states.push(AutomatonState {
            regex,
            id,
            accepting,
        });
        self.transitions.push(SmallVec::new());
        self.regex_to_state.insert(hash, id);
        id
    }

    /// Get transition for a character, computing derivatives lazily
    pub fn transition(&mut self, state: u32, c: char) -> u32 {
        // Check existing transitions
        for &(lo, hi, target) in &self.transitions[state as usize] {
            if c >= lo && c <= hi {
                return target;
            }
        }

        // Compute derivative
        let regex = self.states[state as usize].regex.clone();
        let derivative = self.cache.derivative(&regex, c);

        if derivative.is_empty() {
            // Create dead state if needed
            let dead = self.get_or_create_state(Regex::none());
            self.transitions[state as usize].push((c, c, dead));
            return dead;
        }

        let target = self.get_or_create_state(derivative);
        self.transitions[state as usize].push((c, c, target));
        target
    }

    /// Check if a string is accepted
    pub fn accepts(&mut self, s: &str) -> bool {
        let mut current = self.initial;
        for c in s.chars() {
            current = self.transition(current, c);
            // Early exit on dead state
            if self.states[current as usize].regex.is_empty() {
                return false;
            }
        }
        self.states[current as usize].accepting
    }

    /// Check if a state is accepting
    pub fn is_accepting(&self, state: u32) -> bool {
        self.states.get(state as usize).is_some_and(|s| s.accepting)
    }

    /// Check if a state is dead (rejects all strings)
    pub fn is_dead(&self, state: u32) -> bool {
        self.states
            .get(state as usize)
            .is_none_or(|s| s.regex.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_epsilon() {
        let r = Regex::epsilon();
        assert!(r.is_nullable());
        assert!(r.matches(""));
        assert!(!r.matches("a"));
    }

    #[test]
    fn test_char() {
        let r = Regex::char('a');
        assert!(!r.is_nullable());
        assert!(r.matches("a"));
        assert!(!r.matches("b"));
        assert!(!r.matches(""));
        assert!(!r.matches("aa"));
    }

    #[test]
    fn test_literal() {
        let r = Regex::literal("hello");
        assert!(r.matches("hello"));
        assert!(!r.matches("hell"));
        assert!(!r.matches("hello!"));
        assert!(!r.matches(""));
    }

    #[test]
    fn test_concat() {
        let r = Regex::concat(vec![Regex::char('a'), Regex::char('b')]);
        assert!(r.matches("ab"));
        assert!(!r.matches("a"));
        assert!(!r.matches("b"));
        assert!(!r.matches("abc"));
    }

    #[test]
    fn test_union() {
        let r = Regex::union(vec![Regex::char('a'), Regex::char('b')]);
        assert!(r.matches("a"));
        assert!(r.matches("b"));
        assert!(!r.matches("c"));
        assert!(!r.matches("ab"));
    }

    #[test]
    fn test_star() {
        let r = Regex::star(Regex::char('a'));
        assert!(r.is_nullable());
        assert!(r.matches(""));
        assert!(r.matches("a"));
        assert!(r.matches("aaa"));
        assert!(!r.matches("b"));
        assert!(!r.matches("ab"));
    }

    #[test]
    fn test_plus() {
        let r = Regex::plus(Regex::char('a'));
        assert!(!r.is_nullable());
        assert!(!r.matches(""));
        assert!(r.matches("a"));
        assert!(r.matches("aaa"));
        assert!(!r.matches("b"));
    }

    #[test]
    fn test_option() {
        let r = Regex::option(Regex::char('a'));
        assert!(r.is_nullable());
        assert!(r.matches(""));
        assert!(r.matches("a"));
        assert!(!r.matches("aa"));
    }

    #[test]
    fn test_range() {
        let r = Regex::range('a', 'z');
        assert!(r.matches("a"));
        assert!(r.matches("m"));
        assert!(r.matches("z"));
        assert!(!r.matches("A"));
        assert!(!r.matches("1"));
    }

    #[test]
    fn test_loop() {
        let r = Regex::loop_bounded(Regex::char('a'), 2, Some(4));
        assert!(!r.matches(""));
        assert!(!r.matches("a"));
        assert!(r.matches("aa"));
        assert!(r.matches("aaa"));
        assert!(r.matches("aaaa"));
        assert!(!r.matches("aaaaa"));
    }

    #[test]
    fn test_complement() {
        let a = Regex::char('a');
        let not_a = Regex::complement(a);
        assert!(not_a.matches(""));
        assert!(!not_a.matches("a"));
        assert!(not_a.matches("b"));
        assert!(not_a.matches("ab"));
    }

    #[test]
    fn test_intersection() {
        // a* ∩ a+ = a+
        let star = Regex::star(Regex::char('a'));
        let plus = Regex::plus(Regex::char('a'));
        let inter = Regex::inter(vec![star, plus]);
        assert!(!inter.matches(""));
        assert!(inter.matches("a"));
        assert!(inter.matches("aa"));
    }

    #[test]
    fn test_automaton() {
        let r = Regex::star(Regex::union(vec![Regex::char('a'), Regex::char('b')]));
        let mut dfa = RegexAutomaton::new(r);
        assert!(dfa.accepts(""));
        assert!(dfa.accepts("a"));
        assert!(dfa.accepts("ab"));
        assert!(dfa.accepts("aabbab"));
        assert!(!dfa.accepts("c"));
    }

    #[test]
    fn test_email_like_pattern() {
        // Simplified email pattern: \w+@\w+\.\w+
        let word_char = Regex::union(vec![
            Regex::range('a', 'z'),
            Regex::range('A', 'Z'),
            Regex::range('0', '9'),
            Regex::char('_'),
        ]);
        let word = Regex::plus(word_char.clone());
        let email = Regex::concat(vec![
            word.clone(),
            Regex::char('@'),
            word.clone(),
            Regex::char('.'),
            word,
        ]);
        assert!(email.matches("user@example.com"));
        assert!(email.matches("test_123@domain.org"));
        assert!(!email.matches("invalid"));
        assert!(!email.matches("@missing.com"));
    }

    // Audit regression (theories-string): `DerivativeCache` keyed its
    // entries by a raw pre-computed `u64` hash with no follow-up equality
    // check, so two DIFFERENT regexes that happen to hash-collide would
    // silently share (and return each other's) cached derivative. This
    // constructs two structurally different regexes and confirms each
    // gets its own, independently-correct cached derivative.
    #[test]
    fn audit_derivative_cache_distinguishes_different_regexes() {
        let mut cache = DerivativeCache::new();

        let a = Regex::char('a');
        let b = Regex::char('b');

        let d_a = cache.derivative(&a, 'a');
        let d_b = cache.derivative(&b, 'b');

        // derivative of `a` w.r.t. 'a' is epsilon (nullable, matches "").
        assert!(d_a.matches(""));
        // derivative of `b` w.r.t. 'b' is ALSO epsilon -- but it must have
        // been computed independently (from `b`, not misappropriated from
        // the cached entry for `a`), and cross-checking against the wrong
        // *source* regex is exactly the failure mode a hash collision (or
        // a cache bug) would produce.
        assert!(d_b.matches(""));

        // A derivative that should NOT match must not do so because of a
        // cache mix-up: derivative of `a` w.r.t. 'b' is the empty language.
        let d_a_wrt_b = cache.derivative(&a, 'b');
        assert!(!d_a_wrt_b.matches(""));
        assert!(!d_a_wrt_b.matches("a"));

        // Re-querying the same (regex, char) pair must return the SAME
        // (cached) derivative rather than recomputing something different.
        let d_a_again = cache.derivative(&a, 'a');
        assert_eq!(*d_a_again, *d_a);
    }

    // Audit regression (theories-string): `Regex::union`/`Regex::inter`
    // used to canonicalize operand order via
    // `format!("{:?}", ...).cmp(...)` on the whole regex tree. Confirm the
    // real replacement (`regex_op_cmp`) still produces order-independent,
    // deduplicated results.
    #[test]
    fn audit_union_canonicalizes_regardless_of_input_order() {
        let a = Regex::char('a');
        let b = Regex::char('b');
        let c = Regex::char('c');

        let u1 = Regex::union(vec![a.clone(), b.clone(), c.clone()]);
        let u2 = Regex::union(vec![c.clone(), a.clone(), b.clone()]);
        let u3 = Regex::union(vec![b, c, a]);

        assert_eq!(u1, u2, "union must not depend on input order");
        assert_eq!(u1, u3, "union must not depend on input order");
    }

    #[test]
    fn audit_union_deduplicates_repeated_operands() {
        let a = Regex::char('a');
        let b = Regex::char('b');

        let u = Regex::union(vec![a.clone(), b.clone(), a.clone(), b]);
        if let RegexOp::Union(parts) = &u.op {
            assert_eq!(
                parts.len(),
                2,
                "duplicate operands must be removed after canonical sort"
            );
        } else {
            panic!("expected a Union node, got {:?}", u.op);
        }
    }

    #[test]
    fn audit_regex_op_cmp_is_consistent_with_eq() {
        // Structurally-equal regexes must compare as `Equal`, and the
        // comparator must be antisymmetric for structurally different
        // ones -- basic total-order sanity checks for the hand-written
        // comparator that replaced the `Debug`-string-based sort.
        let variants = vec![
            Regex::epsilon(),
            Regex::none(),
            Regex::all(),
            Regex::all_char(),
            Regex::char('x'),
            Regex::range('a', 'z'),
            Regex::star(Regex::char('x')),
            Regex::plus(Regex::char('x')),
            Regex::concat(vec![Regex::char('x'), Regex::char('y')]),
        ];

        for v in &variants {
            assert_eq!(regex_cmp(v, v), Ordering::Equal);
        }

        for i in 0..variants.len() {
            for j in 0..variants.len() {
                if i == j {
                    continue;
                }
                let ord_ij = regex_cmp(&variants[i], &variants[j]);
                let ord_ji = regex_cmp(&variants[j], &variants[i]);
                assert_eq!(
                    ord_ij,
                    ord_ji.reverse(),
                    "comparator must be antisymmetric for distinct regexes"
                );
                assert_ne!(
                    ord_ij,
                    Ordering::Equal,
                    "structurally different regexes must not compare Equal"
                );
            }
        }
    }
}

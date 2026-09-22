# Binary extension fields: representation and bounded QF_FF

This change adds F_2[X]/(f) to the existing finite-field theory, retaining
prime-field solving. This is a new supported fragment, not a heuristic
experiment or a claim of improved search performance.

## Representation and API

`(_ BinaryField 283)` denotes F_2[X]/(X^8+X^4+X^3+X+1). The decimal
index packs polynomial coefficients little-endian: bit i is the coefficient
of X^i, including the monic leading coefficient. The implicit prime base is
F_2. The constructor accepts degrees 2 through 256 and proves irreducibility;
zero, constants, degree-one descriptions, reducible polynomials (including
repeated factors), and degrees above the implementation bound are errors.
This syntax is a Nixie extension, not SMT-LIB standard or cvc5 syntax.

Elements are `(as ffN (_ BinaryField F))`, with 0 <= N < 2^degree(F).
N encodes coefficients in the polynomial basis 1,X,...,X^(k-1); it is
**not** an integer embedded in the field. In particular `ff2` denotes X,
whereas 1+1 is zero. Out-of-range or negative encodings are rejected,
not silently reduced as integers. `ff.add`, `ff.mul`, `ff.neg`, `=`, and
`distinct` retain their field meanings. `ff.bitsum` means sum_i (1+1)^i b_i,
so in characteristic two its value is b_0. There is no new division or
integer/bit-vector conversion operator.

The Rust entry points are `SortManager::binary_field(BigUint)`,
`FieldTable::intern_binary(BigUint)`, and existing `TermManager::mk_ff_*`
constructors. `BinaryField::new` constructs a checked immutable arithmetic
context; `add`, `mul`, `pow`, and `inverse` take canonical encodings and
return `None` on invalid operands (also on inversion of zero). `reduce`
explicitly reduces a binary polynomial, unlike element construction.
Field elements at the term/model layer always carry a `FieldId`.

The intern key includes the defining polynomial. The two F_8
representations with indices 11 and 13 have different identities and
cannot mix in an operation or equality. `FieldDesc::modulus()` retains
its historical meaning of **order**; `FieldTable::modulus(id)` remains
**prime-only**. That distinction fences existing prime algebra from
extension fields. `FieldKind::Extension` records characteristic, degree,
and the validated defining polynomial; primality evidence concerns the
characteristic, with irreducibility established separately.

## Supported solving and proof modes

Quantifier-free Boolean combinations of polynomial equalities and
disequalities are supported under QF_FF, including several independent
fields and `push`/`pop`/`assert`. The existing Boolean dispatcher calls a
separate bounded extension enumeration procedure. It considers all q^n
assignments in canonical order. The initial space bound is 2^22 points;
the ordinary per-conjunction work budget is 2^24 units. Units charge
assignment attempts, literal visits, DAG evaluation frames, additions,
and each coefficient step of the independent multiplication algorithm.
The Boolean loop additionally caps extension cases at 1024. Exhaustion
returns Unknown; only visiting every point without a solution returns
ordinary Unsat. These limits are deterministic, never wall-clock policy.

A field of degree 128 can be constructed, folded, and printed exactly,
but a symbolic 128-bit field variable exceeds the enumeration fragment.
There is no claim that this first procedure can solve a symbolic AES
circuit. Small systems over F_256 are supported within the work budget.

Extension-field UF applications (including QF_UFFF), quantifiers, other
mixed theories, and unsupported term shapes decline to Unknown. Existing
prime QF_UFFF remains enabled. Extension Gröbner bases, linear-core
elimination, minimal polynomials, general polynomial division/factorization,
and algebraic root certificates are not implemented or silently reused.
Root constraints are solved by exhaustive field evaluation within budget.

SAT is re-evaluated before installation; certified SAT additionally runs
the independent core AST evaluator. No extension UNSAT certificate is
exported. Certified mode therefore declines arithmetic enumeration
refutations to Unknown (a Boolean-only contradiction can still certify
through the existing Boolean checker). Prime ideal-membership, case-tree,
and cardinality certificates reject extension IDs. There is no extension
Alethe/LFSC/DRAT/assistant proof export promised by this fragment.

Models, default values, sort declarations, and arbitrary supported
field-valued `get-value` queries print the defining polynomial and canonical
element. Model definitions parse back into the same representation.

## Algorithm sources consulted before implementation

* Menezes, van Oorschot, Vanstone, *Handbook of Applied Cryptography*,
  sections 2.6 and 4.5.1, especially Algorithm 4.69 (Ben-Or):
  <https://cacr.uwaterloo.ca/hac/about/chap4.pdf>.
  For every i=1,...,floor(k/2), test gcd(f, X^(2^i)-X)=1. Every reducible
  degree-k polynomial has a factor of degree at most k/2; this includes
  nonsquarefree inputs. Repeated squaring and Euclidean polynomial
  remainder compute the test exactly.
* NTL `GF2XFactoring.cpp::IterIrredTest` (same test with batched gcds):
  <https://raw.githubusercontent.com/libntl/ntl/main/src/GF2XFactoring.cpp>.
  NTL GF2E representation/arithmetic contract:
  <https://libntl.org/doc/GF2E.cpp.html>. Nixie requires irreducibility,
  unlike NTL's more general quotient-ring context.
* Local cvc5 `src/util/finite_field_value.cpp`,
  `src/theory/ff/uni_roots.cpp`: the scalar representation and root splitter
  are prime-specific; distinct-root construction distinguishes characteristic
  from cardinality, but the later splitting code assumes prime fields.

No external arithmetic implementation is linked or added as a dependency.

## Independent layer audit and evidence

| Layer | Invariant and evidence |
|---|---|
| Identity | Interning uses the full polynomial, never cardinality alone. Tests distinguish both F_8 representations and refuse mixed terms. All sort readers/printers, including context reconstruction and structural sort names, preserve it. |
| Irreducibility | Exhaustive comparison against trial division for every monic binary polynomial of degree 2..8, including squares and products without base-field roots. Construction is bounded at degree 256. |
| Exact arithmetic | Core uses carryless convolution followed by polynomial long division. Tests use independent coefficient arrays; exhaustive tiny addition/multiplication and inverses, AES 0x57*0x83=0xc1, and degree-128 high-bit reduction and inversion. No truncation to machine integers. |
| Inversion | Nonzero a maps to a^(q-2), using q=2^k, not p=2. Every tiny inverse is checked against an independently found multiplicative partner; zero and noncanonical operands reject. |
| Rewriting | Binary terms have a separate fold; prime integer scalar collection never sees them. Negation is identity; bitsum uses characteristic two. Raw-AST tests bypass folds so an outer fix cannot mask evaluator defects. |
| Polynomial/GB algorithms | Audited `FieldCtx`, `UniPoly` derivative/squarefree/division, `MPoly`, Buchberger/front-end, minimal-polynomial and root paths. They require prime coefficient embeddings, p-based inverses and/or odd-characteristic splitting. Binary conjunctions dispatch before all of them; prime-only modulus access remains a second fence. |
| Roots/characteristic | Every quadratic over F_4, both F_8 representations, and F_16 is checked against independently enumerated root sets, including zero derivative/repeated roots, no roots and the zero polynomial. No x^p-x assumption is reused for extensions. |
| Search and budgets | Enumeration separates complete exhaustion from unsupported input/work exhaustion. Zero/tiny budgets reject; >2^22 spaces reject before exponentiation; every missing evaluation declines rather than counting as false. |
| Validation | Theory evaluation uses shift-and-reduce multiplication, independent of core's convolution/division. Cached core model evaluation checks representation, canonical leaves and sorts. Invalid and foreign assignments reject; a 20,000-deep AST plus shared squaring DAG stays iterative and memoized. |
| Combination | Pure QF_FF slices are separated by FieldId; extension UF combinations decline before prime QF_UFFF completion/cardinality code. Tests distinguish order four from characteristic two, and cover independent representations. |
| Certificates | Every prime replay entry point still requires a prime modulus. A separate defect was found: cardinality replay trusted the claimed field without checking the arguments' sorts. It now binds every argument to the certificate FieldId. Direct forged F_2 certificates over satisfiable F_3 and F_4 triples regress this defect; a genuine F_2 refutation still verifies. Ideal-membership/case-tree replay independently checks variable sorts and constant fields while re-encoding, so that same substitution cannot bypass their prime fence. Certified extension arithmetic Unsat becomes Unknown. |
| Scope/readback | Push/pop/assert sequences, compound get-value, printed-model round trips, and independently planted F_8/F_256 witnesses are exercised end to end. Compound field readback previously echoed the query; it now evaluates exactly for prime and binary fields. |

## Landing verification and performance protocol

Required workspace checks, prime FF regressions, Z3 parity (installed
4.16.0), and the pinned deterministic-counter perf gate are run before
landing. Z3 has no FF theory; it is a shared-code regression canary, not
an extension-field oracle. The independent tests above supply that oracle.

Performance pre-registration: this change makes no search-heuristic
selection change and claims no speedup. Run the standard perf landing
gate once against its pinned cached baseline, retain its raw result,
and report verdict/solved-count parity plus deterministic counter ratios.
Do not interpret this gate as an extension-field performance experiment.
No wall-clock number is a primary metric or solver policy input. Any future
extension search optimization needs a separately registered experiment and
run-once cells in the benchmark store under docs/BENCHMARKING.md.

Verification on the isolated implementation at base `1c9a2ef8`:

* `cargo build --all-features`: passed.
* `cargo nextest run --workspace --all-features`: 12,260 passed, 17 existing
  skips, no failures (385 test binaries).
* `cargo test --workspace --all-features --doc`: 114 passed, 31 ignored.
* `cargo clippy --all-features --all-targets -- -D warnings`: passed.
* `cargo fmt --all -- --check`: passed.
* `RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --all-features`: passed.
* The separately required ignored `pete_cxs_bp_is_unsat_on_every_trajectory`
  canary passed with workspace/all-features unification. An initial
  package-only invocation was canceled during its redundant compilation;
  it produced no test verdict.

* `./bench/z3_parity/run_parity.sh`, Z3 **4.16.0**: 177 cases,
  176 decisive matches, zero wrong answers, one inconclusive case
  (`array_unique.smt2`: Nixie Unsat, Z3 Unknown). Unknown is not counted as
  agreement.

* Standard perf gate against pinned `28e82c65`: **PASS**, 12 matching
  verdicts, nine nontrivial counter pairs and three trivial cases, no lost
  samples. Conflict and decision geomeans are both **1.000**. The printed
  wall ratio (1.03) is observational, not evidence of a speed change.
  Frozen workspace release binary SHA-256:
  `8419990f520d2a435b21e1a1eeb71ff72091fa4d9a7d17e289cd7d452cf5e3c5`.
  This gate was run once with its default seed and external cap; no
  heuristic performance claim is made.

Raw verification logs, parity JSON, and the binary are retained in the
untracked commit-addressed `precompile/` cache.

### Integration with concurrent main changes

The feature commit is `f8a8ca0d`; merge `4ce171d8` integrates the concurrently
landed CP scheduling changes and documentation without conflicts. The
integrated workspace release rebuild is byte-for-byte identical to the
frozen binary above. Its perf measurement is therefore **reused**, not
rerun. The integrated Z3 4.16.0 parity check again has 176 decisive matches,
zero mismatches and the same one inconclusive case out of 177. All integrated
workspace checks passed: build, **12,261 nextest tests**
(17 existing skips), **114 doctests** (31 ignored), Clippy with warnings
as errors, formatting, and warning-free documentation. The extra arrangement
canary passed in the feature verification; the merge did not modify its
arrangement or model-checking code. A CLI smoke test over `(_ BinaryField 7)`
returned `a = ff2` for `a*a = a+1` and evaluated `a*a` as `ff3`.

Integrated logs and parity JSON live under
`precompile/4ce171d811802c30cdb49a954b77c3feeabcf351/benchmark/binary-extension-landing/`;
`verification.json` records the reused performance result's source commit
and binary digest. No performance cell was rerun.

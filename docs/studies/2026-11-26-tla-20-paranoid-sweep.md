# Issue #20 – the `--paranoid` corpus sweep, a falsified frame, and two soundness fixes

`--paranoid` (issue #20, step 6) asks the solver, at every step and for
every framed variable, whether a member of the variable can lie outside the
universe the frame analysis derived: `Init /\ Trans_{<k} /\ ~(v@k \subseteq
U_k)`. `Unsat` discharges it; `Sat` or `Unknown` fails closed. Until now
that was pinned by two unit tests and never run over the corpus. This is
the sweep, what it found, and what followed.

## The sweep

`bmccheck` grew `NIXIE_BMC_PARANOID=1` (the same probe, the same 20 000
conflicts per query, every module of `tlaplus-examples` + `apalache/test`).
Binary: `main` @ `47b5c438` with that knob. 907 modules; the plain run is
the `new` arm of the #46 study (same binary, probe off).

| | plain | `--paranoid` |
|---|---:|---:|
| no-violation | 77 | 75 |
| violation | 21 | 21 |
| deadlock | 7 | 6 |
| undecided | 62 | 36 |
| blocked | 277 | 304 |
| timeout (1 500 s) | 0 | 2 |

**No verdict changed into another verdict.** Every module that moved went
to `blocked` (30, by the probe) or `timeout` (2: `Paxos.tla` in both Paxos
directories, which the plain run blocks at the first invariant encoding;
with the probe on, the step-0 obligation is asked first and does not finish).
Of the 30 the probe stopped:

| the probe's answer | count |
|---|---:|
| containment **is undecided** (the budget ran out) | 26 |
| containment **could not be stated** (the universe term cannot be built) | 2 – `Bug1682.tla` `messages`, `CigaretteSmokers.tla` `dealer` |
| containment **is falsified** (`Sat`) | **1 – `Rand.tla`, `S` at step 0** |

What the 30 were without the probe: 26 `undecided` anyway, 2 `no-violation`
(`ModelVal.tla`, `locks_auxiliary_vars/Peterson.tla`), 1 `deadlock`
(`Bug20190118.tla`). Those three verdicts rest on frames whose containment
the solver could not confirm within the budget; none was shown unsound.

## The falsified frame: `Rand.tla`

```tla
Init == /\ S \in SUBSET (1..10)
        /\ Cardinality(S) >= 5
Next == \/ \E x \in S: x % 2 = 0 /\ S' = (S \ { x }) \union { x + x }
       \/ \E x \in S: x % 2 /= 0 /\ S' = S \ { x }
```

`S@0` is a five-member subset of `1..10`; the frame's universe for `S` held
**one** term, `{x#1!skolem1 + x#1!skolem1}` – a sum over a skolem witness.
Two things were wrong at once.

**The frame analysis took an unreadable assignment for an empty one.**
`analyze` starts every set variable at the *empty* universe ("a weak one,
grown by the transition's assignments") and `offer` ignored a right-hand
side `elements` could not read: `S \in SUBSET (1..10)` contributed nothing,
and nothing poisoned `S`. The transition then grew the empty universe by
whatever its assignments did read – and what it read was the witness.

**So `S` was framed with a universe that misses every member but one**, and
a `\A y \in S` instantiated over it would have skipped the rest. On
`Rand.tla` the invariant's quantifier is an existential, skolemized rather
than enumerated, and the run was `undecided` anyway; no verdict rested on
it. The next specification need not be so lucky.

### The fix: read what can be read, refuse what cannot

Two things were wrong with the frame, and the first cut fixed only one.

**An unreadable assignment must poison the variable.** `offer` records a
right-hand side with no certain-superset reading and the round's end marks
the variable `NoFrame::Unreadable` – here and in every later round, so
nothing the transitions grow is mistaken for a frame. `elements`' own
contract said so all along ("a shape without a certain-superset reading is
`None`, and the variable stays unframed"); the implementation kept that
promise only when nothing else had framed the variable. A set-valued
conditional (`v' = IF c THEN v \cup {1} ELSE v`) is read as both branches,
an over-approximation in the sound direction.

**`v \in SUBSET T` is readable**: `v`'s members are among `T`'s, so the
base is the superset (and `v \in UNION S` is the members of `S`'s
members). Taken as unreadable, `chosen \in SUBSET {"a", "b", "c"}`
poisoned `chosen` in `MCConsensus.tla` and took a deadlock verdict with it;
taken as nothing, it was `Rand.tla`'s falsified frame. With the base read,
`Rand.tla`'s `S` is framed over `1..10` and the probe no longer falsifies
it.

**The witness is a sound candidate where it is received.** `sent' = sent
\cup {c}` under `\E d \in Data : Send(d)` grows `sent` by exactly `c`;
`sent` – framed from a readable `Init` – must keep that candidate, or
`\A m \in sent` would skip the message just added (the Channel shape,
pinned both ways). And since the previous section made a witness one
variable per step, an element that mentions one is read at **every** step
up to the one being encoded: the member it denotes was added by whichever
earlier transition fired the quantifier, and stays. Read at the current
step alone it named the *next* transition's witness – `Paxos/Consensus.tla`
(`chosen' = {c}` under `\E v \in Value`) was falsified at step 1 that
way, a second time.

With the fixes, re-running the probe on the 29 with this tree: **none
falsified**, 23 undecided, 3 that still cannot be stated (`Bug1682.tla`
`messages`, `Bug20190118.tla` `msgs`, `CigaretteSmokers.tla` `dealer`), and
3 whose obligations are now discharged within the budget (`Rand.tla`,
`EWD840.tla`, `APEWD840.tla`; their checks run on to `undecided`). The
undecided obligations are set-theory queries of the kind #49 makes slow; a
universe with an element the encoder cannot build cannot be asked about at
all – a named gap for #20.

## Found on the way: one skolem witness for the whole unrolling

The debug print that showed the witness entering `S`'s universe showed its
name: `x#1!skolem1`, a free name – a **rigid constant**, one SMT variable
for the whole unrolling. `\E k \in Nat : P(k)` in `Next` picks a `k` at
every step; the encoding kept every step to the same one:

```tla
Init == x = 0
Next == \E k \in Nat : (k = 2 \/ k = 3) /\ x' = x + k
Inv  == x # 5
```

`nixie-tla check --inv=Inv --length=2` printed *no counterexample of 2
step(s) or fewer* (exit 0). The behaviour `0 -> 2 -> 5` breaks the
invariant at step 2; the same spec over the literal set `{2, 3}` –
enumerated exactly, never skolemized – found it and replayed it.

A witness now gets one SMT variable **per step** (`nixie_tla::lower::
is_skolem_witness`; the encoder treats it as flexible, like a `VARIABLE`),
the read-back decodes it per state, and the replay confirms the
counterexample with `k = 3` on the first step and `k = 2` on the second.
Landed before the frame fix, on its own (`tests/skolem.rs`).

This was not visible in the corpus because every module that skolemizes
was `undecided` at the budget (the step-4 cells of #20) or blocked later.
It is the kind of defect the corpus cannot see and a two-line spec can.

## Corpus A/B of the two fixes

`bmccheck`, 907 modules, depth 4, 20 000 conflicts; `main` @ `47b5c438`
with the #46 harness against this tree (the skolem fix, the frame fix, and
the inline roles).

| | `main` | this tree |
|---|---:|---:|
| no-violation | 77 | 77 |
| violation | 21 | 21 |
| deadlock | 7 | 7 |
| undecided | 62 | 62 |
| blocked | 272 | 267 |
| skipped | 465 | 467 |
| timeout (1 500 s) | 3 | 6 |

**Identical class for class on every verdict.** The moves: three
`Paxos*.tla` modules that `blocked` on `main`'s arm and exceeded the cap
here – `main`'s own binary exceeds it too when run alone at the time of
writing; a front-end cost that varies from run to run, not a change in what
they answer – and two modules whose `SPECIFICATION` the inline-role change
reads and which then have no invariant to check (`test64a`,
`EWD998ChanTrace`; the harness now prints the reason). `Rand.tla` is
`undecided` on both, on a frame the probe now discharges.

The first cut of the frame fix (frames on the pre-skolemization roles) was
measured the same way before it was replaced: it withdrew the two
`MCConsensus` deadlocks. The measurement is what sent it back.

## What `--paranoid` is for, and what it is not

The probe found one falsified frame in 907 modules and could not decide 26;
`--paranoid` remains opt-in because it roughly doubles the query count and
its obligations are as hard as the specification's own set theory. What it
is good at is exactly this: turning an argument ("the fixpoint says
containment holds") into a question the solver answers per specification,
so that a counterexample to the argument is a cell in a table rather than a
wrong `NoError` a user finds. The fixes above came from reading one cell.

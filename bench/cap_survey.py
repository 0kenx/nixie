#!/usr/bin/env python3
"""Completeness-cap survey for the eager set/bag reductions.

The caps (`bag_elements=24`, `bag_pairs=128`, `set_count_elements=24`,
`set_derived_elements=24`, `set_cone_sets=40`) bound the reductions'
identity products. A firing is a completeness event: the construct is
skipped and a `Sat` degrades to `Unknown` (every `Unsat` stays sound).
This survey measures the two things a re-tuning decision needs:

1. **Where the workloads actually sit.** Generators span element counts
   4..64 over the bag and set surfaces, and report the verdict at the
   default caps vs raised caps (`NIXIE_CAPS=…`), with runtimes — the
   completeness each band buys and what it costs.
2. **What the corpora hit.** Any `.smt2` files passed as arguments are run
   under `NIXIE_DEBUG_CAPS=1` and the `[cap]` lines tallied.

Usage: python3 bench/cap_survey.py [nixie] [--corpus FILE.smt2 ...]
"""
import os, subprocess, sys, tempfile, time, collections

NIXIE = sys.argv[1] if len(sys.argv) > 1 else "target/release/nixie"
CAPS_DEFAULT = {}
CAPS_RAISED = {
    "bag_elements": 64,
    "bag_pairs": 512,
    "set_count_elements": 64,
    "set_derived_elements": 64,
    "set_cone_sets": 128,
}

def run(script, caps=None, timeout=20):
    env = dict(os.environ)
    env["NIXIE_DEBUG_CAPS"] = "1"  # tally fires regardless of the A/B side
    if caps:
        env["NIXIE_CAPS"] = ",".join(f"{k}={v}" for k, v in caps.items())
    else:
        env.pop("NIXIE_CAPS", None)
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(script)
        path = f.name
    try:
        t0 = time.monotonic()
        out = subprocess.run([NIXIE, path], capture_output=True, text=True,
                             timeout=timeout, env=env)
        dt = time.monotonic() - t0
        verdict = next((l.strip() for l in out.stdout.splitlines()
                        if l.strip() in ("sat", "unsat", "unknown")), "none")
        hits = [l for l in (out.stdout + out.stderr).splitlines()
                if l.startswith("[cap]")]
        return verdict, dt, hits
    except subprocess.TimeoutExpired:
        return "timeout", timeout, []
    finally:
        os.unlink(path)

def bag_script(n, true_card):
    # `bag.union_disjoint` is binary; left-fold an n-element chain.
    chain = f"(bag 0 2)"
    for i in range(1, n):
        chain = f"(bag.union_disjoint {chain} (bag {i} 2))"
    return f"""(set-logic ALL)
(assert (= (bag.card {chain}) {true_card}))
(check-sat)
"""

def set_script(n, true_card):
    elems = " ".join(str(i) for i in range(n))
    return f"""(set-logic ALL)
(assert (= (set.card (set.union (set.insert {elems} (as set.empty (Set Int))))) {true_card}))
(check-sat)
"""

def survey_generator(name, gen, true_total):
    print(f"\n== {name}: verdict by element count (default vs raised caps)")
    print(f"{'n':>4} {'default':>9} {'t(s)':>6} {'raised':>9} {'t(s)':>6} cap-fires(default)")
    for n in [4, 8, 16, 24, 25, 32, 48, 64]:
        want = true_total(n)
        vd, td, hd = run(gen(n, want))
        vr, tr, hr = run(gen(n, want), CAPS_RAISED)
        fired = collections.Counter(h.split()[1] for h in hd)
        fired_s = ",".join(f"{k}x{v}" for k, v in fired.items()) or "-"
        print(f"{n:>4} {vd:>9} {td:>6.2f} {vr:>9} {tr:>6.2f} {fired_s}")

def main():
    survey_generator("bag cardinality", bag_script, lambda n: 2 * n)
    survey_generator("set cardinality", set_script, lambda n: n)
    corpus = [a for a in sys.argv[2:] if a.endswith(".smt2")]
    if corpus:
        print(f"\n== corpus cap-fires over {len(corpus)} files")
        tally = collections.Counter()
        for path in corpus:
            v, dt, hits = run(open(path).read(), timeout=60)
            for h in hits:
                tally[h.split()[1]] += 1
            # one file's script
        for k, v in tally.most_common():
            print(f"  {k}: {v}")
        if not tally:
            print("  (none)")

if __name__ == "__main__":
    main()

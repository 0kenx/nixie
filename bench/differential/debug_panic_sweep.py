#!/usr/bin/env python3
"""Run a corpus through the DEBUG nixie binary (overflow-checks on): every
panic is an unchecked fixed-width arithmetic site that silently wraps in
release — a wrong-verdict hazard, in ANY theory, not just arithmetic.

The oracle that made the 2026-09-14 arithmetic hunt mechanical: the debug
profile turns every wrap into a loud abort with a backtrace naming the
site. Sweep whatever corpus you have (glob patterns as arguments):

    python3 bench/differential/debug_panic_sweep.py \
        target/debug/nixie 'bench/z3_parity/benchmarks/**/*.smt2'

Baseline (2026-09-14, main 931e318f): 490 files across the parity corpus,
the 270-instance pinned differential sample and the extended-theories
corpus — zero panics (the two nonzero exits there are honest logic-
contract rejections, not crashes)."""
import subprocess, sys, glob, collections, os

BIN = sys.argv[1]
roots = sys.argv[2:]
TIMEOUT = 20

files = []
for r in roots:
    files += sorted(glob.glob(r, recursive=True))
stats = collections.Counter()
panics = []
for i, f in enumerate(files):
    try:
        with open(f, 'rb') as fh:
            data = fh.read(2_000_000)
        data2 = b"\n".join(l for l in data.splitlines() if not l.lstrip().startswith(b";"))
        if not data2.lstrip().startswith(b"("):
            continue  # not SMT-LIB
        p = subprocess.run([BIN, f], capture_output=True, text=True, timeout=TIMEOUT, input="")
        err = p.stderr
        if "panicked at" in err:
            loc = [l for l in err.splitlines() if "panicked at" in l][0]
            frame = [l for l in err.splitlines() if "nixie_" in l][:2]
            panics.append((f, loc.split("panicked at ")[1], frame))
            stats["panic"] += 1
        elif p.returncode != 0:
            stats["fail"] += 1
        else:
            out = p.stdout.strip().splitlines()
            v = out[-1] if out else "?"
            stats[v.split()[0] if v else "?"] += 1
    except subprocess.TimeoutExpired:
        stats["timeout"] += 1
    except Exception as e:
        stats["err"] += 1
print(f"{len(files)} files")
for k, v in stats.most_common():
    print(f"  {k}: {v}")
for f, loc, frame in panics[:10]:
    print(f"PANIC {f}\n  {loc}\n  {' / '.join(x.strip() for x in frame)}")

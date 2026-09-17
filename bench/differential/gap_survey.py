#!/usr/bin/env python3
"""The gap survey: nixie `unknown` where z3 is decisive, captured for replay.

Reuses `mixed_fuzz.py`'s generator verbatim (imported, never copied, so the
seed -> instance mapping is identical to the standing differential) and adds
a capture loop: every instance where nixie answers `unknown` (or times out)
while z3 decides is written to disk under a run directory, with a manifest
recording both verdicts.  Re-run on the same seeds to attribute a delta;
fresh seeds hunt new members (the arc's rule: extend SHAPES, not seeds).

Usage:
    python3 bench/differential/gap_survey.py <nixie> <outdir> <n> <seeds...>

Example (the standing survey, ~181 members on a post-item-66 binary):
    python3 bench/differential/gap_survey.py precompile/<sha>/nixie /tmp/gap 600 20261000 20261001 20261002
"""
import json
import os
import subprocess
import sys
import tempfile
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

NIXIE = sys.argv[1]
OUTDIR = sys.argv[2]
N = int(sys.argv[3])
SEEDS = [int(s) for s in sys.argv[4:]]

# mixed_fuzz.py runs its loop at import: import it with N=0 (a no-op run) and
# its own argv temporarily swapped in, so only the generator survives.
_argv, sys.argv = sys.argv, [sys.argv[0], NIXIE, "0", str(SEEDS[0])]
import contextlib, io  # noqa: E402

with contextlib.redirect_stdout(io.StringIO()):
    import mixed_fuzz  # noqa: E402  (the generator is the module's own)
sys.argv = _argv


def run(binary, path):
    args = [binary, path]
    try:
        out = subprocess.run(args, capture_output=True, text=True, timeout=10).stdout
    except subprocess.TimeoutExpired:
        return "timeout", None
    lines = [l.strip() for l in out.splitlines() if l.strip() and not l.startswith("Processing")]
    if not lines:
        return "none", None
    return lines[0], "\n".join(lines[1:])


def main():
    os.makedirs(OUTDIR, exist_ok=True)
    stats = collections.Counter()
    manifest = []
    for seed in SEEDS:
        mixed_fuzz.random.seed(seed)
        for i in range(N):
            src = mixed_fuzz.gen()
            with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
                f.write(src)
                path = f.name
            try:
                nz, _ = run(NIXIE, path)
                z3v, _ = run("z3", path)
                stats[f"nixie={nz}"] += 1
                stats[f"z3={z3v}"] += 1
                if nz == "unknown" and z3v in ("sat", "unsat"):
                    stats[f"gap_{z3v}"] += 1
                    name = f"gap_s{seed}_i{i}_{z3v}.smt2"
                    with open(os.path.join(OUTDIR, name), "w") as g:
                        g.write(src)
                    manifest.append(
                        {"seed": seed, "idx": i, "z3": z3v, "file": name}
                    )
                elif nz == "timeout":
                    stats["nixie_timeouts"] += 1
                    if z3v in ("sat", "unsat"):
                        stats[f"timeout_gap_{z3v}"] += 1
            finally:
                os.unlink(path)
    with open(os.path.join(OUTDIR, "manifest.json"), "w") as f:
        json.dump(manifest, f, indent=1)
    for k, v in sorted(stats.items()):
        print(f"  {k}: {v}")
    print(f"captured {len(manifest)} gap members to {OUTDIR}")


if __name__ == "__main__":
    main()

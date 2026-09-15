#!/usr/bin/env python3
"""Serial back-to-back A/B wall check: treatment (flag off) vs pre-change
baseline, 3 repetitions each, alternating order per rep to cancel drift."""
import subprocess, sys, time
from pathlib import Path

ROOT = Path("/media/data/proj/nixie")
BIN = ROOT / "outputs/target-csr/release/examples/cnf_solve"
BASE = ROOT / "outputs/target-baseline/release/examples/cnf_solve"
files = [
    "af750c18578d52e60472315692ad83c0-si2-b03m-m800-03",
    "ddc0720fa5a91d9cc0dc726644ab9e9f-6s167-opt",
    "9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized",
    "170b13af977e962321c493544b2bd0a9",
    "8b31606e10656ff7eb2936262b647443",
]
def run(b, f):
    t0 = time.monotonic()
    subprocess.run([str(b), str(f)], capture_output=True, timeout=300)
    return time.monotonic() - t0
for frag in files:
    hits = sorted((ROOT / "precompile/corpus-sc24f").glob(frag + "*"))
    if not hits:
        print(f"{frag}: NOT FOUND")
        continue
    f = hits[0]
    ta, tc = [], []
    for rep in range(3):
        if rep % 2 == 0:
            tc.append(run(BASE, f)); ta.append(run(BIN, f))
        else:
            ta.append(run(BIN, f)); tc.append(run(BASE, f))
    ma, mc = sorted(ta)[1], sorted(tc)[1]
    print(f"{f.name[:52]:52s} base={mc:6.2f}s treat={ma:6.2f}s ratio={ma/mc:.3f}")

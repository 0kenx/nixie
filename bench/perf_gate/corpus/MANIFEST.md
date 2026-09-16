# perf-gate corpus (in-repo core)

Nine SATCOMP 2025 main-track instances, chosen for: deterministic verdicts,
0.05-47 s solve time at the 2026-09-15 post-env-fix HEAD, and coverage of
the families that carried the 36 h regression signal (SCPC, frb, WS,
circuit, hwmcc, GP; plus the s38584/x9/Carry/6s299 set used in the study).
Stored xz-compressed; run_gate.sh decompresses into .cache/ (gitignored).

Provenance: satcomp2025/main_2025 (benchmark-database.de, track=main_2025,
downloaded 2026-09-15 — see satcomp2025/main_2025/PROVENANCE.md in the
primary checkout).  Selection recorded in
docs/studies/2026-09-15-env-probe-regression.md.

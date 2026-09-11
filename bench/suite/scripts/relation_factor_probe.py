#!/usr/bin/env python3
"""One registered relation-factorization feasibility cell, including preprocessing.

Also independently checks every binary resolution, output ID and local truth
table. See docs/studies/2026-09-08-relation-factorization.md. No solver reruns.
"""
import argparse
import datetime
import json
import os
import platform
import re
import signal
import subprocess
import time
from pathlib import Path

import benchstore
from watch_group_probe import check_model, digest

if not __debug__:
    raise RuntimeError("certificate auditing requires Python assertions; do not use -O")

SUITE = "relation-factorization-feasibility"
INPUT_HASH = "d3338c04e29f5c8b7e75686fa30fd9927babb7b34b9f7c87785397662f59d8e2"


def read_cnf(path):
    header, clauses, pending = None, [], []
    for line in path.read_text().splitlines():
        tokens = line.split()
        if not tokens or tokens[0] == "c":
            continue
        if tokens[0] == "p":
            assert header is None and len(tokens) == 4 and tokens[1] == "cnf"
            header = tuple(map(int, tokens[2:]))
            continue
        assert header is not None
        for lit in map(int, tokens):
            if lit:
                assert 0 < abs(lit) <= header[0]
                pending.append(lit)
            else:
                clauses.append(tuple(pending))
                pending = []
    assert header is not None and not pending and len(clauses) == header[1]
    return header[0], clauses


def check_certificate(original_path, output_path, proof_path, map_path):
    """Independent set-resolution checker plus exhaustive reverse implication."""
    vars_, original = read_cnf(original_path)
    out_vars, output = read_cnf(output_path)
    mapping = json.loads(map_path.read_text())
    assert vars_ == out_vars
    active = {i: frozenset(c) for i, c in enumerate(original, 1)}
    supports = {i: tuple(sorted(map(abs, c))) for i, c in enumerate(original, 1)}
    old_rows = {}
    for support, c in zip(supports.values(), original):
        if len(support) == 8 and len(set(support)) == 8:
            row = sum(1 << support.index(abs(lit)) for lit in c if lit < 0)
            old_rows.setdefault(support, set()).add(row)
    added, deleted, latest = 0, 0, len(original)
    with proof_path.open() as proof:
        for line in proof:
            fields = line.split()
            assert fields
            if fields[1] == "d":
                assert int(fields[0]) == latest and fields[-1] == "0"
                for ident in map(int, fields[2:-1]):
                    assert ident in active
                    del active[ident]
                    del supports[ident]
                    deleted += 1
                continue
            values = list(map(int, fields))
            ident = values[0]
            end = values.index(0)
            literals = values[1:end]
            assert ident == latest + 1 and values[-1] == 0 and len(values[end + 1:-1]) == 2
            a, b = values[end + 1:-1]
            assert 0 < a < ident and 0 < b < ident and a in active and b in active
            left, right = active[a], active[b]
            assert supports[a] == supports[b]
            pivots = left & {-lit for lit in right}
            assert len(pivots) == 1
            pivot = next(iter(pivots))
            expected = (left - {pivot}) | (right - {-pivot})
            assert len(literals) == len(expected) and frozenset(literals) == expected
            assert not (expected & {-lit for lit in expected})
            active[ident], supports[ident] = expected, supports[a]
            latest, added = ident, added + 1
    ids = mapping["clause_ids"]
    assert latest == mapping["summary"]["last_proof_id"]
    assert added == mapping["summary"]["resolutions"]
    assert len(ids) == len(output) == len(active) and len(set(ids)) == len(ids)
    new_cubes = {}
    for ident, c in zip(ids, output):
        assert active[ident] == frozenset(c)
        if ident <= len(original):
            assert c == original[ident - 1]
            continue
        support = supports[ident]
        assert len(support) == 8 and len(set(support)) == 8
        mask = sum(1 << support.index(abs(lit)) for lit in c)
        forbidden = sum(1 << support.index(abs(lit)) for lit in c if lit < 0)
        new_cubes.setdefault(support, []).append((mask, forbidden))
    retained_ids = set(ids)
    for ident, c in enumerate(original, 1):
        if ident not in retained_ids:
            support = tuple(sorted(map(abs, c)))
            assert len(support) == 8 and len(set(support)) == 8
            assert support in new_cubes, "deleted an original outside a certified replacement"
    checks = 0
    for support, cubes in new_cubes.items():
        assert len(old_rows[support]) == 240 and len(cubes) == 64
        assert all(mask.bit_count() == 5 for mask, _ in cubes)
        for row in range(256):
            assert all(row & mask != forbidden for mask, forbidden in cubes) == (row not in old_rows[support])
            checks += 1
    return dict(resolutions_checked=added, deleted_ids_checked=deleted,
                relations_checked=len(new_cubes), assignments_checked=checks,
                output_clauses_checked=len(output))


def perf_run(command, label, directory, env):
    raw = {kind: directory / f"{label}.{kind}" for kind in ("stdout", "stderr", "perf")}
    argv = ["taskset", "-c", "2", "perf", "stat", "-x", ";", "-o", str(raw["perf"]),
            "-e", "instructions:u,cycles:u", "--", *map(str, command)]
    result_path = directory / f"{label}.result.json"
    command_path = directory / f"{label}.command.json"
    if result_path.exists():
        assert json.loads(command_path.read_text()) == argv
        return json.loads(result_path.read_text())
    with command_path.open("x") as file:
        json.dump(argv, file, indent=2)
    start, timeout = time.monotonic(), False
    with raw["stdout"].open("x") as out, raw["stderr"].open("x") as err:
        process = subprocess.Popen(argv, env=env, stdout=out, stderr=err, start_new_session=True)
        try:
            status = process.wait(timeout=300)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            status, timeout = process.returncode, True
    metrics, events = {}, []
    for line in raw["perf"].read_text().splitlines():
        fields = line.split(";")
        if len(fields) <= 2:
            continue
        # Hybrid Intel PMUs print both atom/core variants, with the inactive
        # variant '<not counted>' under a fixed CPU affinity. Retain exactly
        # one counted event per metric, rather than silently losing this host.
        event = re.fullmatch(r"(?:cpu_(?:core|atom)/)?(instructions|cycles)(?::u|/u)", fields[2])
        if event:
            if fields[0].strip() == "<not counted>":
                continue
            assert fields[0].strip().isdigit(), "PMU count unavailable"
            name = event.group(1)
            assert name not in metrics, "multiple counted PMUs under fixed CPU affinity"
            metrics[name] = int(fields[0])
            events.append(fields[2])
            # Require no multiplexing; counter coverage is whole process.
            if len(fields) > 4:
                assert float(fields[4].replace("%", "")) >= 99.9
    assert set(metrics) == {"instructions", "cycles"}
    result = dict(status=status, timeout=timeout, wall_clock_s=time.monotonic() - start,
                  metrics=metrics, pmu_events=events, artifacts={k: str(v) for k, v in raw.items()})
    with result_path.open("x") as file:
        json.dump(result, file, indent=2)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--sha", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    sha = subprocess.check_output(["git", "rev-parse", args.sha], text=True).strip()
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == sha
    assert not subprocess.check_output(["git", "status", "--porcelain"], text=True)
    cache = root / "precompile" / sha[:7]
    factor, solver = cache / "relation_factor", cache / "cnf_solve"
    inputs = list((root / "satcomp2024/bench").glob("*circuit*.cnf"))
    assert len(inputs) == 1 and digest(inputs[0]) == INPUT_HASH
    cnf = inputs[0]
    flags = dict(cpu=2, seed=1, max_conflicts=10_000_000, preset="CaDiCaL",
                 algorithm="exact-8var-4input-lexicographic-v1", profile="release",
                 solver_sha256=digest(solver), pmu=["instructions:u", "cycles:u"],
                 pmu_scope="user-space",
                 limits=[2_000_000, 16_000_000, 10_000, 5_000_000],
                 emergency_timeout_s=300, print_model=True, proof_prefix=True)
    record = dict(schema=benchstore.SCHEMA, suite=SUITE,
                  created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  host=dict(id=platform.node(), cpu="Intel Core Ultra 7 265K, CPU 2", os=platform.platform()),
                  git=dict(sha_long=sha, sha_short=sha[:7], dirty=False),
                  binary=dict(path=str(factor), sha256=digest(factor)),
                  instance=dict(name="circuit_48in64out", family="circuit_48in64out", sha256=INPUT_HASH),
                  config=dict(id="exact-relation-factor", flags=flags, features=[],
                              cmdline=["python3", "bench/suite/scripts/relation_factor_probe.py",
                                       "--root", str(root), "--sha", sha]), seed=1,
                  arm=dict(role="treatment"))
    record["config_hash"] = benchstore.canonical_flags(flags)
    dest = benchstore.record_path(root / "precompile", record)
    if dest.exists():
        prior = json.loads(dest.read_text())
        benchstore.validate(prior)
        assert benchstore.canonical_join_key(prior) == benchstore.canonical_join_key(record)
        print("reuse", prior["record_id"])
        return
    directory = cache / "benchmark" / SUITE
    directory.mkdir(parents=True, exist_ok=True)
    manifest = directory / "manifest.started.json"
    if manifest.exists():
        previous = json.loads(manifest.read_text())
        assert benchstore.canonical_join_key(previous) == benchstore.canonical_join_key(record)
        record = previous
    else:
        with manifest.open("x") as file:
            json.dump(record, file, indent=2)
    transformed, proof, mapping = [directory / n for n in ("circuit.factored.cnf", "prefix.lrat", "map.json")]
    env = {k: v for k, v in os.environ.items() if not k.startswith((
        "NIXIE_", "ELS", "FACTOR", "NO_", "MAXC", "SEED", "INPROC", "STAB_",
        "REPHASE", "WALK", "RANDPOL", "PRINT_MODEL", "PHASE_HINT", "GATE_COUNT", "SCC_MASS"))}
    env.update(MAXC="10000000", SEED="1", DIAG="1", PRINT_MODEL="1", LC_ALL="C")
    print("start transformation", flush=True)
    transform = perf_run([factor, cnf, transformed, proof, mapping], "transform", directory, env)
    assert transform["status"] == 0 and not transform["timeout"]
    checks = check_certificate(cnf, transformed, proof, mapping)
    (directory / "certificate-check.json").write_text(json.dumps(checks, indent=2) + "\n")
    assert checks == dict(resolutions_checked=313600, deleted_ids_checked=436800,
                          relations_checked=700, assignments_checked=179200, output_clauses_checked=44864)
    print("certificate checked; start single solve", flush=True)
    solve = perf_run([solver, transformed], "solve", directory, env)
    stdout = Path(solve["artifacts"]["stdout"]).read_text()
    match = re.search(r"^result=(\w+)", stdout, re.M)
    answer = match.group(1).lower() if match else "unknown"
    checked = solve["status"] == 0 and answer == "sat"
    if checked:
        check_model(cnf, stdout)
        check_model(transformed, stdout)
    conflict = re.search(r"^conflicts=(\d+)", stdout, re.M)
    conflicts = int(conflict.group(1)) if conflict else None
    totals = {name: transform["metrics"][name] + solve["metrics"][name] for name in ("instructions", "cycles")}
    record.update(
        metrics=dict(primary=dict(name="instructions", value=totals["instructions"]),
                     secondary=dict(**totals, conflicts=conflicts,
                                    cycles_per_conflict=totals["cycles"] / conflicts if conflicts else None,
                                    transform=transform["metrics"], solve=solve["metrics"]),
                     counter_coverage_verified=True,
                     wall_clock_s=transform["wall_clock_s"] + solve["wall_clock_s"]),
        observations=dict(transform=transform, solve=solve, certificate=checks,
                          transformed_sha256=digest(transformed), proof_sha256=digest(proof),
                          map_sha256=digest(mapping), reported_answer=answer,
                          original_model_checked=checked, feasibility_passed=checked,
                          coverage="sum of whole-process user-space PMU counts for factorization/proof emission and solving; kernel work and independent audit checks excluded"),
        verdict=dict(answer=answer if checked else "unknown", verified_model_or_proof=checked))
    record["record_id"] = benchstore.record_id(record)
    benchstore.validate(record)
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open("x") as file:
        json.dump(record, file, indent=2, sort_keys=True)
        file.write("\n")
    (directory / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(dict(record=record["record_id"], answer=answer, conflicts=conflicts, **totals)), flush=True)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Canonical per-machine benchmark result store for OxiZ.

Results live under ./precompile/<sha>/benchmark/runs/<suite>/ (gitignored,
per machine). A measurement is identified by its join key:

    (host, git sha, binary sha256, suite, instance sha256, config id, seed)

Once a cell exists it must be reused, never re-run; experiments only execute
the cells `missing` reports. See docs/BENCHMARKING.md section 9.

Commands:
  record  RECORD.json        validate a record and file it into the store
  locate  --suite S --instance NAME (--host H | --any-host)
                             [--config C] [--seed N] [--sha X]
                             [--include-dirty] [--root R]
                             print paths of matching stored records
  missing MANIFEST.json      list experiment cells not yet in the store
  verify  [--root R]         revalidate every stored record

Manifest format (for `missing`):
{
  "suite": "satcomp25-easy",
  "host": "devbox",
  "configs": ["default", "rephase-null"],
  "seeds": [0, 1, 2],
  "instances": [{"name": "6s167-opt.cnf",
                 "path": "satcomp2025/main_easy_mid/6s167-opt.cnf"}]
}
`path` may be omitted if the instance carries an explicit "sha256".
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

SCHEMA = "oxiz-bench-record/1"
ARM_ROLES = {"treatment", "null", "baseline", "reference"}
VERDICTS = {"sat", "unsat", "unknown"}

HEX64 = re.compile(r"[0-9a-f]{64}")

SUBOBJECT_KEYS = {
    "host": {"id", "cpu", "os"},
    "git": {"sha_long", "sha_short", "dirty"},
    "binary": {"path", "sha256"},
    "instance": {"name", "sha256", "family", "sat_expected"},
    "config": {"id", "flags", "features", "cmdline"},
    "metrics": {"primary", "secondary", "wall_clock_s", "counter_coverage_verified"},
    "verdict": {"answer", "verified_model_or_proof"},
}


class SchemaError(ValueError):
    pass


def fail(msg):
    print(f"benchstore: {msg}", file=sys.stderr)
    sys.exit(1)


def slug(text):
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "_", str(text)).strip("._")
    if not cleaned:
        raise SchemaError(f"empty slug from {text!r}")
    return cleaned


def canonical_join_key(rec):
    payload = {
        "host": rec["host"]["id"],
        "sha_long": rec["git"]["sha_long"],
        "binary_sha256": rec["binary"]["sha256"],
        "suite": rec["suite"],
        "instance_sha256": rec["instance"]["sha256"],
        "config_id": rec["config"]["id"],
        "seed": rec["seed"],
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def record_id(rec):
    return hashlib.sha256(canonical_join_key(rec).encode()).hexdigest()[:16]


def runs_dir(root, rec):
    return Path(root) / rec["git"]["sha_short"] / "benchmark" / "runs" / slug(rec["suite"])


def record_path(root, rec):
    inst8 = rec["instance"]["sha256"][:8]
    name = f"{slug(rec['instance']['name'])}__{inst8}__{slug(rec['config']['id'])}__s{rec['seed']}.json"
    return runs_dir(root, rec) / name


def validate(rec):
    if not isinstance(rec, dict):
        raise SchemaError("record is not a JSON object")
    for key in ("schema", "created_utc", "suite"):
        val = rec.get(key)
        if not isinstance(val, str) or not val:
            raise SchemaError(f"missing or empty string field {key!r}")
    if rec["schema"] != SCHEMA:
        raise SchemaError(f"unsupported schema {rec['schema']!r}, expected {SCHEMA!r}")
    for sub, allowed in SUBOBJECT_KEYS.items():
        obj = rec.get(sub)
        if not isinstance(obj, dict):
            raise SchemaError(f"missing object field {sub!r}")
        unknown = set(obj) - allowed
        if unknown:
            raise SchemaError(f"unknown keys in {sub!r}: {sorted(unknown)}")
    for key, pattern in (("sha_long", r"[0-9a-f]{40}"), ("sha_short", r"[0-9a-f]{7,40}")):
        val = rec["git"].get(key)
        if not isinstance(val, str) or not re.fullmatch(pattern, val):
            raise SchemaError(f"git.{key} must match {pattern}")
    if not HEX64.fullmatch(rec["binary"].get("sha256", "")):
        raise SchemaError("binary.sha256 must be 64-hex")
    if not HEX64.fullmatch(rec["instance"].get("sha256", "")):
        raise SchemaError("instance.sha256 must be 64-hex")
    if not isinstance(rec["instance"].get("name"), str) or not rec["instance"]["name"]:
        raise SchemaError("instance.name required")
    if not isinstance(rec["config"].get("id"), str) or not rec["config"]["id"]:
        raise SchemaError("config.id required")
    seed = rec.get("seed")
    if not isinstance(seed, int) or isinstance(seed, bool) or seed < 0:
        raise SchemaError("seed must be a non-negative integer")
    if not isinstance(rec["host"].get("id"), str) or not rec["host"]["id"]:
        raise SchemaError("host.id required")
    role = (rec.get("arm") or {}).get("role")
    if role not in ARM_ROLES:
        raise SchemaError(f"arm.role must be one of {sorted(ARM_ROLES)}")
    primary = rec["metrics"].get("primary")
    if (
        not isinstance(primary, dict)
        or set(primary) - {"name", "value"}
        or not isinstance(primary.get("name"), str)
        or not primary.get("name")
        or not isinstance(primary.get("value"), int)
        or isinstance(primary.get("value"), bool)
    ):
        raise SchemaError('metrics.primary must be exactly {"name": str, "value": int}')
    if rec["metrics"].get("counter_coverage_verified") is not True:
        raise SchemaError("metrics.counter_coverage_verified must be true (verify the counter covers all changed work)")
    answer = rec["verdict"].get("answer")
    if answer not in VERDICTS:
        raise SchemaError(f"verdict.answer must be one of {sorted(VERDICTS)}")
    if answer != "unknown" and rec["verdict"].get("verified_model_or_proof") is not True:
        raise SchemaError("non-unknown verdicts require verdict.verified_model_or_proof = true")
    return rec


def load_json(path):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read {path}: {exc}")


def iter_records(root, include_dirty=False):
    for path in sorted(Path(root).glob("*/benchmark/runs/*/*.json")):
        try:
            rec = validate(load_json(path))
        except SchemaError:
            continue
        if rec["git"].get("dirty") and not include_dirty:
            continue
        yield path, rec


def cmd_record(args):
    try:
        rec = validate(load_json(args.record))
    except SchemaError as exc:
        fail(str(exc))
    rid = record_id(rec)
    declared = rec.get("record_id")
    if declared is not None and declared != rid:
        fail(f"record_id mismatch: file says {declared!r}, join key says {rid!r}")
    rec["record_id"] = rid
    out = record_path(args.root, rec)
    if out.exists():
        existing = load_json(out)
        try:
            validate(existing)
        except SchemaError as exc:
            fail(f"existing record at {out} is invalid: {exc}")
        if canonical_join_key(existing) == canonical_join_key(rec):
            print(f"already stored: {out}")
            return
        fail(f"join-key collision at {out} with different content")
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(out)
    print(out)


def cmd_locate(args):
    if not args.any_host and not args.host:
        fail("cross-machine comparison is invalid: pass --host or --any-host explicitly")
    hits = []
    for path, rec in iter_records(args.root, args.include_dirty):
        if args.suite and rec["suite"] != args.suite:
            continue
        if args.instance and rec["instance"]["name"] != args.instance:
            continue
        if args.config and rec["config"]["id"] != args.config:
            continue
        if args.seed is not None and rec["seed"] != args.seed:
            continue
        if args.sha and rec["git"]["sha_short"] != args.sha:
            continue
        if args.host and rec["host"]["id"] != args.host:
            continue
        hits.append((path, rec))
    for path, rec in hits:
        primary = rec["metrics"]["primary"]
        print(f"{path}\t{primary['name']}={primary['value']}\t{rec['verdict']['answer']}")
    print(f"# {len(hits)} record(s)", file=sys.stderr)
    sys.exit(0 if hits else 1)


def cmd_missing(args):
    manifest = load_json(args.manifest)
    for key in ("suite", "host", "configs", "seeds", "instances"):
        if key not in manifest:
            fail(f"manifest missing {key!r}")
    stored = {}
    for _, rec in iter_records(args.root, include_dirty=args.include_dirty):
        if rec["host"]["id"] != manifest["host"] or rec["suite"] != manifest["suite"]:
            continue
        key = (rec["instance"]["sha256"], rec["config"]["id"], rec["seed"])
        stored.setdefault(key, []).append(rec["git"]["sha_short"])

    def instance_hash(entry):
        if entry.get("sha256"):
            return entry["sha256"]
        path = entry.get("path")
        if not path:
            fail(f"instance {entry.get('name')!r} needs either sha256 or path")
        try:
            data = Path(path).read_bytes()
        except OSError as exc:
            fail(f"cannot hash instance {entry.get('name')!r}: {exc}")
        return hashlib.sha256(data).hexdigest()

    missing = []
    total = 0
    for entry in manifest["instances"]:
        ihash = instance_hash(entry)
        for config in manifest["configs"]:
            for seed in manifest["seeds"]:
                total += 1
                if stored.get((ihash, config, seed)):
                    continue
                missing.append((manifest["suite"], entry["name"], config, seed))
    for suite, name, config, seed in missing:
        print(f"{suite}\t{name}\t{config}\t{seed}")
    print(f"# {len(missing)}/{total} cell(s) to run", file=sys.stderr)
    sys.exit(1 if missing else 0)


def cmd_verify(args):
    bad = 0
    count = 0
    for path in sorted(Path(args.root).glob("*/benchmark/runs/*/*.json")):
        count += 1
        rec = load_json(path)
        try:
            validate(rec)
            expected_path = record_path(args.root, rec)
            expected_rid = record_id(rec)
        except SchemaError as exc:
            print(f"INVALID {path}: {exc}")
            bad += 1
            continue
        problems = []
        if path != expected_path:
            problems.append(f"path should be {expected_path}")
        if rec.get("record_id") != expected_rid:
            problems.append(f"record_id should be {expected_rid}")
        if problems:
            print(f"MISMATCH {path}: {'; '.join(problems)}")
            bad += 1
    print(f"# {count - bad}/{count} valid", file=sys.stderr)
    sys.exit(1 if bad else 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=None, help="store root (default: <repo>/precompile)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("record")
    p.add_argument("record")

    p = sub.add_parser("locate")
    p.add_argument("--suite")
    p.add_argument("--instance")
    p.add_argument("--config")
    p.add_argument("--seed", type=int)
    p.add_argument("--sha")
    p.add_argument("--host")
    p.add_argument("--any-host", action="store_true")
    p.add_argument("--include-dirty", action="store_true")

    p = sub.add_parser("missing")
    p.add_argument("manifest")
    p.add_argument("--include-dirty", action="store_true")

    p = sub.add_parser("verify")

    args = ap.parse_args()
    args.root = Path(args.root) if args.root else Path(__file__).resolve().parents[3] / "precompile"
    {"record": cmd_record, "locate": cmd_locate, "missing": cmd_missing, "verify": cmd_verify}[args.cmd](args)


if __name__ == "__main__":
    main()

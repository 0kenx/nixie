#!/usr/bin/env bash
#
# Nixie crates.io Publish-Order Script
#
# Publishes the workspace's crates.io-eligible crates in dependency order,
# so that every crate's path dependencies already have a matching version
# live on crates.io by the time it is published.
#
# The order is *derived at run time* from `cargo metadata` (a topological
# sort over the intra-workspace dependency DAG), not hand-maintained, so it
# stays correct as crates are added/removed or dependencies change. Crates
# marked `publish = false` (currently nixie-py, nixie-wasm, and the bench/*
# harnesses) are excluded automatically because `cargo metadata` reports an
# empty `publish` registry list for them.
#
# Modes
# -----
#   (no flags) / --dry-run   Mandatory default. Prints the derived publish
#                             order and the exact command that would run for
#                             each crate. Makes NO network calls and invokes
#                             NO `cargo publish` (not even `--dry-run`).
#
#   --cargo-dry-run           Additionally runs `cargo publish -p <crate>
#                             --dry-run` for each crate in order (compiles
#                             and packages, contacts crates.io's index, but
#                             uploads nothing). Still refuses real publishing.
#
#   --danger-real-publish     REAL crates.io publish. Requires the env var
#                             NIXIE_PUBLISH_CONFIRM=yes to be set; refuses
#                             otherwise. Waits for each crate's new version
#                             to become resolvable on the crates.io index
#                             before moving on to its dependents.
#
# Usage
# -----
#   scripts/publish_order.sh                        # dry-run (default)
#   scripts/publish_order.sh --dry-run               # same, explicit
#   scripts/publish_order.sh --cargo-dry-run          # cargo-verified dry run
#   NIXIE_PUBLISH_CONFIRM=yes scripts/publish_order.sh --danger-real-publish
#
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# ---------------------------------------------------------------------------
# Colors
# ---------------------------------------------------------------------------
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

print_info()  { echo -e "${GREEN}[INFO]${NC} $1"; }
print_warn()  { echo -e "${YELLOW}[WARN]${NC} $1"; }
print_error() { echo -e "${RED}[ERROR]${NC} $1"; }
print_step()  { echo -e "${BLUE}[STEP]${NC} $1"; }

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
MODE="dry-run"

for arg in "$@"; do
    case "$arg" in
        --dry-run)
            MODE="dry-run"
            ;;
        --cargo-dry-run)
            MODE="cargo-dry-run"
            ;;
        --danger-real-publish)
            MODE="danger-real-publish"
            ;;
        -h|--help)
            sed -n '2,33p' "$0"
            exit 0
            ;;
        *)
            print_error "Unknown argument: $arg (see --help)"
            exit 1
            ;;
    esac
done

# ---------------------------------------------------------------------------
# Derive the publish order from `cargo metadata` (topological sort over the
# intra-workspace dependency DAG, restricted to publishable crates).
# ---------------------------------------------------------------------------
print_step "Deriving publish order from workspace dependency graph..."

PUBLISH_ORDER="$(cargo metadata --no-deps --format-version 1 2>/dev/null | python3 -c '
import json
import sys

data = json.load(sys.stdin)
pkgs = {p["name"]: p for p in data["packages"]}

# Only crates that are actually publishable to *some* registry
# (cargo reports `publish: []` for `publish = false`, `null` for the
# unrestricted default).
publishable = {
    name for name, p in pkgs.items()
    if p.get("publish") is None or len(p.get("publish") or []) > 0
}

edges = {}
for name in publishable:
    deps = {
        d["name"]
        for d in pkgs[name]["dependencies"]
        if d["name"] in publishable and d.get("kind") != "dev"
    }
    edges[name] = deps

# Kahn'"'"'s algorithm, alphabetical tie-break for determinism -- except the
# facade/meta crate ("nixie" itself), which nothing else in the workspace
# depends on: it is deferred whenever any other crate is also ready, so it
# always lands last in the emitted order (nixie-math/nixie-core first ... nixie
# meta last), even though it has no direct DAG edge forcing that.
META_CRATE = "nixie"
order = []
remaining = dict(edges)
while remaining:
    ready = sorted(n for n, deps in remaining.items() if not deps)
    if not ready:
        sys.stderr.write(
            "publish_order: dependency cycle among: "
            + ", ".join(sorted(remaining)) + "\n"
        )
        sys.exit(1)
    if len(ready) > 1 and META_CRATE in ready:
        ready.remove(META_CRATE)
    for n in ready:
        order.append(n)
        del remaining[n]
    for deps in remaining.values():
        deps.difference_update(ready)

print("\n".join(order))
')"

if [ -z "$PUBLISH_ORDER" ]; then
    print_error "Failed to derive a publish order from \`cargo metadata\`."
    exit 1
fi

print_info "Publish order (dependency-DAG topological sort):"
i=0
while IFS= read -r crate; do
    i=$((i + 1))
    echo "  ${i}. ${crate}"
done <<< "$PUBLISH_ORDER"

# ---------------------------------------------------------------------------
# Mode dispatch
# ---------------------------------------------------------------------------
case "$MODE" in
    dry-run)
        echo ""
        print_warn "DRY RUN (default mode) -- no cargo command will be executed."
        while IFS= read -r crate; do
            echo "  would run: cargo publish -p ${crate}"
        done <<< "$PUBLISH_ORDER"
        echo ""
        print_info "Nothing was published. Re-run with --cargo-dry-run for a"
        print_info "cargo-verified (compile + package, no upload) dry run, or"
        print_info "NIXIE_PUBLISH_CONFIRM=yes ... --danger-real-publish to publish for real."
        exit 0
        ;;

    cargo-dry-run)
        echo ""
        print_step "Running \`cargo publish --dry-run\` per crate (no upload)..."
        while IFS= read -r crate; do
            print_step "cargo publish -p ${crate} --dry-run"
            cargo publish -p "${crate}" --dry-run
        done <<< "$PUBLISH_ORDER"
        print_info "Cargo dry-run completed for all crates. Nothing was published."
        exit 0
        ;;

    danger-real-publish)
        if [ "${NIXIE_PUBLISH_CONFIRM:-}" != "yes" ]; then
            print_error "Refusing to publish for real: NIXIE_PUBLISH_CONFIRM=yes is not set."
            print_error "This is the DANGER path -- it uploads permanently to crates.io."
            print_error "Set NIXIE_PUBLISH_CONFIRM=yes explicitly to proceed."
            exit 1
        fi

        echo ""
        print_warn "############################################################"
        print_warn "# DANGER: REAL crates.io publish, in dependency order.     #"
        print_warn "# This is IRREVERSIBLE (crates.io does not allow re-       #"
        print_warn "# uploading a version once yanked; yanking != deleting).   #"
        print_warn "############################################################"
        echo ""
        read -r -p "Type the workspace version to confirm (see Cargo.toml): " CONFIRM_VERSION
        WORKSPACE_VERSION="$(cargo metadata --no-deps --format-version 1 | python3 -c '
import json, sys
d = json.load(sys.stdin)
print(next(p["version"] for p in d["packages"] if p["name"] == "nixie"))
')"
        if [ "$CONFIRM_VERSION" != "$WORKSPACE_VERSION" ]; then
            print_error "Version mismatch (typed '${CONFIRM_VERSION}', expected '${WORKSPACE_VERSION}'). Aborting."
            exit 1
        fi

        while IFS= read -r crate; do
            print_step "Publishing ${crate}..."
            cargo publish -p "${crate}"

            crate_version="$(cargo metadata --no-deps --format-version 1 | python3 -c "
import json, sys
d = json.load(sys.stdin)
print(next(p['version'] for p in d['packages'] if p['name'] == '${crate}'))
")"

            print_step "Waiting for ${crate}@${crate_version} to appear on the crates.io index..."
            attempt=0
            max_attempts=60
            until cargo info "${crate}@${crate_version}" >/dev/null 2>&1; do
                attempt=$((attempt + 1))
                if [ "$attempt" -ge "$max_attempts" ]; then
                    print_error "Timed out waiting for ${crate}@${crate_version} to index."
                    print_error "Verify manually before re-running (dependents will fail to resolve otherwise)."
                    exit 1
                fi
                sleep 5
            done
            print_info "${crate}@${crate_version} is live."
        done <<< "$PUBLISH_ORDER"

        print_info "All crates published in dependency order."
        ;;
esac

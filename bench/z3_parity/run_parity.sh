#!/usr/bin/env bash

set -e

# Run from the script's own directory so the `cd ../..` below lands on the
# workspace root regardless of where the script was invoked from (the
# verification gate runs `./bench/z3_parity/run_parity.sh` from the repo
# root; without this it fails with "could not find Cargo.toml").
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Z3 release the recorded baseline was measured against. Z3 verdicts (and its
# unknown/timeout behaviour) change between releases, so comparing Nixie against
# a different Z3 than the baseline makes any disagreement unattributable: it is
# impossible to tell whether Nixie moved or Z3 did.
Z3_BASELINE_VERSION="4.15.4"
Z3_RELEASE_URL="https://github.com/Z3Prover/z3/releases/tag/z3-${Z3_BASELINE_VERSION}"

echo -e "${GREEN}=== Nixie Z3 Parity Test Suite ===${NC}\n"

# Check if Z3 is installed
if ! command -v z3 &> /dev/null; then
    echo -e "${RED}ERROR: Z3 not found!${NC}"
    echo "Please install Z3 ${Z3_BASELINE_VERSION} - the release the recorded baseline"
    echo "was measured against. Any other version makes a disagreement unattributable,"
    echo "because Z3's own verdicts move between releases."
    echo "  Pinned release (all platforms): ${Z3_RELEASE_URL}"
    echo "    Linux x86_64:  z3-${Z3_BASELINE_VERSION}-x64-glibc-2.39.zip"
    echo "    Linux aarch64: z3-${Z3_BASELINE_VERSION}-arm64-glibc-2.34.zip"
    echo "    macOS arm64:   z3-${Z3_BASELINE_VERSION}-arm64-osx-13.7.6.zip"
    echo "  Unzip it and put its bin/z3 on PATH."
    echo
    echo "  Do NOT use 'sudo apt-get install z3' for baseline comparisons:"
    echo "  Ubuntu ships Z3 4.13.3, not ${Z3_BASELINE_VERSION}."
    echo "  'brew install z3' on macOS is fine only if 'z3 --version' already"
    echo "  reports ${Z3_BASELINE_VERSION}."
    exit 1
fi

echo -e "${GREEN}✓ Z3 found:${NC} $(which z3)"
z3 --version

# Warn (but do not block) on a Z3 that is not the baseline release: the run is
# still useful, its numbers just are not comparable to the recorded snapshots.
Z3_FOUND_VERSION="$(z3 --version 2>/dev/null | head -1 | tr ' ' '\n' | grep -E '^[0-9]+(\.[0-9]+)+$' | head -1 || true)"
if [ "$Z3_FOUND_VERSION" != "$Z3_BASELINE_VERSION" ]; then
    echo -e "${YELLOW}! Z3 ${Z3_FOUND_VERSION:-<unknown>} is not the baseline ${Z3_BASELINE_VERSION}.${NC}"
    echo "  Results will still be recorded (the version is captured in the results"
    echo "  metadata), but they are not directly comparable to snapshots taken"
    echo "  against ${Z3_BASELINE_VERSION}. Pinned release: ${Z3_RELEASE_URL}"
fi

# Build Nixie
echo -e "\n${YELLOW}Building Nixie...${NC}"
cd ../..
cargo build --release --quiet

# Run parity tests
echo -e "\n${YELLOW}Running parity tests...${NC}"
cd bench/z3_parity
cargo run --release

# Per-environment snapshot name, mirroring the harness's own
# std::env::consts::OS / std::env::consts::ARCH.
case "$(uname -s)" in
    Darwin) RESULT_OS="macos" ;;
    Linux)  RESULT_OS="linux" ;;
    *)      RESULT_OS="$(uname -s | tr '[:upper:]' '[:lower:]')" ;;
esac
case "$(uname -m)" in
    x86_64|amd64)  RESULT_ARCH="x86_64" ;;
    arm64|aarch64) RESULT_ARCH="aarch64" ;;
    *)             RESULT_ARCH="$(uname -m)" ;;
esac
ENV_RESULTS="results.${RESULT_OS}-${RESULT_ARCH}.json"

# Check results
if [ ! -f "results.json" ]; then
    echo -e "\n${RED}✗ No results file generated${NC}"
    exit 1
fi

echo -e "\n${GREEN}✓ Scratch copy saved to results.json${NC} (git-ignored; every run overwrites it)"
if [ -f "$ENV_RESULTS" ]; then
    echo -e "${GREEN}✓ Per-environment record saved to ${ENV_RESULTS}${NC}"
    echo "  That is the tracked file - commit ${ENV_RESULTS}, never results.json,"
    echo "  so this run cannot clobber another platform's recorded verdicts."
else
    echo -e "${YELLOW}! Expected per-environment record ${ENV_RESULTS} was not found.${NC}"
    echo "  The harness names it from Rust's OS/arch constants; if it wrote a"
    echo "  differently named results.<os>-<arch>.json, commit that one instead."
fi

echo -e "\n${GREEN}=== Parity test complete ===${NC}"

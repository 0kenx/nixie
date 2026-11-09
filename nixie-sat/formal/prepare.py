#!/usr/bin/env python3
"""Create an isolated formal package using an explicitly supplied verifier crate."""
import argparse
import json
from pathlib import Path
import shutil
import tomllib


def prepare(source: Path, oxiformal: Path, output: Path) -> None:
    source = source.resolve()
    oxiformal = oxiformal.resolve(strict=True)
    manifest = tomllib.loads((oxiformal / "Cargo.toml").read_text())
    if manifest.get("package", {}).get("name") != "oxiformal":
        raise ValueError("--oxiformal must name the directory of the real oxiformal crate")
    output = output.resolve()
    if output.is_relative_to(source):
        raise ValueError("--output must be outside the source package")
    # Refuse every existing destination: never overlay or discard other work.
    output.mkdir(parents=True, exist_ok=False)
    shutil.copytree(source / "src", output / "src")
    for name in ["README.md", "UPSTREAM_EXPECTED.toml"]:
        shutil.copy2(source / name, output / name)
    cargo = (source / "Cargo.toml").read_text()
    cargo = cargo.replace('path = ".."', f'path = {json.dumps(str(source.parent))}')
    cargo = cargo.replace(
        "# prepare.py inserts the explicitly selected local oxiformal dependency here.",
        f'oxiformal = {{ path = {json.dumps(str(oxiformal))} }}',
    )
    (output / "Cargo.toml").write_text(cargo)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--oxiformal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        prepare(Path(__file__).parent, args.oxiformal, args.output)
    except (OSError, ValueError) as error:
        parser.exit(1, f"cannot prepare formal package: {error}\n")
    print(f"Prepared {args.output.resolve()}; no proof has been run.")


if __name__ == "__main__":
    main()

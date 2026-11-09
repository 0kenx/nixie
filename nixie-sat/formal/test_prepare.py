"""Configuration tests only: fixture manifests are never verifier implementations."""
from pathlib import Path
import tempfile
import tomllib
import unittest

from prepare import prepare


class PreparationTests(unittest.TestCase):
    def test_configuration_keeps_explicit_paths_and_contract_metadata(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            source = root / "sat" / "formal"
            (source / "src").mkdir(parents=True)
            (source / "src" / "lib.rs").write_text("// source fixture\n")
            original = Path(__file__).parent
            for name in ["Cargo.toml", "README.md", "UPSTREAM_EXPECTED.toml"]:
                (source / name).write_text((original / name).read_text())
            dep = root / 'dependency "with spaces"'
            dep.mkdir()
            (dep / "Cargo.toml").write_text('[package]\nname = "oxiformal"\n')
            output = root / "configured"
            prepare(source, dep, output)
            cargo = tomllib.loads((output / "Cargo.toml").read_text())
            self.assertEqual(cargo["dependencies"]["oxiformal"]["path"], str(dep))
            self.assertEqual(cargo["dependencies"]["nixie-sat"]["path"], str(source.parent))
            self.assertTrue(cargo["package"]["metadata"]["formal"]["self-host"])
            self.assertFalse((output / "EXPECTED.toml").exists())
            marker = output / "do-not-overwrite"
            marker.write_text("keep")
            with self.assertRaises(FileExistsError):
                prepare(source, dep, output)
            self.assertEqual(marker.read_text(), "keep")
            with self.assertRaises(ValueError):
                prepare(source, dep, source / "nested-output")

    def test_wrong_dependency_fails_before_creating_output(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            dep = root / "wrong-crate"
            dep.mkdir()
            (dep / "Cargo.toml").write_text('[package]\nname = "unrelated"\n')
            output = root / "configured"
            with self.assertRaises(ValueError):
                prepare(Path(__file__).parent, dep, output)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()

"""Fail-closed checks for the independent preprocessing certificate auditor."""
import json
from pathlib import Path
import tempfile
import unittest

from relation_factor_probe import check_certificate


class CertificateAuditTests(unittest.TestCase):
    def audit(self, output, proof, ids):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            original, transformed, prefix, mapping = [root / n for n in ("in", "out", "proof", "map")]
            original.write_text("p cnf 3 2\n1 1 0\n-2 3 0\n")
            transformed.write_text(output)
            prefix.write_text(proof)
            mapping.write_text(json.dumps(dict(clause_ids=ids, summary=dict(last_proof_id=2, resolutions=0))))
            return check_certificate(original, transformed, prefix, mapping)

    def test_inert_certificate_preserves_exact_original_clauses(self):
        result = self.audit("p cnf 3 2\n1 1 0\n-2 3 0\n", "", [1, 2])
        self.assertEqual(result["output_clauses_checked"], 2)
        self.assertEqual(result["resolutions_checked"], 0)

    def test_deletion_outside_replaced_relation_is_rejected(self):
        with self.assertRaises(AssertionError):
            self.audit("p cnf 3 1\n-2 3 0\n", "2 d 1 0\n", [2])

    def test_forged_output_or_id_map_is_rejected(self):
        for output, ids in [("p cnf 3 2\n-1 0\n-2 3 0\n", [1, 2]),
                            ("p cnf 3 2\n1 1 0\n1 1 0\n", [1, 1]),
                            ("p cnf 3 2\n1 0\n-2 3 0\n", [1, 2])]:
            with self.subTest(output=output, ids=ids), self.assertRaises(AssertionError):
                self.audit(output, "", ids)


if __name__ == "__main__":
    unittest.main()

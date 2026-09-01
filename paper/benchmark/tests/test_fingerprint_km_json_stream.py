import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).parents[1]
GENERIC = ROOT / "runners" / "full_iri_fingerprint.py"
STREAM = ROOT / "runners" / "fingerprint_km_json_stream.py"
SPARSE = ROOT / "runners" / "fingerprint_km_json_sparse.py"


class KmJsonStreamFingerprintTest(unittest.TestCase):
    def compare(self, payload: dict) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.ofn"
            source.write_text(
                "Ontology(<urn:test>\n"
                "Declaration(Class(<urn:A>))\nDeclaration(Class(<urn:B>))\n"
                "Declaration(Class(<urn:C>))\n)\n", encoding="utf-8")
            result = root / "taxonomy.json"
            result.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")
            old_prefix = root / "old"
            new_prefix = root / "new"
            old = subprocess.run([
                sys.executable, str(GENERIC), "--input", str(result), "--format", "json",
                "--source-ontology", str(source), "--output-prefix", str(old_prefix),
            ], check=True, capture_output=True, text=True)
            new = subprocess.run([
                sys.executable, str(STREAM), "--input", str(result),
                "--source-ontology", str(source), "--output-prefix", str(new_prefix),
            ], check=True, capture_output=True, text=True)
            a, b = json.loads(old.stdout), json.loads(new.stdout)
            for field in ("consistent", "subsumptions", "unsatisfiable",
                          "nonempty_lefts", "taxonomy_sha256", "relation_sha256"):
                self.assertEqual(a[field], b[field], field)
            sparse = subprocess.run([
                sys.executable, str(SPARSE), "--input", str(result),
                "--source-ontology", str(source), "--output-prefix", str(root / "sparse"),
            ], check=True, capture_output=True, text=True)
            c = json.loads(sparse.stdout)
            for field in ("consistent", "subsumptions", "unsatisfiable",
                          "nonempty_lefts", "taxonomy_sha256", "relation_sha256"):
                self.assertEqual(a[field], c[field], "sparse " + field)

    def test_closed_chain_matches_scc_fingerprint(self):
        self.compare({
            "consistent": True,
            "subsumptions": [["urn:A", "urn:B"], ["urn:A", "urn:C"],
                             ["urn:B", "urn:C"]],
            "unsatisfiable": [], "dropped": 0,
        })

    def test_equivalence_and_unsatisfiability_match(self):
        self.compare({
            "consistent": True,
            "subsumptions": [["urn:A", "urn:B"], ["urn:B", "urn:A"],
                             ["urn:C", "http://www.w3.org/2002/07/owl#Nothing"]],
            "unsatisfiable": ["urn:C"], "dropped": 0,
        })

    def test_inconsistent_result_matches(self):
        self.compare({"consistent": False, "subsumptions": [],
                      "unsatisfiable": ["urn:A"], "dropped": 0})

    def test_sparse_path_reconstructs_missing_transitive_pair(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.ofn"
            source.write_text("Ontology(<urn:test>)\n", encoding="utf-8")
            result = root / "taxonomy.json"
            result.write_text(json.dumps({
                "consistent": True,
                "subsumptions": [["urn:A", "urn:B"], ["urn:B", "urn:C"]],
                "unsatisfiable": [], "dropped": 0,
            }), encoding="utf-8")
            outputs = []
            for script, prefix in ((GENERIC, "old"), (SPARSE, "sparse")):
                command = [sys.executable, str(script), "--input", str(result)]
                if script == GENERIC:
                    command += ["--format", "json"]
                command += ["--source-ontology", str(source),
                            "--output-prefix", str(root / prefix)]
                completed = subprocess.run(command, check=True, capture_output=True, text=True)
                outputs.append(json.loads(completed.stdout))
            for field in ("subsumptions", "taxonomy_sha256", "relation_sha256"):
                self.assertEqual(outputs[0][field], outputs[1][field], field)
            self.assertEqual(outputs[1]["subsumptions"], 3)

    def test_sparse_pair_output_is_sorted_closed_relation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.ofn"
            source.write_text("Ontology(<urn:test>)\n", encoding="utf-8")
            result = root / "taxonomy.json"
            result.write_text(json.dumps({
                "consistent": True,
                "subsumptions": [["urn:A", "urn:B"], ["urn:B", "urn:C"]],
                "unsatisfiable": [], "dropped": 0,
            }), encoding="utf-8")
            pairs = root / "pairs.tsv"
            subprocess.run([
                sys.executable, str(SPARSE), "--input", str(result),
                "--source-ontology", str(source),
                "--output-prefix", str(root / "sparse"),
                "--pairs-output", str(pairs),
            ], check=True, capture_output=True, text=True)
            self.assertEqual(pairs.read_text(encoding="utf-8"),
                             "S\turn:A\turn:B\nS\turn:A\turn:C\nS\turn:B\turn:C\n")

    def test_sparse_owlxml_matches_reference_with_unordered_axioms(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.ofn"
            source.write_text(
                "Ontology(<urn:test>\n"
                "Declaration(Class(<urn:A>))\nDeclaration(Class(<urn:B>))\n"
                "Declaration(Class(<urn:C>))\nDeclaration(Class(<urn:D>))\n)\n",
                encoding="utf-8",
            )
            result = root / "taxonomy.owl.xml"
            result.write_text(
                '<?xml version="1.0"?>\n'
                '<Ontology xmlns="http://www.w3.org/2002/07/owl#">\n'
                '<Declaration><Class IRI="urn:D"/></Declaration>\n'
                '<SubClassOf><Class IRI="urn:B"/><Class IRI="urn:C"/></SubClassOf>\n'
                '<Declaration><Class IRI="urn:A"/></Declaration>\n'
                '<EquivalentClasses><Class IRI="urn:A"/><Class IRI="urn:B"/></EquivalentClasses>\n'
                '<Declaration><Class IRI="urn:C"/></Declaration>\n'
                '<Declaration><Class IRI="urn:B"/></Declaration>\n'
                '</Ontology>\n',
                encoding="utf-8",
            )
            outputs = []
            for script, prefix in ((GENERIC, "old-xml"), (SPARSE, "sparse-xml")):
                completed = subprocess.run([
                    sys.executable, str(script), "--input", str(result),
                    "--format", "owlxml", "--source-ontology", str(source),
                    "--output-prefix", str(root / prefix),
                ], check=True, capture_output=True, text=True)
                outputs.append(json.loads(completed.stdout))
            for field in (
                "consistent", "subsumptions", "unsatisfiable", "nonempty_lefts",
                "taxonomy_sha256", "relation_sha256", "source_edges",
                "source_equivalence_groups", "source_declarations",
                "output_declarations", "ontology_declarations",
                "missing_source_declarations",
            ):
                self.assertEqual(outputs[0][field], outputs[1][field], field)

    def test_sparse_owlxml_matches_reference_for_derived_inconsistency(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.ofn"
            source.write_text(
                "Ontology(<urn:test>\nDeclaration(Class(<urn:A>))\n)\n",
                encoding="utf-8",
            )
            result = root / "taxonomy.owlxml"
            result.write_text(
                '<Ontology xmlns="http://www.w3.org/2002/07/owl#">\n'
                '<Declaration><Class IRI="urn:A"/></Declaration>\n'
                '<Declaration><Class IRI="http://www.w3.org/2002/07/owl#Thing"/></Declaration>\n'
                '<Declaration><Class IRI="http://www.w3.org/2002/07/owl#Nothing"/></Declaration>\n'
                '<EquivalentClasses><Class IRI="urn:A"/>'
                '<Class IRI="http://www.w3.org/2002/07/owl#Thing"/>'
                '<Class IRI="http://www.w3.org/2002/07/owl#Nothing"/>'
                '</EquivalentClasses>\n</Ontology>\n',
                encoding="utf-8",
            )
            outputs = []
            for script, prefix in ((GENERIC, "old-inconsistent"),
                                   (SPARSE, "sparse-inconsistent")):
                completed = subprocess.run([
                    sys.executable, str(script), "--input", str(result),
                    "--format", "owlxml", "--source-ontology", str(source),
                    "--output-prefix", str(root / prefix),
                ], check=True, capture_output=True, text=True)
                outputs.append(json.loads(completed.stdout))
            for field in (
                "consistent", "subsumptions", "unsatisfiable", "nonempty_lefts",
                "components", "taxonomy_sha256", "relation_sha256",
                "source_edges", "source_equivalence_groups", "source_declarations",
                "output_declarations", "ontology_declarations",
                "missing_source_declarations",
            ):
                self.assertEqual(outputs[0][field], outputs[1][field], field)


if __name__ == "__main__":
    unittest.main()

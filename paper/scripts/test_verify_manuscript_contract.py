import unittest

from verify_manuscript_contract import REQUIRED_BASELINES, REQUIRED_SECTIONS, verify


def fixture(*, abstract_words: int = 180, keywords: int = 4) -> str:
    abstract = " ".join("word" for _ in range(abstract_words))
    keyword_text = "; ".join(f"keyword {index}" for index in range(keywords))
    sections = []
    for section in REQUIRED_SECTIONS:
        sections.append(rf"\section{{{section}}}")
        if section == "Evaluation":
            sections.append(" ".join(REQUIRED_BASELINES))
    declarations = "\n".join(
        rf"\paragraph{{{name}.}} text"
        for name in (
            "Ethical considerations", "Author contributions",
            "Declaration of conflicting interests", "Funding", "Data availability",
        )
    )
    return (
        rf"\begin{{abstract}}{abstract}\end{{abstract}}" + "\n"
        rf"\noindent\textbf{{Keywords:}} {keyword_text}\n\n"
        + "\n".join(sections) + "\n" + declarations
    )


class ManuscriptContractTest(unittest.TestCase):
    def test_complete_contract_passes(self):
        result = verify(fixture())
        self.assertEqual(result["abstract_words"], 180)
        self.assertEqual(result["keywords"], 4)

    def test_abstract_limit_is_enforced(self):
        with self.assertRaisesRegex(ValueError, "abstract has 251 words"):
            verify(fixture(abstract_words=251))

    def test_keyword_limit_is_enforced(self):
        with self.assertRaisesRegex(ValueError, "found 8 keywords"):
            verify(fixture(keywords=8))

    def test_missing_baseline_fails(self):
        with self.assertRaisesRegex(ValueError, "evaluation omits baselines: Whelk"):
            verify(fixture().replace("Whelk", ""))

    def test_stale_result_marker_fails(self):
        with self.assertRaisesRegex(ValueError, "unresolved manuscript markers"):
            verify(fixture() + "still running at this manuscript cutoff")


if __name__ == "__main__":
    unittest.main()

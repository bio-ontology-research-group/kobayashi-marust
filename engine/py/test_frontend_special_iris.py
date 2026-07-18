#!/usr/bin/env python3
"""Regression tests for OWL builtin recognition in the Python frontend."""

import unittest
from unittest.mock import patch

import frontend
import owl_classify
import route


OWL_THING = "<http://www.w3.org/2002/07/owl#Thing>"
OWL_NOTHING = "<http://www.w3.org/2002/07/owl#Nothing>"
SOURCE_THING = "<http://example.org/source#Thing>"
DAML_NOTHING = "<http://www.daml.org/2001/03/daml+oil#Nothing>"
SOURCE_OWL_THING = "<http://example.org/source#owl:Thing>"
SOURCE_OWL_NOTHING = "<http://example.org/source#owl:Nothing>"


class _FakeSyntax:
    """Expose only the constructors needed to distinguish cls() branches."""

    @staticmethod
    def Top():
        return ("top",)

    @staticmethod
    def Bottom():
        return ("bottom",)

    @staticmethod
    def ConceptName(name):
        return ("named", name)


class SpecialIriTest(unittest.TestCase):
    def setUp(self):
        frontend.reset_short()

    def test_cls_recognises_builtins_by_full_identity(self):
        with patch.object(frontend, "sx", _FakeSyntax):
            self.assertEqual(frontend.cls("owl:Thing"), ("top",))
            self.assertEqual(frontend.cls(OWL_THING), ("top",))
            self.assertEqual(frontend.cls("owl:Nothing"), ("bottom",))
            self.assertEqual(frontend.cls(OWL_NOTHING), ("bottom",))

    def test_cls_preserves_source_iris_with_builtin_local_names(self):
        with patch.object(frontend, "sx", _FakeSyntax):
            self.assertEqual(frontend.cls(SOURCE_THING), ("named", "km_src_Thing"))
            self.assertEqual(frontend.cls(DAML_NOTHING), ("named", "km_src_Nothing"))
            self.assertEqual(
                frontend.cls(SOURCE_OWL_THING), ("named", "km_src_owl:Thing")
            )
            self.assertEqual(
                frontend.cls(SOURCE_OWL_NOTHING),
                ("named", "km_src_owl:Nothing"),
            )

        self.assertTrue(frontend.is_named_iri("km_src_Thing"))
        self.assertTrue(frontend.is_named_iri("km_src_Nothing"))
        self.assertEqual(frontend.full_iri("km_src_Thing"), SOURCE_THING[1:-1])
        self.assertEqual(frontend.full_iri("km_src_Nothing"), DAML_NOTHING[1:-1])
        self.assertEqual(
            frontend.full_iri("km_src_owl:Thing"), SOURCE_OWL_THING[1:-1]
        )
        self.assertEqual(
            frontend.full_iri("km_src_owl:Nothing"), SOURCE_OWL_NOTHING[1:-1]
        )

    def test_plain_class_uses_the_same_identity_safe_shortening(self):
        self.assertEqual(frontend._plain_class("owl:Thing"), "")
        self.assertEqual(frontend._plain_class(OWL_THING), "")
        self.assertIsNone(frontend._plain_class("owl:Nothing"))
        self.assertIsNone(frontend._plain_class(OWL_NOTHING))
        self.assertEqual(frontend._plain_class(SOURCE_THING), "km_src_Thing")
        self.assertEqual(frontend._plain_class(DAML_NOTHING), "km_src_Nothing")

    def test_declarations_keep_only_source_lookalikes(self):
        text = f"""Ontology(
          Declaration(Class({SOURCE_THING}))
          Declaration(Class({DAML_NOTHING}))
          Declaration(Class(owl:Thing))
          Declaration(Class({OWL_NOTHING}))
        )"""
        self.assertEqual(
            frontend.declared_classes(text), ["km_src_Thing", "km_src_Nothing"]
        )

    def test_bottom_recognition_checks_symbol_ownership_before_spelling(self):
        source_bottom = frontend.short(DAML_NOTHING)
        self.assertEqual(source_bottom, "km_src_Nothing")
        self.assertFalse(owl_classify.is_semantic_bottom(source_bottom))

        for spelling in ("Nothing", "owl:Nothing", "⊥"):
            self.assertTrue(owl_classify.is_semantic_bottom(spelling))
            self.assertFalse(
                owl_classify.is_semantic_bottom(spelling, {spelling}.__contains__)
            )

    def test_legacy_router_does_not_turn_a_source_self_edge_into_bottom(self):
        source_bottom = frontend.short(DAML_NOTHING)
        result = route._filter_engine_out(
            {"subsumptions": {source_bottom: [source_bottom]}, "inconsistent": False}
        )
        self.assertEqual(result["subsumptions"], [])
        self.assertEqual(result["unsatisfiable"], [])

        result = route._filter_engine_out(
            {
                "subsumptions": {source_bottom: [source_bottom, "owl:Nothing"]},
                "inconsistent": False,
            }
        )
        self.assertEqual(result["unsatisfiable"], ["Nothing"])


if __name__ == "__main__":
    unittest.main()

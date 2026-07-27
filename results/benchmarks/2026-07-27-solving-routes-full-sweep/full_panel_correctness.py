#!/usr/bin/env python3
"""Collision-safe correctness adjudication for ORE classification panels.

This module is deliberately independent of a particular dated benchmark run.
Both the per-ontology runner and the final aggregator for new panels must use
this implementation.  In particular, an aggregator must re-score the retained
measurements instead of trusting correctness labels written during execution.
"""

from __future__ import annotations


INCONSISTENT_ADJUDICATIONS = {"ore_ont_2669.owl", "ore_ont_15516.owl"}
FULLIRI_ONLY_ONTOLOGIES = {"ore_ont_3524.owl", "ore_ont_15703.owl"}
FULLIRI_ONLY_VERDICT = "localname_not_applicable_fulliri_only"


def _false(value: object) -> bool:
    """Return true only for an explicitly recorded false value."""

    return value is False or (
        isinstance(value, str) and value.strip().lower() in {"false", "0"}
    )


def _integer(value: object, default: int = 0) -> int:
    try:
        return int(value)  # type: ignore[arg-type]
    except (TypeError, ValueError):
        return default


def _reference_is_trusted(ontology: str, reference: dict | None) -> bool:
    """Validate the same-job Konclude row as a comparison reference.

    Most ontologies retain a collision-safe-enough local-name gold signature,
    so the same-job reference must reproduce it.  ORE 3524 and 15703 are the
    two audited exceptions: their local-name projection is non-injective and
    deliberately skipped, so a successful full-IRI fingerprint is the primary
    reference rather than a fallback from local-name scoring.
    """

    if not reference:
        return False
    # ``gold_kind`` describes the frozen local-name oracle, not the identity of
    # this retained same-job row.  It is deliberately ``none`` for the two
    # non-injective local-name ontologies, so using it here recreates the v1
    # undercount.  The caller passes the row whose procedure is Konclude; bind
    # that trust decision to the procedure identity instead.
    if reference.get("status") != "ok" or reference.get("arm") != "konclude":
        return False
    if reference.get("fulliri_fingerprint_status") != "ok":
        return False
    verdict = reference.get("verdict")
    if verdict == "match":
        return True
    if (
        ontology == "ore_ont_13503.owl"
        and verdict == "unsound"
        and _integer(reference.get("extra")) == 0
        and _integer(reference.get("missing")) == 0
        and _integer(reference.get("extra_unsat")) == 1
        and _integer(reference.get("missing_unsat")) == 0
    ):
        return True
    return bool(
        ontology in FULLIRI_ONLY_ONTOLOGIES
        and verdict == FULLIRI_ONLY_VERDICT
        and reference.get("localname_identity_capable") is False
        and reference.get("localname_canonicalization_status")
        == "skipped_noninjective_projection"
        and reference.get("fulliri_taxonomy_sha256")
    )


def classify_correctness(row: dict, reference: dict | None) -> None:
    """Mutate one retained measurement with sound/complete adjudication.

    The comparison is semantic.  Two trusted classifiers that both report an
    inconsistent ontology agree even if one emits an empty taxonomy and the
    other materializes every named class under bottom.  For a consistent
    ontology, exact full-IRI fingerprint identity remains the strongest test.
    """

    ontology = row["ont"]
    status = row.get("status")
    fingerprint_ok = row.get("fulliri_fingerprint_status") == "ok"
    reference_fingerprint_ok = bool(
        reference and reference.get("fulliri_fingerprint_status") == "ok"
    )

    if not row.get("fulliri_identity_capable", True):
        row["fulliri_verdict"] = "not_comparable"
    elif reference_fingerprint_ok and fingerprint_ok:
        if row.get("fulliri_taxonomy_sha256") == reference.get(
            "fulliri_taxonomy_sha256"
        ):
            row["fulliri_verdict"] = "match"
        else:
            row["fulliri_verdict"] = "different"
    elif not fingerprint_ok:
        row["fulliri_verdict"] = "no_answer"
    else:
        row["fulliri_verdict"] = "no_reference"

    if status != "ok" or not fingerprint_ok:
        row["sound"] = "not_applicable"
        row["complete"] = "no"
        row["correctness_basis"] = "no_parseable_classification_answer"
        row["solved"] = False
        return

    if ontology in INCONSISTENT_ADJUDICATIONS:
        if _false(row.get("consistent")):
            row["sound"] = "yes"
            row["complete"] = "yes"
            row["correctness_basis"] = "independently_adjudicated_inconsistency"
        else:
            row["sound"] = "yes"
            row["complete"] = "no"
            row["correctness_basis"] = (
                "consistent_answer_on_adjudicated_inconsistent_input"
            )
        row["solved"] = row["sound"] == row["complete"] == "yes"
        return

    reference_trusted = _reference_is_trusted(ontology, reference)

    # In OWL, an inconsistent ontology entails every axiom.  KM records this as
    # `consistent=false` with no materialized taxonomy, while Konclude commonly
    # lists every named class as unsatisfiable.  Comparing those serializations'
    # taxonomy hashes is invalid; the trusted shared inconsistency verdict is
    # the complete semantic answer.
    if (
        reference_trusted
        and _false(row.get("consistent"))
        and _false(reference.get("consistent"))
    ):
        row["sound"] = "yes"
        row["complete"] = "yes"
        row["correctness_basis"] = "same_job_shared_inconsistency"
        row["solved"] = True
        return

    if (
        reference_trusted
        and row["fulliri_verdict"] == "match"
    ):
        row["sound"] = "yes"
        row["complete"] = "yes"
        row["correctness_basis"] = (
            "same_job_fulliri_konclude_reference"
            if row.get("arm") == "konclude"
            else "same_job_fulliri_identity_to_konclude"
        )
        row["solved"] = True
        return

    verdict = row.get("verdict")
    if ontology == "ore_ont_13503.owl" and verdict == "unsound":
        if (
            _integer(row.get("extra")) == 0
            and _integer(row.get("missing")) == 0
            and _integer(row.get("extra_unsat")) == 1
            and _integer(row.get("missing_unsat")) == 0
        ):
            row["sound"] = "yes"
            row["complete"] = "yes"
            row["correctness_basis"] = "adjudicated_missing_unsat_in_frozen_gold"
            row["solved"] = True
            return

    mapping = {
        "match": ("yes", "yes", "frozen_konclude_signature"),
        "incomplete": ("yes", "no", "strict_subset_of_frozen_signature"),
        "unsound": ("no", "yes", "strict_superset_of_frozen_signature"),
        "both": ("no", "no", "incomparable_with_frozen_signature"),
        "consistency_mismatch": (
            "no",
            "no",
            "consistency_disagrees_with_frozen_signature",
        ),
        "nogold": ("unknown", "unknown", "no_authoritative_reference"),
        "noparse": ("not_applicable", "no", "canonicalization_failed"),
    }
    sound, complete, basis = mapping.get(
        verdict, ("unknown", "unknown", "unclassified_correctness_evidence")
    )
    if verdict == "match" and row["fulliri_verdict"] == "different":
        sound, complete, basis = (
            "unknown",
            "unknown",
            "localname_match_but_fulliri_difference",
        )
    row["sound"] = sound
    row["complete"] = complete
    row["correctness_basis"] = basis
    row["solved"] = sound == complete == "yes"


def apply_retained_targeted_adjudication(row: dict) -> None:
    """Reapply a hash-bound targeted counterexample after generic scoring."""

    if _integer(row.get("targeted_counterexample_count")) > 0:
        row["pre_targeted_sound"] = row.get("sound")
        row["pre_targeted_complete"] = row.get("complete")
        row["pre_targeted_correctness_basis"] = row.get("correctness_basis")
        row["sound"] = "no"
        row["solved"] = False
        row["correctness_basis"] = "targeted_satisfiability_counterexample"

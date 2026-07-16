#!/usr/bin/env python3
"""Audit the IBEX procedure matrix and learn a correctness-first router.

The default policy objective is deliberately not "fastest successful sample".
For every ontology/procedure pair it first requires an exact Konclude signature
(or exact agreement with HermiT for the five no-gold inputs), then minimizes the larger of the
same-node Konclude-normalized wall and peak-RSS ratios.  A greedy policy tree
chooses each leaf's procedure lexicographically by:

  1. fewest classification failures in the leaf;
  2. lowest summed balanced time/memory cost among successful rows.

Only source-level profile fields and Konclude-compatible expressivity flags are
eligible features.  Clause statistics remain in the corpus report but are not
training features because a route such as trigger absorption changes the
clauses it must be chosen *before* normalisation.  The implementation has no
numpy/scikit-learn dependency and emits a small JSON tree for the Rust router.
"""

import argparse
import collections
import csv
import glob
import gzip
import hashlib
import json
import math
import os
import statistics

from matrix_contract import ALL_ARMS, BASELINE_ARMS, KM_ARMS, NO_KONCLUDE_GOLD

EXPECTED_KM_ARMS = list(KM_ARMS)
EXPECTED_BASELINE_ARMS = list(BASELINE_ARMS)
EXPECTED_ARMS = list(ALL_ARMS)

# The learner may compare only mechanisms with an independently established
# soundness+completeness contract.  Corpus agreement alone can never promote a
# measurement-only arm.  The hard per-ontology fragment mask below is part of
# this contract: ordinary proxy CB is not eligible when singleton/ABox semantics
# is required, the exact nominal arm is mandatory there, and the rules worker is
# used only for its validated rule fragment.
BASE_CB_POLICY_ARMS = [
    "cb_plain16",
    "cb_plain8",
    "cb_plain1",
    "cb_absorb16",
    "cb_absorb8",
    "cb_absorb1",
    "lean",
    "seq_on",
    "seq_off",
]

DEFAULT_POLICY_ARMS = [
    "elc",
    *BASE_CB_POLICY_ARMS,
    "nominals",
    "ht_rules",
]

# Konclude cannot parse these SWRL ontologies; the retained ORE signatures are
# parse-failure artifacts.  Minimal inconsistent cores checked with HermiT are
# committed under results/contested-cores and documented in CONTESTED-GOLD.md.
# An inconsistent classifier answer is complete (explosion), so it is the only
# empirically recognizable adjudicated result we accept here.
ADJUDICATED_INCONSISTENT = {
    "ore_ont_2669.owl",
    "ore_ont_10906.owl",
    "ore_ont_15516.owl",
}


def percentile(values, fraction):
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, math.ceil(fraction * len(ordered)) - 1))
    return ordered[index]


def mean(values):
    return sum(values) / len(values) if values else None


def finite_number(value):
    return isinstance(value, (int, float)) and math.isfinite(value)


def is_correct(ont, row):
    if row.get("status") != "ok":
        return False
    if row.get("gold_kind") == "konclude":
        return row.get("signature_exact") is True
    if row.get("verdict") in ("match", "match_hermit"):
        return True
    return ont in ADJUDICATED_INCONSISTENT and row.get("consistent") is False


def semantic_fragment(profile_row):
    """Return the hard soundness/completeness fragment for policy selection."""
    profile = profile_row["profile"]
    expr = profile["expressivity"]
    source = profile["source"]
    if source.get("unsupported_rule_axioms", 0) > 0:
        return "unsupported_rules"
    if source.get("rule_axioms", 0) > 0:
        return "rules"
    if (
        source.get("abox_axioms", 0) > 0
        and profile.get("positive_abox_tbox_separable", False)
    ):
        return "positive_abox"
    if source.get("abox_axioms", 0) > 0 or expr.get("nominal_individual", False):
        return "nominal"
    return "sriq_core"


def hard_fragment_route(fragment):
    """Return the deterministic semantic route outside the learned TBox tree.

    Unsupported rules still select the rule-aware frontend so it can issue an
    explicit out-of-fragment result.  They have no correctness-eligible arm.
    """
    if fragment in ("unsupported_rules", "rules"):
        return "ht_rules"
    if fragment == "nominal":
        return "nominals"
    return None


def arm_contract_eligible(arm, profile_row, row=None):
    """Apply the independent mechanism contract before looking at performance.

    The ELC worker's `unsupported` result is its exact normalized-clause
    fragment test for this frozen matrix.  Production routing performs the same
    check inside the frontend and never learns eligibility from benchmark time.
    """
    if not profile_row:
        return False
    fragment = semantic_fragment(profile_row)
    if fragment == "unsupported_rules":
        return False
    if fragment == "rules":
        return arm == "ht_rules"
    if fragment == "nominal":
        return arm == "nominals"
    if arm in BASE_CB_POLICY_ARMS:
        return True
    if arm == "elc":
        return row is not None and row.get("status") != "unsupported"
    return False


def is_reference(row):
    if row.get("status") != "ok":
        return False
    if row.get("gold_kind") == "konclude":
        return row.get("signature_exact") is True
    return row.get("verdict") in ("match", "match_hermit", "reference")


def apply_canonical_gold_hashes(results, ontologies, gold_dir):
    """Audit exactness against the immutable canonical signature bytes.

    Matrix runner b725 applied `localname` a second time while loading retained
    signatures. That changes already-canonical class names containing `/` or
    `#`. Every output row also records the SHA-256 of its canonical signature,
    so exactness can be recovered without rerunning a single reasoner by hashing
    the decompressed immutable gold bytes. Directional extra/missing counts from
    the affected runner remain diagnostic only.
    """
    errors = []
    corrections = []
    for ont in ontologies:
        rows = results.get(ont, {})
        if ont in NO_KONCLUDE_GOLD:
            continue
        path = os.path.join(gold_dir, f"konclude__{ont}.sig.gz")
        try:
            with gzip.open(path, "rb") as handle:
                canonical_bytes = handle.read()
        except OSError as error:
            errors.append({"ont": ont, "path": path, "error": str(error)})
            continue
        expected = hashlib.sha256(canonical_bytes).hexdigest()
        for arm, row in rows.items():
            if row.get("gold_kind") != "konclude":
                continue
            observed = row.get("signature_sha256")
            exact = row.get("status") == "ok" and observed == expected
            row["signature_exact"] = exact
            row["canonical_gold_signature_sha256"] = expected
            runner_exact = row.get("verdict") == "match"
            if observed and runner_exact != exact:
                corrections.append(
                    {
                        "ont": ont,
                        "arm": arm,
                        "runner_verdict": row.get("verdict"),
                        "signature_exact": exact,
                        "observed_signature_sha256": observed,
                        "canonical_gold_signature_sha256": expected,
                    }
                )
    return errors, corrections


def adjudicate_missing_konclude_gold(results):
    """Compare no-Konclude-signature rows to the independent HermiT result.

    `nogold` is never treated as correctness by itself. The frozen runner emits
    a canonical signature hash, so equality here is exact despite large raw
    taxonomies being deleted. If HermiT does not return a parseable answer, the
    ontology remains explicitly unadjudicated and strict analysis fails.
    """
    unadjudicated = []
    adjudicated = []
    for ont, rows in sorted(results.items()):
        no_gold_rows = [row for row in rows.values() if row.get("gold_kind") == "none"]
        if not no_gold_rows:
            continue
        hermit = rows.get("hermit", {})
        hermit_sha = (
            hermit.get("signature_sha256")
            if hermit.get("status") == "ok"
            and hermit.get("verdict") == "nogold"
            and hermit.get("gold_kind") == "none"
            else None
        )
        if not hermit_sha:
            unadjudicated.append(
                {
                    "ont": ont,
                    "hermit_status": hermit.get("status"),
                    "hermit_verdict": hermit.get("verdict"),
                }
            )
            continue
        matches = 0
        disagreements = 0
        for row in no_gold_rows:
            if row.get("status") != "ok" or row.get("verdict") != "nogold":
                continue
            row["raw_verdict"] = "nogold"
            row["fallback_reference"] = "hermit"
            if row.get("signature_sha256") == hermit_sha:
                row["verdict"] = "match_hermit"
                row["solved"] = True
                matches += 1
            else:
                row["verdict"] = "disagree_hermit"
                row["solved"] = False
                disagreements += 1
        adjudicated.append(
            {
                "ont": ont,
                "reference": "hermit",
                "signature_sha256": hermit_sha,
                "matches": matches,
                "disagreements": disagreements,
            }
        )
    return adjudicated, unadjudicated


def audit_gold_provenance(results, ontologies):
    """Require the frozen 587-Konclude/5-no-gold contract in every panel."""
    errors = []
    counts = collections.Counter()
    for ont in ontologies:
        rows = results.get(ont, {})
        expected_kind = "none" if ont in NO_KONCLUDE_GOLD else "konclude"
        kinds = {row.get("gold_kind") for row in rows.values()}
        names = {row.get("gold_basename") for row in rows.values()}
        hashes = {row.get("gold_sha256") for row in rows.values()}
        counts[expected_kind] += 1
        if rows and kinds != {expected_kind}:
            errors.append(
                {
                    "ont": ont,
                    "error": "gold_kind",
                    "expected": expected_kind,
                    "observed": sorted(str(value) for value in kinds),
                }
            )
        if expected_kind == "konclude":
            expected_name = f"konclude__{ont}.sig.gz"
            if rows and (names != {expected_name} or len(hashes) != 1 or None in hashes):
                errors.append(
                    {
                        "ont": ont,
                        "error": "konclude_gold_provenance",
                        "expected_name": expected_name,
                        "observed_names": sorted(str(value) for value in names),
                        "observed_hashes": sorted(str(value) for value in hashes),
                    }
                )
        elif rows and (names != {None} or hashes != {None}):
            errors.append(
                {
                    "ont": ont,
                    "error": "unexpected_gold_for_no_gold_ontology",
                    "observed_names": sorted(str(value) for value in names),
                    "observed_hashes": sorted(str(value) for value in hashes),
                }
            )
    return errors, dict(sorted(counts.items()))


def reference_for(rows, requested):
    """Return a reference row, optionally the strict two-arm Konclude envelope."""
    if requested != "konclude_envelope":
        row = rows.get(requested)
        return row if row is not None and is_reference(row) else None
    available = [
        (arm, rows.get(arm)) for arm in ("konclude_w1", "konclude_w16")
        if rows.get(arm) is not None and is_reference(rows[arm])
    ]
    if not available:
        return None
    time_arm, time_row = min(available, key=lambda item: item[1].get("wall_s", float("inf")))
    memory_arm, memory_row = min(
        available, key=lambda item: item[1].get("peak_mb", float("inf"))
    )
    return {
        "status": "ok",
        "verdict": "reference",
        "wall_s": time_row["wall_s"],
        "peak_mb": memory_row["peak_mb"],
        "time_arm": time_arm,
        "memory_arm": memory_arm,
    }


def read_expected(path):
    if not path:
        return []
    with open(path, encoding="utf-8") as handle:
        return [line.strip() for line in handle if line.strip()]


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_profile_directory(path):
    """Hash the immutable profile corpus, including each basename boundary."""
    digest = hashlib.sha256()
    paths = sorted(
        glob.glob(os.path.join(path, "*.json")), key=lambda item: os.path.basename(item)
    )
    for profile_path in paths:
        digest.update(os.path.basename(profile_path).encode("utf-8"))
        digest.update(b"\0")
        with open(profile_path, "rb") as handle:
            for block in iter(lambda: handle.read(1 << 20), b""):
                digest.update(block)
        digest.update(b"\0")
    return digest.hexdigest()


def load_results(patterns):
    by_ontology = collections.defaultdict(dict)
    parse_errors = []
    duplicate_rows = []
    paths = []
    for pattern in patterns:
        paths.extend(glob.glob(pattern))
    for path in sorted(set(paths)):
        with open(path, encoding="utf-8", errors="replace") as handle:
            for line_number, line in enumerate(handle, 1):
                if not line.strip():
                    continue
                try:
                    row = json.loads(line)
                except ValueError as error:
                    parse_errors.append(
                        {"path": path, "line": line_number, "error": str(error)}
                    )
                    continue
                ont = row.get("ont")
                arm = row.get("arm")
                if not ont or not arm:
                    parse_errors.append(
                        {"path": path, "line": line_number, "error": "missing ont/arm"}
                    )
                    continue
                if arm in by_ontology[ont]:
                    duplicate_rows.append({"ont": ont, "arm": arm, "path": path})
                    continue
                by_ontology[ont][arm] = row
    return dict(by_ontology), parse_errors, duplicate_rows, sorted(set(paths))


def load_profiles(profile_dir):
    profiles = {}
    errors = []
    for path in sorted(glob.glob(os.path.join(profile_dir, "*.json"))):
        try:
            data = json.load(open(path, encoding="utf-8"))
        except (OSError, ValueError) as error:
            errors.append({"path": path, "error": str(error)})
            continue
        ont = data.get("ont")
        if not ont:
            name = os.path.basename(path)
            ont = name[:-5] if name.endswith(".json") else name
        if data.get("status") != "ok" or not isinstance(data.get("profile"), dict):
            errors.append({"ont": ont, "error": data.get("error", data.get("status"))})
            continue
        profiles[ont] = data
    return profiles, errors


def ratio(numerator, denominator):
    if not finite_number(numerator) or not finite_number(denominator) or denominator <= 0:
        return None
    return numerator / denominator


def normalized_cost(row, reference):
    wall_ratio = ratio(row.get("wall_s"), reference.get("wall_s"))
    memory_ratio = ratio(row.get("peak_mb"), reference.get("peak_mb"))
    if wall_ratio is None or memory_ratio is None:
        return None
    # Chebyshev distance enforces the user's two-dimensional goal: a route that
    # is excellent on time but bad on memory (or vice versa) cannot hide behind
    # an average.  The small mean term deterministically breaks near-ties.
    score = max(wall_ratio, memory_ratio) + 0.025 * (wall_ratio + memory_ratio)
    return {
        "time_ratio": wall_ratio,
        "memory_ratio": memory_ratio,
        "score": min(score, 1000.0),
    }


def safe_div(a, b):
    return float(a) / float(b) if b else 0.0


def base_features(profile_row):
    profile = profile_row["profile"]
    expr = profile["expressivity"]
    source = profile["source"]
    features = {}
    for key, value in expr.items():
        if key != "code" and isinstance(value, bool):
            features[f"expressivity.{key}"] = float(value)
    for key, value in source.items():
        if key != "axiom_types" and isinstance(value, (bool, int, float)):
            features[f"source.{key}"] = float(value)
    for key, value in source.get("axiom_types", {}).items():
        if isinstance(value, (int, float)):
            features[f"axiom_type.{key}"] = float(value)

    logical = source.get("logical_axioms", 0)
    children = source.get("ontology_children", 0)
    concepts = source.get("concept_expressions", 0)
    entities = (
        source.get("distinct_classes", 0)
        + source.get("distinct_object_properties", 0)
        + source.get("distinct_data_properties", 0)
        + source.get("distinct_individuals", 0)
    )
    cardinalities = (
        source.get("min_cardinalities", 0)
        + source.get("max_cardinalities", 0)
        + source.get("exact_cardinalities", 0)
    )
    features.update(
        {
            "derived.tbox_fraction": safe_div(source.get("tbox_axioms", 0), logical),
            "derived.rbox_fraction": safe_div(source.get("rbox_axioms", 0), logical),
            "derived.abox_fraction": safe_div(source.get("abox_axioms", 0), logical),
            "derived.rule_fraction": safe_div(source.get("rule_axioms", 0), logical),
            "derived.logical_fraction": safe_div(logical, children),
            "derived.expressions_per_axiom": safe_div(concepts, logical),
            "derived.entities_per_axiom": safe_div(entities, logical),
            "derived.existential_fraction": safe_div(
                source.get("existentials", 0), concepts
            ),
            "derived.universal_fraction": safe_div(source.get("universals", 0), concepts),
            "derived.disjunction_fraction": safe_div(
                source.get("unions", 0) + source.get("complements", 0), concepts
            ),
            "derived.cardinality_fraction": safe_div(cardinalities, concepts),
            "derived.role_chain_fraction": safe_div(
                source.get("role_chain_axioms", 0), logical
            ),
        }
    )
    return features, expr.get("code", "")


def build_features(profiles, ontologies):
    rows = {}
    codes = set()
    for ont in ontologies:
        if ont not in profiles:
            continue
        feats, code = base_features(profiles[ont])
        rows[ont] = feats
        codes.add(code)
    # A one-hot code lets the tree use Konclude's exact combined description
    # without assigning a false numeric ordering to DL names such as SRIQ.
    for ont, feats in rows.items():
        code = profiles[ont]["profile"]["expressivity"].get("code", "")
        for known in sorted(codes):
            feats[f"expressivity_code.{known}"] = float(code == known)
    feature_names = sorted({key for row in rows.values() for key in row})
    for row in rows.values():
        for key in feature_names:
            row.setdefault(key, 0.0)
    # Constant columns cannot split a tree. Dropping them substantially reduces
    # policy-training work without changing a single candidate partition.
    feature_names = [
        key for key in feature_names if len({row[key] for row in rows.values()}) > 1
    ]
    return rows, feature_names


def features_for_tree(profile_row, feature_names):
    """Build one inference row using exactly the training feature vocabulary."""
    features, code = base_features(profile_row)
    for feature in feature_names:
        if feature.startswith("expressivity_code."):
            features[feature] = float(code == feature.split(".", 1)[1])
        else:
            features.setdefault(feature, 0.0)
    return features


class PolicyTree:
    def __init__(self, arms, feature_names, max_depth, min_leaf, min_cost_gain=0.02):
        self.arms = list(arms)
        self.feature_names = list(feature_names)
        self.max_depth = max_depth
        self.min_leaf = min_leaf
        self.min_cost_gain = min_cost_gain
        self.root = None
        self._features = None
        self._performance = None

    def _leaf_choice(self, indices):
        choices = []
        for arm_index, arm in enumerate(self.arms):
            failures = 0
            cost = 0.0
            successes = 0
            for index in indices:
                outcome = self._performance[index][arm_index]
                if outcome is None:
                    failures += 1
                else:
                    successes += 1
                    cost += outcome
            choices.append((failures, cost, arm_index, arm, successes))
        failures, cost, _, arm, successes = min(choices)
        return {
            "arm": arm,
            "failures": failures,
            "cost_sum": cost,
            "successes": successes,
        }

    @staticmethod
    def _better_objective(candidate, incumbent):
        if candidate[0] != incumbent[0]:
            return candidate[0] < incumbent[0]
        return candidate[1] < incumbent[1] - 1e-12

    def _best_split(self, indices, leaf):
        best = None
        n = len(indices)
        if n < 2 * self.min_leaf:
            return None
        for feature in self.feature_names:
            ordered = sorted(indices, key=lambda i: self._features[i].get(feature, 0.0))
            total_fail = [0] * len(self.arms)
            total_cost = [0.0] * len(self.arms)
            for index in ordered:
                for arm_index in range(len(self.arms)):
                    outcome = self._performance[index][arm_index]
                    if outcome is None:
                        total_fail[arm_index] += 1
                    else:
                        total_cost[arm_index] += outcome
            left_fail = [0] * len(self.arms)
            left_cost = [0.0] * len(self.arms)
            for position, index in enumerate(ordered[:-1], 1):
                for arm_index in range(len(self.arms)):
                    outcome = self._performance[index][arm_index]
                    if outcome is None:
                        left_fail[arm_index] += 1
                    else:
                        left_cost[arm_index] += outcome
                if position < self.min_leaf or n - position < self.min_leaf:
                    continue
                value = self._features[index].get(feature, 0.0)
                next_value = self._features[ordered[position]].get(feature, 0.0)
                if value == next_value:
                    continue
                left_choice = min(
                    (left_fail[a], left_cost[a], a) for a in range(len(self.arms))
                )
                right_choice = min(
                    (
                        total_fail[a] - left_fail[a],
                        total_cost[a] - left_cost[a],
                        a,
                    )
                    for a in range(len(self.arms))
                )
                objective = (
                    left_choice[0] + right_choice[0],
                    left_choice[1] + right_choice[1],
                )
                threshold = value + (next_value - value) / 2.0
                candidate = {
                    "feature": feature,
                    "threshold": threshold,
                    "position": position,
                    "ordered": ordered,
                    "objective": objective,
                }
                if best is None or self._better_objective(objective, best["objective"]):
                    best = candidate
        if best is None:
            return None
        leaf_objective = (leaf["failures"], leaf["cost_sum"])
        split_objective = best["objective"]
        if split_objective[0] < leaf_objective[0]:
            return best
        cost_gain = leaf_objective[1] - split_objective[1]
        if split_objective[0] == leaf_objective[0] and cost_gain >= self.min_cost_gain * n:
            return best
        return None

    def _build(self, indices, depth):
        leaf = self._leaf_choice(indices)
        node = {
            "samples": len(indices),
            "training_failures": leaf["failures"],
            "training_successes": leaf["successes"],
            "training_cost_sum": round(leaf["cost_sum"], 8),
            "arm": leaf["arm"],
        }
        if depth >= self.max_depth:
            node["kind"] = "leaf"
            return node
        split = self._best_split(indices, leaf)
        if split is None:
            node["kind"] = "leaf"
            return node
        position = split["position"]
        ordered = split["ordered"]
        node.update(
            kind="split",
            feature=split["feature"],
            threshold=split["threshold"],
            left=self._build(ordered[:position], depth + 1),
            right=self._build(ordered[position:], depth + 1),
        )
        return node

    def fit(self, indices, features, performance):
        self._features = features
        self._performance = performance
        self.root = self._build(list(indices), 0)
        return self

    def predict_one(self, features):
        node = self.root
        while node["kind"] == "split":
            if features.get(node["feature"], 0.0) <= node["threshold"]:
                node = node["left"]
            else:
                node = node["right"]
        return node["arm"]

    def node_count(self):
        def count(node):
            if node["kind"] == "leaf":
                return 1
            return 1 + count(node["left"]) + count(node["right"])

        return count(self.root)


def tree_text(node, indent=""):
    if node["kind"] == "leaf":
        return [
            f"{indent}=> {node['arm']}  "
            f"[n={node['samples']}, failures={node['training_failures']}, "
            f"cost={node['training_cost_sum']:.3f}]"
        ]
    lines = [f"{indent}if {node['feature']} <= {node['threshold']:.9g}:"]
    lines.extend(tree_text(node["left"], indent + "  "))
    lines.append(f"{indent}else:")
    lines.extend(tree_text(node["right"], indent + "  "))
    return lines


def deterministic_folds(ontologies, folds):
    ordered = sorted(
        range(len(ontologies)),
        key=lambda i: hashlib.sha256(ontologies[i].encode("utf-8")).digest(),
    )
    assignments = [0] * len(ontologies)
    for position, index in enumerate(ordered):
        assignments[index] = position % folds
    return assignments


def evaluate_predictions(indices, predictions, performance, arms):
    arm_indices = {arm: index for index, arm in enumerate(arms)}
    solved = 0
    oracle_solved = 0
    avoidable_failures = 0
    costs = []
    for index, arm in zip(indices, predictions):
        oracle = any(value is not None for value in performance[index])
        actual = performance[index][arm_indices[arm]]
        oracle_solved += int(oracle)
        if actual is None:
            avoidable_failures += int(oracle)
        else:
            solved += 1
            costs.append(actual)
    return {
        "samples": len(indices),
        "solved": solved,
        "oracle_solved": oracle_solved,
        "avoidable_failures": avoidable_failures,
        "mean_cost": mean(costs),
        "median_cost": statistics.median(costs) if costs else None,
        "p95_cost": percentile(costs, 0.95),
    }


def cross_validate(ontologies, features, performance, feature_names, arms, folds):
    assignments = deterministic_folds(ontologies, folds)
    candidates = []
    # Small declared grid: enough to expose under/overfitting while keeping the
    # complete 592-ontology analysis a lightweight batch job. Hyperparameters
    # are selected only by out-of-fold policy outcomes, never training fit.
    for depth in (3, 5, 7):
        for min_leaf in (4, 8, 16):
            all_indices = []
            all_predictions = []
            nodes = []
            for fold in range(folds):
                train = [i for i, assigned in enumerate(assignments) if assigned != fold]
                test = [i for i, assigned in enumerate(assignments) if assigned == fold]
                tree = PolicyTree(arms, feature_names, depth, min_leaf).fit(
                    train, features, performance
                )
                all_indices.extend(test)
                all_predictions.extend(tree.predict_one(features[i]) for i in test)
                nodes.append(tree.node_count())
            metrics = evaluate_predictions(
                all_indices, all_predictions, performance, arms
            )
            metrics.update(
                max_depth=depth,
                min_leaf=min_leaf,
                mean_nodes=mean(nodes),
            )
            candidates.append(metrics)
    candidates.sort(
        key=lambda row: (
            row["avoidable_failures"],
            row["mean_cost"] if row["mean_cost"] is not None else float("inf"),
            row["mean_nodes"],
            row["max_depth"],
            -row["min_leaf"],
        )
    )
    return candidates


def arm_summary(results, ontologies, arms):
    output = {}
    for arm in arms:
        rows = [results[ont][arm] for ont in ontologies if arm in results.get(ont, {})]
        walls = [row["wall_s"] for row in rows if row.get("status") == "ok"]
        peaks = [row["peak_mb"] for row in rows if row.get("status") == "ok"]
        output[arm] = {
            "rows": len(rows),
            "exact": sum(
                is_correct(row.get("ont", ""), row) for row in rows
            ),
            "reference": sum(is_reference(row) for row in rows),
            "status": dict(collections.Counter(row.get("status") for row in rows)),
            "verdict": dict(collections.Counter(row.get("verdict") for row in rows)),
            "wall_s": {
                "median": statistics.median(walls) if walls else None,
                "mean": mean(walls),
                "p95": percentile(walls, 0.95),
                "max": max(walls) if walls else None,
            },
            "peak_mb": {
                "median": statistics.median(peaks) if peaks else None,
                "mean": mean(peaks),
                "p95": percentile(peaks, 0.95),
                "max": max(peaks) if peaks else None,
            },
        }
    return output


def expressivity_mechanism_summary(results, profiles, ontologies, arms):
    """Characterize every isolated mechanism by exact Konclude expressivity.

    This is evidence, not a learned correctness boundary: one counterexample
    excludes a mechanism from that bucket, while an all-green finite bucket is
    only promoted after its algorithmic fragment contract is documented.
    """
    corpus_counts = collections.Counter()
    for ont in ontologies:
        if ont in profiles:
            code = profiles[ont]["profile"]["expressivity"].get("code", "unknown")
            corpus_counts[code] += 1
    output = {}
    for arm in arms:
        buckets = collections.defaultdict(list)
        for ont in ontologies:
            if ont not in profiles or arm not in results.get(ont, {}):
                continue
            code = profiles[ont]["profile"]["expressivity"].get("code", "unknown")
            buckets[code].append((ont, results[ont][arm]))
        arm_out = {}
        for code in sorted(corpus_counts):
            entries = buckets.get(code, [])
            status = collections.Counter(row.get("status") for _, row in entries)
            verdict = collections.Counter(row.get("verdict") for _, row in entries)
            incorrect = [
                {
                    "ont": ont,
                    "status": row.get("status"),
                    "verdict": row.get("verdict"),
                    "extra": row.get("extra", 0),
                    "missing": row.get("missing", 0),
                    "extra_unsat": row.get("extra_unsat", 0),
                    "missing_unsat": row.get("missing_unsat", 0),
                }
                for ont, row in entries
                if row.get("status") == "ok" and not is_correct(ont, row)
            ]
            arm_out[code] = {
                "corpus": corpus_counts[code],
                "rows": len(entries),
                "exact": sum(is_correct(ont, row) for ont, row in entries),
                "unsupported": status.get("unsupported", 0),
                "timeout": status.get("timeout", 0),
                "memout": status.get("memout", 0),
                "error": status.get("error", 0),
                "incorrect": len(incorrect),
                "status": dict(status),
                "verdict": dict(verdict),
                "incorrect_examples": incorrect,
            }
        output[arm] = arm_out
    return {
        "corpus_by_expressivity": dict(sorted(corpus_counts.items())),
        "mechanisms": output,
    }


def write_csv(path, rows, fields):
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--results-glob", action="append")
    parser.add_argument("--profiles")
    parser.add_argument("--expected-onts")
    parser.add_argument("--output-dir")
    parser.add_argument("--reference", default="konclude_envelope")
    parser.add_argument("--policy-arms", default=",".join(DEFAULT_POLICY_ARMS))
    parser.add_argument("--folds", type=int, default=5)
    parser.add_argument("--allow-partial", action="store_true")
    parser.add_argument("--expected-km-sha")
    parser.add_argument("--expected-konclude-sha")
    parser.add_argument("--expected-elk-sha")
    parser.add_argument("--expected-hermit-sha")
    parser.add_argument("--expected-java-sha")
    parser.add_argument("--expected-canonicalizer-sha")
    parser.add_argument("--expected-profile-sha")
    parser.add_argument("--expected-list-sha")
    parser.add_argument("--expected-runner-sha")
    parser.add_argument("--runner-path")
    args = parser.parse_args()

    root = os.path.abspath(args.root)
    output_dir = os.path.abspath(args.output_dir or root)
    os.makedirs(output_dir, exist_ok=True)
    patterns = args.results_glob or [os.path.join(root, "matrix-results", "*.jsonl")]
    profiles_dir = os.path.abspath(args.profiles or os.path.join(root, "profiles"))
    expected_path = args.expected_onts or os.path.join(root, "onts.txt")
    expected = read_expected(expected_path)
    expected_set = set(expected)
    results, parse_errors, duplicate_rows, result_paths = load_results(patterns)
    gold_dir = os.path.join(os.path.dirname(root), "gold")
    canonical_gold_errors, canonical_gold_corrections = apply_canonical_gold_hashes(
        results, expected or sorted(results), gold_dir
    )
    gold_provenance_errors, gold_contract_counts = audit_gold_provenance(
        results, expected or sorted(results)
    )
    fallback_adjudications, unadjudicated_ontologies = adjudicate_missing_konclude_gold(
        results
    )
    profiles, profile_errors = load_profiles(profiles_dir)
    policy_arms = [arm for arm in args.policy_arms.split(",") if arm]

    missing_result_files = sorted(expected_set - set(results)) if expected else []
    unexpected_ontologies = sorted(set(results) - expected_set) if expected else []
    missing_profiles = sorted((expected_set or set(results)) - set(profiles))
    missing_rows = []
    bad_order = []
    host_mismatches = []
    expressivity_mismatches = []
    route_mismatches = []
    km_hashes = set()
    konclude_hashes = set()
    baseline_hashes = collections.defaultdict(set)
    runtime_hashes = collections.defaultdict(set)
    canonicalizer_hashes = set()
    row_runner_hashes = set()
    cpu_models = set()
    cpu_allocations = set()
    for ont in expected or sorted(results):
        rows = results.get(ont, {})
        wanted = set(EXPECTED_ARMS)
        missing = sorted(wanted - set(rows))
        if missing:
            missing_rows.append({"ont": ont, "arms": missing})
        observed_order = sorted(
            row.get("order_index")
            for arm, row in rows.items()
            if arm in EXPECTED_ARMS and isinstance(row.get("order_index"), int)
        )
        if len(observed_order) == len(EXPECTED_ARMS) and observed_order != list(
            range(len(EXPECTED_ARMS))
        ):
            bad_order.append({"ont": ont, "order": observed_order})
        hosts = {row.get("host") for row in rows.values() if row.get("host")}
        if len(hosts) > 1:
            host_mismatches.append({"ont": ont, "hosts": sorted(hosts)})
        for arm, row in rows.items():
            if arm in EXPECTED_KM_ARMS and row.get("requested_route") != arm:
                route_mismatches.append(
                    {
                        "ont": ont,
                        "arm": arm,
                        "requested_route": row.get("requested_route"),
                    }
                )
            digest = row.get("binary_sha256")
            if digest:
                if row.get("kind") == "km":
                    km_hashes.add(digest)
                elif row.get("kind") == "konclude":
                    konclude_hashes.add(digest)
                else:
                    baseline_hashes[row.get("kind", "unknown")].add(digest)
            runtime_digest = row.get("runtime_sha256")
            if runtime_digest:
                runtime_hashes[row.get("kind", "unknown")].add(runtime_digest)
            canonicalizer_digest = row.get("canonicalizer_sha256")
            if canonicalizer_digest:
                canonicalizer_hashes.add(canonicalizer_digest)
            runner_digest = row.get("runner_sha256")
            if runner_digest:
                row_runner_hashes.add(runner_digest)
            if row.get("cpu_model"):
                cpu_models.add(row["cpu_model"])
            if isinstance(row.get("cpus"), int):
                cpu_allocations.add(row["cpus"])
            if (
                arm.startswith("konclude_")
                and row.get("status") == "ok"
                and ont in profiles
            ):
                official = row.get("expressivity")
                ported = profiles[ont]["profile"]["expressivity"].get("code")
                if official != ported:
                    expressivity_mismatches.append(
                        {"ont": ont, "arm": arm, "konclude": official, "km": ported}
                    )

    reproducibility_errors = []
    observed_profile_sha = sha256_profile_directory(profiles_dir)
    if args.expected_profile_sha and observed_profile_sha != args.expected_profile_sha:
        reproducibility_errors.append(
            {
                "profile_corpus_hash_mismatch": {
                    "expected": args.expected_profile_sha,
                    "observed": observed_profile_sha,
                }
            }
        )
    if len(km_hashes) > 1:
        reproducibility_errors.append({"multiple_km_hashes": sorted(km_hashes)})
    if args.expected_km_sha and km_hashes != {args.expected_km_sha}:
        reproducibility_errors.append(
            {
                "km_hash_mismatch": {
                    "expected": args.expected_km_sha,
                    "observed": sorted(km_hashes),
                }
            }
        )
    if len(konclude_hashes) > 1:
        reproducibility_errors.append(
            {"multiple_konclude_hashes": sorted(konclude_hashes)}
        )
    if args.expected_konclude_sha and konclude_hashes != {args.expected_konclude_sha}:
        reproducibility_errors.append(
            {
                "konclude_hash_mismatch": {
                    "expected": args.expected_konclude_sha,
                    "observed": sorted(konclude_hashes),
                }
            }
        )
    expected_baseline_hashes = {
        "elk": args.expected_elk_sha,
        "hermit": args.expected_hermit_sha,
    }
    for kind, expected_digest in expected_baseline_hashes.items():
        observed = baseline_hashes.get(kind, set())
        if len(observed) > 1:
            reproducibility_errors.append(
                {f"multiple_{kind}_hashes": sorted(observed)}
            )
        if expected_digest and observed != {expected_digest}:
            reproducibility_errors.append(
                {
                    f"{kind}_hash_mismatch": {
                        "expected": expected_digest,
                        "observed": sorted(observed),
                    }
                }
            )
    observed_java_hashes = set().union(
        runtime_hashes.get("elk", set()), runtime_hashes.get("hermit", set())
    )
    if len(observed_java_hashes) > 1:
        reproducibility_errors.append(
            {"multiple_java_hashes": sorted(observed_java_hashes)}
        )
    if args.expected_java_sha and observed_java_hashes != {args.expected_java_sha}:
        reproducibility_errors.append(
            {
                "java_hash_mismatch": {
                    "expected": args.expected_java_sha,
                    "observed": sorted(observed_java_hashes),
                }
            }
        )
    if args.expected_canonicalizer_sha and canonicalizer_hashes != {
        args.expected_canonicalizer_sha
    }:
        reproducibility_errors.append(
            {
                "canonicalizer_hash_mismatch": {
                    "expected": args.expected_canonicalizer_sha,
                    "observed": sorted(canonicalizer_hashes),
                }
            }
        )
    if args.expected_list_sha:
        observed_list_sha = sha256_file(expected_path)
        if observed_list_sha != args.expected_list_sha:
            reproducibility_errors.append(
                {
                    "corpus_list_hash_mismatch": {
                        "expected": args.expected_list_sha,
                        "observed": observed_list_sha,
                    }
                }
            )
    observed_runner_sha = None
    if args.expected_runner_sha:
        runner_path = os.path.abspath(
            args.runner_path or os.path.join(root, "bench_one_matrix_frozen.py")
        )
        observed_runner_sha = sha256_file(runner_path)
        if observed_runner_sha != args.expected_runner_sha:
            reproducibility_errors.append(
                {
                    "runner_hash_mismatch": {
                        "expected": args.expected_runner_sha,
                        "observed": observed_runner_sha,
                    }
                }
            )
        if row_runner_hashes != {args.expected_runner_sha}:
            reproducibility_errors.append(
                {
                    "row_runner_hash_mismatch": {
                        "expected": args.expected_runner_sha,
                        "observed": sorted(row_runner_hashes),
                    }
                }
            )
    if any("Intel(R) Xeon(R) Gold 6248" not in model for model in cpu_models):
        reproducibility_errors.append({"unexpected_cpu_models": sorted(cpu_models)})
    if cpu_allocations - {16}:
        reproducibility_errors.append(
            {"unexpected_cpu_allocations": sorted(cpu_allocations)}
        )

    complete = not (
        parse_errors
        or duplicate_rows
        or missing_result_files
        or unexpected_ontologies
        or missing_profiles
        or missing_rows
        or bad_order
        or profile_errors
        or host_mismatches
        or expressivity_mismatches
        or route_mismatches
        or canonical_gold_errors
        or gold_provenance_errors
        or unadjudicated_ontologies
        or reproducibility_errors
    )
    if not complete and not args.allow_partial:
        audit = {
            "complete": False,
            "result_files": len(result_paths),
            "parse_errors": parse_errors,
            "duplicate_rows": duplicate_rows,
            "missing_result_files": missing_result_files,
            "unexpected_ontologies": unexpected_ontologies,
            "missing_profiles": missing_profiles,
            "missing_rows": missing_rows,
            "bad_order": bad_order,
            "profile_errors": profile_errors,
            "host_mismatches": host_mismatches,
            "expressivity_mismatches": expressivity_mismatches,
            "route_mismatches": route_mismatches,
            "gold_contract_counts": gold_contract_counts,
            "gold_provenance_errors": gold_provenance_errors,
            "fallback_adjudications": fallback_adjudications,
            "unadjudicated_ontologies": unadjudicated_ontologies,
            "reproducibility_errors": reproducibility_errors,
            "km_binary_hashes": sorted(km_hashes),
            "konclude_binary_hashes": sorted(konclude_hashes),
            "baseline_binary_hashes": {
                kind: sorted(values) for kind, values in sorted(baseline_hashes.items())
            },
            "runtime_hashes": {
                kind: sorted(values) for kind, values in sorted(runtime_hashes.items())
            },
            "canonicalizer_hashes": sorted(canonicalizer_hashes),
            "row_runner_hashes": sorted(row_runner_hashes),
            "cpu_models": sorted(cpu_models),
            "cpu_allocations": sorted(cpu_allocations),
            "runner_sha256": observed_runner_sha,
            "profile_corpus_sha256": observed_profile_sha,
            "canonical_gold_errors": canonical_gold_errors,
            "canonical_gold_corrections": canonical_gold_corrections,
        }
        print(json.dumps(audit, indent=2, sort_keys=True))
        raise SystemExit(2)

    usable = [
        ont
        for ont in (expected or sorted(results))
        if ont in profiles
        and ont in results
        and reference_for(results[ont], args.reference) is not None
        and all(arm in results[ont] for arm in policy_arms)
    ]

    performance_by_ont = {}
    oracle_rows = []
    gaps = []
    for ont in usable:
        reference = reference_for(results[ont], args.reference)
        assert reference is not None
        fragment = semantic_fragment(profiles[ont])
        arm_outcomes = []
        candidates = []
        for arm in policy_arms:
            row = results[ont][arm]
            eligible = arm_contract_eligible(arm, profiles[ont], row)
            cost = (
                normalized_cost(row, reference)
                if eligible and is_correct(ont, row)
                else None
            )
            arm_outcomes.append(cost["score"] if cost else None)
            if cost:
                candidates.append((cost["score"], arm, cost, row))
        performance_by_ont[ont] = arm_outcomes
        if candidates:
            score, arm, cost, row = min(candidates)
            oracle_rows.append(
                {
                    "ont": ont,
                    "fragment": fragment,
                    "oracle_arm": arm,
                    "score": score,
                    "time_ratio": cost["time_ratio"],
                    "memory_ratio": cost["memory_ratio"],
                    "km_wall_s": row["wall_s"],
                    "km_peak_mb": row["peak_mb"],
                    "konclude_wall_s": reference["wall_s"],
                    "konclude_peak_mb": reference["peak_mb"],
                    "konclude_time_arm": reference.get("time_arm", args.reference),
                    "konclude_memory_arm": reference.get("memory_arm", args.reference),
                    "beats_time": cost["time_ratio"] < 1.0,
                    "beats_memory": cost["memory_ratio"] < 1.0,
                }
            )
            if cost["time_ratio"] > 1.2 or cost["memory_ratio"] > 1.2:
                gaps.append(oracle_rows[-1].copy())
        else:
            oracle_rows.append(
                {
                    "ont": ont,
                    "fragment": fragment,
                    "oracle_arm": "none",
                    "score": None,
                    "time_ratio": None,
                    "memory_ratio": None,
                    "km_wall_s": None,
                    "km_peak_mb": None,
                    "konclude_wall_s": reference.get("wall_s"),
                    "konclude_peak_mb": reference.get("peak_mb"),
                    "konclude_time_arm": reference.get("time_arm", args.reference),
                    "konclude_memory_arm": reference.get("memory_arm", args.reference),
                    "beats_time": False,
                    "beats_memory": False,
                }
            )

    # Uncertified nominal/ABox and rule ontologies are dispatched by semantic
    # gates in routing.rs before the generated tree is called. Training the tree
    # on those rows would waste depth relearning unreachable branches. The
    # source-certified positive ABox fragment is TBox-separable, so it has the
    # same independently complete mechanisms as the nominal-free SRIQ core and
    # participates in performance learning.
    tree_arms = [
        arm
        for arm in policy_arms
        if arm == "elc" or arm in BASE_CB_POLICY_ARMS
    ]
    tree_usable = [
        ont
        for ont in usable
        if semantic_fragment(profiles[ont]) in ("sriq_core", "positive_abox")
    ]
    feature_map, feature_names = build_features(profiles, tree_usable)
    tree_usable = [ont for ont in tree_usable if ont in feature_map]
    tree_features = [feature_map[ont] for ont in tree_usable]
    tree_performance = [
        [performance_by_ont[ont][policy_arms.index(arm)] for arm in tree_arms]
        for ont in tree_usable
    ]

    cv_candidates = []
    tree = None
    prediction_rows = []
    if len(tree_usable) >= max(20, args.folds * 2):
        cv_candidates = cross_validate(
            tree_usable,
            tree_features,
            tree_performance,
            feature_names,
            tree_arms,
            args.folds,
        )
        selected = cv_candidates[0]
        tree = PolicyTree(
            tree_arms,
            feature_names,
            selected["max_depth"],
            selected["min_leaf"],
        ).fit(range(len(tree_usable)), tree_features, tree_performance)
        oracle_by_ont = {row["ont"]: row for row in oracle_rows}
        # Emit a route for every successfully profiled corpus ontology, including
        # the few inputs for which official Konclude supplies no usable paired
        # reference. Those inputs cannot contribute a training cost, but the
        # production classifier must still make a deterministic source-only
        # decision and the final paired sweep must verify Python/Rust identity.
        prediction_ontologies = expected or sorted(profiles)
        for ont in prediction_ontologies:
            if ont not in profiles:
                continue
            fragment = semantic_fragment(profiles[ont])
            tree_arm = None
            exact_gate_fallback = False
            predicted = hard_fragment_route(fragment)
            if predicted is None:
                inference_features = features_for_tree(profiles[ont], feature_names)
                tree_arm = tree.predict_one(inference_features)
                predicted = tree_arm
                # The frontend performs the exact normalized-clause and RBox
                # gate before an ELC worker starts.  A rejected source-tree
                # proposal becomes one cb_plain16 run, never an ELC/CB race.
                elc_row = results.get(ont, {}).get("elc")
                if predicted == "elc" and (
                    elc_row is None or elc_row.get("status") == "unsupported"
                ):
                    predicted = "cb_plain16"
                    exact_gate_fallback = True
            outcomes = performance_by_ont.get(ont)
            outcome = (
                outcomes[policy_arms.index(predicted)]
                if outcomes is not None and predicted in policy_arms
                else None
            )
            oracle = oracle_by_ont.get(ont)
            reference = reference_for(results.get(ont, {}), args.reference)
            predicted_row = results.get(ont, {}).get(predicted)
            predicted_eligible = arm_contract_eligible(
                predicted, profiles[ont], predicted_row
            )
            predicted_cost = (
                normalized_cost(predicted_row, reference)
                if reference is not None
                and predicted_row is not None
                and predicted_eligible
                and is_correct(ont, predicted_row)
                else None
            )
            prediction_rows.append(
                {
                    "ont": ont,
                    "fragment": fragment,
                    "tree_arm": tree_arm,
                    "exact_gate_fallback": exact_gate_fallback,
                    "predicted_arm": predicted,
                    "predicted_eligible": predicted_eligible,
                    "policy_evaluable": outcomes is not None,
                    "predicted_exact": outcome is not None if outcomes is not None else None,
                    "predicted_score": outcome,
                    "predicted_time_ratio": (
                        predicted_cost["time_ratio"] if predicted_cost else None
                    ),
                    "predicted_memory_ratio": (
                        predicted_cost["memory_ratio"] if predicted_cost else None
                    ),
                    "predicted_beats_both": bool(
                        predicted_cost
                        and predicted_cost["time_ratio"] < 1.0
                        and predicted_cost["memory_ratio"] < 1.0
                    ),
                    "oracle_arm": oracle["oracle_arm"] if oracle else None,
                    "oracle_score": oracle["score"] if oracle else None,
                }
            )

    all_arms = EXPECTED_ARMS
    summaries = arm_summary(results, expected or sorted(results), all_arms)
    mechanism_expressivity = expressivity_mechanism_summary(
        results,
        profiles,
        expected or sorted(results),
        EXPECTED_KM_ARMS,
    )
    policy_ontologies = expected or sorted(results)
    fragment_counts = collections.Counter(
        semantic_fragment(profiles[ont])
        for ont in policy_ontologies
        if ont in profiles
    )
    eligible_arm_counts = {
        arm: sum(
            ont in profiles
            and arm_contract_eligible(
                arm, profiles[ont], results.get(ont, {}).get(arm)
            )
            for ont in policy_ontologies
        )
        for arm in policy_arms
    }
    union_exact = sum(
        ont in profiles
        and any(
            arm_contract_eligible(arm, profiles[ont], results.get(ont, {}).get(arm))
            and is_correct(ont, results.get(ont, {}).get(arm, {}))
            for arm in policy_arms
        )
        for ont in policy_ontologies
    )
    oracle_solved = [row for row in oracle_rows if row["oracle_arm"] != "none"]
    no_policy_candidate = [
        row["ont"] for row in oracle_rows if row["oracle_arm"] == "none"
    ]
    beat_both = sum(row["beats_time"] and row["beats_memory"] for row in oracle_solved)
    routed_exact = sum(row["predicted_exact"] is True for row in prediction_rows)
    routed_beat_both = sum(row["predicted_beats_both"] for row in prediction_rows)
    routed_over_20 = sum(
        row["predicted_exact"] is True
        and (
            row["predicted_time_ratio"] > 1.2
            or row["predicted_memory_ratio"] > 1.2
        )
        for row in prediction_rows
    )
    audit = {
        "complete": complete,
        "expected_ontologies": len(expected),
        "result_files": len(result_paths),
        "usable_for_policy": len(usable),
        "usable_for_learned_tbox_tree": len(tree_usable),
        "parse_errors": parse_errors,
        "duplicate_rows": duplicate_rows,
        "missing_result_files": missing_result_files,
        "unexpected_ontologies": unexpected_ontologies,
        "missing_profiles": missing_profiles,
        "missing_rows": missing_rows,
        "bad_order": bad_order,
        "profile_errors": profile_errors,
        "host_mismatches": host_mismatches,
        "expressivity_mismatches": expressivity_mismatches,
        "route_mismatches": route_mismatches,
        "gold_contract_counts": gold_contract_counts,
        "gold_provenance_errors": gold_provenance_errors,
        "fallback_adjudications": fallback_adjudications,
        "unadjudicated_ontologies": unadjudicated_ontologies,
        "reproducibility_errors": reproducibility_errors,
        "km_binary_hashes": sorted(km_hashes),
        "konclude_binary_hashes": sorted(konclude_hashes),
        "baseline_binary_hashes": {
            kind: sorted(values) for kind, values in sorted(baseline_hashes.items())
        },
        "runtime_hashes": {
            kind: sorted(values) for kind, values in sorted(runtime_hashes.items())
        },
        "canonicalizer_hashes": sorted(canonicalizer_hashes),
        "row_runner_hashes": sorted(row_runner_hashes),
        "cpu_models": sorted(cpu_models),
        "cpu_allocations": sorted(cpu_allocations),
        "runner_sha256": observed_runner_sha,
        "profile_corpus_sha256": observed_profile_sha,
        "canonical_gold_errors": canonical_gold_errors,
        "canonical_gold_corrections": canonical_gold_corrections,
        "semantic_fragment_counts": dict(sorted(fragment_counts.items())),
        "eligible_ontology_counts_by_arm": eligible_arm_counts,
        "no_policy_candidate_ontologies": no_policy_candidate,
    }
    summary = {
        "audit": audit,
        "reference": args.reference,
        "policy_arms": policy_arms,
        "learned_tbox_tree_arms": tree_arms,
        "arm_summary": summaries,
        "policy_union_exact": union_exact,
        "semantic_fragment_counts": dict(sorted(fragment_counts.items())),
        "eligible_ontology_counts_by_arm": eligible_arm_counts,
        "no_policy_candidate_ontologies": no_policy_candidate,
        "oracle_solved": len(oracle_solved),
        "oracle_beats_konclude_time_and_memory": beat_both,
        "oracle_over_20_percent_gaps": len(gaps),
        "selected_tree_cv": cv_candidates[0] if cv_candidates else None,
        "fitted_tree_exact": routed_exact,
        "fitted_tree_beats_konclude_time_and_memory": routed_beat_both,
        "fitted_tree_over_20_percent_gaps": routed_over_20,
    }
    with open(os.path.join(output_dir, "matrix-summary.json"), "w", encoding="utf-8") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)
        handle.write("\n")
    with open(
        os.path.join(output_dir, "mechanism-expressivity.json"),
        "w",
        encoding="utf-8",
    ) as handle:
        json.dump(mechanism_expressivity, handle, indent=2, sort_keys=True)
        handle.write("\n")
    with open(os.path.join(output_dir, "router-cv.json"), "w", encoding="utf-8") as handle:
        json.dump(cv_candidates, handle, indent=2, sort_keys=True)
        handle.write("\n")
    write_csv(
        os.path.join(output_dir, "oracle-best.csv"),
        oracle_rows,
        [
            "ont",
            "fragment",
            "oracle_arm",
            "score",
            "time_ratio",
            "memory_ratio",
            "km_wall_s",
            "km_peak_mb",
            "konclude_wall_s",
            "konclude_peak_mb",
            "konclude_time_arm",
            "konclude_memory_arm",
            "beats_time",
            "beats_memory",
        ],
    )
    write_csv(
        os.path.join(output_dir, "gaps-over-20-percent.csv"),
        sorted(
            gaps,
            key=lambda row: max(row["time_ratio"], row["memory_ratio"]),
            reverse=True,
        ),
        [
            "ont",
            "fragment",
            "oracle_arm",
            "score",
            "time_ratio",
            "memory_ratio",
            "km_wall_s",
            "km_peak_mb",
            "konclude_wall_s",
            "konclude_peak_mb",
            "konclude_time_arm",
            "konclude_memory_arm",
            "beats_time",
            "beats_memory",
        ],
    )
    if tree is not None:
        tree_document = {
            "schema_version": 1,
            "objective": (
                "exact-first; min max(time/Konclude-envelope,"
                "memory/Konclude-envelope)"
                if args.reference == "konclude_envelope"
                else f"exact-first; min max(time/{args.reference},memory/{args.reference})"
            ),
            "reference": args.reference,
            "policy_arms": tree_arms,
            "hard_fragment_contract": {
                "unsupported_rules": ["ht_rules_explicit_decline"],
                "rules": ["ht_rules"],
                "nominal": ["nominals"],
                "positive_abox": ["elc", *BASE_CB_POLICY_ARMS],
                "sriq_core": ["elc", *BASE_CB_POLICY_ARMS],
                "elc_requires_normalized_fragment_check": True,
            },
            "tree_scope": (
                "sriq_core_and_source_certified_positive_abox; "
                "other hard fragments bypass this tree"
            ),
            "feature_scope": "source-and-expressivity-only",
            "cv": cv_candidates[0],
            "tree": tree.root,
        }
        with open(os.path.join(output_dir, "router-tree.json"), "w", encoding="utf-8") as handle:
            json.dump(tree_document, handle, indent=2, sort_keys=True)
            handle.write("\n")
        text = "\n".join(tree_text(tree.root)) + "\n"
        with open(os.path.join(output_dir, "router-tree.txt"), "w", encoding="utf-8") as handle:
            handle.write(text)
        write_csv(
            os.path.join(output_dir, "router-predictions.csv"),
            prediction_rows,
            [
                "ont",
                "fragment",
                "tree_arm",
                "exact_gate_fallback",
                "predicted_arm",
                "predicted_eligible",
                "policy_evaluable",
                "predicted_exact",
                "predicted_score",
                "predicted_time_ratio",
                "predicted_memory_ratio",
                "predicted_beats_both",
                "oracle_arm",
                "oracle_score",
            ],
        )

    print(
        json.dumps(
            {
                "complete": complete,
                "usable": len(usable),
                "usable_for_learned_tbox_tree": len(tree_usable),
                "policy_union_exact": union_exact,
                "semantic_fragment_counts": dict(sorted(fragment_counts.items())),
                "no_policy_candidate_ontologies": no_policy_candidate,
                "oracle_beats_both": beat_both,
                "gaps_over_20_percent": len(gaps),
                "fitted_tree_exact": routed_exact,
                "fitted_tree_beats_both": routed_beat_both,
                "fitted_tree_over_20_percent": routed_over_20,
                "selected_tree_cv": cv_candidates[0] if cv_candidates else None,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()

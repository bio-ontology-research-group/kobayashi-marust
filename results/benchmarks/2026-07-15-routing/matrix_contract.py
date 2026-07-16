#!/usr/bin/env python3
"""Frozen arm contract for the ontology-sharded IBEX benchmark."""

KM_ARMS = (
    "elc",
    "elc_cert",
    "cb_plain16",
    "cb_plain8",
    "cb_plain1",
    "cb_absorb16",
    "cb_absorb8",
    "cb_absorb1",
    "cb_trigger16",
    "cb_trigger8",
    "cb_trigger1",
    "lean",
    "ht_general",
    "ht_qo",
    "ht_shoq",
    "ht_card",
    "ht_bridge",
    "ht_features",
    "ht_full",
    "ht_rules",
    "card_fn",
    "nominals",
    "seq_on",
    "seq_off",
)

BASELINE_ARMS = (
    "elk",
    "hermit",
    "konclude_w1",
    "konclude_w16",
)

ALL_ARMS = KM_ARMS + BASELINE_ARMS

ARM_KIND = {
    **{arm: "km" for arm in KM_ARMS},
    "elk": "elk",
    "hermit": "hermit",
    "konclude_w1": "konclude",
    "konclude_w16": "konclude",
}

# The official ORE run retained 587 Konclude taxonomies. These five inputs have
# no Konclude signature at all, so their benchmark rows must be marked as such
# and adjudicated separately. Keeping the list in the frozen contract prevents
# a missing or misnamed gold file from silently changing the correctness rule.
NO_KONCLUDE_GOLD = frozenset(
    {
        "ore_ont_10860.owl",
        "ore_ont_1194.owl",
        "ore_ont_15703.owl",
        "ore_ont_3524.owl",
        "ore_ont_4669.owl",
    }
)


if __name__ == "__main__":
    for arm in ALL_ARMS:
        print(arm)

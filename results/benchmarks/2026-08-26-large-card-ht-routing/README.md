# Large cardinality terminology HT routing

ORE7499 spent almost all automatic-route time in the certified cardinality
proxy portfolio. A paired workstation diagnostic with frozen v5 binary
`e9f06cda45e0...` produced byte-identical classification JSON:

| route | wall | peak RSS |
|---|---:|---:|
| automatic `certified_card_proxy_abox` | 37.97 s | 2,371.9 MiB |
| isolated `ht_general` | 8.42 s | 578.3 MiB |

The only other corpus ontology carrying the same
`card_number_role_separable` source certificate is ORE9540. Its profile is
small and structurally different; isolated general HT did not complete within
the diagnostic interval, while v1.0.0 automatic classification took 0.7165
seconds. The feature gate therefore requires at least 10,000 logical axioms,
at most 500 ABox axioms, at least 100 unions, qualified cardinality, and a role
chain. It selects ORE7499 and excludes ORE9540 in the complete profile census.

This gate schedules a complete-answer-or-defer mechanism. The general HT
worker validates converted-input coverage before publication, and a refusal
restores the exact nominal fallback. A source-bound IBEX exact pair and full
592-ontology sweep remain required.

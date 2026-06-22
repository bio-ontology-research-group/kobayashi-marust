# 2026-06-22 — KM vs ELK clean-set comparison (ORE 2015 scored, n=587)

Are we "strictly as good or better than ELK on EL++"? This compares the
**gold-clean** sets (status ok AND signature == Konclude gold, 0 unsound / 0
incomplete) of KM (sweep `47711943`, HEAD `b527a3a`) and ELK 0.6.0 (recorded in
`km-incr/bigsweep/results.jsonl`).

## Headline

| | gold-clean onts |
|---|---|
| **KM** | **568** |
| ELK | 530 |
| KM-clean ∧ ¬ELK-clean (**we win**) | **44** |
| ELK-clean ∧ ¬KM-clean (**we lose**) | **6** |

KM passes 44 onts ELK cannot classify cleanly, and loses 6. Net **+38**, and KM
is **never wrong** where ELK is right (KM's only failures are timeout/memout; 0
unsound, 0 incomplete corpus-wide).

## The 6 we "lose" are all non-EL++ — ELK gets them by dropping axioms

ELK implements only EL++. On a non-EL ontology its OWL frontend **silently drops**
the axioms it cannot express (disjunction, number restrictions, inverse roles) and
classifies the EL remainder. For these 6, the dropped axioms happen to be
inferentially inert, so ELK's EL-approximation coincides with the full-DL gold —
coincidental completeness, not sound reasoning of the ontology as written.

| ont | el_rbox_safe | disj. heads | eq atoms | non-EL feature | KM | konclude | hermit |
|---|---|---|---|---|---|---|---|
| 1603  | False | 43  | 16 | disjunction + cardinality | timeout (18.4 GB) | ok | ok |
| 6934  | False | 18  | 25 | disjunction + cardinality | timeout (2.7 GB)  | ok | ok |
| 7581  | False | 0   | 1  | non-EL RBox (inverse/func)| timeout (9.5 GB)  | ok | timeout |
| 10908 | False | 26  | 7  | disjunction + cardinality | timeout (18.4 GB) | ok | ok |
| 12653 | False | 15  | 66 | disjunction + cardinality | timeout (0.28 GB) | ok | ok |
| 16444 | False | 110 | 0  | disjunction               | timeout (17.4 GB) | ok | ok |

Every one carries disjunction, number restrictions, and/or non-EL roles — outside
the EL++ profile. So **there is no EL++ ontology ELK classifies that KM misses**.

## Verdict

- **On EL++ ontologies: KM ⊇ ELK (strictly ≥)** — KM passes every EL++ ont ELK
  passes, and is lighter on the big ones (8737: KM 5.5 GB vs ELK 16.4 GB JVM;
  16744 similar).
- **Whole corpus: KM strictly better** — 568 vs 530, +44 net, never incorrect.
- The only place ELK "passes" and KM does not is 6 SROIQ ontologies where ELK's
  axiom-dropping coincidentally lands on the gold classification. KM instead runs
  a sound+complete procedure (CB / hypertableau) that times out on them. These are
  candidates for the elc **repair certificate** extended to prove inertness of
  cardinality / inverse residuals (the same mechanism that recovered 15803, 6212).

## The 44 KM wins (onts ELK cannot do cleanly)

Non-EL ontologies KM classifies gold-clean via the CB engine / hypertableau /
elc-repair-certificate, that ELK either gets wrong (drops decisive axioms) or
cannot process:

```
1016 10594 11460 11623 12141 12698 13383 13912 148 14896 15491 16461 1790 2313
3050 3795 4604 4827 4834 5107 5303 5564 5943 6060 6246 6765 6999 7025 7216 7320
7455 7474 7901 8006 8322 8941 8999 9024 9096 9557 960 9635 9654 9668
```

Notable: 5303 (the live ∀+⊔ disjunction family, recovered via HT), 9024 / 12141 /
9635 (emelim-recovered), 6999 (datatypes), 16461 (qualified cardinality), 8941 /
13912 (contested gold where HermiT/KM are correct and ELK is not), 4604 / 11460
(central-blowup recovered).

## Method note

ELK numbers are from the prior `km-incr/bigsweep` run (same 587-ont corpus, same
Konclude `ore_canon` gold). KM numbers are the current sweep `47711943`. "clean" =
status ok AND `match`/`gold_match` true AND 0 unsound AND 0 incomplete.

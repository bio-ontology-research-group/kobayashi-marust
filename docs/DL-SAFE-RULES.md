# DL-safe rules (SWRL `DLSafeRule`) — fragment and contract

KM supports SWRL DL-safe rules through the **ABox-seeded HT consistency
precheck** (`KM_HT_RULES`, default on). A rule fires only over *named
individuals* (DL-safety: every rule variable is `__O__`-guarded, and every
`Ind(a)` term is pinned by `__nom__a`). The precheck is one-sided: it seeds the
ground ABox as nominal nodes, fires the representable rules, and short-circuits
to **inconsistent** on a clash; otherwise it falls through to normal TBox
taxonomy classification. Dropping a rule from this precheck is sound — a lost
constraint can lose an inconsistency, never invent one.

## The rule pipeline

| stage | file | role |
|-------|------|------|
| parse | `frontend/parse.rs::parse_rule_atoms` | AST rule atoms; drops the whole rule on a Data/BuiltIn/DataRange atom |
| profile | `frontend/profile.rs::rule_atoms` | counts `unsupported_rule_axioms` (the semantic probe) |
| contract | `frontend/mod.rs::collect_rules` | `parsed == source` gate; converts to `JRule` or DECLINES |
| encode | `orchestrate/cb_to_ht.rs::build_rule_clause` | rule → HT clause; fires or defers |
| reason | `tableau.rs::rules_consistency_verdict` | seeds ABox, fires rules, one-sided clash check |

## The three tiers (rule atom shapes)

- **FIRED** — every atom is a `ClassAtom` over a *named* class, an
  `ObjectPropertyAtom`, or a `SameIndividualAtom`. Terms may be variables or
  named individuals.
  - A body `SameAs(u, v)` guard unifies u and v onto one Subst variable
    (union-find over rule terms); both `__nom__` pins land on the shared node.
  - A head `SameAs(u, v)` conclusion emits `HAtom::Eq{u,v}` (the rule derives the
    equality; the tableau o-rule then merges).
- **DEFERRED** — the rule additionally carries a `DifferentIndividualsAtom`. The
  fast Ht tracks no node distinctness (`HAtom` = Concept/Role/Eq/Exist only), so
  a `u ≠ v` guard has no sound encoding. `build_rule_clause` returns `None` and
  the rule is dropped (counted in `dropped`). It is **carried through
  `collect_rules`** (does NOT decline the route) — declining would forfeit the
  fired rules that detect the 2669/15516 clash.
- **DECLINED** — the rule has a `DataPropertyAtom`, `BuiltInAtom`,
  `DataRangeAtom` (a concrete-domain obligation with no DL encoding) or a
  `ClassAtom` over a complex class expression. The parser omits the AST rule, so
  `parsed < source` in `collect_rules` and the whole rule-aware route is
  rejected. KM declines rather than silently approximating a datatype rule.

## ORE `DLSafeRule` corpus (6 ontologies)

Gold: Konclude cannot parse `DLSafeRule` (exits 0 with empty output), so the
adjudicated gold is HermiT on a cleaned core (see `CONTESTED-GOLD.md`).

| ont | verdict | KM |
|-----|---------|----|
| 2669  | inconsistent | inconsistent ✓ (5 pure rules fire; 3 Diff deferred) |
| 15516 | inconsistent | inconsistent ✓ (2 pure rules fire) |
| 10906 | inconsistent | closed via the ABox/datatype precheck |
| 13129 | consistent | consistent ✓ |
| 12451 | consistent | — |
| 10860 | under adjudication | **honest decline** (see below) |

### ORE 10860 — the 17-shape breakdown

The 17 `DLSafeRule` axioms partition into:

| count | shape | tier |
|-------|-------|------|
| 8 | Class + Role (some Class/head args are named individuals) | FIRED |
| 5 | Class + Role + `DifferentIndividualsAtom` | DEFERRED |
| 4 | + `DataPropertyAtom` / `BuiltInAtom` (`greaterThan` on dates, `hasClass`, `isSubClassOf`) | DECLINED |

10860 is **not closed**: 4 rules carry built-ins, so the current parser declines
the whole ontology (`unsupported: DL-safe rules: parsed 13 of 17`). A direct
source audit on the frozen corpus file (SHA-256
`480139a6018bc4eb0d35e47edf00a6d257dd87137c1d0f93a27021cf154f4a2d`)
narrows the live obligation substantially:

- Three rules compare access/authorization dates or shift times. The ontology
  contains zero `DataPropertyAssertion`, zero `SubDataPropertyOf`, and zero
  `EquivalentDataProperties` axioms. No named binding can satisfy either data
  atom in these DL-safe rule bodies, so all three rules are provably inert;
  evaluating `swrlb:greaterThan` is unnecessary for this ontology.
- One rule uses `abox:hasClass` twice and `tbox:isSubClassOf` once. This is the
  sole remaining semantically live unsupported rule. Its head derives a
  `hasR2RRelation` edge when the EHR-section class of one named individual is a
  subclass of the class of another.

The exact closure task is therefore to retain and evaluate that finite
named-ABox meta-rule, together with all 13 already parsed rules, then check the
materialized ABox for consistency. KM must continue to decline until that
check is complete; inertness of the three data rules does not justify dropping
the live meta-rule.

## Soundness note

Firing a *subset* of DL-safe Horn rules is a sound under-approximation for
consistency and classification (fewer constraints ⇒ a superset of models ⇒ a
subset of entailments). KM does NOT partial-fire a DECLINED ontology, but the
DEFERRED (Diff) drop within an otherwise-representable ontology relies on exactly
this: a dropped Diff rule can only lose a clash, never fabricate one.

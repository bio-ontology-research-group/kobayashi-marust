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

10860 is **not closed**: 4 rules carry SWRL built-ins that compare dates and do
custom `hasClass`/`isSubClassOf` meta-reasoning — concrete-domain obligations
with no DL encoding. Because those 4 rules decline the route, the 8 FIRED and 5
DEFERRED rules are not partially fired: KM declines the whole ontology
(`unsupported: DL-safe rules: parsed 13 of 17`). This is the deliberate
policy-leaf boundary — a datatype rule is not an approximable constraint.

## Soundness note

Firing a *subset* of DL-safe Horn rules is a sound under-approximation for
consistency and classification (fewer constraints ⇒ a superset of models ⇒ a
subset of entailments). KM does NOT partial-fire a DECLINED ontology, but the
DEFERRED (Diff) drop within an otherwise-representable ontology relies on exactly
this: a dropped Diff rule can only lose a clash, never fabricate one.

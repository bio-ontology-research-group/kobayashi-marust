# Finite-rule taxonomy publication boundary

The automatic finite-rule path classifies Boolean class theories whose named
graph contains DL-safe rules. `KM_NO_FINITE_DATA_RULE_NORMALIZE` disables finite
grounding, and `KM_NO_FINITE_RULE_TAXONOMY` disables this publication path. A rule conclusion about a
named individual must not become a universal class inclusion. Conversely,
classifying the TBox alone cannot detect an inconsistent rule ABox.

The orchestrator therefore requires both of the following:

1. A model of the original source, independently checked against its original
   Boolean class axioms, object assertions, object-property axioms, data axioms
   and every original logical rule. Grounded clauses alone are insufficient.
2. Complete classification of the source's Boolean class projection, with zero
   dropped clauses. The projection preserves every public query class.

`frontend/finite_data_rules.rs` admits the projection only when adding an
isolated, unnamed object cannot violate the remaining theory. In particular,
nominals, object restrictions, reflexive properties, universal properties,
imports, keys and unrecognized syntax decline this path. Full source names and
property sorts are carried through the worker input; ambiguous mappings decline.

The rule model checker uses actual named denotations, permitting different
names to denote the same object. Data nodes receive concrete literal values
with checked datatype memberships. Object and data relations have checked
sorts. Unknown datatype interpretations, unresolved builtins and exhausted
verification budgets do not establish a model. Rule-join pruning changes only
enumeration: a branch can stop when a premise is false for every extension of
its binding, or when its entire head is already true for every extension.

## Lean correspondence

`DLSafeAtomicTaxonomyExtension.boolean_query_projection_exact` proves equality
of Boolean query consequences between the admitted class theory and the full
theory, conditional on an original model and preservation under every valid
fresh-object valuation. Subsumption uses the query `A → B`; unsatisfiability
uses `¬ A`. The module's named-rule, role-chain, Boolean domain/range and data
property preservation lemmas discharge the corresponding extension conditions.

`DLSafeRuleJoinOrdering` proves permutation invariance and the conditions for
false-premise pruning, true-head pruning and class-domain restriction. Both
CB and HT certification surfaces audit the relevant modules. The routing gate
also requires the projection/pruning audits, the model-checker tests and the
`finite_rule_taxonomy` command-line tests.

## Remaining certification boundary

These proofs do not extract the Rust parser, source partitioner, concrete-value
evaluator or finite-model checker into Lean. The implementation remains
responsible for complete source coverage and correct interpretation of every
accepted source construct. The full exact-tag release gates and corpus
correctness comparison remain required.

An explicitly requested HT runtime certificate currently rejects the
rules-consistency worker path. The new orchestrator must not bypass that
rejection; a command-line regression checks it without opt-in flags. Default
activation does not claim that this runtime certification obligation has been
discharged. An inconsistent completion result reports global inconsistency;
it does not require a model or publish the Boolean projection.

The regression fixture also checks that `Bad(b)`, derived by a numeric rule,
does not imply `P ⊑ Bad`; an asserted `¬Bad(b)` cannot publish a consistent
TBox projection. A worker response without an explicit consistency verdict
must fail instead of defaulting to true.

Finite grounding can produce zero executable rules when no concrete data
assignment satisfies a premise. That does not remove the original rule/model
obligation: the frontend retains the named assertions and role axioms, and
`convert_rule_model` explicitly preserves the named graph even with an empty
rule vector. Ordinary rule-free conversion remains unchanged. The routing gate
checks both this distinction and the missing-data CLI case.

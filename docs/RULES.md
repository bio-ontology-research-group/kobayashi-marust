# DL-safe rules: what km supports, what it declines, what HermiT does

Status 2026-11-15 (engine round 3). History and mechanisms:
`docs/DL-SAFE-RULES.md`.

## Semantics

A `DLSafeRule` binds its object variables to named individuals and its
data variables to data values (any value, including values that no literal
of the source names: HermiT answers `a : ∃p.xsd:integer`,
`p(?x, ?v) → B(?x)` with `a : B`, and so does km). An answer km publishes for
an ontology with rules is exact under this reading, or km declines with exit
code 3 and the reason.

## Supported

- Body and head atoms over named classes and named object properties
  (`ObjectInverseOf(r)` swaps the arguments), `SameIndividualAtom`,
  `DifferentIndividualsAtom`, individual constants.
- Class atoms with class expressions (the ground-rule source gives each
  expression a fresh private class).
- `DataPropertyAtom` with a constant literal, in the body or the head.
- A data variable that occurs in the body in one `DataPropertyAtom(p t ?v)`
  and otherwise only in `DataRangeAtom(D ?v)` atoms: the atoms are replaced
  by a class atom for a fresh class `≡ DataSomeValuesFrom(p ⋂D)`
  (`frontend::rule_data_atoms`, W8).
- OWL 2 keys (`HasKey`), rewritten to the rules they denote
  (`frontend::has_key`).

## Declined (exit 3)

- A data variable shared by two data property atoms (a join on a value), a
  data variable in a head atom, and `BuiltInAtom` (HermiT refuses built-ins
  too: "built-in atoms are not supported yet").
- Rules that reach class queries through a nominal (`ObjectOneOf`,
  `ObjectHasValue`) or the universal role when the rule worker's input has
  inverse roles together with number restrictions (SHOIQ), or any construct
  the rule worker fences: the rule-aware taxonomy is the clausal tableau over
  the nominal-seeded ABox, which has no SHOIQ reasoning. Message: "DL-safe
  rules reach class queries through a nominal, and the rule-aware taxonomy
  would omit ... fenced construct(s) ... (inverse+number(SHIQ))". Pool
  inputs: ore_ont_8250, 3726, 7278 (plain classification), ore_ont_2526
  (with `--properties`: its property probes `∃r⁻.B` add the inverse role;
  the range-by-assertion shortcut that avoids them is not sound with rules,
  because rules apply to the fresh named individuals of that run).
- Rule shapes outside the certified rule compilers ("parsed N and certified
  M of K; an atom or head shape is unsupported").

## HermiT

HermiT 1.4.3 reads DL-safe rules with the semantics above, supports every
atom kind except built-ins, and has no nominal or SHOIQ restriction. On the
round 3 rule fixtures (`scratch/engine3/p2/rules`, 25 inputs) km agrees with
HermiT wherever km answers; HermiT's types are wrong on one input
(`DifferentIndividualsAtom`, refuted by HermiT's own consistency check).

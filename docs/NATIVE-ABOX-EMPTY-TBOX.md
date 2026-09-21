# Native ABox with an empty source TBox

The native bridge previously required a nonempty source TBox before installing
its complete typed ABox. That declined assertion-only ontologies, including
finite data-value clashes after exact unary translation.

The candidate allows typed ABox installation when the source TBox is empty.
It keeps source mode false: all retained clauses and definers still pass through
the ordinary encoder, with its unsupported-input refusal. Source-only positive
model certificates remain disabled. A disabled nonempty source TBox still
refuses native metadata. Complete metadata, proxy coverage, and role/individual
checks remain mandatory. Neither general hypertableau nor CB fallback is added.

The Lean retained-theory theorem composes the existing exact native seed model
equivalence with every retained clause. It does not certify Rust parsing,
encoding, coverage, or completion. The focused Rust test includes a consistent
control, a retained A <= B clause contradicting A(a) and not B(a), and malformed
metadata refusal. CLI fixtures cover complements, aliases, and equality in both
in-process and isolated bridge runs. All runtime and global release checks are
still required before promotion.

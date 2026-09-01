# UO singleton-nominal witness

The three axioms in `witness.tsv` occur verbatim in the frozen UO input with
SHA-256 `b6f4a0fa082b6357dd34801d09bbf4041667698374aaf8474b900f819f15ffa7`.
They establish one representative relation omitted by ELK and Whelk:
`UO_0000244 SubClassOf UO_0000329`.

The checker validates the exact singleton-punning shape and replays the finite
semantic argument. If `A` is the singleton `{a}`, `B` is the singleton `{b}`,
and `B SubClassOf A`, then `b` belongs to `A`, so `b=a`; the singleton classes
are equal and `A SubClassOf B` follows. This witness does not claim that the
three axioms explain all 54 omitted pairs; it certifies one representative of
the repeated source pattern.


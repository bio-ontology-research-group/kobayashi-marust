# Finite data source identities

The admission scanner now recognizes a conservative ASCII subset of anonymous
individual labels only in individual argument positions. It retains each source
label unchanged for the existing collision-safe registry and typed ABox. It does
not introduce a unique-name assumption or accept blank labels as classes or
properties. Unexpanded ordinary prefixes remain refused. Named individual
arguments are no longer mistaken for class/property occurrences.

An ordinary data property included in owl:topDataProperty imposes no constraint.
The scanner admits that tautology without adding a finite value or propagation
edge for the universal relation. Other uses of the universal data property stay
refused, and the whole-source owl-prefix binding check remains mandatory.

FiniteDataSourceIdentities proves exact transport under existential assignment
of anonymous labels and elimination of a subproperty-to-universal tautology.
The theorems do not validate lexical decoding, fresh-name allocation, parser
position checks or native completion. Regression fixtures cover shared labels,
distinct labels without a unique-name assumption, same-individual aliasing,
a named IRI with the same local spelling, object-role links, and top-property
positive/negative controls. Full native reference and certification gates are
required before promotion.

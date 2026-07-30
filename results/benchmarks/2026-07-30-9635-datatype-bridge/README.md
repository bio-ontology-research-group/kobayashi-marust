# ORE 9635 exact datatype bridge restoration

This change restores `ore_ont_9635.owl` through the automatic
`certified_nominals` portfolio. Dispatch uses source features only. The
converted-input bridge independently certifies the exact fragment and either
returns a complete classification or defers to nominal-aware CB.

The exact bridge additions are:

- treat `DataOneOf(false, true)` as extensionally equal to `xsd:boolean`;
- retain `xsd:int` as a separate exact atomic datatype family;
- accept datatype-bearing atomic existential conjuncts in source
  equivalences;
- preserve bounds zero and one over a data property with `owl:Thing` filler,
  including when nested below an ordinary object-role restriction;
- permit multiple datatype symbols for one exact family only when every
  symbol has the required value memberships and, for Boolean, the exact
  two-value cover.

All larger data-property bounds, non-Top data fillers, unsupported complex
datatypes, incomplete singleton relations, and data ABox assertions remain
fail-closed.

Local release evidence:

- the serial release suite passes: 1,804 library tests plus all integration
  and documentation tests, with zero failures;
- automatic routing selects `certified_nominals`;
- classification completes in 0.14 seconds at 17,136 KiB peak RSS;
- the result matches Konclude exactly: 159/159 subsumptions, one identical
  unsatisfiable class, and the same consistency verdict.
- post-change automatic-route controls remain exact for 10621 (70,827
  subsumptions and 33,433 unsatisfiable classes), 15672 (142 subsumptions),
  and 9540 (66 subsumptions).

The source-bound focused IBEX result and complete 592-ontology sweep are added
after their terminal audits pass.

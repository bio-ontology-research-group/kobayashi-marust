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

IBEX acceptance is bound to source commit `93dcec4`, archive SHA-256
`39850e9eca2359b87ebc88d468ddc3c7f8eb6215628d210ce5fad2b781ddcb83`,
and binary SHA-256
`03bc9facf50cef57cbf9657952a7b34d7b94f378441cdd968c46c56ecb886f08`.
Build job 49640672 completed. Focused exactness array 49640673 remains the
source-bound acceptance gate. Complete sweep 49640841 and audit 49640842 were
cancelled before any task started because the newer 6999 dateTime restoration
superseded this source revision. The replacement full sweep uses that newer
revision and retains 9635 in its focused regression panel.

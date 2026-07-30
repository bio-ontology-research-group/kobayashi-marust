# ORE 6999 exact dateTime bridge restoration

This change restores `ore_ont_6999.owl` through the automatic
`certified_nominals` portfolio. The source router already selected that
complete-answer-or-defer portfolio; the converted-input bridge previously
declined because its datatype certificate omitted bare `xsd:dateTime` and
data-property cardinality two.

The certificate now admits:

- bare `xsd:dateTime` as a nonempty atomic family with at least two values;
- `owl:Thing`-filled data-property lower and upper bounds from zero through
  two.

It still rejects date/time literals, facets, `xsd:dateTimeStamp`, bounds above
two, and non-Top data fillers. The existing validator continues to require
lossless source axioms, normalized clauses, singleton relations, range
memberships, and complete typed ABox data before the bridge may answer.

Local source evidence:

- the full serial release suite passes with 1,805 library tests and all
  integration tests, with zero failures;
- automatic routing selects `certified_nominals`;
- 6999 completes in 0.39 seconds at 44,056 KiB peak RSS;
- 6999 matches Konclude exactly: zero named-class subsumption pairs, one
  identical unsatisfiable class, and the same consistency verdict;
- 9635 remains exact at 159 subsumptions and one unsatisfiable class;
- 10621 remains exact at 70,827 subsumptions and 33,433 unsatisfiable classes.

IBEX acceptance campaign:

- source archive SHA-256:
  `c3bbf880faa958df53ed552e17f20dd32044f9380dd628e26ca6c88904f7ceef`;
- build job `49641505` completed with
  `DATETIME_BRIDGE_BUILD_COMPLETE`;
- resulting binary SHA-256:
  `8928277f4a7f605332633703552f57265462356e09a40da29378f33a50da4595`;
- focused exactness array `49641506` covers 6999, 9635, 10621, 15672, and
  9540 and is pending;
- resumable 592-ontology array `49641693` depends on successful completion of
  that focused gate;
- terminal audit job `49641694` runs after the complete array.

The focused and full-sweep results remain provisional until their terminal
audits pass. The production sweep uses the same binary byte-for-byte as the
focused gate.

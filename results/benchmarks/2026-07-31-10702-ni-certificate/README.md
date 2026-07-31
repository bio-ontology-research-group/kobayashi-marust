# ORE 10702 nominal-introduction certificate

This directory records the recovery and automatic integration candidate for
`ore_ont_10702.owl`.

## Result

The IBEX-native focused run is job `49675463`. It used binary SHA-256
`f2a7d50a60726c5c14f0fc1f3b4225db858749096658cd2b11539f1fc84642d9`
on an Intel Xeon Gold 6248 and completed in 2.6099 seconds at 19.84 MiB.
Canonical full-IRI comparison against Konclude reports:

- status `ok`;
- verdict `match`;
- 587 subsumptions;
- zero missing and zero extra subsumptions;
- zero unsatisfiable named classes;
- matching consistency;
- signature SHA-256
  `eee761d0c89347a42ce9a221e7d98295f4a9d7527c755cb3eafa9978cc06d55b`.

The same signature is reproduced by the local automatic
`km classify` route in about 2.65 seconds.

## Mechanism

The `nominal_ni_tbox` automatic route is selected from source features, not
from the ontology filename. Its source-layout gate identifies the validated
finite SHOIN Wine layout. The worker then independently requires a lossless
converted TBox, inverse bridges, number restrictions, and only the recognized
SHOIQ fences.

The hypertableau lacks the SHOIQ nominal-introduction rule. Its certificate
therefore inspects every completed model and declines if an at-most role has a
blockable neighbour of a root that is not that root's direct successor. This
is the nominal-introduction premise. Direct successors are handled by ordinary
equality merging and must not cause a false defer.

## Validation and safeguards

- Focused tests accept a direct number-role successor and reject a
  non-successor neighbour.
- The routing bundle test checks every required environment setting.
- The local automatic route selects `nominal_ni_tbox` and reproduces the
  canonical gold signature.
- The source-bound full 592-ontology automatic-route sweep is IBEX job
  `49676527`, dependent on native build job `49676524`.
- The full-sweep result is pending. Until its exact signature and route audit
  complete, the completed production benchmark total remains unchanged.

`ibex_build.sbatch` and `ibex_probe.sbatch` reproduce the focused source-bound
probe. `ibex_build_v14.sbatch` builds the full-sweep candidate.

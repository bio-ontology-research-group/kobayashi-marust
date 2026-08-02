# ORE 1194 eager inverse-bridge batching

This experiment tested an exact scheduling change in the certified-EL repair
upper model. It does not close ORE 1194 and is not enabled in production.

## Design

The retained residual contains forced inverse-role bridge clauses of the form
`R(x,y) -> S(y,x)`. Each has one body atom and one head atom, so satisfying a
violation involves no model-search choice. The prototype materializes all
currently forced bridge edges in a repair-pass fork, closes once under the EL
rules, and then uses the existing complete residual validator.

This differs from the rejected virtual-inverse lower-bound experiment. The
prototype never changes the sound EL lower bound. It acts only in a certificate
upper-model fork, where the inserted edges are required by the full ontology.
The final acceptance predicate is unchanged and still checks every residual
clause.

Two focused tests check the exact swapped-variable bridge shape, reject
forward and disjunctive near misses, and check bridge-rule fixpoint chaining.
The complete EL/certificate module passed 71 tests on the uncompressed
prototype and 73 tests after combining it with the existing upper-model
compression and complete top-cover batching.

## Production-bounded measurements

Input `/tmp/1194.clauses.json`:

- 1,062,240 clauses;
- SHA-256 `5c0fdb40e5252e1d3092127bbe77c4cba74abf9da27041767f5c2959c2bc7da0`.

Every run used `KM_ELC_CERT=2`, a 240-second timeout, and produced zero output.

| candidate | binary SHA-256 | forced bridge edges | wall | peak RSS | result |
| --- | --- | ---: | ---: | ---: | --- |
| ordinary labels, hashed candidate batch | `8051d4c6b038df412eb8e509522e8904fddeaa97dd10ce923ec6a2dcb6696e4e` | 22,853,033 | 240.84 s | 19,411,364 KiB | timeout, no taxonomy |
| adaptive labels + cover batching, hashed candidate batch | `21fa5361a891f59594f5456c59ac6d14633ec9cac275da1de6357fc66ad5043d` | 22,853,033 | 240.46 s | 17,841,848 KiB | timeout, no taxonomy |
| adaptive labels + cover batching, flat candidate batch | `e5bbe016c4cc2e8f1798c5f61e1501cc10f91951bd72aafa7de6d3861d71f7e6` | 22,853,033 | 240.74 s | 17,120,788 KiB | timeout, no taxonomy |

The flat batch removes the redundant temporary hash set. `State::add_edge`
remains the authoritative exact membership check, and successful additions are
counted from its edge epoch. This moved the start of the combined EL closure
from about 177 seconds to about 139 seconds and lowered peak memory, but the
closure still did not finish before the benchmark limit.

## Decision

Reject eager physical materialization as a production route. It is exact, but
the combined 22.85-million-edge closure remains too large. The useful next
architectural target is a repair-fork-only predecessor-sensitive or virtual
edge representation whose residual validator and EL joins see the required
inverse relation without storing a second physical copy. Such a representation
must remain isolated from the sound EL lower bound.

The automatic result remains 591/592. ORE 1194 still fails closed.

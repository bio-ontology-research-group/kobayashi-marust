# IRI-cached full classification candidate

Job 53332943 runs the exact pinned 35408ae7e29c binary from source commit 4475c8cb over all 1,920 unchanged inputs. The inventory pins the same 240-second, 20-GiB, one-CPU limits and independent taxonomy comparisons as the earlier full sweeps. It enables the repeated-IRI cache alongside the existing single-worker, native and conformance-cache flags. Timing instrumentation is disabled.

This is a candidate measurement, not a release. The inventory records certification as pending at submission and stays immutable so every measurement has the same inventory hash. Later certification evidence belongs in the separate iri-cached-certification-receipt.json; passing those gates does not itself prove the performance targets.

The grammar-only comparison is job 53332675. It independently retains all 212 refused inputs, but compares grammar acceptance and exact error text only. The full classifier still applies the remaining admission checks and audits completed taxonomies.

The earlier role-index sweep has a broad timing increase relative to the single-worker sweep, despite large gains on a few hard cases. Job 53333094 compares those two pinned binaries in alternating order on the same allocated node for five selected controls. It is diagnostic evidence; it does not replace the full corpus or discard slowdowns.

# ORE 1194 ordered posting-removal screen

This experiment tested detached candidate `83bb37a`, based on the linked
worked-off representation from `4a34d3c`. It replaces full `retain` scans when
removing a known clause identifier from posting lists with a position lookup
followed by ordered `remove`. This preserves posting membership and order, and
therefore preserves the existing saturation schedule.

The candidate is not included in `main`. It did not close ORE ontology 1194 or
produce a measurable performance improvement.

## Validation

Two optimized exact rebuild-oracle tests passed before the IBEX screen:

- `back_subsume_incremental_unindex_matches_rebuild`
- `back_subsume_incremental_unindex_matches_rebuild_roles`

The candidate source archive had SHA-256
`26f7bd68222a18c339dd989bd3325d6701819816693e943dc2774bd329ac467b`.
IBEX build job `49865056` completed revision `83bb37a`; its screened `km`
binary had SHA-256
`06b19d211dc3a50c0d38f1626d77136086cf46b08a241cc35d4cf9a4bc79ee5c`.

## Focused result

Slurm job `49865250_1` ran the exact manual CB route used by the linked
baseline: two CB threads, a 225-second central cap, nominal handling enabled,
chain axioms retained, and the production 240-second / 20-GiB outer contract.
The harness required a binary-hash match, selected-route trace, checkpoint,
recognized terminal status, and `TASK_COMPLETE` marker.

| Candidate | Status | Wall time (s) | Peak RSS (MB) |
|---|---:|---:|---:|
| linked baseline `4a34d3c` | error | 234.4951 | 14,891.39 |
| ordered posting removal `83bb37a` | error | 234.4272 | 14,898.35 |

The 0.0679-second wall-time difference and 6.96-MB RSS difference are noise.
The candidate does not justify broader regression gates or integration.

Raw checkpoint, result, resource report, stderr, and submitted Slurm script
are retained under `evidence/`.

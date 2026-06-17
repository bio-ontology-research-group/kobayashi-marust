# Versioned benchmark snapshots

Each `YYYY-MM-DD-<topic>.md` here is a **point-in-time** snapshot of a full
benchmark table. We keep every version (never overwrite) so changes can be
compared across time. When a sweep finishes, append a new dated file rather than
editing an old one.

Every snapshot must report the full panel for each measure (standing rule):
**passrate (ok) / MATCH / sound / complete / unsound / incomplete /
avg + median wall / avg + median peak-mem** — no single metric defines
success/failure.

Gold = Konclude with the `ore_canon` `Thing≡Nothing` fix; SWRL/`DLSafeRule`
ontologies use HermiT (Konclude cannot parse them). See
[`../../docs/CONTESTED-GOLD.md`](../../docs/CONTESTED-GOLD.md) for which oracle is
correct where.

## Index

- `2026-06-17-ht-matrix.md` — HT 9-arm version matrix (after the cb_to_ht
  query-set incompleteness fix) + proactive-router sim. Adds the `ht-modelprune`
  arm (HermiT QuasiOrder multi-model pruning, output-identical).

# ore_ont_1194: inverse-role bridges on the certified-EL route (2026-08-02)

Host `leechuck-office`, branch `codex/opus-1194-inverse`. Input is the frontend
clause payload `/tmp/1194.clauses.json` (270 MB, 1,062,240 clauses). Every run
is bounded by `run_1194.sh`: `systemd-run --scope MemoryMax=24G MemorySwapMax=0`
around `/usr/bin/time -v /usr/bin/timeout 240`.

## 1. What the bridge roles are actually used for

`audit_roles.py` classifies every role atom by the syntactic position it holds
(`role-audit.txt`). 1194 carries 14 bridge clauses: six mutual pairs and two
one-way inclusions.

| role | `A ⊑ ∃R.f` | `∃R.C ⊑ D` | reverse-shaped | chain |
| --- | --- | --- | --- | --- |
| BFO_0000050 | 28,826 | 144,130 | 0 | 0 |
| BFO_0000051 | 10,256 | 45,127 | 0 | 0 |
| RO_0002202 | 28,826 | 144,130 | 0 | 0 |
| RO_0002203 | 102 | 107 | 0 | 0 |
| BSPO_0000098 / 0000102 | 4 / 2 | 12 / 6 | 0 | 0 |
| BSPO_0000124 / 0000125 | 1 / 1 | 1 / 1 | 0 | 0 |
| distally_ / proximally_connected_to | 37 / 56 | 37 / 56 | 0 | 0 |
| surrounded_by__uberon / surrounds | 32 / 20 | 32 / 20 | 0 | 0 |
| has_distal_part, has_proximal_part | 0 | 0 | 0 | 0 |

Both sides of every mutual pair carry NF3 and NF4 axioms, and no role appears in
an already reverse-shaped clause or a chain. So for each pair, whichever side is
eliminated, tens of thousands of its axioms become reverse-oriented rules. There
is no free orientation to pick.

The two one-way roles have no uses at all beyond their bridge.

## 2. Why reverse-oriented rules cannot be run here

`elcomplete::tests::reverse_oriented_inverse_nf4_would_be_unsound` is the
countermodel, verified in both directions:

- on the clean tree the test passes;
- applied to the eager-canonicalisation candidate this session started from, it
  fails with `unsound: derived D ⊑ E, which has a countermodel`.

`C ⊑ ∃R.D`, `C ⊑ A`, `S = R⁻`, `∃S.A ⊑ E`. The rewrite makes the last axiom
`R(y,x) ∧ A(y) → E(x)`, which fires along `C —R→ D` and yields `D ⊑ E`. The
interpretation `Δ = {d}`, `D = {d}`, all other names empty, models all four
axioms with `d ∉ E`.

A node in this completion denotes the generic instance of a concept name, so one
successor node `D` is shared by every `X ⊑ ∃R.D`. A reverse-oriented rule
concludes at that shared successor from one of its predecessors. Making it sound
needs the successor to carry `∃R⁻.A` in its identity, which is a concept-set
context and so the CB engine.

The earlier measurement of the same candidate (`/tmp/1194-inverse-v1.log`,
`v2.log`) had it at 14.0-14.2 GB without finishing base saturation in 150 s,
against 96.19 s / 3.29 GB for the ordinary base. The soundness result makes the
performance result moot.

## 3. What the exact rewrites recover

Same binary, `KM_ELC_NO_BRIDGE_PREP=1` switching the preprocessing off, both
runs `KM_ELC_CERT=2` at 240 s / 24 GiB.

| | residual clauses | peak RSS | conflict restarts reached | output |
| --- | --- | --- | --- | --- |
| prep off (`elc-cert2-prep-off.err`) | 217 | 6.73 GiB | 5 | none, timeout |
| prep on (`elc-cert2-prep-on.err`) | 202 | 6.27 GiB | 15 | none, timeout |

The prep removes 52 clauses over 25 head-free roles, 15 of them residual. It
refuses all six mutual pairs by name, and takes both one-way bridges through the
vacuous-role rule. Each residual clause costs a join over a 499,904-node,
44.2M-edge model on every repair round, so the same wall budget carries the
search about three times as far.

## 4. Where 1194 is still blocked

Not on the bridges. The trace ends in covering-disjunction repair and the
conflict restarts it drives (`clause 131 conflict, banning choice (490064, 134,
281002)` at `__chain__BFO_0000051__HP_0001941`). This matches the earlier
per-round histogram finding: an empty-body cover is violated once per domain
element over 499,904 nodes, so one clause spans several rounds at
`REPAIR_VIOL_CAP=100_000`, and the disjunction census exhausts `MAX_ROUNDS`
before a bridge is ever enumerated.

The next lever on this route is the covering-disjunction model search: bulk
repair for clauses whose violation set is the whole domain, and a
non-restarting conflict strategy. Not the bridges.

## Reproduce

```bash
CARGO_TARGET_DIR=.../engine/target cargo build --release --bin elc
BIN=.../release/elc ./run_1194.sh prep-on  KM_ELC_CERT=2 KM_ELC_DEBUG=1 KM_ELC_TIMING=1
BIN=.../release/elc ./run_1194.sh prep-off KM_ELC_CERT=2 KM_ELC_DEBUG=1 KM_ELC_TIMING=1 \
    KM_ELC_NO_BRIDGE_PREP=1
python3 audit_roles.py /tmp/1194.clauses.json
python3 audit_vacuous.py /tmp/1194.clauses.json
```

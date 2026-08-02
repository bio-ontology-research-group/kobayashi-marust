# Streamed worker-input candidate

Claude Opus commit `c23fd13`, replayed on the certified shared-base result as
`703873e`, shortened the lifetime of the parsed clause arena and streamed the
converted `TInput` directly into an HT worker's stdin instead of materializing
a second serialized copy. It did not alter route admission or the worker JSON
contract.

Twenty-five focused release tests passed, including byte identity between the
streamed and materialized JSON encodings and unchanged candidate sets for the
affected portfolio routes.

## IBEX provenance

- Candidate commit: `703873e`
- Source archive SHA-256: `012f1a78a29bea0ae11968a6a945ba273aa4687e34a330352408c17b0fb0b6ba`
- Build job: `49845080`
- Built binary SHA-256: `ba0b647aa0e45b53d3458c1734b1dee9620df367b2ef5919a3b2e76f8d2c1813`
- Production gate array: `49845083` (indices 274, 389, and 558)
- Baseline: automatic sweep `49841416`, commit `02a563f`

## Paired gates

| ontology | route | baseline wall s | candidate wall s | baseline peak MiB | candidate peak MiB | signature |
|---|---|---:|---:|---:|---:|---|
| 7499 | `certified_card_proxy_abox` | 87.6332 | 87.5151 | 2,980.82 | 2,985.12 | identical |
| 10621 | `certified_nominals` | 88.0925 | 88.1227 | 6,930.49 | 7,300.81 | identical |
| 15846 | `certified_nominals` | 197.8516 | 196.3073 | 18,944.27 | 18,963.54 | identical |

All three outputs and selected routes were unchanged. The candidate produced
no repeatable memory reduction: peaks changed by +4.30 MiB, +370.32 MiB, and
+19.27 MiB. It was therefore rejected and was not integrated into `main` or
sent to a full 592-ontology sweep.

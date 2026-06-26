# Card-on sweep — 2026-06-27

Binary: km @ ec43a3b (gated KM_HT_CARD=1), KM_THREADS=8, 240s timeout, peak via
/usr/bin/time -v. Gold = Konclude. Array job (10 chunks, serial per chunk for
clean per-ont timing).

## Result
- 564 ok / 12 timeout / 2 incomplete, **0 unsound / 0 both** (578 onts w/ gold).
- median wall 0.90 s, median peak 88 MB, p90 wall 21 s, max peak 18.5 GB.

## Card closures (confirmed: card-OFF timeout, card-ON ok, same 8-thread config)
- 1603  ok 20.5s 2.3 GB  (SHQ)
- 7499  ok 79.0s 18.1 GB (SHQ, previously never-pass in any config)
- 7409  ok 107.4s 3.2 GB (SHOQ, 18 nominals)

## Not-ok (14): real-hard (11) + contested gold (3)
541 3215 7914 9540 9663 9724 10702 12653 12698 14817 16444  (real)
2669 15516 10621  (contested: Konclude wrong, HermiT-correct)

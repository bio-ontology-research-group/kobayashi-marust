# m2197 top-nominal data-successor fix: validation

Binaries: `km.base` = 24dada89, `km.fix` = 19ccfb34 (sorts gate widened).
Affected set (`affected.txt`): inputs whose `KM_NOMINALS=1 km ofn` output differs
between the two binaries (2 of 11 sorts fixtures, 57 of 400 fresh2 seeds 2000-2399,
28 of 200 fresh3 seeds 7000-7199 from `gen_nomdata.py --no-inverse`). All other
inputs have byte-identical clause streams, so they were not rerun.
`diff-<set>-<before|after>.tsv`: `diff_run.py` at a 60 s cap, 4 threads, routes
nominals, certified_nominals, ht_general, auto (columns in diff_run.py). The
machine load was 40-48 during the runs. `summary.txt`: verdict counts.

Result: m2197 is fixed on nominals, certified_nominals and auto. The widened
gate makes the nominal CB route much slower on some newly gated inputs:
m2090 0.08 s -> >170 s, m2182 0.8 s -> >170 s (both reruns at 170 s), and
m2137, m2207, m2218, m2278 now exceed 60 s. ht_general refuses (ERR) or is
wrong as before.

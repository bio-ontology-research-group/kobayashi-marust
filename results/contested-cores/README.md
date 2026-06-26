# Contested-gold proof cores

Minimal inconsistent cores for the ORE-2015 ontologies where the recorded
Konclude gold is **wrong** and KM (agreeing with HermiT) is right. These make
the proof in [`docs/CONTESTED-GOLD.md`](../../docs/CONTESTED-GOLD.md)
self-contained: each `.min.owl` is a 2–8 axiom ontology that **HermiT and
Konclude both report inconsistent** when run directly, while the benchmark's
recorded gold mis-records it as consistent.

| core | ont | proven truth | why the recorded gold is wrong |
|------|-----|--------------|--------------------------------|
| `ore_ont_8941.min.owl` | 8941 | inconsistent | `ore_canon.py` mis-read Konclude's `Thing≡Nothing` as "consistent" |
| `ore_ont_13912.min.owl` | 13912 | inconsistent | same `ore_canon.py` bug |
| `ore_ont_15516_norules.min.owl` | 15516 | inconsistent | SWRL `DLSafeRule`: Konclude can't parse, exits 0 empty → bogus "consistent" |
| `ore_ont_2669_norules.min.owl` | 2669 | inconsistent | same SWRL parse-fail |

(The `_norules` cores have the SWRL `DLSafeRule` axioms stripped — Konclude still
cannot reach the same verdict, but HermiT confirms the remaining DL axioms are
already inconsistent.)

A fifth proven case, **10621** (functional-datatype unsat Konclude misses), is
documented in `docs/CONTESTED-GOLD.md` from its minimal told-axiom derivation;
its core was produced on IBEX (job 47787383) and is not yet copied here.

Reproduce a verdict:
```
HermiT:   java -cp .:hermit_cp/* Oracle ore_ont_8941.min.owl     # -> inconsistent
Konclude: Konclude classification -i ore_ont_8941.min.owl -o /tmp/o  # -> Thing≡Nothing
```

**Operating rule:** any SWRL/`DLSafeRule` or functional-datatype ontology →
adjudicate with HermiT, not Konclude. See the full record in
`docs/CONTESTED-GOLD.md`.

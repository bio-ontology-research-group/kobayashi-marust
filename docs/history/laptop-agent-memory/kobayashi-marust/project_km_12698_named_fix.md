---
name: project-km-12698-named-fix
description: "2026-07-05 fixed 12698 incompleteness — HT/tableau race arms passed empty named set to cb_to_ht::convert, colon-heuristic dropped declared classes"
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-05, commit 03cdb8b (payg-strategy). 12698 was DIFF vs gold (84 missing
subs, 0 unsound). ROOT CAUSE: `spawn_ht`/`spawn_tableau` in
orchestrate/race.rs called `cb_to_ht::convert` with an EMPTY `named` HashSet.
cb_to_ht's query filter is `(n in named) || !is_internal(n)`; is_internal
treats any localname containing ':' as generated. So declared classes whose
IRI localname has a colon — e.g. `<...ebi.ac.uk/chebi/searchId.do?chebiId=
CHEBI:37577>` (localname `searchId.do?chebiId=CHEBI:37577`) — were dropped
from the query set and never appeared as subsumers. The Python reference
(cb_to_ht.py convert) documents `named` exists exactly to prevent this; the
in-process Rust arms just never supplied it.

FIX: thread `meta.named` (from FrontendMeta) through cb_stack ->
race_cb_vs_tableau / race_cb_vs_ht -> spawn_tableau / spawn_ht; also added a
`named` field to the standalone `km cb_to_ht` CbInput. Monotone-safe (only
rescues genuinely-declared classes; cannot add unsound subs).

RESULT: 12698 84->18 missing. The residual 18 are a GOLD localname-collision
artifact: two distinct IRIs `purl.org/obo/owl/NCBITaxon#NCBITaxon_10239`
(no super axioms) and `obo/NCBITaxon_10239` (⊑ OBI_0100026 ⊑ MaterialEntity
⊑ EFO_0000001) canonicalise to one localname; CCONT_0000179..184 ⊑ the
owl-frag one, which entails nothing further. So KM is SOUND AND COMPLETE on
12698; gold is wrong (ore_canon collision family, see project_km_contested_gold).
Validated on ws: 10908/15672 SHOQ recoveries stay gold-exact, 10702 unchanged.
Deployed for the corpus regression sweep (IBEX build 48057549, panel 48057552).
Also observed: 12698 t16 peak 45GB vs t1 6GB same wall — memory-tail evidence.

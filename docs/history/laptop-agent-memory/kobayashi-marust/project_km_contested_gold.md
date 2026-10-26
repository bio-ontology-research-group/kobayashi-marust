---
name: project_km_contested_gold
description: Which reasoner to trust as gold where Konclude and HermiT disagree on ORE-2015 (HermiT was right on all 4 proven cases)
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

On every ORE-2015 ontology proven so far where the recorded Konclude gold
disagreed with HermiT, the **correct verdict is INCONSISTENT = HermiT's verdict**.
KM was right; Konclude's *gold* was wrong. Proven 2026-06-11 via `ddmin` minimal
inconsistent cores (oracle = HermiT-inconsistent) run through BOTH HermiT and
Konclude. Durable record + proof: `docs/CONTESTED-GOLD.md`. Also in CHANGELOG.md
~986-1019 and [[project_km_unsound_diagnosis]].

The proven onts and why Konclude's gold was wrong:
- **8941, 13912**: ontology IS inconsistent; Konclude *reasons* correctly (emits
  `EquivalentClasses(Thing Nothing ...)`) but the HARNESS `ore_canon.py`
  mis-canonicalised that as "consistent + N unsat". Fixed (Thing-in-Nothing-SCC →
  empty inconsistent sig).
- **15516, 2669**: SWRL `DLSafeRule` onts. **Konclude cannot parse them** (exits 0
  empty → recorded bogus "consistent"). HermiT parses; core is inconsistent.
- **10621 (PROVEN 2026-06-25)**: FMAInOWL anatomy ont with FUNCTIONAL boolean
  datatype properties. Konclude gold = consistent, EMPTY `#UNSAT` block (0 unsat) =
  WRONG. Genuinely has many UNSATISFIABLE named concepts via the told chain
  `Zone_of_cell ⊑ Fiat_cell_part ⊑ Fiat_anatomical_structure ⊑ Anatomical_structure
  ⊑ Material_physical_anatomical_entity ⊑ DataHasValue(has_mass,true)` PLUS
  `Zone_of_cell ⊑ DataHasValue(has_mass,false)` PLUS `FunctionalDataProperty(has_mass)`
  ⇒ `Zone_of_cell ⊑ ⊥`. PROOF (minimal extracted ont, IBEX job 47787383):
  **HermiT 1.4.6 → "Classes equivalent to owl:Nothing: Zone_of_cell"**; KM CB engine
  → `unsatisfiable:[Zone_of_cell]`; Konclude/gold → 0 unsat. **ELK can't see it
  (EL profile drops functional datatypes)** — so ELK "consistent" does NOT validate
  the gold here. KM (CB and fast Ht) is SOUND on 10621; its "spurious unsat" is
  GENUINE. The 10621 Ht/CB timeout is correct-but-expensive unsat work, NOT a bug.
  So there is NO Konclude method to port for 10621 — Konclude is the one that's wrong.

**Operating rule (which gold to use):**
- Default oracle = Konclude WITH the ore_canon fix.
- Any SWRL / `DLSafeRule` ontology → use HermiT; Konclude is invalid there.
- HermiT "inconsistent" beats a Konclude "consistent" that comes from a
  `Thing≡Nothing` encoding or empty/parse-failure output.

**Host caveat:** gold copies are per-host and not all regenerated together.
Verified 2026-06-17 on IBEX `/ibex/scratch/hohndor/km/gold/`: 8941/13912 first
line `0` (corrected), but **15516/2669 still `1` (stale)** — exclude them from
Konclude comparison on IBEX (Konclude has no valid sig for SWRL).

**Scope:** 5 are now PROVEN (8941, 13912, 15516, 2669, 10621). CLAUDE.md notes
~12 HermiT/Konclude disagreements total; the rest are NOT adjudicated — don't
assume HermiT is right on those without the same ddmin-core / minimal-ont proof.
NB **functional-datatype unsatisfiability is a Konclude-gold blind spot** (10621):
suspect any FMAInOWL / datatype ont where KM finds unsats but Konclude+ELK say
consistent — re-adjudicate with HermiT, do not treat KM as unsound.

TODO: copy the 4 `.min.owl` cores from `ws:~/minimize/` into
`results/contested-cores/` so the proof is self-contained (ws currently down).

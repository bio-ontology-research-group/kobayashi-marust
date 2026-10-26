---
name: project_km_el_certificate
description: "EL completeness certificate in elc: saturate the EL subset, then check residual non-EL clauses against the canonical model (sound + complete EL routing for near-EL ontologies)"
metadata:
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-11, branch payg-strategy. New lever for the ELK-MATCH timeout/memout
onts (ELK byte-matches the Konclude gold on 12 of KM's 28 non-ok onts:
11311 11745 15803 1603 16444 4205 6212 6682 7127 7246 7581 8737). ELK gets them
by being a complete EL reasoner and DROPPING the non-EL axioms; the drop is
answer-preserving when those axioms add no named subsumption.

**Implemented (elcomplete.rs): canonical-model completeness certificate.**
Instead of `to_nf` returning None on the first non-EL clause, it now collects
non-EL clauses into a RESIDUAL list and still saturates the EL subset. The
saturated structure IS the canonical model I (domain = satisfiable concept
nodes x_C; x_C in D^I iff C<=D derived; (x_C,x_D) in R^I iff edge (C,R,D)
derived). Each completion rule is the closure condition of one normal form, so
I satisfies every EL clause at fixpoint. `check_certificate` then evaluates
every residual clause (compiled to interned atoms + per-clause var indices) as
a first-order constraint over I via a bound-first backtracking join. If ALL
residuals hold, I |= O (full ontology), so for any O |= A<=B we have x_A in A^I
(Init) => x_A in B^I (I|=O) => A<=B already derived (membership IS derivedness).
=> the EL answer is exact (sound AND complete) for sat, unsat, and consistency.
Any residual that fails (or work budget 2e8 exhausted) => classify returns None
=> CB-engine fallback, exactly as before. NEVER an approximation.

Env: `KM_ELC_CERT=0` disables (old behaviour); `KM_ELC_DEBUG=1` prints residual
count + verdict. 7 unit tests (cert_passes_when_disjunction_already_decided,
cert_fails_on_live_disjunction, range/cardinality-eq/empty-head-constraint
checks, nominal bail, pure_el_unchanged).

**Residual scoping (job 5653) confirms the shape is favourable:** 4205 has
746785 EL / 10 residual (all 2-disjunctions on x); 6212 887717/3; 15803
904747/16; 7127/7581 ~13 (range+domain+inverse-bridge+1 cardinality); 1603
1875/949 (526 range, 198 inverse-bridge, 174 domain, 35 disj, 16 eq -- the hard
one). The disjunction-only residuals (4205/6212/15803) are the strongest
candidates: tiny residual over a giant EL closure elc does in seconds.

**CAVEAT -- inverse bridges:** a residual `R(x,y)->S(y,x)` checks against I,
which has only FORWARD edges; it fails unless S(y,x) was derived another way.
So onts whose inverse role is NOT inert fail the certificate (correctly: the EL
answer would be incomplete) and fall back to CB. The inert case is already
handled upstream by the Skolem-exclusion routing relaxation ([[project_km_giant_routing]]),
which prunes inert bridges before elc. So the certificate's inverse-bridge
failures are sound, not a missed win.

ALSO landed in elc.rs: read stdin as bytes + `serde_json::from_slice` (skips
whole-buffer UTF-8 validation) -- 8737's elc was 248s, JUST over the 240s
timeout; shaving parse time targets it. 8737 elc profile: ofn 23.6s/3.6GB,
elc 248s CPU/9GB, 1.18GB output. 16744 elc 93s.

**RESULT (validated, landed `cb508c6`, default OFF): the certificate gains 0
passrate on ORE.** Job 5656 debug: it FAILS at residual clause 0 on every
candidate (4205 6212 7127 7246 11311), budget barely touched -- the residuals
are live covering disjunctions / non-inert inverse bridges / multi-successor
functionality, which the canonical EL model genuinely violates. Job 5654 (full
pipeline) confirmed all 12 still timeout/memout, identical to baseline. ALSO:
7127/7246/11311 have el_rbox_safe=False so never reach elc anyway. And attempting
the cert on 4205/6212 (which DO reach elc) would saturate their 746k-887k clause
EL closure (~40-60s) before failing -> steals CB-fallback time. Hence DEFAULT
OFF: with the flag off, routing is byte-identical to the prior binary (non-empty
residual -> classify None -> exit-3 fallback). Kept as a sound, tested, opt-in
capability for FUTURE near-EL ontologies whose non-EL part is model-satisfiable;
inert on this corpus.

Pure-legacy (job 5655) ALSO times out on ALL 7 ELK-DIFF disjunction onts (10702
9540 1603 10860 5303 10621 9663) -- so neither the certificate NOR strategy
routing rescues the genuine-disjunction class; it needs real CB ordered-
resolution work (the Sequoia ordering rewrite, see
[[project_km_disjunction_blowup]] / task #10). Lean re-cert of the canonical-
model lemma deferred by explicit user decision.

8737 timing (KM_ELC_TIMING): saturation-bound, classify=252s of a 263s elc run
(read 0.5s parse 8s serialise 2.8s). Pipeline ofn 24s + elc 263s = 287s >> 240s.
The from_slice I/O change is harmless but does NOT help (parse was only 8s). 8737
needs a parallel ELK-style EL completion (task #9), not an I/O fix.

Related: [[project_km_giant_routing]], [[project_km_disjunction_blowup]], [[project_km_rust_elc]].

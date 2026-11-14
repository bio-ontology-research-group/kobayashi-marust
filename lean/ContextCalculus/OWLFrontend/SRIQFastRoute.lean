import ContextCalculus.OWLFrontend.SRIQReference
import ContextCalculus.SRIQ.FastCheck
import ContextCalculus.SRIQ.FastElimAProof
import ContextCalculus.SRIQ.ElimMarkers

/-!
# The checked fast SHIQ route (stage C1c)

`owlSHIQFast gen` is `owlSHIQReference` with the star elimination replaced
by the certificate check: after `translateSRIQ`, `isSHIQFastB` (equal to
`isSHIQB`), `encTransQ` and the elimination of body markers
(`SRIQ/ElimMarkers.lean`, subsumptions between the requested names are
unchanged), the generator `gen` proposes an array candidate set,
`closedFastB` (`SRIQ/FastCheckA.lean`) checks it, and the route answers
from its live nodes (`SRIQ/FastElimA.lean`) only when the check passes;
otherwise it declines (`none`). `owlSHIQFast_sound` holds for every
generator.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy
open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

/-! ## A fast simple-role check

`isSHIQB` computes the super-roles of each transitive role with `2 m + 1`
rounds of `upStep` (seconds on inputs with hundreds of roles).
`isSHIQFastB` takes them from the breadth-first search of `mkIx` (`upS`)
and checks that the result is closed under the one-step super-roles; a
closed set that contains the role holds every super-role, and `upS`
holds super-roles only, so the answer is the same (`isSHIQFastB_eq`).
When the closure check fails, it falls back to `roleUp`. -/

/-- The simple-role condition for one transitive role `T`. -/
def simpleT {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) (ix : SRIQ.Fast.Ix n m)
    (T : RoleT (Fin m)) : Bool :=
  let U := SRIQ.Fast.upS ix T
  if SRIQ.Fast.upClosedB ix U then
    (countRoles O).all fun R => !(decide (R ∈ U)) && !(decide (R.flip ∈ U))
  else
    let up := SRI.Proc.roleUp (sriPart O) T
    (countRoles O).all fun R => !(up.contains R) && !(up.contains R.flip)

/-- `isSHIQB` with the super-roles from `mkIx`. -/
def isSHIQFastB {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : Bool :=
  O.all chainOKQ && (let ix := SRIQ.Fast.mkIx O; (transRoles O).all (simpleT O ix))

theorem simpleT_eq {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) (T : RoleT (Fin m)) :
    simpleT O (SRIQ.Fast.mkIx O) T =
      (let up := SRI.Proc.roleUp (sriPart O) T
       (countRoles O).all fun R => !(up.contains R) && !(up.contains R.flip)) := by
  unfold simpleT
  dsimp only
  split
  · next hc =>
    have hU : ∀ R, R ∈ SRIQ.Fast.upS (SRIQ.Fast.mkIx O) T ↔ (SRI.Proc.roleUp (sriPart O) T).contains R = true := by
      intro R
      rw [List.contains_iff_mem, SRI.Proc.mem_roleUp]
      constructor
      · exact SRIQ.Fast.upS_sound
      · intro h
        exact SRIQ.Fast.upClosedB_sound hc T (SRIQ.Fast.upS_self T) R h
    congr 1
    funext R
    rw [SRIQ.Fast.decide_eq_of_iff (hU R), SRIQ.Fast.decide_eq_of_iff (hU R.flip)]
  · rfl

theorem isSHIQFastB_eq {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : isSHIQFastB O = isSHIQB O := by
  unfold isSHIQFastB isSHIQB simpleB
  dsimp only
  congr 1
  congr 1
  funext T
  exact simpleT_eq O T

/-- Rows that are exact one by one, in request order, give exact bits. -/
theorem sriq_bit_rows (T : SRIQTranslation) {k : Nat}
    {O' : SRIQ.Ontology (Fin (T.conceptCount + k)) (Fin T.roleCount)}
    {cls : List (Fin (T.conceptCount + k) × Option (List (Fin (T.conceptCount + k))))}
    (hrow : ∀ i (hi : i < (sriqRequest T k).length), ∃ p, cls[i]? = some p ∧
      p.1 = (sriqRequest T k)[i] ∧
      (p.2 = none → ∀ (D : Type) [Nonempty D] (I : Interp D (Fin (T.conceptCount + k)) (Fin T.roleCount)),
        models I O' → ∀ x, ¬ I.c p.1 x) ∧
      ∀ L, p.2 = some L → ∀ b, b ∈ L ↔ SRIQ.EntailsSub O' p.1 b)
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWLAnswer.bit { named := T.named, rows := sriqRows T cls } i j = true ↔
      SRIQ.EntailsSub O' (Fin.castAdd k ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩)
        (Fin.castAdd k ⟨j, Nat.lt_of_lt_of_le hj T.hnamed⟩) := by
  have hlen : (sriqRequest T k).length = T.named.length := by simp [sriqRequest]
  obtain ⟨p, hp, hp1, hnone, hsome⟩ := hrow i (hlen ▸ hi)
  have hiC : i < T.conceptCount := Nat.lt_of_lt_of_le hi T.hnamed
  have hjC : j < T.conceptCount := Nat.lt_of_lt_of_le hj T.hnamed
  have hp1' : p.1 = Fin.castAdd k ⟨i, hiC⟩ := by
    rw [hp1]; simp [sriqRequest]
  have hrowi : OWLAnswer.bit { named := T.named, rows := sriqRows T cls } i j =
      (sriRowN T.named.length p).bit j := by
    simp only [OWLAnswer.bit, sriqRows, sriRowsN, List.getElem?_map, hp, Option.map_some]
  rw [hrowi, ← hp1']
  cases hga : p.2 with
  | none =>
    simp only [sriRowN, hga, SparseRow.bit, Bool.true_or, true_iff]
    intro D _ I hI x hx
    exact absurd hx (hnone hga D I hI x)
  | some L =>
    simp only [sriRowN, hga, SparseRow.bit, Bool.false_or, List.contains_iff_mem, List.mem_filter,
      List.mem_map, decide_eq_true_eq]
    rw [← hsome L hga]
    constructor
    · rintro ⟨⟨b, hb, hbj⟩, -⟩
      have : Fin.castAdd k ⟨j, hjC⟩ = b := Fin.ext (by simp [hbj])
      rw [this]; exact hb
    · intro h
      exact ⟨⟨_, h, rfl⟩, by simpa using hj⟩

/-- The checked fast SHIQ route with the candidate generator `gen`. -/
def owlSHIQFast
    (gen : ∀ {N M : Nat}, SRIQ.Ontology (Fin N) (Fin M) → List (Fin N) → SRIQ.Fast.CandA)
    (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match translateSRIQ O requested with
  | none => none
  | some T =>
      if isSHIQFastB T.ontology then
        let E := SRIQ.Proc.encTransQ T.ontology
        let E2 := SRIQ.Elim.elimChecked E.2 T.named.length
        match SRIQ.Fast.fastClassifyA E2 (sriqRequest T E.1) (gen E2 (sriqRequest T E.1)) with
        | some cls => some { named := T.named, rows := sriqRows T cls }
        | none => none
      else none

/-- **Every answer of the checked route is exact** under the OWL 2 direct
semantics, for every requested pair and every generator. -/
theorem owlSHIQFast_sound
    (gen : ∀ {N M : Nat}, SRIQ.Ontology (Fin N) (Fin M) → List (Fin N) → SRIQ.Fast.CandA)
    {O : OWL.Ontology} {requested : List OWL.IRI} {a : OWLAnswer}
    (h : owlSHIQFast gen O requested = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlSHIQFast at h
  split at h
  · exact absurd h (by simp)
  next T hT =>
    split at h
    · next hS =>
      dsimp only at h
      split at h
      · next cls hcls =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨translateSRIQ_named hT, ?_⟩
        intro i j hi hj
        rw [translateSRIQ_correct hT i j hi hj,
          SRIQ.Proc.encTransQ_correct (isSHIQ_of_isSHIQB ((isSHIQFastB_eq _) ▸ hS)),
          ← SRIQ.Elim.entailsSub_elimChecked (bound := T.named.length) (by simpa using hi)
            (by simpa using hj)]
        refine sriq_bit_rows T (fun i' hi' => ?_) i j hi hj
        obtain ⟨p, hp, hp1⟩ := SRIQ.Fast.fastClassifyA_get hcls hi'
        obtain ⟨-, hall⟩ := SRIQ.Fast.fastClassifyA_spec
          (SRIQ.Elim.isALCHIQ_elimChecked (SRIQ.Proc.encTransQ_isALCHIQ T.ontology)) hcls
        obtain ⟨-, hn, hs⟩ := hall p (List.mem_of_getElem? hp)
        exact ⟨p, hp, hp1, hn.1, hs⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.isSHIQFastB_eq
#print axioms ContextCalculus.OWLFrontend.sriq_bit_rows
#print axioms ContextCalculus.OWLFrontend.owlSHIQFast_sound

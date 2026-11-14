import ContextCalculus.OWLFrontend.SRIQReference
import ContextCalculus.SRIQ.FastCheck

/-!
# The checked fast SHIQ route (stage C1c)

`owlSHIQFast gen` is `owlSHIQReference` with the star elimination replaced
by the certificate check of `SRIQ/FastCheck.lean`: after `translateSRIQ`,
`isSHIQB` and `encTransQ`, the generator `gen` proposes a candidate set,
`closedB` checks it, and the route answers from its live nodes only when
the check passes; otherwise it declines (`none`). `owlSHIQFast_sound`
holds for every generator.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy
open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

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
    (gen : ∀ {N M : Nat}, SRIQ.Ontology (Fin N) (Fin M) → List (Fin N) → SRIQ.Fast.Cand N M)
    (O : OWL.Ontology) (requested : List OWL.IRI) : Option OWLAnswer :=
  match translateSRIQ O requested with
  | none => none
  | some T =>
      if isSHIQB T.ontology then
        let E := SRIQ.Proc.encTransQ T.ontology
        match SRIQ.Fast.fastClassify E.2 (sriqRequest T E.1) (gen E.2 (sriqRequest T E.1)) with
        | some cls => some { named := T.named, rows := sriqRows T cls }
        | none => none
      else none

/-- **Every answer of the checked route is exact** under the OWL 2 direct
semantics, for every requested pair and every generator. -/
theorem owlSHIQFast_sound
    (gen : ∀ {N M : Nat}, SRIQ.Ontology (Fin N) (Fin M) → List (Fin N) → SRIQ.Fast.Cand N M)
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
          SRIQ.Proc.encTransQ_correct (isSHIQ_of_isSHIQB hS)]
        refine sriq_bit_rows T (fun i' hi' => ?_) i j hi hj
        obtain ⟨p, hp, hp1⟩ := SRIQ.Fast.fastClassify_get hcls hi'
        obtain ⟨-, hall⟩ := SRIQ.Fast.fastClassify_spec (SRIQ.Proc.encTransQ_isALCHIQ T.ontology) hcls
        obtain ⟨-, hn, hs⟩ := hall p (List.mem_of_getElem? hp)
        exact ⟨p, hp, hp1, hn.1, hs⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.sriq_bit_rows
#print axioms ContextCalculus.OWLFrontend.owlSHIQFast_sound

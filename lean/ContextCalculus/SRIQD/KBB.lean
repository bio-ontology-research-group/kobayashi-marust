import ContextCalculus.SRIQD.OracleB
import ContextCalculus.SRIQD.KBTransitivity

/-!
# Knowledge bases under bounded oracles (stage C4)

`consistentKBD_iffB`: the consistency procedure of `SRIQD/ABoxProcedure.lean`
is exact for every hint under a bounded oracle `OracleSpecB Θ card B` with
`dbnd (encO O A) ≤ B`. The data stars of the reduced types are taken short
(`dataSat_cap_iff`), so the demands stay below `B`.
`consistentKBDS_iffB` adds transitivity removal.
-/

namespace ContextCalculus.SRIQD

set_option linter.unusedSectionVars false

variable {DAtom : Type} [Fintype DAtom] [DecidableEq DAtom]

/-- The lower half of `OracleSpec` for the capped oracle. -/
theorem OracleSpecB.lowCap {Θ : DataTheory DAtom} {card : Finset DAtom → Option Nat} {B : Nat}
    (hspec : OracleSpecB Θ card B) :
    ∀ need : Finset DAtom → Nat, (∀ τ k, capCard card B τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ := by
  intro need hneed
  refine hspec.lower need (fun τ => ?_) (fun τ k hk => ?_)
  · cases hc : card τ with
    | none => exact hneed τ B (by simp [capCard, hc])
    | some k => have := hneed τ (min k B) (by simp [capCard, hc]); omega
  · have := hneed τ (min k B) (by simp [capCard, hk]); omega

section Reduce

variable {CName Role DProp Ind : Type}
variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp]
variable {Θ : DataTheory DAtom} {card : Finset DAtom → Option Nat} {B : Nat}

/-- **Reduction under a bounded oracle.** -/
theorem consistentKB_reduceWithB (hspec : OracleSpecB Θ card B)
    {O : Ontology CName Role DProp DAtom} (hB : dbnd O ≤ B)
    {toL : Finset CName → List CName} (htoL : ∀ t a, a ∈ toL t ↔ a ∈ t)
    {bad : List (Finset CName)} (hbad : ∀ t, t ∈ bad ↔ ¬ DataSat O card t)
    (A : SRIQ.ABox CName Role Ind) :
    SRIQ.ConsistentKB (reduceWith O toL bad) A ↔ ConsistentKB Θ O (A.map Assertion.obj) := by
  constructor
  · rintro ⟨D, hD, I, ind, hI, hA⟩
    obtain ⟨hIo, hds⟩ := (models_reduceWith_iff htoL hbad).1 hI
    obtain ⟨V, atom, hΘ, d, hm⟩ := exists_dmodel_types (card := capCard card B) hspec.lowCap
      I hIo (SRIQ.typeOf I) (fun a x => (SRIQ.mem_typeOf I).symm)
      (fun x => (dataSat_cap_iff hB _).2 (hds x))
    exact ⟨D, V, hD, atom, hΘ, _, ind, hm, satABox_map_obj.2 hA⟩
  · rintro ⟨D, V, hD, atom, hΘ, I, ind, hI, hA⟩
    refine ⟨D, hD, I.toInterp, ind, (models_reduceWith_iff htoL hbad).2
      ⟨(models_iff.1 hI).1, dataSat_of_model hspec.upper hΘ hI⟩, satABox_map_obj.1 hA⟩

end Reduce

namespace Proc

variable {n m p q k : Nat} {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat} {B : Nat}

/-- **Consistency with a bounded oracle**, for every hint. -/
theorem consistentKBD_iffB (hspec : OracleSpecB Θ card B)
    {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} (hA : IsALCHIQ O)
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)) (hB : dbnd (encO O A) ≤ B)
    (hint : Option (SRIQ.Proc.Hint (n + k) m k)) :
    consistentKBD O card A hint = true ↔ ConsistentKB Θ O A := by
  rw [consistentKBD, reduceQ,
    SRIQ.Proc.consistentKB_iff (isALCHIQ_reduceWith (isALCHIQ_encO hA A) _ _),
    consistentKB_reduceWithB hspec hB (mem_toLFin) mem_badQ, ← consistentKB_enc]

/-- Consistency of a SHIQ(D) knowledge base with a bounded oracle. -/
theorem consistentKBDS_iffB (hspec : OracleSpecB Θ card B)
    {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)} (h : IsSHIQDKB O A)
    (hB : dbnd (encO (encTransQD O).2 (encABoxD O A)) ≤ B)
    (hint : Option (SRIQ.Proc.Hint (n + (encTransQD O).1 + k) m k)) :
    consistentKBDS O card A hint = true ↔ ConsistentKB Θ O A := by
  rw [consistentKBDS, consistentKBD_iffB hspec (encTransQD_isALCHIQ O) _ hB,
    ← consistentKB_encTransQD h]

end Proc

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.Proc.consistentKBD_iffB
#print axioms ContextCalculus.SRIQD.Proc.consistentKBDS_iffB

import ContextCalculus.SRIQD.Procedure

/-!
# Bounded oracles (stage C4)

`OracleSpecB Θ card B` weakens the lower half of `OracleSpec`: values need
only be supplied for demands of at most `B` per value type. Data stars can
be pruned to at most `dbnd O` entries (`dsupport_bound`), so for
`dbnd O ≤ B` a bounded oracle decides the same data stars as a full one
would, and `entailsQD` is exact (`entailsQD_iffB`).

The bounded form is what the OWL 2 map with datatypes outside the map
needs: a large finite value type can then be shared among readings of the
free datatypes (`SRIQD/CellParts.lean`).
-/

namespace ContextCalculus.SRIQD

set_option linter.unusedSectionVars false

open ContextCalculus.SRI (RoleT Interp)

variable {DAtom : Type} [Fintype DAtom] [DecidableEq DAtom]

/-- The oracle specification with demands bounded by `B`. -/
structure OracleSpecB (Θ : DataTheory DAtom) (card : Finset DAtom → Option Nat) (B : Nat) :
    Prop where
  upper : ∀ (V : Type) (atom : DAtom → V → Prop), Θ V atom → ∀ τ k, card τ = some k →
    ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) → l.length ≤ k
  lower : ∀ need : Finset DAtom → Nat, (∀ τ, need τ ≤ B) →
    (∀ τ k, card τ = some k → need τ ≤ k) →
    ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
      ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ

/-- A full oracle is a bounded one. -/
theorem OracleSpec.toB {Θ : DataTheory DAtom} {card : Finset DAtom → Option Nat}
    (h : OracleSpec Θ card) (B : Nat) : OracleSpecB Θ card B :=
  ⟨h.upper, fun need _ hk => h.lower need hk⟩

/-- `card` capped at `B`. -/
def capCard (card : Finset DAtom → Option Nat) (B : Nat) (τ : Finset DAtom) : Option Nat :=
  match card τ with
  | some k => some (min k B)
  | none => some B

section Cap

set_option linter.unusedSectionVars false

variable {CName Role DProp : Type} [DecidableEq CName] [DecidableEq Role] [DecidableEq DProp]
  {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat} {B : Nat}

theorem tcnt_le_length (Dn : List (DNbr DProp DAtom)) (τ : Finset DAtom) :
    tcnt Dn τ ≤ Dn.length := List.countP_le_length

theorem dok_of_cap {t : Finset CName} {Dn : List (DNbr DProp DAtom)}
    (h : DOK O (capCard card B) t Dn) : DOK O card t Dn := by
  refine ⟨h.up, fun τ k hk => ?_, h.all, h.ex, h.atLeast, h.atMost⟩
  have := h.card τ (min k B) (by simp [capCard, hk])
  omega

theorem dok_cap_of_short {t : Finset CName} {Dn : List (DNbr DProp DAtom)}
    (h : DOK O card t Dn) (hl : Dn.length ≤ B) : DOK O (capCard card B) t Dn := by
  refine ⟨h.up, fun τ k hk => ?_, h.all, h.ex, h.atLeast, h.atMost⟩
  have h1 := tcnt_le_length Dn τ
  unfold capCard at hk
  cases hc : card τ with
  | none => rw [hc] at hk; cases hk; omega
  | some k' =>
    rw [hc] at hk
    cases hk
    have := h.card τ k' hc
    omega

theorem dataSat_cap_iff (hB : dbnd O ≤ B) (t : Finset CName) :
    DataSat O (capCard card B) t ↔ DataSat O card t := by
  constructor
  · rintro ⟨Dn, h⟩
    exact ⟨Dn, dok_of_cap h⟩
  · rintro ⟨Dn, h⟩
    obtain ⟨Dn', -, hl, -, h'⟩ := dsupport_bound h
    exact ⟨Dn', dok_cap_of_short h' (hl.trans hB)⟩

end Cap

section Char

set_option linter.unusedSectionVars false

variable {CName Role DProp : Type}
variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp]
variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
  {Θ : DataTheory DAtom} {B : Nat}

theorem dgood_cap_iff (hB : dbnd O ≤ B) (ρ : SRIQ.Rec CName Role) :
    DGood O (capCard card B) ρ ↔ DGood O card ρ := by
  constructor
  · rintro ⟨G, hρ, hG⟩
    obtain ⟨h1, h2⟩ := dselfSupp_iff.1 hG
    exact ⟨G, hρ, dselfSupp_iff.2 ⟨h1, fun σ hσ => (dataSat_cap_iff hB _).1 (h2 σ hσ)⟩⟩
  · rintro ⟨G, hρ, hG⟩
    obtain ⟨h1, h2⟩ := dselfSupp_iff.1 hG
    exact ⟨G, hρ, dselfSupp_iff.2 ⟨h1, fun σ hσ => (dataSat_cap_iff hB _).2 (h2 σ hσ)⟩⟩

/-- **Characterisation with a bounded oracle.** -/
theorem entailsSub_iff_dstarB (hspec : OracleSpecB Θ card B) (hB : dbnd O ≤ B)
    (hA : IsALCHIQ O) (a b : CName) :
    EntailsSub Θ O a b ↔ ∀ t, DGood O card (t, none) → a ∈ t → b ∈ t := by
  have hlow : ∀ need : Finset DAtom → Nat, (∀ τ k, capCard card B τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ := by
    intro need hneed
    refine hspec.lower need (fun τ => ?_) (fun τ k hk => ?_)
    · cases hc : card τ with
      | none => exact hneed τ B (by simp [capCard, hc])
      | some k => have := hneed τ (min k B) (by simp [capCard, hc]); omega
    · have := hneed τ (min k B) (by simp [capCard, hk]); omega
  constructor
  · intro hent t hg hat
    obtain ⟨D, V, hD, atom, hΘ, I, x, hm, hx⟩ :=
      model_of_dgood hlow hA ((dgood_cap_iff hB _).2 hg)
    exact (hx b).1 (hent D V atom hΘ I hm x ((hx a).2 hat))
  · intro hgood D V _ atom hΘ I hI x hax
    exact (SRIQ.mem_typeOf I.toInterp).1 (hgood _ (dgood_of_model hspec.upper hΘ hI x)
      ((SRIQ.mem_typeOf I.toInterp).2 hax))

end Char

namespace Proc

variable {n m p q : Nat} {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
  {card : Finset (Fin q) → Option Nat} {Θ : DataTheory (Fin q)} {B : Nat}

/-- **Exactness of `entailsQD` with a bounded oracle.** -/
theorem entailsQD_iffB (hspec : OracleSpecB Θ card B) (hB : dbnd O ≤ B) (hA : IsALCHIQ O)
    (a b : Fin n) : entailsQD O card a b = true ↔ EntailsSub Θ O a b := by
  rw [entailsSub_iff_dstarB hspec hB hA, entailsQD, decide_eq_true_iff]
  constructor
  · intro h t ht hat
    exact h _ ((good_iff_mem_aliveD _).1 ht) rfl hat
  · intro h ρ hρ hn hat
    obtain ⟨t, par⟩ := ρ
    simp only at hn hat ⊢
    subst hn
    exact h t ((good_iff_mem_aliveD _).2 hρ) hat

end Proc

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.entailsSub_iff_dstarB
#print axioms ContextCalculus.SRIQD.Proc.entailsQD_iffB

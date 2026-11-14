import ContextCalculus.OWL.Datatypes.Oracle

/-!
# Free datatypes and finite value types have no oracle (v1.7.0 stage C4)

The design note (section 3) assumes that the OWL 2 map induces a data
theory with an oracle. With a datatype outside the map that is not true:
for the atoms `F` (a free datatype) and `{"a"}` (a literal), the value types
`{F, {"a"}}` and `{{"a"}}` each have one value in some admissible pair, so
`OracleSpec.upper` forces `card ≥ 1` for both, and `OracleSpec.lower` then
asks for one pair with two distinct values in `{"a"}`
(`no_oracle_free_literal`). This is why `owlCheck` declines a free datatype
together with a finite value type (`freeCheck`). The smallest repair is to
split the theory by the reading of the free datatypes on the finite value
types (finitely many choices up to the bound of the data stars): each part
has an oracle, and entailment is the conjunction over the parts.
-/

namespace ContextCalculus.OWL.Datatypes

open ContextCalculus.SRIQD

/-- The atoms: a free datatype and the literal `"a"^^xsd:string`. -/
def obstacleSpec : Fin 2 → DataRange :=
  ![.datatype "urn:km:free-datatype", .oneOf [⟨"a", Parse.xsdNs ++ "string", none⟩]]

theorem kindOf_free : kindOf "urn:km:free-datatype" = none := by decide +kernel

theorem litVal_a : litVal ⟨"a", Parse.xsdNs ++ "string", none⟩ = some (.str "a" none) := by
  decide +kernel

/-- The value of the literal. -/
noncomputable def aVal : Val := toVal (.str "a" none)

theorem atom_obstacle (pat : String → String → Prop) (dtype : IRI → Val → Prop) (v : Val) :
    ((obstacleSpec 0).ext (owl2MapP pat) dtype v ↔ dtype "urn:km:free-datatype" v) ∧
      ((obstacleSpec 1).ext (owl2MapP pat) dtype v ↔ v = aVal) := by
  constructor
  · show DataRange.ext (owl2MapP pat) dtype (.datatype "urn:km:free-datatype") v ↔ _
    rw [DataRange.ext, dtExt_none pat kindOf_free]
  · show DataRange.ext (owl2MapP pat) dtype (.oneOf [⟨"a", Parse.xsdNs ++ "string", none⟩]) v ↔ _
    rw [DataRange.ext]
    simp only [List.mem_singleton, exists_eq_left, owl2MapP_literal, litVal_a, Option.map_some,
      aVal]
    exact ⟨fun h => (Option.some_inj.1 h).symm, fun h => by rw [h]; rfl⟩

/-- **No oracle.** -/
theorem no_oracle_free_literal (pat : String → String → Prop) (card : Finset (Fin 2) → Option Nat) :
    ¬ OracleSpec (owlTheory pat obstacleSpec) card := by
  classical
  intro h
  -- the two readings of the free datatype
  let atomOf : (IRI → Val → Prop) → Fin 2 → Val → Prop := fun dtype p v =>
    (obstacleSpec p).ext (owl2MapP pat) dtype v
  have hΘ : ∀ dtype, owlTheory pat obstacleSpec Val (atomOf dtype) := fun dtype =>
    ⟨Equiv.refl _, dtype, fun _ _ => Iff.rfl⟩
  let d1 : IRI → Val → Prop := fun _ v => v = aVal
  let d0 : IRI → Val → Prop := fun _ _ => False
  have hvt1 : vt (atomOf d1) aVal = Finset.univ := by
    ext p; rw [mem_vt]
    fin_cases p
    · exact iff_of_true ((atom_obstacle pat d1 aVal).1.2 rfl) (Finset.mem_univ _)
    · exact iff_of_true ((atom_obstacle pat d1 aVal).2.2 rfl) (Finset.mem_univ _)
  have hvt0 : vt (atomOf d0) aVal = {1} := by
    ext p; rw [mem_vt]
    fin_cases p
    · constructor
      · intro hx; exact ((atom_obstacle pat d0 aVal).1.1 hx).elim
      · intro hx; simp at hx
    · exact iff_of_true ((atom_obstacle pat d0 aVal).2.2 rfl) (Finset.mem_singleton_self _)
  -- each value type has at least one value somewhere
  have hc1 : ∀ k, card Finset.univ = some k → 1 ≤ k := fun k hk =>
    h.upper Val (atomOf d1) (hΘ d1) _ k hk [aVal] (List.nodup_singleton _) (by simp [hvt1])
  have hc0 : ∀ k, card {1} = some k → 1 ≤ k := fun k hk =>
    h.upper Val (atomOf d0) (hΘ d0) _ k hk [aVal] (List.nodup_singleton _) (by simp [hvt0])
  let need : Finset (Fin 2) → Nat := fun τ => if τ = Finset.univ ∨ τ = {1} then 1 else 0
  obtain ⟨V, atom, ⟨e, dtype, hat⟩, hS⟩ := h.lower need (by
    intro τ k hk
    simp only [need]
    split_ifs with hτ
    · rcases hτ with rfl | rfl
      · exact hc1 k hk
      · exact hc0 k hk
    · exact Nat.zero_le _)
  obtain ⟨l1, -, hl1, hv1⟩ := hS Finset.univ
  obtain ⟨l0, -, hl0, hv0⟩ := hS {1}
  simp only [need, true_or, if_true] at hl1
  simp only [need, or_true, if_true] at hl0
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.1 hl1
  obtain ⟨w, rfl⟩ := List.length_eq_one_iff.1 hl0
  have hv := hv1 v List.mem_cons_self
  have hw := hv0 w List.mem_cons_self
  -- both satisfy the literal, so both are `aVal`
  have hva : e v = aVal := by
    have : (1 : Fin 2) ∈ vt atom v := by rw [hv]; exact Finset.mem_univ _
    rw [mem_vt, hat] at this
    exact (atom_obstacle pat dtype (e v)).2.1 this
  have hwa : e w = aVal := by
    have : (1 : Fin 2) ∈ vt atom w := by rw [hw]; exact Finset.mem_singleton_self _
    rw [mem_vt, hat] at this
    exact (atom_obstacle pat dtype (e w)).2.1 this
  have hvw : v = w := e.injective (hva.trans hwa.symm)
  subst hvw
  rw [hv] at hw
  have : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by rw [← hw]; exact Finset.mem_univ _
  simp at this

end ContextCalculus.OWL.Datatypes

#print axioms ContextCalculus.OWL.Datatypes.no_oracle_free_literal

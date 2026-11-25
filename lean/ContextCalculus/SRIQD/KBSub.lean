import ContextCalculus.SRIQD.ABoxProcedure

/-!
# Subsumption under knowledge bases with data assertions (stage C4)

`EntailsSubKB Θ O A a b`: every model of the knowledge base `(O, A)` over
an admissible pair of `Θ` has `a ⊑ b`.

`entailsSubKB_iff`: under an oracle, a subsumption follows from a
knowledge base iff the knowledge base is inconsistent or the subsumption
follows from the TBox alone. The disjoint sum of `SRIQ/ABox.lean` does
not carry over directly: the two models may use different value types.
The proof keeps the object parts of both models, takes their disjoint
sum, and builds the data anew with one admissible pair from
`OracleSpec.lower` (`exists_dmodel`). The data star of an individual is
read off the model of the knowledge base, with the witnesses of its data
assertions; every other element gets some data star of its type.

`classifyKBD` gives the `classifyQD` rows for a consistent knowledge base
and every name otherwise (`classifyKBD_spec`).
-/

namespace ContextCalculus.SRIQD

open ContextCalculus.SRI (RoleT Interp)

variable {CName Role DProp DAtom Ind : Type}

/-- Every model of the knowledge base has `a ⊑ b`. -/
def EntailsSubKB (Θ : DataTheory DAtom) (O : Ontology CName Role DProp DAtom)
    (A : ABox CName Role DProp DAtom Ind) (a b : CName) : Prop :=
  ∀ (D V : Type) [Nonempty D] (atom : DAtom → V → Prop), Θ V atom →
    ∀ (I : DInterp D V CName Role DProp) (ind : Ind → D), models atom I O →
      satABox atom I ind A → ∀ x, I.c a x → I.c b x

section Sum

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
  {Θ : DataTheory DAtom}

theorem typeOf_sumI_inl {D1 D2 : Type} (I : Interp D1 CName Role) (J : Interp D2 CName Role)
    (y : D1) : SRIQ.typeOf (SRIQ.sumI I J) (.inl y) = SRIQ.typeOf I y := by
  ext a
  rw [SRIQ.mem_typeOf, SRIQ.mem_typeOf]
  rfl

theorem typeOf_sumI_inr {D1 D2 : Type} (I : Interp D1 CName Role) (J : Interp D2 CName Role)
    (y : D2) : SRIQ.typeOf (SRIQ.sumI I J) (.inr y) = SRIQ.typeOf J y := by
  ext a
  rw [SRIQ.mem_typeOf, SRIQ.mem_typeOf]
  rfl

/-- **The sum of two models with data.** A model of the knowledge base and
a model of the TBox, possibly over different admissible pairs, give one
model of the knowledge base over one admissible pair whose domain holds
both object parts. -/
theorem exists_sum_model [Finite Ind] (hspec : OracleSpec Θ card)
    {A : ABox CName Role DProp DAtom Ind}
    {D1 V1 : Type} {atom1 : DAtom → V1 → Prop} (hΘ1 : Θ V1 atom1)
    {I1 : DInterp D1 V1 CName Role DProp} {ind : Ind → D1} (hI1 : models atom1 I1 O)
    (hA1 : satABox atom1 I1 ind A)
    {D2 V2 : Type} {atom2 : DAtom → V2 → Prop} (hΘ2 : Θ V2 atom2)
    {I2 : DInterp D2 V2 CName Role DProp} (hI2 : models atom2 I2 O) :
    ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧ ∃ d : DProp → D1 ⊕ D2 → V → Prop,
      models atom { toInterp := SRIQ.sumI I1.toInterp I2.toInterp, d := d } O ∧
      satABox atom { toInterp := SRIQ.sumI I1.toInterp I2.toInterp, d := d } (Sum.inl ∘ ind) A := by
  classical
  letI : Fintype Ind := Fintype.ofFinite _
  let S := SRIQ.sumI I1.toInterp I2.toInterp
  have hS : SRIQ.models S (objPart O) :=
    SRIQ.models_sumI _ _ (models_iff.1 hI1).1 (models_iff.1 hI2).1
  let T := {t : Finset CName // DataSat O card t}
  letI : Fintype T := Fintype.ofFinite _
  let X := Ind ⊕ T
  let g : D1 ⊕ D2 → X := fun z => match z with
    | .inl y => if h : ∃ i, ind i = y then .inl h.choose
        else .inr ⟨SRIQ.typeOf I1.toInterp y, dataSat_of_model hspec.upper hΘ1 hI1 y⟩
    | .inr y => .inr ⟨SRIQ.typeOf I2.toInterp y, dataSat_of_model hspec.upper hΘ2 hI2 y⟩
  let ty : X → Finset CName := fun z => match z with
    | .inl i => SRIQ.typeOf I1.toInterp (ind i)
    | .inr t => t.1
  have hty : ∀ a z, S.c a z ↔ a ∈ ty (g z) := by
    intro a z
    cases z with
    | inl y =>
      by_cases h : ∃ i, ind i = y
      · simp only [g, dif_pos h, ty]
        rw [h.choose_spec, SRIQ.mem_typeOf]
        rfl
      · simp only [g, dif_neg h, ty]
        rw [SRIQ.mem_typeOf]
        rfl
    | inr y =>
      simp only [g, ty]
      rw [SRIQ.mem_typeOf]
      rfl
  let W : D1 → List (DNbr DProp DAtom) := fun y =>
    (dwit O atom1 (fun u => I1.d u y) ++ assertWit atom1 I1 ind A y).dedup.map
      (dentry atom1 fun u => I1.d u y)
  let f : X → List (DNbr DProp DAtom) := fun z => match z with
    | .inl i => W (ind i)
    | .inr t => t.2.choose
  have hok : ∀ z, DOK O card (ty z) (f z) := by
    intro z
    cases z with
    | inl i =>
      exact dok_of_local_dwit atom1 (hspec.upper V1 atom1 hΘ1)
        (fun cl hcl => (models_iff.1 hI1).2 cl hcl (ind i)) (fun a => SRIQ.mem_typeOf I1.toInterp) _
    | inr t => exact t.2.choose_spec
  obtain ⟨V, atom, hΘ, d, hm, hpos, hneg⟩ := exists_dmodel hspec.lower S hS g ty hty f hok
  have hfg : ∀ i, f (g (.inl (ind i))) = W (ind i) := by
    intro i
    have h : ∃ j, ind j = ind i := ⟨i, rfl⟩
    simp only [g, dif_pos h, f]
    rw [h.choose_spec]
  refine ⟨V, atom, hΘ, d, hm, fun as has => ?_⟩
  cases as with
  | obj as => exact SRIQ.satABox_sumI _ _ (satABox_objABox hA1) _ (mem_objABox.2 has)
  | dPos a u L =>
    obtain ⟨w, hw, hd, hL⟩ := assertWit_mem has (hA1 _ has)
    have he : dentry atom1 (fun u => I1.d u (ind a)) w ∈ f (g (.inl (ind a))) := by
      rw [hfg]
      exact List.mem_map_of_mem (List.mem_dedup.2 (List.mem_append_right _ hw))
    obtain ⟨v, hv, hdv⟩ := hpos (.inl (ind a)) _ he
    refine ⟨v, hdv u (mem_labD.2 hd), mem_vt.1 ?_⟩
    rw [hv]
    exact mem_vt.2 hL
  | dNeg a u L =>
    intro v hd hL
    obtain ⟨e, he, hu, hv⟩ := hneg (.inl (ind a)) u v hd
    rw [hfg] at he
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 he
    have hdw : I1.d u (ind a) w := (mem_labD (d := fun u => I1.d u (ind a))).1 hu
    have hLw : atom1 L w := by
      have : L ∈ vt atom v := mem_vt.2 hL
      rw [hv] at this
      exact mem_vt.1 this
    exact hA1 _ has w hdw hLw

/-- **The TBox answer does not change.** Under an oracle and for finitely
many individuals, a subsumption follows from a knowledge base with data
assertions iff the knowledge base is inconsistent or the subsumption
follows from the TBox alone. -/
theorem entailsSubKB_iff [Finite Ind] (hspec : OracleSpec Θ card)
    (O : Ontology CName Role DProp DAtom) (A : ABox CName Role DProp DAtom Ind) (a b : CName) :
    EntailsSubKB Θ O A a b ↔ ¬ ConsistentKB Θ O A ∨ EntailsSub Θ O a b := by
  constructor
  · intro h
    by_cases hc : ConsistentKB Θ O A
    · right
      obtain ⟨D1, V1, hD1, atom1, hΘ1, I1, ind, hI1, hA1⟩ := hc
      intro D2 V2 _ atom2 hΘ2 I2 hI2 x hx
      obtain ⟨V, atom, hΘ, d, hm, hA⟩ := exists_sum_model hspec hΘ1 hI1 hA1 hΘ2 hI2
      exact h (D1 ⊕ D2) V atom hΘ _ _ hm hA (.inr x) hx
    · exact Or.inl hc
  · rintro (hn | he) D V _ atom hΘ I ind hI hA x hx
    · exact absurd ⟨D, V, inferInstance, atom, hΘ, I, ind, hI, hA⟩ hn
    · exact he D V atom hΘ I hI x hx

/-- An inconsistent knowledge base entails every subsumption. -/
theorem entailsSubKB_of_not_consistent {A : ABox CName Role DProp DAtom Ind}
    (hn : ¬ ConsistentKB Θ O A) (a b : CName) : EntailsSubKB Θ O A a b :=
  fun D V _ atom hΘ I ind hI hA _ _ =>
    absurd ⟨D, V, inferInstance, atom, hΘ, I, ind, hI, hA⟩ hn

end Sum

/-! ## Classification with data assertions -/

namespace Proc

variable {n m p q k : Nat}

/-- **Classification with data assertions.** The `classifyQD` rows if the
knowledge base is consistent, every name otherwise. -/
def classifyKBD (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k))
    (hint : Option (SRIQ.Proc.Hint (n + k) m k)) (req : List (Fin n)) :
    List (Fin n × List (Fin n)) :=
  if consistentKBD O card A hint then classifyQD O card req
  else req.map fun a => (a, List.finRange n)

/-- Each requested name comes with exactly its subsumers under the
knowledge base, for an ALCHIQ object part and every data theory for
which `card` satisfies `OracleSpec`. -/
theorem classifyKBD_spec {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    (hspec : OracleSpec Θ card) {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} (hA : IsALCHIQ O)
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k))
    (hint : Option (SRIQ.Proc.Hint (n + k) m k)) {req : List (Fin n)} :
    ∀ r ∈ classifyKBD O card A hint req, r.1 ∈ req ∧
      ∀ b, b ∈ r.2 ↔ EntailsSubKB Θ O A r.1 b := by
  intro r hr
  unfold classifyKBD at hr
  split_ifs at hr with hc
  · obtain ⟨hreq, hb⟩ := classifyQD_spec hspec hA r hr
    refine ⟨hreq, fun b => ?_⟩
    rw [hb, entailsSubKB_iff hspec]
    have : ConsistentKB Θ O A := (consistentKBD_iff hspec hA A hint).1 hc
    simp [this]
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    refine ⟨ha, fun b => ?_⟩
    have : ¬ ConsistentKB Θ O A := fun h => hc ((consistentKBD_iff hspec hA A hint).2 h)
    simp only [List.mem_finRange, true_iff]
    exact entailsSubKB_of_not_consistent this a b

end Proc

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.exists_sum_model
#print axioms ContextCalculus.SRIQD.entailsSubKB_iff
#print axioms ContextCalculus.SRIQD.Proc.classifyKBD_spec

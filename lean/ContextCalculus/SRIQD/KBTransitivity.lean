import ContextCalculus.SRIQD.KBSub
import ContextCalculus.SRIQD.Transitivity

/-!
# Transitivity removal for SHIQ(D) knowledge bases (stage C4)

`encTransQD` (`SRIQD/Transitivity.lean`) with an ABox: object assertions
move to the old names of the encoding (`SRIQ.Proc.liftAssert`), data
assertions stay as they are (`encABoxD`). The model maps `upI` and
`downI` of `SRIQ/Transitivity.lean` keep the old names, the individuals
and the data relation, and they keep the roles of the object assertions
for a SHIQ knowledge base (`SRIQ.Proc.IsSHIQKB`: simple roles in negative
role assertions). So the encoding keeps consistency
(`consistentKB_encTransQD`) and, under an oracle, subsumption between old
names (`entailsSubKB_encTransQD`).

`consistentKBDS` and `classifyKBDS` are the procedures for SHIQ(D)
knowledge bases: `consistentKBD` and the `classifyQD` rows on the encoding.
-/

namespace ContextCalculus.SRIQD.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ.Proc (encTransQ models_upI models_downI)

variable {n m p q : Nat} {D V Ind : Type}

/-- A SHIQ(D) knowledge base: the object part and the object assertions
form a SHIQ knowledge base. -/
def IsSHIQDKB (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) Ind) : Prop :=
  SRIQ.Proc.IsSHIQKB (objPart O) (objABox A)

/-- An assertion on the old names of an encoding with `k` new names. -/
def liftAssertD (k : Nat) :
    Assertion (Fin n) (Fin m) (Fin p) (Fin q) Ind → Assertion (Fin (n + k)) (Fin m) (Fin p) (Fin q) Ind
  | .obj as => .obj (SRIQ.Proc.liftAssert k as)
  | .dPos a u L => .dPos a u L
  | .dNeg a u L => .dNeg a u L

/-- The ABox of the encoding. -/
def encABoxD (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) Ind) :
    ABox (Fin (n + (encTransQD O).1)) (Fin m) (Fin p) (Fin q) Ind :=
  A.map (liftAssertD (encTransQD O).1)

/-- The model map up keeps models. -/
theorem models_upD {atom : Fin q → V → Prop} {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {I : DInterp D V (Fin n) (Fin m) (Fin p)} (hI : models atom I O) :
    models atom ({ toInterp := SRI.Proc.upI (SRIQ.sriPart (objPart O)) I.toInterp, d := I.d } :
      DInterp D V (Fin (n + (encTransQD O).1)) (Fin m) (Fin p)) (encTransQD O).2 := by
  obtain ⟨hIo, hId⟩ := models_iff.1 hI
  refine models_iff.2 ⟨?_, fun cl hcl y => ?_⟩
  · rw [objPart_encTransQD]
    exact models_upI hIo
  · rcases List.mem_append.1 hcl with h1 | h1
    · obtain ⟨cl0, -, rfl⟩ := List.mem_map.1 h1
      trivial
    · obtain ⟨cl0, h0, hl⟩ := List.mem_filterMap.1 h1
      refine (dLocal_liftData atom hl _ (fun u => I.d u y)).2 ?_
      have := hId cl0 h0 y
      convert this using 2 with a
      exact SRI.Proc.upI_old I.toInterp a y

/-- The model map down keeps models, for a SHIQ object part. -/
theorem models_downD {atom : Fin q → V → Prop} {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    (h : IsSHIQD O) {J : DInterp D V (Fin (n + (encTransQD O).1)) (Fin m) (Fin p)}
    (hJ : models atom J (encTransQD O).2) :
    models atom { toInterp := SRI.Proc.downI (SRIQ.sriPart (objPart O)) J.toInterp, d := J.d } O := by
  obtain ⟨hJo, hJd⟩ := models_iff.1 hJ
  rw [objPart_encTransQD] at hJo
  refine models_iff.2 ⟨models_downI h hJo, fun cl hcl y => ?_⟩
  cases hl : liftData (encTransQ (objPart O)).1 cl with
  | none =>
    cases cl <;> simp only [liftData, reduceCtorEq] at hl
    trivial
  | some cl' =>
    have := hJd cl' (List.mem_append_right _ (List.mem_filterMap.2 ⟨cl, hcl, hl⟩)) y
    exact (dLocal_liftData atom hl _ _).1 this

/-- **Transitivity removal with data assertions.** For a SHIQ(D) knowledge
base, the encoding keeps consistency, for every data theory. -/
theorem consistentKB_encTransQD {Θ : DataTheory (Fin q)} {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {A : ABox (Fin n) (Fin m) (Fin p) (Fin q) Ind} (h : IsSHIQDKB O A) :
    ConsistentKB Θ O A ↔ ConsistentKB Θ (encTransQD O).2 (encABoxD O A) := by
  constructor
  · rintro ⟨D, V, hD, atom, hΘ, I, ind, hI, hA⟩
    refine ⟨D, V, hD, atom, hΘ, _, ind, models_upD hI, ?_⟩
    intro as has
    obtain ⟨as0, h0, rfl⟩ := List.mem_map.1 has
    have hs := hA as0 h0
    cases as0 with
    | obj as0 =>
      cases as0 with
      | cls a X => exact (SRI.Proc.upI_old I.toInterp X _).2 hs
      | role a R b =>
        show (SRI.Proc.upI (SRIQ.sriPart (objPart O)) I.toInterp).rt R _ _
        rw [SRI.Proc.upI_rt]; exact hs
      | nrole a R b =>
        show ¬ (SRI.Proc.upI (SRIQ.sriPart (objPart O)) I.toInterp).rt R _ _
        rw [SRI.Proc.upI_rt]; exact hs
      | same a b => exact hs
      | diff a b => exact hs
    | dPos a u L => exact hs
    | dNeg a u L => exact hs
  · rintro ⟨D, V, hD, atom, hΘ, J, ind, hJ, hA⟩
    refine ⟨D, V, hD, atom, hΘ, _, ind, models_downD h.1 hJ, ?_⟩
    intro as has
    have hs := hA _ (List.mem_map_of_mem (f := liftAssertD (encTransQD O).1) has)
    cases as with
    | obj as =>
      cases as with
      | cls a X => exact hs
      | role a R b => exact (SRI.Proc.downI_rt J.toInterp R _ _).2 (Or.inl hs)
      | nrole a R b =>
        intro h'
        exact hs ((SRIQ.Proc.downI_rt_simple J.toInterp (h.2 a R b (mem_objABox.2 has)) _ _).1 h')
      | same a b => exact hs
      | diff a b => exact hs
    | dPos a u L => exact hs
    | dNeg a u L => exact hs

/-- Subsumption with data assertions through the encoding, under an
oracle. -/
theorem entailsSubKB_encTransQD {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    (hspec : OracleSpec Θ card) [Finite Ind] {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {A : ABox (Fin n) (Fin m) (Fin p) (Fin q) Ind} (h : IsSHIQDKB O A) (a b : Fin n) :
    EntailsSubKB Θ O A a b ↔
      EntailsSubKB Θ (encTransQD O).2 (encABoxD O A) (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  rw [entailsSubKB_iff hspec, entailsSubKB_iff hspec, consistentKB_encTransQD h,
    encTransQD_correct h.1]

/-! ## Procedures for SHIQ(D) knowledge bases -/

variable {k : Nat}

/-- Consistency of a SHIQ(D) knowledge base: `consistentKBD` on the
encoding, with a hint over the names of the reduced encoding. -/
def consistentKBDS (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k))
    (hint : Option (SRIQ.Proc.Hint (n + (encTransQD O).1 + k) m k)) : Bool :=
  consistentKBD (encTransQD O).2 card (encABoxD O A) hint

theorem consistentKBDS_iff {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    (hspec : OracleSpec Θ card) {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)} (h : IsSHIQDKB O A)
    (hint : Option (SRIQ.Proc.Hint (n + (encTransQD O).1 + k) m k)) :
    consistentKBDS O card A hint = true ↔ ConsistentKB Θ O A := by
  rw [consistentKBDS, consistentKBD_iff hspec (encTransQD_isALCHIQ O), ← consistentKB_encTransQD h]

/-- **Classification of a SHIQ(D) knowledge base.** The subsumers of each
requested name, read off the alive records of the encoding (computed
once), if the knowledge base is consistent; every name otherwise. -/
def classifyKBDS (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k))
    (hint : Option (SRIQ.Proc.Hint (n + (encTransQD O).1 + k) m k)) (req : List (Fin n)) :
    List (Fin n × List (Fin n)) :=
  if consistentKBDS O card A hint then
    let G := aliveD (encTransQD O).2 card
    req.map fun a => (a, (List.finRange n).filter fun b =>
      decide (∀ ρ ∈ G, ρ.2 = none → Fin.castAdd _ a ∈ ρ.1 → Fin.castAdd _ b ∈ ρ.1))
  else req.map fun a => (a, List.finRange n)

theorem classifyKBDS_spec {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    (hspec : OracleSpec Θ card) {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)} (h : IsSHIQDKB O A)
    (hint : Option (SRIQ.Proc.Hint (n + (encTransQD O).1 + k) m k)) {req : List (Fin n)} :
    ∀ r ∈ classifyKBDS O card A hint req, r.1 ∈ req ∧
      ∀ b, b ∈ r.2 ↔ EntailsSubKB Θ O A r.1 b := by
  intro r hr
  unfold classifyKBDS at hr
  split_ifs at hr with hc
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    refine ⟨ha, fun b => ?_⟩
    have hcons : ConsistentKB Θ O A := (consistentKBDS_iff hspec h hint).1 hc
    rw [entailsSubKB_iff hspec, ← entailsQDS_iff hspec h.1]
    simp only [List.mem_filter, List.mem_finRange, true_and, hcons, not_true_eq_false,
      false_or, entailsQDS, entailsQD]
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    refine ⟨ha, fun b => ?_⟩
    have : ¬ ConsistentKB Θ O A := fun h' => hc ((consistentKBDS_iff hspec h hint).2 h')
    simp only [List.mem_finRange, true_iff]
    exact entailsSubKB_of_not_consistent this a b

end ContextCalculus.SRIQD.Proc

#print axioms ContextCalculus.SRIQD.Proc.consistentKB_encTransQD
#print axioms ContextCalculus.SRIQD.Proc.entailsSubKB_encTransQD
#print axioms ContextCalculus.SRIQD.Proc.consistentKBDS_iff
#print axioms ContextCalculus.SRIQD.Proc.classifyKBDS_spec

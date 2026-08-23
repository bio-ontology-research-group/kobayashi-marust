import ContextCalculus.ELRawNormalization
import ContextCalculus.ELResidualCompilation
import ContextCalculus.CheckerTerm
import Mathlib.Data.Nat.Pairing

/-!
# Embedding frontend ELC clauses into the common first-order source

The automatic routing certificate needs one semantic source language shared by
ELC, HT, and CB.  CB's `CheckerTerm` language is the most general executable
clause language already certified in the repository.  This module embeds the
ELC worker's exact raw frontend clauses into that language and proves clause
satisfaction equivalent.

Individuals and auxiliary names occupy disjoint tagged regions of the common
constant namespace. Nested Skolem functions remain nested first-order terms.
The theorem is semantic and does not rely on serialization equality or hashes.
-/

namespace ContextCalculus.ELCheckerTermEmbedding

open ContextCalculus
open ContextCalculus.ELCompletion
open ContextCalculus.CheckerTerm

private def intCode (value : Int) : Nat :=
  match value with
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

private def labelCode : List (Nat × Int) → Nat
  | [] => 0
  | (concept, polarity) :: tail =>
      Nat.pair (Nat.pair concept (intCode polarity)) (labelCode tail) + 1

private theorem intCode_injective : Function.Injective intCode := by
  intro left right heq
  cases left with
  | ofNat left =>
      cases right with
      | ofNat right =>
          simp [intCode] at heq
          exact congrArg Int.ofNat (Nat.mul_left_cancel (by omega) heq)
      | negSucc right => simp [intCode] at heq; omega
  | negSucc left =>
      cases right with
      | ofNat right => simp [intCode] at heq; omega
      | negSucc right =>
          simp [intCode] at heq
          exact congrArg Int.negSucc (Nat.mul_left_cancel (by omega) heq)

private theorem labelCode_injective : Function.Injective labelCode := by
  intro left
  induction left with
  | nil =>
      intro right heq
      cases right with
      | nil => rfl
      | cons head tail => simp [labelCode] at heq
  | cons head tail ih =>
      intro right heq
      cases right with
      | nil => simp [labelCode] at heq
      | cons other rest =>
          simp only [labelCode] at heq
          have heq' := Nat.add_right_cancel heq
          have hpair := Nat.pair_eq_pair.mp heq'
          have hheadPair := Nat.pair_eq_pair.mp hpair.1
          have hconcept : head.1 = other.1 := hheadPair.1
          have hpolarity : head.2 = other.2 := intCode_injective hheadPair.2
          have hhead : head = other := Prod.ext hconcept hpolarity
          have htail : tail = rest := ih hpair.2
          simp [hhead, htail]

def individualCode (individual : Nat) : Nat := Nat.pair 0 individual

def auxiliaryCode (root : Nat) (label : List (Nat × Int)) : Nat :=
  Nat.pair 1 (Nat.pair root (labelCode label))

theorem individualCode_injective : Function.Injective individualCode := by
  intro left right heq
  exact (Nat.pair_eq_pair.mp heq).2

theorem auxiliaryCode_injective :
    Function.Injective (fun value : Nat × List (Nat × Int) =>
      auxiliaryCode value.1 value.2) := by
  intro left right heq
  have houter := Nat.pair_eq_pair.mp heq
  have hinner := Nat.pair_eq_pair.mp houter.2
  exact Prod.ext hinner.1 (labelCode_injective hinner.2)

theorem individualCode_ne_auxiliaryCode (individual root : Nat)
    (label : List (Nat × Int)) :
    individualCode individual ≠ auxiliaryCode root label := by
  intro heq
  have htag := (Nat.pair_eq_pair.mp heq).1
  omega

noncomputable def decodedConstant (T : RawTermInterp Domain) (fallback : Domain)
    (code : Nat) : Domain := by
  classical
  exact if hindividual : ∃ individual, individualCode individual = code then
      T.individual (Classical.choose hindividual)
    else if hauxiliary : ∃ value : Nat × List (Nat × Int),
        auxiliaryCode value.1 value.2 = code then
      T.auxiliary (Classical.choose hauxiliary).1
        (Classical.choose hauxiliary).2
    else fallback

@[simp] theorem decodedConstant_individual (T : RawTermInterp Domain)
    (fallback : Domain) (individual : Nat) :
    decodedConstant T fallback (individualCode individual) =
      T.individual individual := by
  classical
  have hexists : ∃ candidate : Nat,
      individualCode candidate = individualCode individual := ⟨individual, rfl⟩
  simp only [decodedConstant, dif_pos hexists]
  have hchosen := Classical.choose_spec
    hexists
  rw [individualCode_injective hchosen]

@[simp] theorem decodedConstant_auxiliary (T : RawTermInterp Domain)
    (fallback : Domain) (root : Nat) (label : List (Nat × Int)) :
    decodedConstant T fallback (auxiliaryCode root label) =
      T.auxiliary root label := by
  classical
  have hnoIndividual : ¬∃ individual,
      individualCode individual = auxiliaryCode root label := by
    rintro ⟨individual, heq⟩
    exact individualCode_ne_auxiliaryCode individual root label heq
  have hexists : ∃ value : Nat × List (Nat × Int),
      auxiliaryCode value.1 value.2 = auxiliaryCode root label :=
    ⟨(root, label), rfl⟩
  simp only [decodedConstant, dif_neg hnoIndividual, dif_pos hexists]
  let chosen := Classical.choose
    hexists
  have hchosen : auxiliaryCode chosen.1 chosen.2 = auxiliaryCode root label :=
    Classical.choose_spec hexists
  have heq : chosen = (root, label) := auxiliaryCode_injective hchosen
  simpa [chosen] using congrArg (fun value : Nat × List (Nat × Int) =>
    T.auxiliary value.1 value.2) heq

def encodeTerm : RawTerm → FTerm
  | .var index => .var (Int.ofNat index)
  | .ind individual => .const (individualCode individual)
  | .aux root label => .const (auxiliaryCode root label)
  | .fun function argument => .app function (encodeTerm argument)

def encodeAtom : RawAtom Nat Nat → FLit
  | .concept concept term => .P (.concept concept (encodeTerm term))
  | .role role source target =>
      .P (.role role (encodeTerm source) (encodeTerm target))

def encodeClause (clause : RawClause Nat Nat) : FCL :=
  ⟨clause.body.map encodeAtom, clause.head.map encodeAtom⟩

def encodeResidualAtom : RawResidualAtom Nat Nat → FLit
  | .concept concept term => .P (.concept concept (encodeTerm term))
  | .role role source target =>
      .P (.role role (encodeTerm source) (encodeTerm target))
  | .eq left right => .eq (encodeTerm left) (encodeTerm right)

def encodeResidualClause (clause : RawResidualClause Nat Nat) : FCL :=
  ⟨clause.body.map encodeResidualAtom, clause.head.map encodeResidualAtom⟩

def rawTermInterp (model : TModel Domain) : RawTermInterp Domain where
  individual individual := model.const (individualCode individual)
  auxiliary root label := model.const (auxiliaryCode root label)
  function := model.fn

def elInterp (model : TModel Domain) (top bottom : Nat)
    (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value) :
    Interp Domain Nat Nat top bottom where
  concept := model.conc
  role := model.rol
  top_true := topTrue
  bottom_false := bottomFalse

noncomputable def modelOfRaw
    (I : Interp Domain Nat Nat top bottom) (T : RawTermInterp Domain)
    (fallback : Domain) : TModel Domain where
  conc := I.concept
  rol := I.role
  const := decodedConstant T fallback
  fn := T.function

@[simp] theorem rawTermInterp_modelOfRaw
    (I : Interp Domain Nat Nat top bottom) (T : RawTermInterp Domain)
    (fallback : Domain) :
    rawTermInterp (modelOfRaw I T fallback) = T := by
  rcases T with ⟨individuals, auxiliaries, functions⟩
  simp [rawTermInterp, modelOfRaw]

@[simp] theorem elInterp_modelOfRaw
    (I : Interp Domain Nat Nat top bottom) (T : RawTermInterp Domain)
    (fallback : Domain) :
    elInterp (modelOfRaw I T fallback) top bottom I.top_true I.bottom_false = I := by
  rcases I with ⟨concepts, roles, topTrue, bottomFalse⟩
  rfl

@[simp] theorem eval_encodeTerm (model : TModel Domain) (assignment : Int → Domain)
    (term : RawTerm) :
    model.evalT assignment (encodeTerm term) =
      evalRawTerm (rawTermInterp model)
        (fun index => assignment (Int.ofNat index)) term := by
  induction term with
  | var index => rfl
  | ind individual => rfl
  | aux root label => rfl
  | «fun» function argument ih =>
      simp [encodeTerm, TModel.evalT, evalRawTerm, rawTermInterp, ih]

@[simp] theorem eval_encodeAtom (model : TModel Domain) (assignment : Int → Domain)
    (top bottom : Nat) (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value)
    (atom : RawAtom Nat Nat) :
    model.evalL assignment (encodeAtom atom) ↔
      satRawAtom (elInterp model top bottom topTrue bottomFalse)
        (rawTermInterp model) (fun index => assignment (Int.ofNat index)) atom := by
  cases atom <;> simp [encodeAtom, TModel.evalL, satRawAtom, elInterp]

/-- Every raw ELC clause has exactly the same truth condition after embedding
into the common proper-term first-order source language. -/
theorem valid_encodeClause_iff (model : TModel Domain) (top bottom : Nat)
    (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value)
    (clause : RawClause Nat Nat) :
    valid model (encodeClause clause) ↔
      satRawClause (elInterp model top bottom topTrue bottomFalse)
        (rawTermInterp model) clause := by
  constructor
  · intro hvalid environment hbody
    let assignment : Int → Domain := fun index =>
      match index with
      | .ofNat index => environment index
      | .negSucc _ => environment 0
    have hencodedBody : ∀ literal ∈ (encodeClause clause).body,
        model.evalL assignment literal := by
      intro literal hliteral
      rcases List.mem_map.mp hliteral with ⟨atom, hatom, rfl⟩
      apply (eval_encodeAtom model assignment top bottom topTrue bottomFalse atom).2
      simpa [assignment] using hbody atom hatom
    rcases hvalid assignment hencodedBody with ⟨literal, hliteral, hlit⟩
    rcases List.mem_map.mp hliteral with ⟨atom, hatom, rfl⟩
    refine ⟨atom, hatom, ?_⟩
    have := (eval_encodeAtom model assignment top bottom topTrue bottomFalse atom).1 hlit
    simpa [assignment] using this
  · intro hraw assignment hbody
    let environment : Nat → Domain :=
      fun index => assignment (Int.ofNat index)
    have hrawBody : holdsRawAtoms
        (elInterp model top bottom topTrue bottomFalse)
        (rawTermInterp model) environment clause.body := by
      intro atom hatom
      apply (eval_encodeAtom model assignment top bottom topTrue bottomFalse atom).1
      exact hbody (encodeAtom atom) (by
        exact List.mem_map.mpr ⟨atom, hatom, rfl⟩)
    rcases hraw environment hrawBody with ⟨atom, hatom, htrue⟩
    refine ⟨encodeAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩, ?_⟩
    exact (eval_encodeAtom model assignment top bottom topTrue bottomFalse atom).2 htrue

theorem models_encode_iff (model : TModel Domain) (top bottom : Nat)
    (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value)
    (ontology : List (RawClause Nat Nat)) :
    (∀ clause ∈ ontology, valid model (encodeClause clause)) ↔
      modelsRaw (elInterp model top bottom topTrue bottomFalse)
        (rawTermInterp model) ontology := by
  constructor <;> intro h clause hclause
  · exact (valid_encodeClause_iff model top bottom topTrue bottomFalse clause).1
      (h clause hclause)
  · exact (valid_encodeClause_iff model top bottom topTrue bottomFalse clause).2
      (h clause hclause)

@[simp] theorem eval_encodeResidualAtom (model : TModel Domain)
    (assignment : Int → Domain) (top bottom : Nat)
    (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value)
    (atom : RawResidualAtom Nat Nat) :
    model.evalL assignment (encodeResidualAtom atom) ↔
      satRawResidualAtom (elInterp model top bottom topTrue bottomFalse)
        (rawTermInterp model) (fun index => assignment (Int.ofNat index)) atom := by
  cases atom <;>
    simp [encodeResidualAtom, TModel.evalL, satRawResidualAtom, elInterp]

theorem valid_encodeResidualClause_iff (model : TModel Domain)
    (top bottom : Nat) (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value)
    (clause : RawResidualClause Nat Nat) :
    valid model (encodeResidualClause clause) ↔
      satRawResidualClause (elInterp model top bottom topTrue bottomFalse)
        (rawTermInterp model) clause := by
  constructor
  · intro hvalid environment hbody
    let assignment : Int → Domain := fun index =>
      match index with
      | .ofNat index => environment index
      | .negSucc _ => environment 0
    have hencodedBody : ∀ literal ∈ (encodeResidualClause clause).body,
        model.evalL assignment literal := by
      intro literal hliteral
      rcases List.mem_map.mp hliteral with ⟨atom, hatom, rfl⟩
      apply (eval_encodeResidualAtom model assignment top bottom topTrue
        bottomFalse atom).2
      simpa [assignment] using hbody atom hatom
    rcases hvalid assignment hencodedBody with ⟨literal, hliteral, htrue⟩
    rcases List.mem_map.mp hliteral with ⟨atom, hatom, rfl⟩
    refine ⟨atom, hatom, ?_⟩
    have hresult := (eval_encodeResidualAtom model assignment top bottom topTrue
      bottomFalse atom).1 htrue
    simpa [assignment] using hresult
  · intro hraw assignment hbody
    let environment : Nat → Domain := fun index => assignment (Int.ofNat index)
    have hrawBody : ∀ atom ∈ clause.body,
        satRawResidualAtom (elInterp model top bottom topTrue bottomFalse)
          (rawTermInterp model) environment atom := by
      intro atom hatom
      apply (eval_encodeResidualAtom model assignment top bottom topTrue
        bottomFalse atom).1
      exact hbody (encodeResidualAtom atom)
        (List.mem_map.mpr ⟨atom, hatom, rfl⟩)
    rcases hraw environment hrawBody with ⟨atom, hatom, htrue⟩
    refine ⟨encodeResidualAtom atom,
      List.mem_map.mpr ⟨atom, hatom, rfl⟩, ?_⟩
    exact (eval_encodeResidualAtom model assignment top bottom topTrue
      bottomFalse atom).2 htrue

theorem models_encodeResidual_iff (model : TModel Domain) (top bottom : Nat)
    (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value)
    (ontology : List (RawResidualClause Nat Nat)) :
    (∀ clause ∈ ontology, valid model (encodeResidualClause clause)) ↔
      modelsRawResidual (elInterp model top bottom topTrue bottomFalse)
        (rawTermInterp model) ontology := by
  constructor <;> intro h clause hclause
  · exact (valid_encodeResidualClause_iff model top bottom topTrue bottomFalse
      clause).1 (h clause hclause)
  · exact (valid_encodeResidualClause_iff model top bottom topTrue bottomFalse
      clause).2 (h clause hclause)

def CommonResidualEntails (top bottom : Nat)
    (ontology : List (RawResidualClause Nat Nat)) (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ value, model.conc top value) →
    (∀ value, ¬model.conc bottom value) →
    (∀ clause ∈ ontology, valid model (encodeResidualClause clause)) →
      ∀ value, model.conc sub value → model.conc sup value

def RawResidualEntails (top bottom : Nat)
    (ontology : List (RawResidualClause Nat Nat)) (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Nat Nat top bottom)
    (T : RawTermInterp Domain),
    modelsRawResidual I T ontology →
      ∀ value, I.concept sub value → I.concept sup value

/-- Bidirectional common-source theorem for the exact residual language used by
the V5 ELC checker. The reverse direction constructs interpretations for every
encoded individual, auxiliary constant, and nested function. -/
theorem commonResidualEntails_iff_raw (top bottom : Nat)
    (ontology : List (RawResidualClause Nat Nat)) (sub sup : Nat) :
    CommonResidualEntails top bottom ontology sub sup ↔
      RawResidualEntails top bottom ontology sub sup := by
  constructor
  · intro hcommon Domain I T hmodels value hsub
    let model := modelOfRaw I T value
    have hencoded : ∀ clause ∈ ontology,
        valid model (encodeResidualClause clause) := by
      apply (models_encodeResidual_iff model top bottom I.top_true
        I.bottom_false ontology).2
      simpa [model] using hmodels
    exact hcommon Domain model (by simpa [model, modelOfRaw] using I.top_true)
      (by simpa [model, modelOfRaw] using I.bottom_false) hencoded value
      (by simpa [model, modelOfRaw] using hsub)
  · intro hraw Domain model htop hbottom hmodels value hsub
    exact hraw Domain (elInterp model top bottom htop hbottom)
      (rawTermInterp model)
      ((models_encodeResidual_iff model top bottom htop hbottom ontology).1 hmodels)
      value hsub

#print axioms valid_encodeClause_iff
#print axioms models_encode_iff
#print axioms valid_encodeResidualClause_iff
#print axioms models_encodeResidual_iff
#print axioms rawTermInterp_modelOfRaw
#print axioms commonResidualEntails_iff_raw

end ContextCalculus.ELCheckerTermEmbedding

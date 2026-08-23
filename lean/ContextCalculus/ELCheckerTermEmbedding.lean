import ContextCalculus.ELRawNormalization
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

def individualCode (individual : Nat) : Nat := Nat.pair 0 individual

def auxiliaryCode (root : Nat) (label : List (Nat × Int)) : Nat :=
  Nat.pair 1 (Nat.pair root (labelCode label))

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

#print axioms valid_encodeClause_iff
#print axioms models_encode_iff

end ContextCalculus.ELCheckerTermEmbedding

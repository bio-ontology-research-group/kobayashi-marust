import ContextCalculus.HTMixedCommonSourceWire
import ContextCalculus.HTDirectCardinalityCommonSourceWire
import ContextCalculus.HypertableauMixedCardinalityProjectionWire

/-!
# Mixed Skolem and cardinality common sources

Mixed HT sources already occupy a checked finite prefix of the common unary
function namespace. Cardinality witness functions are shifted beyond that
prefix. The semantic transport and merged-model construction below prove that
the two independently complete source families coexist without function-name
aliasing.
-/

namespace ContextCalculus.HTMixedCardinalityCommonSourceWire

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.Hypertableau
open ContextCalculus.HTMixedCommonSourceWire
open ContextCalculus.HTDirectCardinalityCommonSourceWire
open ContextCalculus.HTCardinalityCheckerTermEmbedding

def shiftTermFunctions (offset : Nat) : FTerm → FTerm
  | .var index => .var index
  | .const index => .const index
  | .app function argument =>
      .app (offset + function) (shiftTermFunctions offset argument)

def shiftPredicateFunctions (offset : Nat) : FPred → FPred
  | .concept concept term => .concept concept (shiftTermFunctions offset term)
  | .role role source target =>
      .role role (shiftTermFunctions offset source)
        (shiftTermFunctions offset target)

def shiftLiteralFunctions (offset : Nat) : FLit → FLit
  | .P predicate => .P (shiftPredicateFunctions offset predicate)
  | .eq left right =>
      .eq (shiftTermFunctions offset left) (shiftTermFunctions offset right)
  | .ineq left right =>
      .ineq (shiftTermFunctions offset left) (shiftTermFunctions offset right)

def shiftClauseFunctions (offset : Nat) (clause : FCL) : FCL := {
  body := clause.body.map (shiftLiteralFunctions offset)
  head := clause.head.map (shiftLiteralFunctions offset)
}

def shiftOntologyFunctions (offset : Nat) (ontology : List FCL) : List FCL :=
  ontology.map (shiftClauseFunctions offset)

def functionView (model : TModel Domain) (offset : Nat) : TModel Domain where
  conc := model.conc
  rol := model.rol
  const := model.const
  fn function := model.fn (offset + function)

@[simp] theorem eval_shiftTermFunctions (model : TModel Domain)
    (assignment : Int → Domain) (offset : Nat) (term : FTerm) :
    model.evalT assignment (shiftTermFunctions offset term) =
      (functionView model offset).evalT assignment term := by
  induction term with
  | var index => rfl
  | const index => rfl
  | app function argument ih =>
      simp [shiftTermFunctions, TModel.evalT, functionView, ih]

@[simp] theorem eval_shiftLiteralFunctions (model : TModel Domain)
    (assignment : Int → Domain) (offset : Nat) (literal : FLit) :
    model.evalL assignment (shiftLiteralFunctions offset literal) ↔
      (functionView model offset).evalL assignment literal := by
  cases literal with
  | P predicate =>
      cases predicate <;>
        simp [shiftLiteralFunctions, shiftPredicateFunctions, TModel.evalL,
          functionView]
  | eq left right => simp [shiftLiteralFunctions, TModel.evalL]
  | ineq left right => simp [shiftLiteralFunctions, TModel.evalL]

theorem valid_shiftClauseFunctions_iff (model : TModel Domain)
    (offset : Nat) (clause : FCL) :
    valid model (shiftClauseFunctions offset clause) ↔
      valid (functionView model offset) clause := by
  constructor <;> intro hvalid assignment hbody
  · have hshiftedBody : ∀ literal ∈ (shiftClauseFunctions offset clause).body,
        model.evalL assignment literal := by
      intro literal hliteral
      rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
      exact (eval_shiftLiteralFunctions model assignment offset source).2
        (hbody source hsource)
    rcases hvalid assignment hshiftedBody with ⟨literal, hliteral, htrue⟩
    rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource,
      (eval_shiftLiteralFunctions model assignment offset source).1 htrue⟩
  · have hsourceBody : ∀ literal ∈ clause.body,
        (functionView model offset).evalL assignment literal := by
      intro literal hliteral
      exact (eval_shiftLiteralFunctions model assignment offset literal).1
        (hbody (shiftLiteralFunctions offset literal)
          (List.mem_map.mpr ⟨literal, hliteral, rfl⟩))
    rcases hvalid assignment hsourceBody with
      ⟨literal, hliteral, htrue⟩
    exact ⟨shiftLiteralFunctions offset literal,
      List.mem_map.mpr ⟨literal, hliteral, rfl⟩,
      (eval_shiftLiteralFunctions model assignment offset literal).2 htrue⟩

theorem models_shiftOntologyFunctions_iff (model : TModel Domain)
    (offset : Nat) (ontology : List FCL) :
    (∀ clause ∈ shiftOntologyFunctions offset ontology, valid model clause) ↔
      ∀ clause ∈ ontology, valid (functionView model offset) clause := by
  constructor <;> intro hmodels clause hclause
  · exact (valid_shiftClauseFunctions_iff model offset clause).1
      (hmodels (shiftClauseFunctions offset clause)
        (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact (valid_shiftClauseFunctions_iff model offset source).2
      (hmodels source hsource)

def mergeFunctions (offset : Nat)
    (prefixFunctions suffixFunctions : Nat → Domain → Domain) : Nat → Domain → Domain :=
  fun function source =>
    if function < offset then prefixFunctions function source
    else suffixFunctions (function - offset) source

@[simp] theorem mergeFunctions_prefix (offset : Nat)
    (prefixFunctions suffixFunctions : Nat → Domain → Domain) (function : Fin offset)
    (source : Domain) :
    mergeFunctions offset prefixFunctions suffixFunctions function.val source =
      prefixFunctions function.val source := by
  simp [mergeFunctions, function.isLt]

@[simp] theorem mergeFunctions_suffix (offset : Nat)
    (prefixFunctions suffixFunctions : Nat → Domain → Domain) (function : Nat)
    (source : Domain) :
    mergeFunctions offset prefixFunctions suffixFunctions (offset + function) source =
      suffixFunctions function source := by
  simp [mergeFunctions]

def mergedModel (offset : Nat) (prefixFunctions : Nat → Domain → Domain)
    (suffixModel : TModel Domain) : TModel Domain where
  conc := suffixModel.conc
  rol := suffixModel.rol
  const := suffixModel.const
  fn := mergeFunctions offset prefixFunctions suffixModel.fn

@[simp] theorem functionView_mergedModel (offset : Nat)
    (prefixFunctions : Nat → Domain → Domain) (suffixModel : TModel Domain) :
    functionView (mergedModel offset prefixFunctions suffixModel) offset = suffixModel := by
  rcases suffixModel with ⟨concepts, roles, constants, suffixFunctions⟩
  simp only [functionView, mergedModel]
  have hfunctions :
      (fun function => mergeFunctions offset prefixFunctions suffixFunctions
        (offset + function)) = suffixFunctions := by
    funext function source
    exact mergeFunctions_suffix offset prefixFunctions suffixFunctions function source
  rw [hfunctions]

#print axioms valid_shiftClauseFunctions_iff
#print axioms models_shiftOntologyFunctions_iff
#print axioms functionView_mergedModel

end ContextCalculus.HTMixedCardinalityCommonSourceWire

import ContextCalculus.CBFiniteTermOrderWire

/-!
# Proof-carrying finite literal order for production CB closure

This layer extends the exact finite term universe with one duplicate-free
low-to-high permutation of every literal occurring in the verified source or a
terminal retained context. Maximal head positions are recomputed from ranks,
never accepted as runtime booleans. Later Hyper, Eq, and Join closure layers use
this executable maximality boundary.
-/

namespace ContextCalculus.CBFiniteLiteralOrderWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBFiniteTermOrderWire

def clauseLiterals (clause : FCL) : List FLit := clause.body ++ clause.head

def productionLiterals (termOrder : DecodedFiniteTermOrderDocument) : List FLit :=
  let production :=
    termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production
  ((production.source.ontology.flatMap clauseLiterals) ++
    production.contexts.flatMap fun context =>
      context.retained.flatMap clauseLiterals).eraseDups

structure WireFiniteLiteralOrderDocument where
  version : Nat
  term_order : WireFiniteTermOrderDocument
  ordered_literals : List WireLiteral
deriving FromJson, ToJson

structure DecodedFiniteLiteralOrderDocument where
  termOrder : DecodedFiniteTermOrderDocument
  orderedLiterals : List FLit
  ordered_nodup : orderedLiterals.Nodup
  literals_exact : orderedLiterals.toFinset =
    (productionLiterals termOrder).toFinset

def WireFiniteLiteralOrderDocument.decode
    (wire : WireFiniteLiteralOrderDocument) :
    Except String DecodedFiniteLiteralOrderDocument := do
  if wire.version != 1 then
    throw s!"unsupported finite CB literal-order version {wire.version}"
  let termOrder ← wire.term_order.decode
  let production :=
    termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production
  let orderedLiterals ← wire.ordered_literals.mapM
    (WireLiteral.decode production.bounds)
  if hnodup : orderedLiterals.Nodup then
    let expected := productionLiterals termOrder
    if hexact : orderedLiterals.toFinset = expected.toFinset then
      return {
        termOrder
        orderedLiterals
        ordered_nodup := hnodup
        literals_exact := hexact
      }
    else throw "finite CB literal order omits or invents a production literal"
  else throw "finite CB literal order contains a duplicate literal"

def WireFiniteLiteralOrderDocument.check
    (wire : WireFiniteLiteralOrderDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedFiniteLiteralOrderDocument.rank
    (decoded : DecodedFiniteLiteralOrderDocument) (literal : FLit) : Nat :=
  decoded.orderedLiterals.idxOf literal

def DecodedFiniteLiteralOrderDocument.LiteralLt
    (decoded : DecodedFiniteLiteralOrderDocument) (left right : FLit) : Prop :=
  decoded.rank left < decoded.rank right

instance (decoded : DecodedFiniteLiteralOrderDocument) (left right : FLit) :
    Decidable (decoded.LiteralLt left right) := by
  unfold DecodedFiniteLiteralOrderDocument.LiteralLt
  infer_instance

def DecodedFiniteLiteralOrderDocument.maximalHeadIndices
    (decoded : DecodedFiniteLiteralOrderDocument) (head : List FLit) : List Nat :=
  (List.range head.length).filter fun index =>
    match head[index]? with
    | none => false
    | some literal => head.all fun other => decoded.rank other ≤ decoded.rank literal

theorem DecodedFiniteLiteralOrderDocument.mem_ordered_iff
    (decoded : DecodedFiniteLiteralOrderDocument) (literal : FLit) :
    literal ∈ decoded.orderedLiterals ↔
      literal ∈ productionLiterals decoded.termOrder := by
  have hfinset : literal ∈ decoded.orderedLiterals.toFinset ↔
      literal ∈ (productionLiterals decoded.termOrder).toFinset := by
    rw [decoded.literals_exact]
  simpa using hfinset

theorem DecodedFiniteLiteralOrderDocument.rank_injective_on_production
    (decoded : DecodedFiniteLiteralOrderDocument) {left right : FLit}
    (hleft : left ∈ productionLiterals decoded.termOrder)
    (_hright : right ∈ productionLiterals decoded.termOrder)
    (hrank : decoded.rank left = decoded.rank right) : left = right := by
  have hleft' := (decoded.mem_ordered_iff left).mpr hleft
  exact (List.idxOf_inj hleft').mp hrank

theorem mem_maximalHeadIndices_iff
    (decoded : DecodedFiniteLiteralOrderDocument) (head : List FLit)
    (index : Nat) :
    index ∈ decoded.maximalHeadIndices head ↔
      index < head.length ∧
      ∃ literal, head[index]? = some literal ∧
        ∀ other ∈ head, decoded.rank other ≤ decoded.rank literal := by
  simp only [DecodedFiniteLiteralOrderDocument.maximalHeadIndices,
    List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hindex, hmaximal⟩
    cases hliteral : head[index]? with
    | none => simp [hliteral] at hmaximal
    | some literal =>
        refine ⟨hindex, literal, rfl, ?_⟩
        simpa [hliteral, List.all_eq_true] using hmaximal
  · rintro ⟨hindex, literal, hliteral, hmaximal⟩
    refine ⟨hindex, ?_⟩
    simpa [hliteral, List.all_eq_true] using hmaximal

theorem WireFiniteLiteralOrderDocument.check_sound
    (wire : WireFiniteLiteralOrderDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedFiniteLiteralOrderDocument,
      wire.decode = .ok decoded ∧
      decoded.orderedLiterals.Nodup ∧
      (∀ literal, literal ∈ decoded.orderedLiterals ↔
        literal ∈ productionLiterals decoded.termOrder) ∧
      (∀ head index, index ∈ decoded.maximalHeadIndices head ↔
        index < head.length ∧
        ∃ literal, head[index]? = some literal ∧
          ∀ other ∈ head, decoded.rank other ≤ decoded.rank literal) := by
  cases hdecode : wire.decode with
  | error message => simp [WireFiniteLiteralOrderDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.ordered_nodup,
        decoded.mem_ordered_iff, mem_maximalHeadIndices_iff decoded⟩

private def x : WireTerm := .var 0
private def y : WireTerm := .var (-1)
private def z : WireTerm := .var (-2)
private def a : WireTerm := .var (-3)

def acceptedExample : WireFiniteLiteralOrderDocument where
  version := 1
  term_order := CBFiniteTermOrderWire.acceptedExample
  ordered_literals := [
    .predicate (.concept 0 x),
    .predicate (.concept 1 x),
    .predicate (.concept 0 a),
    .equality x y,
    .equality x z,
    .inequality y z,
    .inequality z y]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

private def missingExample : WireFiniteLiteralOrderDocument :=
  { acceptedExample with
    ordered_literals := acceptedExample.ordered_literals.drop 1 }

private def duplicateExample : WireFiniteLiteralOrderDocument :=
  { acceptedExample with
    ordered_literals := WireLiteral.equality x y ::
      acceptedExample.ordered_literals }

example : rejected missingExample.check = true := by native_decide

example : rejected duplicateExample.check = true := by native_decide

example : (match acceptedExample.decode with
    | .ok decoded => decide (decoded.maximalHeadIndices
      [.eq (.var 0) (.var (-1)), .eq (.var 0) (.var (-2))] = [1])
    | .error _ => false) = true := by
  native_decide

#print axioms WireFiniteLiteralOrderDocument.check_sound
#print axioms mem_maximalHeadIndices_iff

end ContextCalculus.CBFiniteLiteralOrderWire

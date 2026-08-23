import ContextCalculus.CBLocalEqClosureWire

/-!
# Checked admissibility conditions for the finite CB term order

A duplicate-free permutation gives a finite strict total order, but that alone
does not justify ordered paramodulation. This layer additionally checks the
two structural conditions relevant to KM's unary term algebra on the complete
production universe: every proper subterm is smaller than its containing term,
and applying the same unary function preserves strict order whenever both
applications occur in that universe.

This is an executable admissibility boundary. The later ordered-paramodulation
model theorem must consume these properties; this module does not claim that
the completeness connection is already proved.
-/

namespace ContextCalculus.CBFiniteOrderAdmissibilityWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBFiniteTermOrderWire
open ContextCalculus.CBFiniteLiteralOrderWire
open ContextCalculus.CBLocalEqClosureWire

def properSubterms : FTerm → List FTerm
  | .var _ | .const _ => []
  | .app _ argument => termAndSubterms argument

def subtermCondition (order : DecodedFiniteTermOrderDocument) : Bool :=
  order.orderedTerms.all fun term =>
    (properSubterms term).all fun subterm => order.rank subterm < order.rank term

def unaryFunctions (order : DecodedFiniteTermOrderDocument) : List Nat :=
  order.orderedTerms.filterMap (fun term => match term with
    | .app function _ => some function
    | _ => none) |>.eraseDups

def unaryMonotoneCondition (order : DecodedFiniteTermOrderDocument) : Bool :=
  (unaryFunctions order).all fun function =>
    order.orderedTerms.all fun left =>
      order.orderedTerms.all fun right =>
        if order.rank left < order.rank right then
          let leftApp := FTerm.app function left
          let rightApp := FTerm.app function right
          if leftApp ∈ order.orderedTerms ∧ rightApp ∈ order.orderedTerms then
            order.rank leftApp < order.rank rightApp
          else true
        else true

structure WireFiniteOrderAdmissibilityDocument where
  version : Nat
  eq_closure : WireLocalEqClosureDocument
deriving FromJson, ToJson

structure DecodedFiniteOrderAdmissibilityDocument where
  eqClosure : DecodedLocalEqClosureDocument
  subterm_condition : subtermCondition eqClosure.literalOrder.termOrder = true
  unary_monotone_condition :
    unaryMonotoneCondition eqClosure.literalOrder.termOrder = true

def WireFiniteOrderAdmissibilityDocument.decode
    (wire : WireFiniteOrderAdmissibilityDocument) :
    Except String DecodedFiniteOrderAdmissibilityDocument := do
  if wire.version != 1 then
    throw s!"unsupported finite CB order-admissibility version {wire.version}"
  let eqClosure ← wire.eq_closure.decode
  let order := eqClosure.literalOrder.termOrder
  if hsubterm : subtermCondition order = true then
    if hmonotone : unaryMonotoneCondition order = true then
      return {
        eqClosure := eqClosure
        subterm_condition := hsubterm
        unary_monotone_condition := hmonotone }
    else throw "finite CB term order is not monotone under unary contexts"
  else throw "finite CB term order violates the proper-subterm condition"

def WireFiniteOrderAdmissibilityDocument.check
    (wire : WireFiniteOrderAdmissibilityDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedFiniteOrderAdmissibilityDocument.properSubterm_lt
    (decoded : DecodedFiniteOrderAdmissibilityDocument)
    {term subterm : FTerm}
    (hterm : term ∈ decoded.eqClosure.literalOrder.termOrder.orderedTerms)
    (hsubterm : subterm ∈ properSubterms term) :
    decoded.eqClosure.literalOrder.termOrder.TermLt subterm term := by
  have hcondition := decoded.subterm_condition
  unfold subtermCondition at hcondition
  rw [List.all_eq_true] at hcondition
  have htermCheck := hcondition term hterm
  rw [List.all_eq_true] at htermCheck
  exact of_decide_eq_true (htermCheck subterm hsubterm)

theorem DecodedFiniteOrderAdmissibilityDocument.unary_monotone
    (decoded : DecodedFiniteOrderAdmissibilityDocument)
    {function : Nat} {left right : FTerm}
    (hfunction : function ∈ unaryFunctions decoded.eqClosure.literalOrder.termOrder)
    (hleft : left ∈ decoded.eqClosure.literalOrder.termOrder.orderedTerms)
    (hright : right ∈ decoded.eqClosure.literalOrder.termOrder.orderedTerms)
    (hlt : decoded.eqClosure.literalOrder.termOrder.TermLt left right)
    (hleftApp : .app function left ∈
      decoded.eqClosure.literalOrder.termOrder.orderedTerms)
    (hrightApp : .app function right ∈
      decoded.eqClosure.literalOrder.termOrder.orderedTerms) :
    decoded.eqClosure.literalOrder.termOrder.TermLt
      (.app function left) (.app function right) := by
  have hcondition := decoded.unary_monotone_condition
  unfold unaryMonotoneCondition at hcondition
  rw [List.all_eq_true] at hcondition
  have hfunctionCheck := hcondition function hfunction
  rw [List.all_eq_true] at hfunctionCheck
  have hleftCheck := hfunctionCheck left hleft
  rw [List.all_eq_true] at hleftCheck
  have hrightCheck := hleftCheck right hright
  simp only [DecodedFiniteTermOrderDocument.TermLt] at hlt ⊢
  simp [hlt, hleftApp, hrightApp] at hrightCheck
  exact hrightCheck

theorem DecodedFiniteOrderAdmissibilityDocument.term_trichotomy
    (decoded : DecodedFiniteOrderAdmissibilityDocument)
    {left right : FTerm}
    (hleft : left ∈ productionTerms
      decoded.eqClosure.literalOrder.termOrder.factorClosure)
    (hright : right ∈ productionTerms
      decoded.eqClosure.literalOrder.termOrder.factorClosure) :
    decoded.eqClosure.literalOrder.termOrder.TermLt left right ∨
      left = right ∨
      decoded.eqClosure.literalOrder.termOrder.TermLt right left := by
  let order := decoded.eqClosure.literalOrder.termOrder
  have hleftMem := (order.mem_ordered_iff left).mpr hleft
  have hrightMem := (order.mem_ordered_iff right).mpr hright
  rcases Nat.lt_trichotomy (order.rank left) (order.rank right) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (order.rank_injective_on_production
      hleft hright h))
  · exact Or.inr (Or.inr h)

theorem DecodedFiniteOrderAdmissibilityDocument.term_wellFounded
    (decoded : DecodedFiniteOrderAdmissibilityDocument) :
    WellFounded decoded.eqClosure.literalOrder.termOrder.TermLt := by
  exact InvImage.wf decoded.eqClosure.literalOrder.termOrder.rank wellFounded_lt

theorem WireFiniteOrderAdmissibilityDocument.check_sound
    (wire : WireFiniteOrderAdmissibilityDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedFiniteOrderAdmissibilityDocument,
      wire.decode = .ok decoded ∧
      subtermCondition decoded.eqClosure.literalOrder.termOrder = true ∧
      unaryMonotoneCondition decoded.eqClosure.literalOrder.termOrder = true ∧
      WellFounded decoded.eqClosure.literalOrder.termOrder.TermLt := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireFiniteOrderAdmissibilityDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.subterm_condition,
        decoded.unary_monotone_condition, decoded.term_wellFounded⟩

#print axioms DecodedFiniteOrderAdmissibilityDocument.properSubterm_lt
#print axioms DecodedFiniteOrderAdmissibilityDocument.unary_monotone
#print axioms DecodedFiniteOrderAdmissibilityDocument.term_trichotomy
#print axioms DecodedFiniteOrderAdmissibilityDocument.term_wellFounded
#print axioms WireFiniteOrderAdmissibilityDocument.check_sound

end ContextCalculus.CBFiniteOrderAdmissibilityWire

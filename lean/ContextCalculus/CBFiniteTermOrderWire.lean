import ContextCalculus.CBLocalFactorClosureWire

/-!
# Proof-carrying finite term order for production CB closure

Equality and ordered-rule closure must not trust a runtime maximality flag. This
layer collects every direct term occurring in the verified source clauses and
every terminal retained context clause. A certificate supplies a duplicate-free
low-to-high permutation of exactly that finite universe. Later Eq and maximal
head checkers derive orientation and maximality from this checked order.

The order is proof-carrying rather than required to equal one hard-coded KM
configuration. This is intentional: any finite linear order accepted by the
eventual ordered-calculus completeness theorem is admissible, provided the
terminal clause set is independently shown closed under the candidates it
induces. Rust still has to emit an order and closure evidence that pass.
-/

namespace ContextCalculus.CBFiniteTermOrderWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBLocalFactorClosureWire

def literalTerms : FLit → List FTerm
  | .P (.concept _ term) => [term]
  | .P (.role _ source target) => [source, target]
  | .eq left right | .ineq left right => [left, right]

def clauseTerms (clause : FCL) : List FTerm :=
  (clause.body.flatMap literalTerms) ++ clause.head.flatMap literalTerms

def productionTerms (factor : DecodedLocalFactorClosureDocument) : List FTerm :=
  let production :=
    factor.localResolution.terminal.sendCoverage.interContext.base.production
  ((production.source.ontology.flatMap clauseTerms) ++
    production.contexts.flatMap fun context =>
      context.retained.flatMap clauseTerms).eraseDups

structure WireFiniteTermOrderDocument where
  version : Nat
  factor_closure : WireLocalFactorClosureDocument
  ordered_terms : List WireTerm
deriving FromJson, ToJson

structure DecodedFiniteTermOrderDocument where
  factorClosure : DecodedLocalFactorClosureDocument
  orderedTerms : List FTerm
  ordered_nodup : orderedTerms.Nodup
  terms_exact : orderedTerms.toFinset = (productionTerms factorClosure).toFinset

def WireFiniteTermOrderDocument.decode (wire : WireFiniteTermOrderDocument) :
    Except String DecodedFiniteTermOrderDocument := do
  if wire.version != 1 then
    throw s!"unsupported finite CB term-order version {wire.version}"
  let factorClosure ← wire.factor_closure.decode
  let production :=
    factorClosure.localResolution.terminal.sendCoverage.interContext.base.production
  let orderedTerms ← wire.ordered_terms.mapM
    (WireTerm.decode production.bounds)
  if hnodup : orderedTerms.Nodup then
    let expected := productionTerms factorClosure
    if hexact : orderedTerms.toFinset = expected.toFinset then
      return {
        factorClosure
        orderedTerms
        ordered_nodup := hnodup
        terms_exact := hexact
      }
    else throw "finite CB term order omits or invents a production term"
  else throw "finite CB term order contains a duplicate term"

def WireFiniteTermOrderDocument.check
    (wire : WireFiniteTermOrderDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedFiniteTermOrderDocument.rank
    (decoded : DecodedFiniteTermOrderDocument) (term : FTerm) : Nat :=
  decoded.orderedTerms.idxOf term

def DecodedFiniteTermOrderDocument.TermLt
    (decoded : DecodedFiniteTermOrderDocument) (left right : FTerm) : Prop :=
  decoded.rank left < decoded.rank right

instance (decoded : DecodedFiniteTermOrderDocument) (left right : FTerm) :
    Decidable (decoded.TermLt left right) := by
  unfold DecodedFiniteTermOrderDocument.TermLt
  infer_instance

theorem DecodedFiniteTermOrderDocument.mem_ordered_iff
    (decoded : DecodedFiniteTermOrderDocument) (term : FTerm) :
    term ∈ decoded.orderedTerms ↔ term ∈ productionTerms decoded.factorClosure := by
  have hfinset : term ∈ decoded.orderedTerms.toFinset ↔
      term ∈ (productionTerms decoded.factorClosure).toFinset := by
    rw [decoded.terms_exact]
  simpa using hfinset

theorem DecodedFiniteTermOrderDocument.rank_lt_length
    (decoded : DecodedFiniteTermOrderDocument) {term : FTerm}
    (hterm : term ∈ productionTerms decoded.factorClosure) :
    decoded.rank term < decoded.orderedTerms.length := by
  unfold DecodedFiniteTermOrderDocument.rank
  exact List.idxOf_lt_length_iff.mpr
    ((decoded.mem_ordered_iff term).mpr hterm)

theorem DecodedFiniteTermOrderDocument.rank_injective_on_production
    (decoded : DecodedFiniteTermOrderDocument) {left right : FTerm}
    (hleft : left ∈ productionTerms decoded.factorClosure)
    (hright : right ∈ productionTerms decoded.factorClosure)
    (hrank : decoded.rank left = decoded.rank right) : left = right := by
  have hleft' := (decoded.mem_ordered_iff left).mpr hleft
  have _hright' := (decoded.mem_ordered_iff right).mpr hright
  exact (List.idxOf_inj hleft').mp hrank

theorem WireFiniteTermOrderDocument.check_sound
    (wire : WireFiniteTermOrderDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedFiniteTermOrderDocument,
      wire.decode = .ok decoded ∧
      decoded.orderedTerms.Nodup ∧
      (∀ term, term ∈ decoded.orderedTerms ↔
        term ∈ productionTerms decoded.factorClosure) ∧
      (∀ {left right},
        left ∈ productionTerms decoded.factorClosure →
        right ∈ productionTerms decoded.factorClosure →
        decoded.rank left = decoded.rank right → left = right) := by
  cases hdecode : wire.decode with
  | error message => simp [WireFiniteTermOrderDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.ordered_nodup,
        decoded.mem_ordered_iff,
        decoded.rank_injective_on_production⟩

def acceptedExample : WireFiniteTermOrderDocument where
  version := 1
  factor_closure := CBLocalFactorClosureWire.acceptedExample
  ordered_terms := [.var (-4), .var (-3), .var (-2), .var (-1), .var 0]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

private def missingExample : WireFiniteTermOrderDocument :=
  { acceptedExample with
    ordered_terms := acceptedExample.ordered_terms.drop 1 }

private def duplicateExample : WireFiniteTermOrderDocument :=
  { acceptedExample with
    ordered_terms := WireTerm.var 0 :: acceptedExample.ordered_terms }

example : rejected missingExample.check = true := by native_decide

example : rejected duplicateExample.check = true := by native_decide

#print axioms WireFiniteTermOrderDocument.check_sound
#print axioms DecodedFiniteTermOrderDocument.rank_injective_on_production

end ContextCalculus.CBFiniteTermOrderWire

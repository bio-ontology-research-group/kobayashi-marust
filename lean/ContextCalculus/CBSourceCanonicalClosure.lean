import ContextCalculus.CBSourceLinearExtension
import ContextCalculus.CBSourceProductionClosure

/-!
# Source-bound CB closure with checked canonical orders

The production-closure document establishes the complete terminal rule
fixpoint.  Canonical-model completeness additionally needs total well-founded
orders extending both production literal orders.  This wrapper computes those
extensions inside the trusted Lean decoder and rejects a document if either
finite production order is cyclic or otherwise fails exact-support checking.
-/

namespace ContextCalculus.CBSourceCanonicalClosure

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBSourceRootPredClosure
open ContextCalculus.CBSourceProductionClosure
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceLinearExtension

structure WireSourceCanonicalClosureDocument where
  version : Nat
  production_closure : WireSourceRootPredClosureDocument
deriving FromJson, ToJson

structure DecodedSourceCanonicalClosureDocument where
  productionClosure : DecodedSourceRootPredClosureDocument
  rootExtension : ComputedLinearExtension
    (hyperOf productionClosure).order true
  nonrootExtension : ComputedLinearExtension
    (hyperOf productionClosure).order false

def WireSourceCanonicalClosureDocument.decode
    (wire : WireSourceCanonicalClosureDocument) :
    Except String DecodedSourceCanonicalClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB canonical-closure version {wire.version}"
  let productionClosure ← wire.production_closure.decode
  let rootExtension ←
    computeLinearExtension (hyperOf productionClosure).order true
  let nonrootExtension ←
    computeLinearExtension (hyperOf productionClosure).order false
  return { productionClosure, rootExtension, nonrootExtension }

def WireSourceCanonicalClosureDocument.check
    (wire : WireSourceCanonicalClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedSourceCanonicalClosureDocument.production_closed
    (decoded : DecodedSourceCanonicalClosureDocument) :
    SourceProductionClosed decoded.productionClosure :=
  CBSourceProductionClosure.DecodedSourceRootPredClosureDocument.production_closed
    decoded.productionClosure

theorem DecodedSourceCanonicalClosureDocument.linear_extension
    (decoded : DecodedSourceCanonicalClosureDocument) (root : Bool) :
    ∃ extension : ComputedLinearExtension
        (hyperOf decoded.productionClosure).order root,
      LinearExtensionOn (hyperOf decoded.productionClosure).order root
        (hyperOf decoded.productionClosure).order.orderedLiterals
        extension.rank := by
  cases root with
  | false =>
      exact ⟨decoded.nonrootExtension,
        decoded.nonrootExtension.linearExtensionOn⟩
  | true =>
      exact ⟨decoded.rootExtension,
        decoded.rootExtension.linearExtensionOn⟩

theorem WireSourceCanonicalClosureDocument.check_sound
    (wire : WireSourceCanonicalClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceCanonicalClosureDocument,
      wire.decode = .ok decoded ∧
      SourceProductionClosed decoded.productionClosure ∧
      ∀ root : Bool,
        ∃ extension : ComputedLinearExtension
            (hyperOf decoded.productionClosure).order root,
          LinearExtensionOn (hyperOf decoded.productionClosure).order root
            (hyperOf decoded.productionClosure).order.orderedLiterals
            extension.rank := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireSourceCanonicalClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.production_closed,
        decoded.linear_extension⟩

#print axioms DecodedSourceCanonicalClosureDocument.production_closed
#print axioms DecodedSourceCanonicalClosureDocument.linear_extension
#print axioms WireSourceCanonicalClosureDocument.check_sound

end ContextCalculus.CBSourceCanonicalClosure

import ContextCalculus.CBTerminalStateWire

/-!
# Exact local-resolution closure for production CB contexts

For every terminal production context this checker independently enumerates
all ordered retained-clause pairs and every literal occurring positively in the
first head and negatively in the second body. Every resulting resolvent must be
represented by a retained clause that syntactically strengthens it. The exact
signature comparison prevents omitted, duplicated, or invented candidates.

This is one production-rule closure family. Hyper, equality, Factor, Join-3,
and Succ still require their own exact candidate enumerators before the whole
terminal state can be called calculus-closed.
-/

namespace ContextCalculus.CBLocalResolutionClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBTerminalStateWire

structure ResolutionSignature where
  positiveIndex : Nat
  negativeIndex : Nat
  literal : FLit
deriving DecidableEq, Repr

def resolutionSignatures (retained : List FCL) : List ResolutionSignature :=
  (List.range retained.length).flatMap fun positiveIndex =>
    (List.range retained.length).flatMap fun negativeIndex =>
      match retained[positiveIndex]?, retained[negativeIndex]? with
      | some positive, some negative =>
          positive.head.filterMap fun literal =>
            if literal ∈ negative.body then
              some { positiveIndex, negativeIndex, literal }
            else none
      | _, _ => []

theorem mem_resolutionSignatures_iff (retained : List FCL)
    (signature : ResolutionSignature) :
    signature ∈ resolutionSignatures retained ↔
      signature.positiveIndex < retained.length ∧
      signature.negativeIndex < retained.length ∧
      ∃ positive negative,
        retained[signature.positiveIndex]? = some positive ∧
        retained[signature.negativeIndex]? = some negative ∧
        signature.literal ∈ positive.head ∧
        signature.literal ∈ negative.body := by
  simp only [resolutionSignatures, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨positiveIndex, hpositive, negativeIndex, hnegative, hmember⟩
    split at hmember
    next positive negative hpositiveGet hnegativeGet =>
      simp only [List.mem_filterMap] at hmember
      obtain ⟨literal, hliteral, hselected⟩ := hmember
      split at hselected
      next hbody =>
        simp only [Option.some.injEq] at hselected
        subst signature
        exact ⟨hpositive, hnegative, positive, negative,
          hpositiveGet, hnegativeGet, hliteral, hbody⟩
      next => simp at hselected
    next => simp at hmember
  · rintro ⟨hpositive, hnegative, positive, negative,
      hpositiveGet, hnegativeGet, hhead, hbody⟩
    refine ⟨signature.positiveIndex, hpositive,
      signature.negativeIndex, hnegative, ?_⟩
    simp only [hpositiveGet, hnegativeGet]
    simp only [List.mem_filterMap]
    exact ⟨signature.literal, hhead, by simp [hbody]⟩

structure WireResolutionCoverage where
  positive_index : Nat
  negative_index : Nat
  literal : WireLiteral
  strengthening_retained : Nat
deriving FromJson, ToJson

structure DecodedResolutionCoverage
    (context : DecodedProductionContext bounds ontology) where
  positiveIndex : Fin context.retained.length
  negativeIndex : Fin context.retained.length
  literal : FLit
  positive_contains : literal ∈
    (context.retained.get positiveIndex).head
  negative_contains : literal ∈
    (context.retained.get negativeIndex).body
  strengtheningIndex : Fin context.retained.length
  strengthens : Strengthens (context.retained.get strengtheningIndex)
    (resolvent (context.retained.get positiveIndex)
      (context.retained.get negativeIndex) literal)

def DecodedResolutionCoverage.signature
    (coverage : DecodedResolutionCoverage context) : ResolutionSignature :=
  { positiveIndex := coverage.positiveIndex.val
    negativeIndex := coverage.negativeIndex.val
    literal := coverage.literal }

def WireResolutionCoverage.decode
    (context : DecodedProductionContext bounds ontology)
    (wire : WireResolutionCoverage) :
    Except String (DecodedResolutionCoverage context) := do
  if hpositive : wire.positive_index < context.retained.length then
    let positiveIndex : Fin context.retained.length :=
      ⟨wire.positive_index, hpositive⟩
    if hnegative : wire.negative_index < context.retained.length then
      let negativeIndex : Fin context.retained.length :=
        ⟨wire.negative_index, hnegative⟩
      let literal ← wire.literal.decode bounds
      let positive := context.retained.get positiveIndex
      let negative := context.retained.get negativeIndex
      if hhead : literal ∈ positive.head then
        if hbody : literal ∈ negative.body then
          if hstrengthening : wire.strengthening_retained < context.retained.length then
            let strengtheningIndex : Fin context.retained.length :=
              ⟨wire.strengthening_retained, hstrengthening⟩
            let result := resolvent positive negative literal
            if hstrengthens : Strengthens
                (context.retained.get strengtheningIndex) result then
              return {
                positiveIndex
                negativeIndex
                literal
                positive_contains := hhead
                negative_contains := hbody
                strengtheningIndex
                strengthens := hstrengthens
              }
            else throw "retained clause does not strengthen local resolution candidate"
          else throw "local resolution strengthening index is outside retained clauses"
        else throw "local resolution literal is absent from the negative body"
      else throw "local resolution literal is absent from the positive head"
    else throw "local resolution negative index is outside retained clauses"
  else throw "local resolution positive index is outside retained clauses"

structure WireContextResolutionClosure where
  context_index : Nat
  context_id : Nat
  generated : List WireResolutionCoverage
deriving FromJson, ToJson

structure DecodedContextResolutionClosure
    (terminal : DecodedCBTerminalStateDocument) where
  contextIndex : Fin terminal.sendCoverage.interContext.base.production.contexts.length
  contextId : Nat
  context_id_eq :
    (terminal.sendCoverage.interContext.base.production.contexts.get
      contextIndex).contextId = contextId
  generated : List (DecodedResolutionCoverage
    (terminal.sendCoverage.interContext.base.production.contexts.get contextIndex))
  signatures_exact : generated.map (·.signature) =
    resolutionSignatures
      (terminal.sendCoverage.interContext.base.production.contexts.get
        contextIndex).retained

def WireContextResolutionClosure.decode
    (terminal : DecodedCBTerminalStateDocument)
    (wire : WireContextResolutionClosure) :
    Except String (DecodedContextResolutionClosure terminal) := do
  let production := terminal.sendCoverage.interContext.base.production
  if hcontext : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length :=
      ⟨wire.context_index, hcontext⟩
    let context := production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      let generated ← wire.generated.mapM (WireResolutionCoverage.decode context)
      let expected := resolutionSignatures context.retained
      if hexact : generated.map (·.signature) = expected then
        return {
          contextIndex
          contextId := wire.context_id
          context_id_eq := hid
          generated
          signatures_exact := hexact
        }
      else throw "local resolution coverage omits, duplicates, or invents a candidate"
    else throw "local resolution context id differs from production context"
  else throw "local resolution context index is outside the production run"

structure WireLocalResolutionClosureDocument where
  version : Nat
  terminal : WireCBTerminalStateDocument
  contexts : List WireContextResolutionClosure
deriving FromJson, ToJson

structure DecodedLocalResolutionClosureDocument where
  terminal : DecodedCBTerminalStateDocument
  contexts : List (DecodedContextResolutionClosure terminal)
  context_indices_exact : contexts.map (fun context => context.contextIndex.val) =
    List.range terminal.sendCoverage.interContext.base.production.contexts.length

def WireLocalResolutionClosureDocument.decode
    (wire : WireLocalResolutionClosureDocument) :
    Except String DecodedLocalResolutionClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported local resolution-closure version {wire.version}"
  let terminal ← wire.terminal.decode
  let contexts ← wire.contexts.mapM
    (WireContextResolutionClosure.decode terminal)
  let actual := contexts.map fun context => context.contextIndex.val
  let expected := List.range
    terminal.sendCoverage.interContext.base.production.contexts.length
  if hexact : actual = expected then
    return { terminal, contexts, context_indices_exact := hexact }
  else throw "local resolution closure does not cover every context exactly once"

def WireLocalResolutionClosureDocument.check
    (wire : WireLocalResolutionClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireLocalResolutionClosureDocument.check_sound
    (wire : WireLocalResolutionClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLocalResolutionClosureDocument,
      wire.decode = .ok decoded ∧
      decoded.contexts.map (fun context => context.contextIndex.val) =
        List.range decoded.terminal.sendCoverage.interContext.base.production.contexts.length ∧
      ∀ context ∈ decoded.contexts,
        context.generated.map (·.signature) =
          resolutionSignatures
            (decoded.terminal.sendCoverage.interContext.base.production.contexts.get
              context.contextIndex).retained ∧
        ∀ coverage ∈ context.generated,
          Strengthens
            ((decoded.terminal.sendCoverage.interContext.base.production.contexts.get
              context.contextIndex).retained.get coverage.strengtheningIndex)
            (resolvent
              ((decoded.terminal.sendCoverage.interContext.base.production.contexts.get
                context.contextIndex).retained.get coverage.positiveIndex)
              ((decoded.terminal.sendCoverage.interContext.base.production.contexts.get
                context.contextIndex).retained.get coverage.negativeIndex)
              coverage.literal) := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireLocalResolutionClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.context_indices_exact, ?_⟩
      intro context _
      refine ⟨context.signatures_exact, ?_⟩
      intro coverage _
      exact coverage.strengthens

private def x : WireTerm := .var 0
private def y : WireTerm := .var (-1)
private def pyy : WireLiteral := .predicate (.concept 0 y)
private def eqxy : WireLiteral := .equality x y

private def resolutionPremise : WireClause :=
  ⟨[pyy], [pyy, eqxy]⟩

private def resolutionResult : WireClause :=
  ⟨[pyy], [eqxy, pyy]⟩

private def resolutionTerminal : WireCBTerminalStateDocument :=
  let terminal := CBTerminalStateWire.acceptedExample
  let send := terminal.send_coverage
  let inter := send.inter_context
  let production := inter.production
  let contexts := production.contexts.map fun context =>
    { context with
      retained := context.retained ++ [resolutionPremise, resolutionResult]
      trace := context.trace ++
        [⟨resolutionPremise, .tautology⟩,
         ⟨resolutionResult, .resolve 1 1 pyy⟩] }
  { terminal with
    send_coverage := { send with
      inter_context := { inter with
        production := { production with contexts } } } }

def vacuousAcceptedExample : WireLocalResolutionClosureDocument where
  version := 1
  terminal := CBTerminalStateWire.acceptedExample
  contexts := [{ context_index := 0, context_id := 7, generated := [] }]

def acceptedExample : WireLocalResolutionClosureDocument where
  version := 1
  terminal := resolutionTerminal
  contexts := [{
    context_index := 0
    context_id := 7
    generated := [{
      positive_index := 1
      negative_index := 1
      literal := pyy
      strengthening_retained := 2
    }, {
      positive_index := 1
      negative_index := 2
      literal := pyy
      strengthening_retained := 2
    }, {
      positive_index := 2
      negative_index := 1
      literal := pyy
      strengthening_retained := 2
    }, {
      positive_index := 2
      negative_index := 2
      literal := pyy
      strengthening_retained := 2
    }]
  }]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

example : resolutionSignatures
    [⟨[], []⟩, ⟨[.P (.concept 0 (.var (-1)))],
      [.P (.concept 0 (.var (-1))), .eq (.var 0) (.var (-1))]⟩,
      ⟨[.P (.concept 0 (.var (-1)))],
        [.eq (.var 0) (.var (-1)), .P (.concept 0 (.var (-1)))]⟩] =
    [{ positiveIndex := 1, negativeIndex := 1,
       literal := .P (.concept 0 (.var (-1))) },
     { positiveIndex := 1, negativeIndex := 2,
       literal := .P (.concept 0 (.var (-1))) },
     { positiveIndex := 2, negativeIndex := 1,
       literal := .P (.concept 0 (.var (-1))) },
     { positiveIndex := 2, negativeIndex := 2,
       literal := .P (.concept 0 (.var (-1))) }] := by native_decide

example : rejected ({ acceptedExample with contexts :=
    [{ context_index := 0, context_id := 7, generated := [] }] }).check = true := by
  native_decide

#print axioms mem_resolutionSignatures_iff
#print axioms WireLocalResolutionClosureDocument.check_sound

end ContextCalculus.CBLocalResolutionClosureWire

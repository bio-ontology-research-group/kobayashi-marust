import ContextCalculus.CheckerTerm
import Lean

/-!
# Source-bound CB term-derivation wire

This module turns the existing nested-term CB derivation theorem into an
executable, bounds-checked wire. The document carries the complete normalized
clause input, query core, claimed verdict, and every derivation step. Acceptance
therefore establishes soundness of that verdict directly from the document's
source clauses. It does not establish completeness of omitted taxonomy cells;
that requires the later terminal-state and blocking certificate.
-/

namespace ContextCalculus.CBTermWire

open Lean
open ContextCalculus
open ContextCalculus.CheckerTerm

inductive WireTerm where
  | var (index : Int)
  | constant (individual : Nat)
  | app (function : Nat) (argument : WireTerm)
deriving DecidableEq, FromJson, ToJson

inductive WirePredicate where
  | concept (concept : Nat) (term : WireTerm)
  | role (role : Nat) (source target : WireTerm)
deriving DecidableEq, FromJson, ToJson

inductive WireLiteral where
  | predicate (predicate : WirePredicate)
  | equality (left right : WireTerm)
  | inequality (left right : WireTerm)
deriving DecidableEq, FromJson, ToJson

structure WireClause where
  body : List WireLiteral
  head : List WireLiteral
deriving DecidableEq, FromJson, ToJson

structure WireSubstitutionEntry where
  variableId : Int
  term : WireTerm
deriving DecidableEq, FromJson, ToJson

inductive WireJustification where
  | premise (index : Nat) (substitution : List WireSubstitutionEntry)
  | core
  | tautology
  | resolve (positive negative : Nat) (literal : WireLiteral)
  | paramodulate (equality other : Nat) (left right : WireTerm)
      (literal : WireLiteral)
deriving FromJson, ToJson

structure WireEntry where
  clause : WireClause
  justification : WireJustification
deriving FromJson, ToJson

inductive WireVerdict where
  | subsumption (superconcept : Nat)
  | unsatisfiable
deriving FromJson, ToJson

structure WireDocument where
  version : Nat
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  individual_count : Nat
  ontology : List WireClause
  core_concept : Nat
  verdict : WireVerdict
  trace : List WireEntry
deriving FromJson, ToJson

structure Bounds where
  concepts : Nat
  roles : Nat
  functions : Nat
  individuals : Nat

def checkId (kind : String) (bound value : Nat) : Except String Nat :=
  if value < bound then .ok value
  else .error s!"{kind} id {value} is outside [0,{bound})"

def WireTerm.decode (bounds : Bounds) : WireTerm → Except String FTerm
  | .var index => return .var index
  | .constant individual =>
      return .const (← checkId "individual" bounds.individuals individual)
  | .app function argument =>
      return .app (← checkId "function" bounds.functions function)
        (← argument.decode bounds)

def WirePredicate.decode (bounds : Bounds) : WirePredicate → Except String FPred
  | .concept conceptId term =>
      return .concept (← checkId "concept" bounds.concepts conceptId)
        (← term.decode bounds)
  | .role roleId source target =>
      return .role (← checkId "role" bounds.roles roleId)
        (← source.decode bounds) (← target.decode bounds)

def WireLiteral.decode (bounds : Bounds) : WireLiteral → Except String FLit
  | .predicate wirePredicate => return .P (← wirePredicate.decode bounds)
  | .equality left right => return .eq (← left.decode bounds) (← right.decode bounds)
  | .inequality left right => return .ineq (← left.decode bounds) (← right.decode bounds)

def WireClause.decode (bounds : Bounds) (clause : WireClause) : Except String FCL := do
  if clause.body.Nodup then
    if clause.head.Nodup then
      return ⟨← clause.body.mapM (WireLiteral.decode bounds),
        ← clause.head.mapM (WireLiteral.decode bounds)⟩
    else
      throw "clause head contains a duplicate literal"
  else
    throw "clause body contains a duplicate literal"

def WireSubstitutionEntry.decode (bounds : Bounds)
    (entry : WireSubstitutionEntry) : Except String (Int × FTerm) :=
  return (entry.variableId, ← entry.term.decode bounds)

def WireJustification.decode (bounds : Bounds) :
    WireJustification → Except String JustifT
  | .premise index substitution => do
      let variables := substitution.map WireSubstitutionEntry.variableId
      if variables.Nodup then
        return .prem index (← substitution.mapM (WireSubstitutionEntry.decode bounds))
      else
        throw "substitution contains a duplicate variable"
  | .core => return .core
  | .tautology => return .taut
  | .resolve positive negative literal =>
      return .res positive negative (← literal.decode bounds)
  | .paramodulate equality other left right literal =>
      return .para equality other (← left.decode bounds) (← right.decode bounds)
        (← literal.decode bounds)

def WireEntry.decode (bounds : Bounds) (entry : WireEntry) :
    Except String (FCL × JustifT) :=
  return (← entry.clause.decode bounds, ← entry.justification.decode bounds)

inductive Verdict where
  | subsumption (superconcept : Nat)
  | unsatisfiable

def WireVerdict.decode (bounds : Bounds) : WireVerdict → Except String Verdict
  | .subsumption superconcept =>
      return .subsumption (← checkId "concept" bounds.concepts superconcept)
  | .unsatisfiable => return .unsatisfiable

structure DecodedDocument where
  ontology : List FCL
  coreConcept : Nat
  verdict : Verdict
  trace : List (FCL × JustifT)

def WireDocument.decode (document : WireDocument) : Except String DecodedDocument := do
  if document.version != 1 then
    throw s!"unsupported CB term certificate version {document.version}"
  else if document.concept_count = 0 then
    throw "concept_count must be positive"
  else do
    let bounds : Bounds :=
      { concepts := document.concept_count
      , roles := document.role_count
      , functions := document.function_count
      , individuals := document.individual_count }
    let core ← checkId "concept" bounds.concepts document.core_concept
    let ontology ← document.ontology.mapM (WireClause.decode bounds)
    let verdict ← document.verdict.decode bounds
    let trace ← document.trace.mapM (WireEntry.decode bounds)
    return DecodedDocument.mk ontology core verdict trace

def Verdict.target : Verdict → FCL
  | .subsumption superconcept =>
      ⟨[], [.P (.concept superconcept (.var 0))]⟩
  | .unsatisfiable => ⟨[], []⟩

def DecodedDocument.check (document : DecodedDocument) : Bool :=
  checkCertT document.ontology document.coreConcept document.trace
    document.verdict.target

def WireDocument.check (document : WireDocument) : Except String Bool := do
  return (← document.decode).check

def Verdict.Semantics (ontology : List FCL) (core : Nat) : Verdict → Prop
  | .subsumption superconcept =>
      ∀ (D : Type) (model : TModel D),
        (∀ clause ∈ ontology, valid model clause) →
        ∀ element, model.conc core element → model.conc superconcept element
  | .unsatisfiable =>
      ∀ (D : Type) (model : TModel D),
        (∀ clause ∈ ontology, valid model clause) →
        ∀ element, ¬model.conc core element

theorem DecodedDocument.check_sound (document : DecodedDocument)
    (hcheck : document.check = true) :
    document.verdict.Semantics document.ontology document.coreConcept := by
  cases hverdict : document.verdict with
  | subsumption superconcept =>
      intro D model hontology element hcore
      exact certifies_subsumptionT document.ontology document.coreConcept
        superconcept document.trace (by simpa [DecodedDocument.check,
          Verdict.target, hverdict] using hcheck) model hontology element hcore
  | unsatisfiable =>
      intro D model hontology element
      exact certifies_unsatT document.ontology document.coreConcept
        document.trace (by simpa [DecodedDocument.check, Verdict.target,
          hverdict] using hcheck) model hontology element

private def x : WireTerm := .var 0
private def concept (id : Nat) : WireLiteral := .predicate (.concept id x)

private def acceptedExample : WireDocument where
  version := 1
  concept_count := 2
  role_count := 0
  function_count := 0
  individual_count := 0
  ontology := [⟨[concept 0], [concept 1]⟩]
  core_concept := 0
  verdict := .subsumption 1
  trace :=
    [ ⟨⟨[concept 0], [concept 1]⟩, .premise 0 []⟩
    , ⟨⟨[], [concept 0]⟩, .core⟩
    , ⟨⟨[], [concept 1]⟩, .resolve 1 0 (concept 0)⟩ ]

private def acceptedResult : Except String Bool → Bool
  | .ok result => result
  | .error _ => false

example : acceptedResult acceptedExample.check = true := by native_decide

private def forgedExample : WireDocument :=
  { acceptedExample with trace :=
      [⟨⟨[], [concept 1]⟩, .premise 0 []⟩] }

example : acceptedResult forgedExample.check = false := by native_decide

#print axioms DecodedDocument.check_sound

end ContextCalculus.CBTermWire

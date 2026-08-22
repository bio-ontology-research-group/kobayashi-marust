import ContextCalculus.ELCompletionCertificate
import ContextCalculus.ELRenaming
import ContextCalculus.ELRawNormalization
import ContextCalculus.ELResidualCertificate
import ContextCalculus.ELResidualWitness
import Lean

/-!
# JSON wire format for executable ELC certificates

The Rust worker emits this schema. All symbol ids are checked against the
declared finite signature before they can enter the semantic checker. Parsing,
bound validation, proof-trace validation, and closure validation therefore fail
closed.
-/

namespace ContextCalculus.ELCompletion

open Lean

inductive WireClause where
  | nf1 (sub sup : Nat)
  | nf2 (left right sup : Nat)
  | nf3 (sub role filler : Nat)
  | nf4 (role filler sup : Nat)
  | nf5 (sub : Nat)
  | nf6 (sub sup : Nat)
  | nf7 (first second sup : Nat)
  | reflexive (role : Nat)
deriving FromJson, ToJson

inductive WireRawTerm where
  | var (name : Nat)
  | fun (function : Nat) (argument : WireRawTerm)
deriving FromJson, ToJson

inductive WireRawAtom where
  | concept (concept : Nat) (term : WireRawTerm)
  | role (role : Nat) (source target : WireRawTerm)
deriving FromJson, ToJson

inductive WireResidualAtom where
  | concept (concept : Nat) (term : WireRawTerm)
  | role (role : Nat) (source target : WireRawTerm)
  | eq (left right : WireRawTerm)
deriving FromJson, ToJson

structure WireResidualClause where
  body : List WireResidualAtom
  head : List WireResidualAtom
deriving FromJson, ToJson

inductive WireResidualOrigin where
  | source (name : Nat)
  | function (function witness : Nat)
deriving FromJson, ToJson

inductive WireCompiledResidualAtom where
  | concept (concept slot : Nat)
  | role (role source target : Nat)
  | eq (left right : Nat)
deriving FromJson, ToJson

structure WireResidualCompilation where
  variable_count : Nat
  origins : List WireResidualOrigin
  raw : WireResidualClause
  body : List WireCompiledResidualAtom
  head : List WireCompiledResidualAtom
  pins : List (Nat × Nat)
deriving FromJson, ToJson

structure WireCanonicalWitnessRecord where
  sub : Nat
  role : Nat
  filler : Nat
  witness : Nat
  function : Nat
  role_variable : Nat
  filler_variable : Nat
deriving FromJson, ToJson

structure WireRawClause where
  body : List WireRawAtom
  head : List WireRawAtom
deriving FromJson, ToJson

inductive WireConceptOrigin where
  | source
  | conjunction (prefix_ids : List Nat)
deriving FromJson, ToJson

inductive WireStep where
  | refl (a : Nat)
  | top (a : Nat)
  | nf1 (a sub sup : Nat)
  | nf2 (a left right sup : Nat)
  | nf5 (a sub : Nat)
  | nf4 (a target filler sup role : Nat)
  | bottom_edge (a target role : Nat)
  | nf3 (a sub filler role : Nat)
  | nf6 (a target sub sup : Nat)
  | nf7 (a middle target first second sup : Nat)
  | reflexive (a role : Nat)
deriving FromJson, ToJson

structure WireSubFact where
  sub : Nat
  sup : Nat
deriving FromJson, ToJson

structure WireEdgeFact where
  source : Nat
  role : Nat
  target : Nat
deriving FromJson, ToJson

structure WireNamedSubFact where
  sub : String
  sup : String
deriving FromJson, ToJson

structure WireCertificate where
  version : Nat
  symbol_count : Nat
  top : Nat
  bottom : Nat
  variable_count : Nat
  source_ontology : List WireResidualClause
  raw_ontology : List WireRawClause
  witness_records : List WireCanonicalWitnessRecord
  residual_compilations : List WireResidualCompilation
  concept_origins : List WireConceptOrigin
  ontology : List WireClause
  trace : List WireStep
  active_concepts : List Nat
  rust_subsumptions : List WireSubFact
  rust_edges : List WireEdgeFact
  public_subsumptions : List WireSubFact
  symbols : List String
  public_named_subsumptions : List WireNamedSubFact
  public_inconsistent : Bool
deriving FromJson, ToJson

def checkedFin (n value : Nat) : Except String (Fin n) :=
  if h : value < n then .ok ⟨value, h⟩
  else .error s!"symbol id {value} is outside [0,{n})"

def WireClause.decode (n : Nat) : WireClause → Except String (Clause (Fin n) (Fin n))
  | .nf1 sub sup => return .nf1 (← checkedFin n sub) (← checkedFin n sup)
  | .nf2 left right sup =>
      return .nf2 (← checkedFin n left) (← checkedFin n right) (← checkedFin n sup)
  | .nf3 sub role filler =>
      return .nf3 (← checkedFin n sub) (← checkedFin n role) (← checkedFin n filler)
  | .nf4 role filler sup =>
      return .nf4 (← checkedFin n role) (← checkedFin n filler) (← checkedFin n sup)
  | .nf5 sub => return .nf5 (← checkedFin n sub)
  | .nf6 sub sup => return .nf6 (← checkedFin n sub) (← checkedFin n sup)
  | .nf7 first second sup =>
      return .nf7 (← checkedFin n first) (← checkedFin n second) (← checkedFin n sup)
  | .reflexive role => return .reflexive (← checkedFin n role)

def WireStep.decode (n : Nat) : WireStep → Except String (Step (Fin n) (Fin n))
  | .refl a => return .refl (← checkedFin n a)
  | .top a => return .top (← checkedFin n a)
  | .nf1 a sub sup => return .nf1 (← checkedFin n a) (← checkedFin n sub) (← checkedFin n sup)
  | .nf2 a left right sup =>
      return .nf2 (← checkedFin n a) (← checkedFin n left) (← checkedFin n right)
        (← checkedFin n sup)
  | .nf5 a sub => return .nf5 (← checkedFin n a) (← checkedFin n sub)
  | .nf4 a target filler sup role =>
      return .nf4 (← checkedFin n a) (← checkedFin n target) (← checkedFin n filler)
        (← checkedFin n sup) (← checkedFin n role)
  | .bottom_edge a target role =>
      return .bottomEdge (← checkedFin n a) (← checkedFin n target) (← checkedFin n role)
  | .nf3 a sub filler role =>
      return .nf3 (← checkedFin n a) (← checkedFin n sub) (← checkedFin n filler)
        (← checkedFin n role)
  | .nf6 a target sub sup =>
      return .nf6 (← checkedFin n a) (← checkedFin n target) (← checkedFin n sub)
        (← checkedFin n sup)
  | .nf7 a middle target first second sup =>
      return .nf7 (← checkedFin n a) (← checkedFin n middle) (← checkedFin n target)
        (← checkedFin n first) (← checkedFin n second) (← checkedFin n sup)
  | .reflexive a role => return .reflexive (← checkedFin n a) (← checkedFin n role)

def WireRawTerm.decode (n variableCount : Nat) : WireRawTerm → Except String RawTerm
  | .var name => return .var (← checkedFin variableCount name).val
  | .fun function argument =>
      return .fun (← checkedFin n function).val (← argument.decode n variableCount)

def WireRawAtom.decode (n variableCount : Nat) : WireRawAtom →
    Except String (RawAtom (Fin n) (Fin n))
  | .concept conceptId term =>
      return .concept (← checkedFin n conceptId) (← term.decode n variableCount)
  | .role roleId source target =>
      return .role (← checkedFin n roleId) (← source.decode n variableCount)
        (← target.decode n variableCount)

def WireRawClause.decode (n variableCount : Nat) (clause : WireRawClause) :
    Except String (RawClause (Fin n) (Fin n)) :=
  return {
    body := ← clause.body.mapM (WireRawAtom.decode n variableCount)
    head := ← clause.head.mapM (WireRawAtom.decode n variableCount)
  }

def WireResidualAtom.decode (n variableCount : Nat) : WireResidualAtom →
    Except String (RawResidualAtom (Fin n) (Fin n))
  | .concept conceptId term =>
      return .concept (← checkedFin n conceptId) (← term.decode n variableCount)
  | .role roleId source target =>
      return .role (← checkedFin n roleId) (← source.decode n variableCount)
        (← target.decode n variableCount)
  | .eq left right =>
      return .eq (← left.decode n variableCount) (← right.decode n variableCount)

def WireResidualClause.decode (n variableCount : Nat) (clause : WireResidualClause) :
    Except String (RawResidualClause (Fin n) (Fin n)) :=
  return {
    body := ← clause.body.mapM (WireResidualAtom.decode n variableCount)
    head := ← clause.head.mapM (WireResidualAtom.decode n variableCount)
  }

def WireResidualOrigin.decode (n : Nat) : WireResidualOrigin →
    Except String (ResidualVarOrigin (Fin n))
  | .source name => return .source name
  | .function functionId witness =>
      return .function (← checkedFin n functionId).val (← checkedFin n witness)

def WireCompiledResidualAtom.decode (n variableCount : Nat) :
    WireCompiledResidualAtom →
    Except String (CompiledResidualAtom (Fin n) (Fin n) (Fin variableCount))
  | .concept conceptId slot =>
      return .concept (← checkedFin n conceptId) (← checkedFin variableCount slot)
  | .role roleId source target =>
      return .role (← checkedFin n roleId) (← checkedFin variableCount source)
        (← checkedFin variableCount target)
  | .eq left right =>
      return .eq (← checkedFin variableCount left) (← checkedFin variableCount right)

structure DecodedResidualCompilation (n variableCount : Nat) where
  origin : Fin variableCount → ResidualVarOrigin (Fin n)
  raw : RawResidualClause (Fin n) (Fin n)
  compiled : CompiledResidualClause (Fin n) (Fin n) (Fin n) (Fin variableCount)

structure SomeDecodedResidualCompilation (n : Nat) where
  variableCount : Nat
  decoded : DecodedResidualCompilation n variableCount

def WireResidualCompilation.decode (n : Nat) (wire : WireResidualCompilation) :
    Except String (DecodedResidualCompilation n wire.variable_count) := do
  if horigins : wire.origins.length = wire.variable_count then
    let origins ← wire.origins.mapM (WireResidualOrigin.decode n)
    return {
      origin := fun slot => origins.getD slot.val (.source 0)
      raw := ← wire.raw.decode n wire.variable_count
      compiled := {
        body := ← wire.body.mapM
          (WireCompiledResidualAtom.decode n wire.variable_count)
        head := ← wire.head.mapM
          (WireCompiledResidualAtom.decode n wire.variable_count)
        pins := ← wire.pins.mapM fun (slot, witness) =>
          return (← checkedFin wire.variable_count slot, ← checkedFin n witness)
      }
    }
  else
    throw s!"residual origin table has length {wire.origins.length}, expected {wire.variable_count}"

def DecodedResidualCompilation.check {n variableCount : Nat}
    (decoded : DecodedResidualCompilation n variableCount) : Bool :=
  checkResidualCompilationEvidence decoded.origin decoded.raw decoded.compiled

def WireResidualCompilation.check (n : Nat) (wire : WireResidualCompilation) :
    Except String Bool := do
  return (← wire.decode n).check

def WireResidualCompilation.decodeSome (n : Nat) (wire : WireResidualCompilation) :
    Except String (SomeDecodedResidualCompilation n) := do
  return { variableCount := wire.variable_count, decoded := ← wire.decode n }

def WireCanonicalWitnessRecord.decode (n variableCount : Nat)
    (wire : WireCanonicalWitnessRecord) :
    Except String (CanonicalWitnessRecord (Fin n) (Fin n)) :=
  return {
    sub := ← checkedFin n wire.sub
    role := ← checkedFin n wire.role
    filler := ← checkedFin n wire.filler
    witness := ← checkedFin n wire.witness
    function := (← checkedFin n wire.function).val
    roleVariable := (← checkedFin variableCount wire.role_variable).val
    fillerVariable := (← checkedFin variableCount wire.filler_variable).val
  }

def SomeDecodedResidualCompilation.check {n : Nat}
    (decoded : SomeDecodedResidualCompilation n) : Bool :=
  decoded.decoded.check

theorem DecodedResidualCompilation.check_iff {n variableCount : Nat}
    (decoded : DecodedResidualCompilation n variableCount) :
  decoded.check = true ↔
      ResidualCompilationEvidence decoded.origin decoded.raw decoded.compiled := by
  exact checkResidualCompilationEvidence_iff decoded.origin decoded.raw decoded.compiled

#print axioms DecodedResidualCompilation.check_iff

def WireConceptOrigin.decode (n : Nat) (id : Fin n) : WireConceptOrigin →
    Except String (ExtendedConcept (Fin n))
  | .source => return .inl id
  | .conjunction prefixIds => return .inr (← prefixIds.mapM (checkedFin n))

def WireClause.decodeExtended (n : Nat)
    (origin : Fin n → ExtendedConcept (Fin n)) : WireClause →
    Except String (Clause (ExtendedConcept (Fin n)) (Fin n))
  | .nf1 sub sup => return .nf1 (origin (← checkedFin n sub)) (origin (← checkedFin n sup))
  | .nf2 left right sup =>
      return .nf2 (origin (← checkedFin n left)) (origin (← checkedFin n right))
        (origin (← checkedFin n sup))
  | .nf3 sub role filler =>
      return .nf3 (origin (← checkedFin n sub)) (← checkedFin n role)
        (origin (← checkedFin n filler))
  | .nf4 role filler sup =>
      return .nf4 (← checkedFin n role) (origin (← checkedFin n filler))
        (origin (← checkedFin n sup))
  | .nf5 sub => return .nf5 (origin (← checkedFin n sub))
  | .nf6 sub sup => return .nf6 (← checkedFin n sub) (← checkedFin n sup)
  | .nf7 first second sup =>
      return .nf7 (← checkedFin n first) (← checkedFin n second) (← checkedFin n sup)
  | .reflexive role => return .reflexive (← checkedFin n role)

structure DecodedCertificate (n : Nat) where
  top : Fin n
  bottom : Fin n
  top_ne_bottom : top ≠ bottom
  source_ontology : List (RawResidualClause (Fin n) (Fin n))
  raw_ontology : List (RawClause (Fin n) (Fin n))
  witness_records : List (CanonicalWitnessRecord (Fin n) (Fin n))
  residual_compilations : List (SomeDecodedResidualCompilation n)
  concept_origins : List (ExtendedConcept (Fin n))
  concept_origins_length : concept_origins.length = n
  concept_origins_nodup : concept_origins.Nodup
  normal_ontology : Ontology (ExtendedConcept (Fin n)) (Fin n)
  ontology : Ontology (Fin n) (Fin n)
  trace : List (Step (Fin n) (Fin n))
  active_concepts : List (Fin n)
  rust_facts : List (Fact (Fin n) (Fin n))
  public_subsumptions : List (Fin n × Fin n)
  symbols : Fin n → String
  symbols_injective : Function.Injective symbols
  public_named_subsumptions : List (String × String)
  public_inconsistent : Bool

def WireSubFact.decode (n : Nat) (fact : WireSubFact) :
    Except String (Fact (Fin n) (Fin n)) :=
  return .sub (← checkedFin n fact.sub) (← checkedFin n fact.sup)

def WireEdgeFact.decode (n : Nat) (fact : WireEdgeFact) :
    Except String (Fact (Fin n) (Fin n)) :=
  return .edge (← checkedFin n fact.source) (← checkedFin n fact.role)
    (← checkedFin n fact.target)

def WireCertificate.decode (doc : WireCertificate) :
    Except String (DecodedCertificate doc.symbol_count) := do
  if doc.version != 5 then
    throw s!"unsupported ELC certificate version {doc.version}"
  let top ← checkedFin doc.symbol_count doc.top
  let bottom ← checkedFin doc.symbol_count doc.bottom
  if hne : top ≠ bottom then
    if hsymbols : doc.symbols.length = doc.symbol_count then
      if hsymbolsNodup : doc.symbols.Nodup then
       if horiginCount : doc.concept_origins.length = doc.symbol_count then
        let origins ← (List.finRange doc.symbol_count).mapM fun id =>
          (doc.concept_origins.get ⟨id.val, by rw [horiginCount]; exact id.isLt⟩).decode
            doc.symbol_count id
        let origin : Fin doc.symbol_count → ExtendedConcept (Fin doc.symbol_count) :=
          fun id => origins.getD id.val (.inl top)
        if horiginsLength : origins.length = doc.symbol_count then
          if horiginsNodup : origins.Nodup then
            return {
            top := top
            bottom := bottom
            top_ne_bottom := hne
            source_ontology := ← doc.source_ontology.mapM
              (WireResidualClause.decode doc.symbol_count doc.variable_count)
            raw_ontology := ← doc.raw_ontology.mapM
              (WireRawClause.decode doc.symbol_count doc.variable_count)
            witness_records := ← doc.witness_records.mapM
              (WireCanonicalWitnessRecord.decode doc.symbol_count doc.variable_count)
            residual_compilations := ← doc.residual_compilations.mapM fun wire =>
              wire.decodeSome doc.symbol_count
            concept_origins := origins
            concept_origins_length := horiginsLength
            concept_origins_nodup := horiginsNodup
            normal_ontology := ← doc.ontology.mapM
              (WireClause.decodeExtended doc.symbol_count origin)
            ontology := ← doc.ontology.mapM (WireClause.decode doc.symbol_count)
            trace := ← doc.trace.mapM (WireStep.decode doc.symbol_count)
            active_concepts := ← doc.active_concepts.mapM (checkedFin doc.symbol_count)
            rust_facts :=
              (← doc.rust_subsumptions.mapM (WireSubFact.decode doc.symbol_count)) ++
              (← doc.rust_edges.mapM (WireEdgeFact.decode doc.symbol_count))
            public_subsumptions := ← doc.public_subsumptions.mapM fun fact =>
              return (← checkedFin doc.symbol_count fact.sub, ← checkedFin doc.symbol_count fact.sup)
            symbols := fun id => doc.symbols.get ⟨id.val, by simpa [hsymbols] using id.isLt⟩
            symbols_injective := by
              intro left right heq
              let leftIndex : Fin doc.symbols.length :=
                ⟨left.val, by simpa [hsymbols] using left.isLt⟩
              let rightIndex : Fin doc.symbols.length :=
                ⟨right.val, by simpa [hsymbols] using right.isLt⟩
              have hindex : leftIndex = rightIndex :=
                hsymbolsNodup.get_inj_iff.mp heq
              have hval : left.val = right.val := by
                exact congrArg (fun index : Fin doc.symbols.length => index.val) hindex
              exact Fin.ext hval
            public_named_subsumptions :=
              doc.public_named_subsumptions.map fun fact => (fact.sub, fact.sup)
            public_inconsistent := doc.public_inconsistent
            }
          else
            throw "concept-origin table is not injective"
        else
          throw s!"decoded concept-origin table has length {origins.length}, expected {doc.symbol_count}"
       else
         throw s!"concept-origin table has length {doc.concept_origins.length}, expected {doc.symbol_count}"
      else
        throw "symbol table contains duplicate names"
    else
      throw s!"symbol table has length {doc.symbols.length}, expected {doc.symbol_count}"
  else
    throw "top and bottom must have distinct symbol ids"

def Fact.source {Concept Role : Type} : Fact Concept Role → Concept
  | .sub a _ => a
  | .edge a _ _ => a

def Clause.concepts {Concept Role : Type} : Clause Concept Role → List Concept
  | .nf1 sub sup => [sub, sup]
  | .nf2 left right sup => [left, right, sup]
  | .nf3 sub _ filler => [sub, filler]
  | .nf4 _ filler sup => [filler, sup]
  | .nf5 sub => [sub]
  | .nf6 _ _ => []
  | .nf7 _ _ _ => []
  | .reflexive _ => []

def DecodedCertificate.expectedActiveConcepts {n : Nat} (doc : DecodedCertificate n) :=
  (doc.top :: doc.ontology.flatMap Clause.concepts).filter (· != doc.bottom)

def DecodedCertificate.checkFactAgreement {n : Nat} (doc : DecodedCertificate n) : Bool :=
  let formal := doc.trace.map (Step.conclusion doc.top doc.bottom)
  doc.rust_facts.all (fun fact =>
    decide (fact ∈ formal ∧ fact.source ∈ doc.active_concepts)) &&
  formal.all (fun fact =>
    if fact.source ∈ doc.active_concepts then decide (fact ∈ doc.rust_facts) else true)

def DecodedCertificate.checkActiveConcepts {n : Nat} (doc : DecodedCertificate n) : Bool :=
  doc.active_concepts.all (fun id => decide (id ∈ doc.expectedActiveConcepts)) &&
    doc.expectedActiveConcepts.all (fun id => decide (id ∈ doc.active_concepts))

def DecodedCertificate.checkSignatureClosed {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  decide (doc.top ∈ doc.active_concepts) &&
    doc.ontology.all fun clause =>
      clause.concepts.all fun concept => decide (concept ∈ doc.active_concepts)

theorem Clause.mentionsConcept_iff_mem_concepts
    (clause : Clause Concept Role) (concept : Concept) :
    clause.mentionsConcept concept ↔ concept ∈ clause.concepts := by
  cases clause <;> simp [Clause.mentionsConcept, Clause.concepts, eq_comm]

theorem DecodedCertificate.checkSignatureClosed_iff {n : Nat}
    (doc : DecodedCertificate n) :
    doc.checkSignatureClosed = true ↔
      SignatureClosed (fun concept => concept ∈ doc.active_concepts)
        doc.top doc.ontology := by
  simp only [DecodedCertificate.checkSignatureClosed, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨htop, hclauses⟩
    refine ⟨htop, ?_⟩
    intro clause hclause concept hmentions
    exact hclauses clause hclause concept
      ((Clause.mentionsConcept_iff_mem_concepts clause concept).mp hmentions)
  · intro hclosed
    refine ⟨hclosed.top_active, ?_⟩
    intro clause hclause concept hconcept
    exact hclosed.clause_active clause hclause concept
      ((Clause.mentionsConcept_iff_mem_concepts clause concept).mpr hconcept)

def DecodedCertificate.checkStateAgreement {n : Nat} (doc : DecodedCertificate n) : Bool :=
  doc.checkFactAgreement && doc.checkActiveConcepts

def DecodedCertificate.expectedPublicOutput {n : Nat} (doc : DecodedCertificate n) :=
  doc.rust_facts.filterMap fun
    | .sub sub sup =>
        if sub != doc.top && sub != doc.bottom && sup != sub && sup != doc.top then
          some (sub, sup)
        else none
    | .edge _ _ _ => none

def DecodedCertificate.checkPublicOutput {n : Nat} (doc : DecodedCertificate n) : Bool :=
  doc.public_subsumptions.all (fun fact => decide (fact ∈ doc.expectedPublicOutput)) &&
    doc.expectedPublicOutput.all (fun fact => decide (fact ∈ doc.public_subsumptions))

def DecodedCertificate.expectedNamedOutput {n : Nat} (doc : DecodedCertificate n) :=
  doc.public_subsumptions.map fun (sub, sup) =>
    (doc.symbols sub, if sup = doc.bottom then "owl:Nothing" else doc.symbols sup)

def DecodedCertificate.checkNamedOutput {n : Nat} (doc : DecodedCertificate n) : Bool :=
  doc.public_named_subsumptions.all (fun fact => decide (fact ∈ doc.expectedNamedOutput)) &&
    doc.expectedNamedOutput.all (fun fact => decide (fact ∈ doc.public_named_subsumptions)) &&
    decide (doc.public_inconsistent = decide (Fact.sub doc.top doc.bottom ∈ doc.rust_facts))

def DecodedCertificate.check {n : Nat} (doc : DecodedCertificate n) : Bool :=
  checkTrace doc.top doc.bottom doc.ontology doc.trace &&
    checkClosedTrace doc.top doc.bottom doc.ontology doc.trace &&
    doc.checkStateAgreement && doc.checkPublicOutput && doc.checkNamedOutput

def DecodedCertificate.conceptOrigin {n : Nat} (doc : DecodedCertificate n) (id : Fin n) :
    ExtendedConcept (Fin n) :=
  doc.concept_origins.get ⟨id.val, by rw [doc.concept_origins_length]; exact id.isLt⟩

theorem DecodedCertificate.conceptOrigin_injective {n : Nat}
    (doc : DecodedCertificate n) : Function.Injective doc.conceptOrigin := by
  intro left right heq
  let leftIndex : Fin doc.concept_origins.length :=
    ⟨left.val, by rw [doc.concept_origins_length]; exact left.isLt⟩
  let rightIndex : Fin doc.concept_origins.length :=
    ⟨right.val, by rw [doc.concept_origins_length]; exact right.isLt⟩
  have hindex : leftIndex = rightIndex :=
    (doc.concept_origins_nodup.get_inj_iff).mp heq
  have hval : leftIndex.val = rightIndex.val :=
    congrArg (fun index => index.val) hindex
  exact Fin.ext hval

def DecodedCertificate.checkCanonicalOrigins {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  decide (doc.conceptOrigin doc.top = .inl doc.top) &&
    decide (doc.conceptOrigin doc.bottom = .inl doc.bottom)

def RawAtom.conceptIds : RawAtom Concept Role → List Concept
  | .concept conceptId _ => [conceptId]
  | .role _ _ _ => []

def RawClause.conceptIds (clause : RawClause Concept Role) : List Concept :=
  (clause.body ++ clause.head).flatMap RawAtom.conceptIds

def RawResidualAtom.conceptIds : RawResidualAtom Concept Role → List Concept
  | .concept conceptId _ => [conceptId]
  | .role _ _ _ => []
  | .eq _ _ => []

def RawResidualClause.conceptIds
    (clause : RawResidualClause Concept Role) : List Concept :=
  (clause.body ++ clause.head).flatMap RawResidualAtom.conceptIds

@[simp] theorem rawAtomToResidual_conceptIds
    (atom : RawAtom Concept Role) :
    (rawAtomToResidual atom).conceptIds = atom.conceptIds := by
  cases atom <;> rfl

@[simp] theorem RawClause.toResidual_conceptIds
    (clause : RawClause Concept Role) :
    clause.toResidual.conceptIds = clause.conceptIds := by
  simp [RawResidualClause.conceptIds, RawClause.conceptIds,
    RawClause.toResidual, List.flatMap_map]

theorem satRawAtom_congrOn
    (I J : Interp Domain Concept Role top bottom)
    (T : RawTermInterp Domain) (env : Nat → Domain)
    (atom : RawAtom Concept Role)
    (hconcept : ∀ concept ∈ atom.conceptIds, ∀ value,
      I.concept concept value ↔ J.concept concept value)
    (hrole : ∀ role source target,
      I.role role source target ↔ J.role role source target) :
    satRawAtom I T env atom ↔ satRawAtom J T env atom := by
  cases atom with
  | concept concept term =>
      exact hconcept concept (by simp [RawAtom.conceptIds]) (evalRawTerm T env term)
  | role role source target =>
      exact hrole role (evalRawTerm T env source) (evalRawTerm T env target)

theorem satRawClause_congrOn
    (I J : Interp Domain Concept Role top bottom)
    (T : RawTermInterp Domain) (clause : RawClause Concept Role)
    (hconcept : ∀ concept ∈ clause.conceptIds, ∀ value,
      I.concept concept value ↔ J.concept concept value)
    (hrole : ∀ role source target,
      I.role role source target ↔ J.role role source target) :
    satRawClause I T clause ↔ satRawClause J T clause := by
  have hatom : ∀ atom ∈ clause.body ++ clause.head, ∀ env,
      satRawAtom I T env atom ↔ satRawAtom J T env atom := by
    intro atom hatom env
    apply satRawAtom_congrOn I J T env atom
    · intro concept hconceptAtom value
      apply hconcept concept
      unfold RawClause.conceptIds
      exact List.mem_flatMap.mpr ⟨atom, hatom, hconceptAtom⟩
    · exact hrole
  constructor
  · intro hsatisfied env hbody
    have hbodyI : holdsRawAtoms I T env clause.body := by
      intro atom hatomBody
      exact (hatom atom (List.mem_append_left _ hatomBody) env).mpr
        (hbody atom hatomBody)
    obtain ⟨atom, hatomHead, hsatisfiedAtom⟩ := hsatisfied env hbodyI
    exact ⟨atom, hatomHead,
      (hatom atom (List.mem_append_right _ hatomHead) env).mp hsatisfiedAtom⟩
  · intro hsatisfied env hbody
    have hbodyJ : holdsRawAtoms J T env clause.body := by
      intro atom hatomBody
      exact (hatom atom (List.mem_append_left _ hatomBody) env).mp
        (hbody atom hatomBody)
    obtain ⟨atom, hatomHead, hsatisfiedAtom⟩ := hsatisfied env hbodyJ
    exact ⟨atom, hatomHead,
      (hatom atom (List.mem_append_right _ hatomHead) env).mpr hsatisfiedAtom⟩

def recastInterpEndpoints
    (I : Interp Domain Concept Role top bottom)
    (htop : top = targetTop) (hbottom : bottom = targetBottom) :
    Interp Domain Concept Role targetTop targetBottom := by
  subst targetTop
  subst targetBottom
  exact I

@[simp] theorem recastInterpEndpoints_concept
    (I : Interp Domain Concept Role top bottom)
    (htop : top = targetTop) (hbottom : bottom = targetBottom) :
    (recastInterpEndpoints I htop hbottom).concept = I.concept := by
  subst targetTop
  subst targetBottom
  rfl

@[simp] theorem recastInterpEndpoints_role
    (I : Interp Domain Concept Role top bottom)
    (htop : top = targetTop) (hbottom : bottom = targetBottom) :
    (recastInterpEndpoints I htop hbottom).role = I.role := by
  subst targetTop
  subst targetBottom
  rfl

theorem models_recastInterpEndpoints_iff
    (I : Interp Domain Concept Role top bottom)
    (htop : top = targetTop) (hbottom : bottom = targetBottom)
    (O : Ontology Concept Role) :
    models (recastInterpEndpoints I htop hbottom) O ↔ models I O := by
  subst targetTop
  subst targetBottom
  rfl

def listSetEq [DecidableEq α] (left right : List α) : Bool :=
  left.all (· ∈ right) && right.all (· ∈ left)

theorem listSetEq_iff [DecidableEq α] {left right : List α} :
    listSetEq left right = true ↔ ∀ value, value ∈ left ↔ value ∈ right := by
  simp [listSetEq]
  constructor
  · rintro ⟨hlr, hrl⟩ value
    exact ⟨hlr value, hrl value⟩
  · intro h
    exact ⟨fun value hmem => (h value).mp hmem,
      fun value hmem => (h value).mpr hmem⟩

def DecodedCertificate.checkOriginOntology {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  listSetEq doc.normal_ontology
    (mapOntologyConcept doc.conceptOrigin doc.ontology)

theorem models_iff_of_listSetEq [DecidableEq Concept] [DecidableEq Role]
    {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    {left right : Ontology Concept Role} (heq : listSetEq left right = true) :
    models I left ↔ models I right := by
  rw [listSetEq_iff] at heq
  simp only [models]
  exact forall_congr' fun clause => imp_congr (heq clause) Iff.rfl

theorem entailsSub_iff_of_listSetEq [DecidableEq Concept] [DecidableEq Role]
    {top bottom : Concept} {left right : Ontology Concept Role}
    (heq : listSetEq left right = true) (sub sup : Concept) :
    EntailsSub (top := top) (bottom := bottom) left sub sup ↔
      EntailsSub (top := top) (bottom := bottom) right sub sup := by
  constructor
  · intro h Domain I hmodels
    exact h I ((models_iff_of_listSetEq I heq).mpr hmodels)
  · intro h Domain I hmodels
    exact h I ((models_iff_of_listSetEq I heq).mp hmodels)

theorem unsatisfiable_iff_of_listSetEq [DecidableEq Concept] [DecidableEq Role]
    {top bottom : Concept} {left right : Ontology Concept Role}
    (heq : listSetEq left right = true) :
    Unsatisfiable (top := top) (bottom := bottom) left ↔
      Unsatisfiable (top := top) (bottom := bottom) right := by
  constructor
  · intro h Domain _ I hmodels
    exact h I ((models_iff_of_listSetEq I heq).mpr hmodels)
  · intro h Domain _ I hmodels
    exact h I ((models_iff_of_listSetEq I heq).mp hmodels)

theorem DecodedCertificate.origin_entails_iff {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkOriginOntology = true)
    (sub sup : Fin n) :
    EntailsSub (top := doc.conceptOrigin doc.top)
        (bottom := doc.conceptOrigin doc.bottom)
        doc.normal_ontology (doc.conceptOrigin sub) (doc.conceptOrigin sup) ↔
      EntailsSub (top := doc.top) (bottom := doc.bottom)
        doc.ontology sub sup := by
  letI : Nonempty (Fin n) := ⟨doc.top⟩
  have hleft : Function.LeftInverse
      (Function.invFun doc.conceptOrigin) doc.conceptOrigin :=
    Function.leftInverse_invFun doc.conceptOrigin_injective
  rw [entailsSub_iff_of_listSetEq hcheck]
  exact entailsSub_mapConcept_iff doc.conceptOrigin
    (Function.invFun doc.conceptOrigin) hleft doc.ontology sub sup

theorem DecodedCertificate.origin_unsatisfiable_iff {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkOriginOntology = true) :
    Unsatisfiable (top := doc.conceptOrigin doc.top)
        (bottom := doc.conceptOrigin doc.bottom) doc.normal_ontology ↔
      Unsatisfiable (top := doc.top) (bottom := doc.bottom) doc.ontology := by
  letI : Nonempty (Fin n) := ⟨doc.top⟩
  have hleft : Function.LeftInverse
      (Function.invFun doc.conceptOrigin) doc.conceptOrigin :=
    Function.leftInverse_invFun doc.conceptOrigin_injective
  rw [unsatisfiable_iff_of_listSetEq hcheck]
  exact unsatisfiable_mapConcept_iff doc.conceptOrigin
    (Function.invFun doc.conceptOrigin) hleft doc.ontology

#print axioms DecodedCertificate.origin_entails_iff
#print axioms DecodedCertificate.origin_unsatisfiable_iff

def DecodedCertificate.residualRawOntology {n : Nat}
    (doc : DecodedCertificate n) :
    List (RawResidualClause (Fin n) (Fin n)) :=
  doc.residual_compilations.map fun residual => residual.decoded.raw

def DecodedCertificate.partitionedSourceOntology {n : Nat}
    (doc : DecodedCertificate n) :
    List (RawResidualClause (Fin n) (Fin n)) :=
  doc.raw_ontology.map RawClause.toResidual ++
    (canonicalWitnessRawOntology doc.witness_records).map RawClause.toResidual ++
    doc.residualRawOntology

def DecodedCertificate.checkSourcePartition {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  listSetEq doc.source_ontology doc.partitionedSourceOntology

theorem DecodedCertificate.checkSourcePartition_iff {n : Nat}
    (doc : DecodedCertificate n) :
    doc.checkSourcePartition = true ↔
      ∀ clause, clause ∈ doc.source_ontology ↔
        clause ∈ doc.partitionedSourceOntology := by
  exact listSetEq_iff

def DecodedCertificate.witnessNormalOntology {n : Nat}
    (doc : DecodedCertificate n) :
    Ontology (ExtendedConcept (Fin n)) (Fin n) :=
  doc.witness_records.flatMap fun record =>
    [.nf3 (doc.conceptOrigin record.sub) record.role
        (doc.conceptOrigin record.witness),
      .nf1 (doc.conceptOrigin record.witness)
        (doc.conceptOrigin record.filler)]

/-- Validate direct normalization and the exact canonical-witness rewrite
without allowing the existential-pair normalizer to choose a different global
Skolem interpretation. -/
def DecodedCertificate.checkPartitionedNormalization {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  let sourceConcepts := doc.source_ontology.flatMap RawResidualClause.conceptIds
  let witnessConcepts := doc.witness_records.flatMap fun record =>
    [record.sub, record.filler, record.witness]
  let sourceOrigins := (sourceConcepts ++ witnessConcepts).all fun concept =>
    decide (doc.conceptOrigin concept = .inl concept)
  match certifyRawDirectToNormal doc.top doc.bottom doc.raw_ontology with
  | none => false
  | some certificate =>
      sourceOrigins && listSetEq doc.normal_ontology
        (certificate.normal.normal ++ doc.witnessNormalOntology)

theorem DecodedCertificate.sourceConcept_origin {n : Nat}
    (doc : DecodedCertificate n)
    (hcheck : doc.checkPartitionedNormalization = true)
    (clause : RawResidualClause (Fin n) (Fin n))
    (hclause : clause ∈ doc.source_ontology)
    (concept : Fin n) (hconcept : concept ∈ clause.conceptIds) :
    doc.conceptOrigin concept = .inl concept := by
  simp only [DecodedCertificate.checkPartitionedNormalization] at hcheck
  split at hcheck
  · contradiction
  · simp only [Bool.and_eq_true] at hcheck
    have horigins := hcheck.1
    simp only [List.all_eq_true, decide_eq_true_eq] at horigins
    apply horigins
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨clause, hclause, hconcept⟩

theorem DecodedCertificate.rawConcept_origin {n : Nat}
    (doc : DecodedCertificate n)
    (hnormal : doc.checkPartitionedNormalization = true)
    (hpartition : doc.checkSourcePartition = true)
    (clause : RawClause (Fin n) (Fin n))
    (hclause : clause ∈ doc.raw_ontology)
    (concept : Fin n) (hconcept : concept ∈ clause.conceptIds) :
    doc.conceptOrigin concept = .inl concept := by
  have hpartitioned : clause.toResidual ∈ doc.partitionedSourceOntology := by
    unfold DecodedCertificate.partitionedSourceOntology
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨clause, hclause, rfl⟩
  have hsource : clause.toResidual ∈ doc.source_ontology :=
    (doc.checkSourcePartition_iff.mp hpartition clause.toResidual).mpr hpartitioned
  exact doc.sourceConcept_origin hnormal clause.toResidual hsource concept (by simpa using hconcept)

/-- Validate the previously trusted normalization boundary. -/
def DecodedCertificate.checkNormalization {n : Nat} (doc : DecodedCertificate n) : Bool :=
  let rawConcepts := doc.raw_ontology.flatMap RawClause.conceptIds
  let sourceOrigins := rawConcepts.all fun concept =>
    decide (doc.conceptOrigin concept = .inl concept)
  match certifyRawToNormal doc.top doc.bottom doc.raw_ontology with
  | none => false
  | some certificate =>
      sourceOrigins && listSetEq doc.normal_ontology certificate.normal.normal

def DecodedCertificate.checkNormalizationV5 {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  doc.checkPartitionedNormalization

/-! ## Finite residual truth check -/

def DecodedCertificate.materialization {n : Nat} (doc : DecodedCertificate n) :
    Materialization (Fin n) (Fin n) :=
  traceMaterialization doc.top doc.bottom doc.trace

abbrev DecodedCertificate.ResidualDomain {n : Nat} (doc : DecodedCertificate n) :=
  MaterializedActiveAlive (fun concept => concept ∈ doc.active_concepts)
    doc.materialization doc.bottom

def DecodedCertificate.residualDomainValue {n : Nat} (doc : DecodedCertificate n)
    (htopActive : doc.top ∈ doc.active_concepts)
    (htopAlive : ¬doc.materialization.sub doc.top doc.bottom)
    (value : Fin n) : doc.ResidualDomain :=
  letI : ∀ a b, Decidable (doc.materialization.sub a b) := fun _ _ => by
    dsimp [DecodedCertificate.materialization, traceMaterialization]
    infer_instance
  if halive : value ∈ doc.active_concepts ∧
      ¬doc.materialization.sub value doc.bottom then
    ⟨value, halive⟩
  else
    ⟨doc.top, htopActive, htopAlive⟩

def DecodedResidualCompilation.mappedOrigin {n variableCount : Nat}
    (decoded : DecodedResidualCompilation n variableCount)
    {Domain : Type} (map : Fin n → Domain) :
    Fin variableCount → ResidualVarOrigin Domain :=
  fun slot => match decoded.origin slot with
    | .source name => .source name
    | .function function witness => .function function (map witness)

def DecodedResidualCompilation.mappedCompiled {n variableCount : Nat}
    (decoded : DecodedResidualCompilation n variableCount)
    {Domain : Type} (map : Fin n → Domain) :
    CompiledResidualClause Domain (Fin n) (Fin n) (Fin variableCount) where
  body := decoded.compiled.body
  head := decoded.compiled.head
  pins := decoded.compiled.pins.map fun pin => (pin.1, map pin.2)

def DecodedCertificate.residualValueAlive {n : Nat}
    (doc : DecodedCertificate n) (value : Fin n) : Bool :=
  letI : ∀ a b, Decidable (doc.materialization.sub a b) := fun _ _ => by
    dsimp [DecodedCertificate.materialization, traceMaterialization]
    infer_instance
  decide (value ∈ doc.active_concepts) &&
    decide (¬doc.materialization.sub value doc.bottom)

def DecodedCertificate.residualWitnessesAlive {n variableCount : Nat}
    (doc : DecodedCertificate n)
    (decoded : DecodedResidualCompilation n variableCount) : Bool :=
  (List.finRange variableCount).all fun slot =>
    match decoded.origin slot with
    | .source _ => true
    | .function _ witness => doc.residualValueAlive witness

def DecodedResidualCompilation.functionBindings {n variableCount : Nat}
    (decoded : DecodedResidualCompilation n variableCount) : List (Nat × Fin n) :=
  (List.finRange variableCount).filterMap fun slot =>
    match decoded.origin slot with
    | .source _ => none
    | .function function witness => some (function, witness)

def DecodedCertificate.functionBindings {n : Nat}
    (doc : DecodedCertificate n) : List (Nat × Fin n) :=
  (doc.witness_records.map fun record => (record.function, record.witness)) ++
    doc.residual_compilations.flatMap fun residual =>
      residual.decoded.functionBindings

def DecodedCertificate.checkFunctionBindings {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  doc.functionBindings.all fun binding =>
    doc.residualValueAlive binding.2 &&
      doc.functionBindings.all fun other =>
        decide (binding.1 = other.1 → binding.2 = other.2)

def DecodedCertificate.checkWitnessRecords {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  doc.witness_records.all fun record =>
    doc.residualValueAlive record.witness &&
      decide (Clause.nf3 record.sub record.role record.witness ∈ doc.ontology) &&
      decide (Clause.nf1 record.witness record.filler ∈ doc.ontology)

def lookupBinding (fallback : α) (function : Nat) : List (Nat × α) → α
  | [] => fallback
  | binding :: bindings =>
      if function = binding.1 then binding.2
      else lookupBinding fallback function bindings

theorem lookupBinding_eq_of_mem [DecidableEq α]
    (fallback : α) (function : Nat) (witness : α)
    (bindings : List (Nat × α))
    (hconsistent : ∀ binding ∈ bindings, ∀ other ∈ bindings,
      binding.1 = other.1 → binding.2 = other.2)
    (hmem : (function, witness) ∈ bindings) :
    lookupBinding fallback function bindings = witness := by
  induction bindings with
  | nil => simp at hmem
  | cons binding bindings ih =>
      simp only [lookupBinding]
      by_cases heq : function = binding.1
      · rw [if_pos heq]
        exact hconsistent binding (by simp) (function, witness) (by simp [hmem]) heq.symm
      · rw [if_neg heq]
        apply ih
        · intro left hleft right hright
          exact hconsistent left (by simp [hleft]) right (by simp [hright])
        · exact (List.mem_cons.mp hmem).resolve_left fun hequal =>
            heq (congrArg Prod.fst hequal)

def DecodedCertificate.bindingWitness {n : Nat}
    (doc : DecodedCertificate n) (function : Nat) : Fin n :=
  lookupBinding doc.top function doc.functionBindings

def DecodedCertificate.sharedPin {n : Nat} (doc : DecodedCertificate n)
    (htopActive : doc.top ∈ doc.active_concepts)
    (htopAlive : ¬doc.materialization.sub doc.top doc.bottom) :
    Nat → doc.ResidualDomain :=
  fun function => doc.residualDomainValue htopActive htopAlive
    (doc.bindingWitness function)

theorem DecodedCertificate.checkFunctionBindings_iff {n : Nat}
    (doc : DecodedCertificate n) :
    doc.checkFunctionBindings = true ↔
      ∀ binding ∈ doc.functionBindings,
        (binding.2 ∈ doc.active_concepts ∧
          ¬doc.materialization.sub binding.2 doc.bottom) ∧
        ∀ other ∈ doc.functionBindings,
          binding.1 = other.1 → binding.2 = other.2 := by
  simp [DecodedCertificate.checkFunctionBindings,
    DecodedCertificate.residualValueAlive, imp_iff_not_or]

theorem DecodedCertificate.sharedPin_eq_of_binding {n : Nat}
    (doc : DecodedCertificate n)
    (htopActive : doc.top ∈ doc.active_concepts)
    (htopAlive : ¬doc.materialization.sub doc.top doc.bottom)
    (hcheck : doc.checkFunctionBindings = true)
    (function : Nat) (witness : Fin n)
    (hbinding : (function, witness) ∈ doc.functionBindings) :
    doc.sharedPin htopActive htopAlive function =
      materializedCanonicalWitness (fun concept => concept ∈ doc.active_concepts)
        doc.materialization doc.bottom witness
        ((doc.checkFunctionBindings_iff.mp hcheck (function, witness) hbinding).1.1)
        ((doc.checkFunctionBindings_iff.mp hcheck (function, witness) hbinding).1.2) := by
  have hvalid := doc.checkFunctionBindings_iff.mp hcheck
  have hlookup : doc.bindingWitness function = witness := by
    apply lookupBinding_eq_of_mem doc.top function witness doc.functionBindings
    · intro binding hbinding' other hother
      exact (hvalid binding hbinding').2 other hother
    · exact hbinding
  unfold DecodedCertificate.sharedPin
  rw [hlookup]
  simp only [DecodedCertificate.residualDomainValue]
  split
  · apply Subtype.ext
    rfl
  · rename_i hnot
    exact False.elim (hnot (hvalid (function, witness) hbinding).1)

theorem DecodedCertificate.witnessBinding_mem {n : Nat}
    (doc : DecodedCertificate n)
    (record : CanonicalWitnessRecord (Fin n) (Fin n))
    (hrecord : record ∈ doc.witness_records) :
    (record.function, record.witness) ∈ doc.functionBindings := by
  unfold DecodedCertificate.functionBindings
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨record, hrecord, rfl⟩

theorem DecodedCertificate.residualBinding_mem {n : Nat}
    (doc : DecodedCertificate n)
    (residual : SomeDecodedResidualCompilation n)
    (hresidual : residual ∈ doc.residual_compilations)
    (slot : Fin residual.variableCount) (function : Nat) (witness : Fin n)
    (horigin : residual.decoded.origin slot = .function function witness) :
    (function, witness) ∈ doc.functionBindings := by
  unfold DecodedCertificate.functionBindings
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨residual, hresidual, ?_⟩
  unfold DecodedResidualCompilation.functionBindings
  apply List.mem_filterMap.mpr
  refine ⟨slot, by simp, ?_⟩
  simp [horigin]

theorem DecodedCertificate.checkWitnessRecords_valid {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkWitnessRecords = true)
    (record : CanonicalWitnessRecord (Fin n) (Fin n))
    (hrecord : record ∈ doc.witness_records) :
    record.MaterializedValid (bottom := doc.bottom)
      (fun concept => concept ∈ doc.active_concepts)
      doc.materialization doc.ontology := by
  simp only [DecodedCertificate.checkWitnessRecords, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hvalid := hcheck record hrecord
  simp only [CanonicalWitnessRecord.MaterializedValid]
  simp only [DecodedCertificate.residualValueAlive, Bool.and_eq_true,
    decide_eq_true_eq] at hvalid
  exact ⟨hvalid.1.1.1, hvalid.1.1.2, hvalid.1.2, hvalid.2⟩

theorem DecodedCertificate.checkWitnessRecords_pinCompatible {n : Nat}
    (doc : DecodedCertificate n)
    (htopActive : doc.top ∈ doc.active_concepts)
    (htopAlive : ¬doc.materialization.sub doc.top doc.bottom)
    (hbindings : doc.checkFunctionBindings = true)
    (record : CanonicalWitnessRecord (Fin n) (Fin n))
    (hrecord : record ∈ doc.witness_records) :
    record.MaterializedPinCompatible (bottom := doc.bottom)
      (fun concept => concept ∈ doc.active_concepts) doc.materialization
      (doc.sharedPin htopActive htopAlive) := by
  intro hactive halive
  have hbinding := doc.witnessBinding_mem record hrecord
  simpa using doc.sharedPin_eq_of_binding htopActive htopAlive hbindings
    record.function record.witness hbinding

theorem DecodedCertificate.sharedPin_eq_residualOrigin {n : Nat}
    (doc : DecodedCertificate n)
    (htopActive : doc.top ∈ doc.active_concepts)
    (htopAlive : ¬doc.materialization.sub doc.top doc.bottom)
    (hbindings : doc.checkFunctionBindings = true)
    (residual : SomeDecodedResidualCompilation n)
    (hresidual : residual ∈ doc.residual_compilations)
    (slot : Fin residual.variableCount) (function : Nat) (witness : Fin n)
    (horigin : residual.decoded.origin slot = .function function witness) :
    doc.sharedPin htopActive htopAlive function =
      doc.residualDomainValue htopActive htopAlive witness := by
  have hbinding := doc.residualBinding_mem residual hresidual slot function witness horigin
  have hvalid := (doc.checkFunctionBindings_iff.mp hbindings
    (function, witness) hbinding).1
  calc
    doc.sharedPin htopActive htopAlive function =
        materializedCanonicalWitness
          (fun concept => concept ∈ doc.active_concepts) doc.materialization
          doc.bottom witness hvalid.1 hvalid.2 := by
      simpa using doc.sharedPin_eq_of_binding htopActive htopAlive hbindings
        function witness hbinding
    _ = doc.residualDomainValue htopActive htopAlive witness := by
      apply Subtype.ext
      simp only [DecodedCertificate.residualDomainValue]
      split
      · rfl
      · rename_i hnot
        exact False.elim (hnot hvalid)

theorem DecodedCertificate.residualOrigin_pinCompatible {n : Nat}
    (doc : DecodedCertificate n)
    (htopActive : doc.top ∈ doc.active_concepts)
    (htopAlive : ¬doc.materialization.sub doc.top doc.bottom)
    (hbindings : doc.checkFunctionBindings = true)
    (residual : SomeDecodedResidualCompilation n)
    (hresidual : residual ∈ doc.residual_compilations) :
    ∀ slot function witness,
      residual.decoded.mappedOrigin
          (doc.residualDomainValue htopActive htopAlive) slot =
        .function function witness →
      doc.sharedPin htopActive htopAlive function = witness := by
  intro slot function witness horigin
  cases hsource : residual.decoded.origin slot with
  | source name =>
      simp [DecodedResidualCompilation.mappedOrigin, hsource] at horigin
  | function sourceFunction sourceWitness =>
      simp only [DecodedResidualCompilation.mappedOrigin, hsource] at horigin
      have hfunction := (ResidualVarOrigin.function.inj horigin).1
      have hwitness := (ResidualVarOrigin.function.inj horigin).2
      subst function
      rw [← hwitness]
      exact doc.sharedPin_eq_residualOrigin htopActive htopAlive hbindings
        residual hresidual slot sourceFunction sourceWitness hsource

def SomeDecodedResidualCompilation.toEntry {n : Nat}
    (residual : SomeDecodedResidualCompilation n) {Domain : Type}
    (map : Fin n → Domain)
    (evidence : ResidualCompilationEvidence
      (residual.decoded.mappedOrigin map) residual.decoded.raw
      (residual.decoded.mappedCompiled map)) :
    ResidualCompilationEntry Domain (Fin n) (Fin n) where
  Var := Fin residual.variableCount
  origin := residual.decoded.mappedOrigin map
  raw := residual.decoded.raw
  compiled := residual.decoded.mappedCompiled map
  evidence := evidence

theorem SomeDecodedResidualCompilation.toEntry_pinCompatible {n : Nat}
    (residual : SomeDecodedResidualCompilation n) {Domain : Type}
    (map : Fin n → Domain)
    (evidence : ResidualCompilationEvidence
      (residual.decoded.mappedOrigin map) residual.decoded.raw
      (residual.decoded.mappedCompiled map))
    (pin : Nat → Domain)
    (hcompatible : ∀ slot function witness,
      residual.decoded.mappedOrigin map slot = .function function witness →
        pin function = witness) :
    (residual.toEntry map evidence).pinCompatible pin := by
  exact hcompatible

@[simp] theorem SomeDecodedResidualCompilation.toEntry_raw {n : Nat}
    (residual : SomeDecodedResidualCompilation n) {Domain : Type}
    (map : Fin n → Domain)
    (evidence : ResidualCompilationEvidence
      (residual.decoded.mappedOrigin map) residual.decoded.raw
      (residual.decoded.mappedCompiled map)) :
    (residual.toEntry map evidence).raw = residual.decoded.raw := rfl

@[simp] theorem SomeDecodedResidualCompilation.toEntry_compiledHolds {n : Nat}
    (residual : SomeDecodedResidualCompilation n) {Domain : Type}
    (map : Fin n → Domain)
    (evidence : ResidualCompilationEvidence
      (residual.decoded.mappedOrigin map) residual.decoded.raw
      (residual.decoded.mappedCompiled map))
    {top bottom : Fin n} (I : Interp Domain (Fin n) (Fin n) top bottom) :
    (residual.toEntry map evidence).compiledHolds I ↔
      satCompiledResidualClause I (residual.decoded.mappedCompiled map) :=
  Iff.rfl

def DecodedCertificate.residualModel {n : Nat} (doc : DecodedCertificate n) :
    FiniteResidualModel doc.ResidualDomain (Fin n) (Fin n) :=
  letI : ∀ a b, Decidable (doc.materialization.sub a b) := fun _ _ => by
    dsimp [DecodedCertificate.materialization, traceMaterialization]
    infer_instance
  letI : ∀ a role target, Decidable (doc.materialization.edge a role target) :=
    fun _ _ _ => by
      dsimp [DecodedCertificate.materialization, traceMaterialization]
      infer_instance
  { concept := fun concept value => decide (doc.materialization.sub value.1 concept)
    role := fun role source target =>
      decide (doc.materialization.edge source.1 role target.1) }

/-- Exhaustively evaluate every compiled residual clause on the finite domain
used by `entailsSubWithResidual_iff_finiteMaterialized`. An already inconsistent
EL core needs no residual countermodel. -/
def DecodedCertificate.checkFiniteResiduals {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  letI : ∀ a b, Decidable (doc.materialization.sub a b) := fun _ _ => by
    dsimp [DecodedCertificate.materialization, traceMaterialization]
    infer_instance
  letI : DecidablePred (fun concept : Fin n =>
      concept ∈ doc.active_concepts ∧
        ¬doc.materialization.sub concept doc.bottom) := fun _ => inferInstance
  if hclosed : checkClosedTrace doc.top doc.bottom doc.ontology doc.trace = true then
    if htopActive : doc.top ∈ doc.active_concepts then
      if htopBottom : doc.materialization.sub doc.top doc.bottom then
        true
      else
        let closed := checkClosedTrace_closed hclosed
        let map := doc.residualDomainValue htopActive htopBottom
        let model := doc.residualModel
        have htop : ∀ value, model.concept doc.top value = true := by
          intro value
          simpa [model, DecodedCertificate.residualModel] using
            closed.initTop value.1
        have hbottom : ∀ value, model.concept doc.bottom value = false := by
          intro value
          simpa [model, DecodedCertificate.residualModel] using value.2.2
        doc.checkFunctionBindings && doc.checkWitnessRecords &&
          doc.residual_compilations.all fun residual =>
            doc.residualWitnessesAlive residual.decoded &&
            checkResidualCompilationEvidence
              (residual.decoded.mappedOrigin map) residual.decoded.raw
              (residual.decoded.mappedCompiled map) &&
            checkCompiledResidualClause model doc.top doc.bottom htop hbottom
              (residual.decoded.mappedCompiled map)
    else false
  else false

theorem DecodedCertificate.residualModel_sat_iff {n variableCount : Nat}
    (doc : DecodedCertificate n)
    (closed : ClosedState doc.materialization doc.top doc.bottom doc.ontology)
    (htop : ∀ value, doc.residualModel.concept doc.top value = true)
    (hbottom : ∀ value, doc.residualModel.concept doc.bottom value = false)
    (clause : CompiledResidualClause doc.ResidualDomain (Fin n) (Fin n)
      (Fin variableCount)) :
    satCompiledResidualClause
        (doc.residualModel.toInterp doc.top doc.bottom htop hbottom) clause ↔
      satCompiledResidualClause
        (materializedCanon (fun concept => concept ∈ doc.active_concepts)
          doc.materialization doc.top doc.bottom closed) clause := by
  simp only [satCompiledResidualClause]
  apply forall_congr'
  intro assignment
  apply imp_congr
  · rfl
  apply imp_congr
  · apply forall₂_congr
    intro atom hatom
    cases atom <;> simp [satCompiledResidualAtom,
      DecodedCertificate.residualModel, FiniteResidualModel.toInterp,
      materializedCanon]
  · apply exists_congr
    intro atom
    apply and_congr Iff.rfl
    cases atom <;> simp [satCompiledResidualAtom,
      DecodedCertificate.residualModel, FiniteResidualModel.toInterp,
      materializedCanon]

theorem DecodedCertificate.checkFiniteResiduals_compiled {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom)
    (residual : SomeDecodedResidualCompilation n)
    (hresidual : residual ∈ doc.residual_compilations) :
    let closed := checkClosedTrace_closed (by
      simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
      split at hcheck
      · assumption
      · contradiction)
    let map := doc.residualDomainValue (by
      simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
      split at hcheck
      · split at hcheck
        · assumption
        · contradiction
      · contradiction) hconsistent
    satCompiledResidualClause
      (materializedCanon (fun concept => concept ∈ doc.active_concepts)
        doc.materialization doc.top doc.bottom closed)
      (residual.decoded.mappedCompiled map) := by
  letI : ∀ a b, Decidable (doc.materialization.sub a b) := fun _ _ => by
    dsimp [DecodedCertificate.materialization, traceMaterialization]
    infer_instance
  letI : DecidablePred (fun concept : Fin n =>
      concept ∈ doc.active_concepts ∧
        ¬doc.materialization.sub concept doc.bottom) := fun _ => inferInstance
  simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
  split at hcheck
  · rename_i hclosed
    split at hcheck
    · rename_i htopActive
      let closed := checkClosedTrace_closed hclosed
      let map := doc.residualDomainValue htopActive hconsistent
      let model := doc.residualModel
      have htop : ∀ value, model.concept doc.top value = true := by
        intro value
        simpa [model, DecodedCertificate.residualModel] using
          closed.initTop value.1
      have hbottom : ∀ value, model.concept doc.bottom value = false := by
        intro value
        simpa [model, DecodedCertificate.residualModel] using value.2.2
      simp only [List.all_eq_true, Bool.and_eq_true] at hcheck
      have hclause := hcheck.2 residual hresidual |>.2
      have hsatisfied :=
        (checkCompiledResidualClause_eq_true model doc.top doc.bottom
          htop hbottom (residual.decoded.mappedCompiled map)).mp hclause
      exact (doc.residualModel_sat_iff closed htop hbottom
        (residual.decoded.mappedCompiled map)).mp hsatisfied
    · contradiction
  · contradiction

theorem DecodedCertificate.checkFiniteResiduals_evidence {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom)
    (residual : SomeDecodedResidualCompilation n)
    (hresidual : residual ∈ doc.residual_compilations) :
    let map := doc.residualDomainValue (by
      simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
      split at hcheck
      · split at hcheck
        · assumption
        · contradiction
      · contradiction) hconsistent
    ResidualCompilationEvidence (residual.decoded.mappedOrigin map)
      residual.decoded.raw (residual.decoded.mappedCompiled map) := by
  simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
  split at hcheck
  · split at hcheck
    · rename_i htopActive
      simp only [List.all_eq_true, Bool.and_eq_true] at hcheck
      have hevidence := hcheck.2 residual hresidual |>.1.2
      exact (checkResidualCompilationEvidence_iff
        (residual.decoded.mappedOrigin
          (doc.residualDomainValue htopActive hconsistent))
        residual.decoded.raw
        (residual.decoded.mappedCompiled
          (doc.residualDomainValue htopActive hconsistent))).mp hevidence
    · contradiction
  · contradiction

def DecodedCertificate.certifiedResidualEntries {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom) :
    List (ResidualCompilationEntry doc.ResidualDomain (Fin n) (Fin n)) :=
  let htopActive : doc.top ∈ doc.active_concepts := by
    simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
    split at hcheck
    · split at hcheck
      · assumption
      · contradiction
    · contradiction
  let map := doc.residualDomainValue htopActive hconsistent
  doc.residual_compilations.attach.map fun residual =>
    residual.1.toEntry map
      (doc.checkFiniteResiduals_evidence hcheck hconsistent residual.1 residual.2)

theorem DecodedCertificate.certifiedResidualEntries_raw {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom) :
    (doc.certifiedResidualEntries hcheck hconsistent).map
        ResidualCompilationEntry.raw = doc.residualRawOntology := by
  simp [DecodedCertificate.certifiedResidualEntries,
    DecodedCertificate.residualRawOntology]

theorem DecodedCertificate.checkFiniteResiduals_closed {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true) :
    checkClosedTrace doc.top doc.bottom doc.ontology doc.trace = true := by
  simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
  split at hcheck
  · assumption
  · contradiction

theorem DecodedCertificate.checkFiniteResiduals_topActive {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true) :
    doc.top ∈ doc.active_concepts := by
  simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
  split at hcheck
  · split at hcheck
    · assumption
    · contradiction
  · contradiction

theorem DecodedCertificate.checkFiniteResiduals_functionBindings {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom) :
    doc.checkFunctionBindings = true := by
  simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
  split at hcheck
  · split at hcheck
    · simp only [Bool.and_eq_true] at hcheck
      exact hcheck.1.1
    · contradiction
  · contradiction

theorem DecodedCertificate.checkFiniteResiduals_witnessRecords {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom) :
    doc.checkWitnessRecords = true := by
  simp only [DecodedCertificate.checkFiniteResiduals] at hcheck
  split at hcheck
  · split at hcheck
    · simp only [Bool.and_eq_true] at hcheck
      exact hcheck.1.2
    · contradiction
  · contradiction

theorem DecodedCertificate.certifiedResidualEntries_pinCompatible {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom) :
    ∀ entry ∈ doc.certifiedResidualEntries hcheck hconsistent,
      entry.pinCompatible
        (doc.sharedPin (doc.checkFiniteResiduals_topActive hcheck) hconsistent) := by
  intro entry hentry
  simp only [DecodedCertificate.certifiedResidualEntries, List.mem_map] at hentry
  rcases hentry with ⟨residual, hresidualEntry⟩
  rcases residual with ⟨residual, hresidual⟩
  rw [← hresidualEntry.2]
  apply SomeDecodedResidualCompilation.toEntry_pinCompatible
  exact doc.residualOrigin_pinCompatible
    (doc.checkFiniteResiduals_topActive hcheck) hconsistent
    (doc.checkFiniteResiduals_functionBindings hcheck hconsistent)
    residual hresidual

theorem DecodedCertificate.certifiedResidualEntries_compiled {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkFiniteResiduals = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom) :
    let closed := checkClosedTrace_closed (doc.checkFiniteResiduals_closed hcheck)
    ∀ entry ∈ doc.certifiedResidualEntries hcheck hconsistent,
      entry.compiledHolds
        (materializedCanon (fun concept => concept ∈ doc.active_concepts)
          doc.materialization doc.top doc.bottom closed) := by
  intro closed entry hentry
  simp only [DecodedCertificate.certifiedResidualEntries, List.mem_map] at hentry
  rcases hentry with ⟨residual, hresidualEntry⟩
  rcases residual with ⟨residual, hresidual⟩
  rw [← hresidualEntry.2]
  exact doc.checkFiniteResiduals_compiled hcheck hconsistent residual hresidual

#print axioms DecodedCertificate.residualModel_sat_iff
#print axioms DecodedCertificate.checkFiniteResiduals_compiled
#print axioms DecodedCertificate.checkFiniteResiduals_evidence

theorem DecodedCertificate.checkPartitionedNormalization_direct_models
    {n : Nat} (doc : DecodedCertificate n)
    (J : Interp Domain (ExtendedConcept (Fin n)) (Fin n)
      (.inl doc.top) (.inl doc.bottom))
    (T : RawTermInterp Domain)
    (hcheck : doc.checkPartitionedNormalization = true)
    (hmodels : models J doc.normal_ontology) :
    modelsRaw (projectInterp J) T doc.raw_ontology := by
  simp only [DecodedCertificate.checkPartitionedNormalization] at hcheck
  split at hcheck
  · contradiction
  · rename_i certificate hcertificate
    simp only [Bool.and_eq_true] at hcheck
    have hall : models J
        (certificate.normal.normal ++ doc.witnessNormalOntology) :=
      (models_iff_of_listSetEq J hcheck.2).mp hmodels
    have hnormal : models J certificate.normal.normal :=
      (models_append J certificate.normal.normal doc.witnessNormalOntology).mp hall |>.1
    have hsources : modelsSource (projectInterp J) certificate.sources :=
      certificate.normal.evidence.models_project J hnormal
    exact (certificate.raw.models_iff (projectInterp J) T).mpr hsources

theorem DecodedCertificate.checkPartitionedNormalization_direct_models_materialized
    {n : Nat} (doc : DecodedCertificate n)
    (closed : ClosedState doc.materialization doc.top doc.bottom doc.ontology)
    (hsig : SignatureClosed (fun concept => concept ∈ doc.active_concepts)
      doc.top doc.ontology)
    (T : RawTermInterp doc.ResidualDomain)
    (hnormal : doc.checkPartitionedNormalization = true)
    (horigin : doc.checkOriginOntology = true)
    (hcanonical : doc.checkCanonicalOrigins = true)
    (hpartition : doc.checkSourcePartition = true) :
    modelsRaw
      (materializedCanon (fun concept => concept ∈ doc.active_concepts)
        doc.materialization doc.top doc.bottom closed)
      T doc.raw_ontology := by
  let I := materializedCanon (fun concept => concept ∈ doc.active_concepts)
    doc.materialization doc.top doc.bottom closed
  letI : Nonempty (Fin n) := ⟨doc.top⟩
  let inverse := Function.invFun doc.conceptOrigin
  have hleft : Function.LeftInverse inverse doc.conceptOrigin :=
    Function.leftInverse_invFun doc.conceptOrigin_injective
  have hmodelsI : models I doc.ontology :=
    materializedCanon_models _ doc.materialization closed hsig
  have hmapped : models
      (pushforwardInterp doc.conceptOrigin inverse hleft I)
      (mapOntologyConcept doc.conceptOrigin doc.ontology) :=
    (models_mapConcept_pushforward_iff doc.conceptOrigin inverse hleft I
      doc.ontology).mpr hmodelsI
  have hnormalModels : models
      (pushforwardInterp doc.conceptOrigin inverse hleft I)
      doc.normal_ontology :=
    (models_iff_of_listSetEq
      (pushforwardInterp doc.conceptOrigin inverse hleft I) horigin).mpr hmapped
  simp only [DecodedCertificate.checkCanonicalOrigins, Bool.and_eq_true,
    decide_eq_true_eq] at hcanonical
  rcases hcanonical with ⟨htop, hbottom⟩
  let J := recastInterpEndpoints
    (pushforwardInterp doc.conceptOrigin inverse hleft I) htop hbottom
  have hnormalJ : models J doc.normal_ontology :=
    (models_recastInterpEndpoints_iff
      (pushforwardInterp doc.conceptOrigin inverse hleft I)
      htop hbottom doc.normal_ontology).mpr hnormalModels
  have hraw := doc.checkPartitionedNormalization_direct_models
    J T hnormal hnormalJ
  intro clause hclause
  have hconceptAgreement : ∀ concept ∈ clause.conceptIds, ∀ value,
      I.concept concept value ↔ (projectInterp J).concept concept value := by
    intro concept hconcept value
    have hinverse := hleft concept
    rw [doc.rawConcept_origin hnormal hpartition clause hclause concept hconcept] at hinverse
    simp [I, J, projectInterp, pushforwardInterp, inverse, hinverse]
  have hroleAgreement : ∀ role source target,
      I.role role source target ↔ (projectInterp J).role role source target := by
    intro role source target
    simp [I, J, projectInterp, pushforwardInterp]
  exact (satRawClause_congrOn I (projectInterp J) T clause
    hconceptAgreement hroleAgreement).mpr (hraw clause hclause)

#print axioms DecodedCertificate.checkPartitionedNormalization_direct_models

def DecodedCertificate.checkV5 {n : Nat} (doc : DecodedCertificate n) : Bool :=
  doc.checkCanonicalOrigins && doc.checkOriginOntology &&
    doc.checkSourcePartition && doc.checkNormalizationV5 &&
    doc.residual_compilations.all (fun residual => residual.check) &&
    doc.checkFiniteResiduals && doc.checkSignatureClosed && doc.check

theorem DecodedCertificate.residualCompilation_valid {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true)
    (residual : SomeDecodedResidualCompilation n)
    (hresidual : residual ∈ doc.residual_compilations) :
    ResidualCompilationEvidence residual.decoded.origin residual.decoded.raw
      residual.decoded.compiled := by
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true, List.all_eq_true] at hcheck
  exact (DecodedResidualCompilation.check_iff residual.decoded).mp
    (hcheck.1.1.1.2 residual hresidual)

def DecodedCertificate.sourceResidualTheory {n : Nat}
    (doc : DecodedCertificate n) :
    ResidualTheory (Fin n) (Fin n) doc.top doc.bottom where
  holds := fun I => ∃ T, modelsRawResidual I T doc.source_ontology

theorem DecodedCertificate.checkV5_finiteResiduals {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true) :
    doc.checkFiniteResiduals = true := by
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  exact hcheck.1.1.2

theorem DecodedCertificate.checkV5_sourceResidual_holds {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true)
    (hconsistent : ¬doc.materialization.sub doc.top doc.bottom) :
    doc.sourceResidualTheory.holds
      (materializedCanon (fun concept => concept ∈ doc.active_concepts)
        doc.materialization doc.top doc.bottom
        (checkClosedTrace_closed
          (doc.checkFiniteResiduals_closed
            (doc.checkV5_finiteResiduals hcheck)))) := by
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  have hcanonical := hcheck.1.1.1.1.1.1.1
  have horigin := hcheck.1.1.1.1.1.1.2
  have hpartition := hcheck.1.1.1.1.1.2
  have hnormal := hcheck.1.1.1.1.2
  have hpartitionedNormalization : doc.checkPartitionedNormalization = true := by
    simpa only [DecodedCertificate.checkNormalizationV5] using hnormal
  have hfinite := hcheck.1.1.2
  have hsignature := hcheck.1.2
  let closed := checkClosedTrace_closed (doc.checkFiniteResiduals_closed hfinite)
  let htopActive := doc.checkFiniteResiduals_topActive hfinite
  let topValue := doc.residualDomainValue htopActive hconsistent doc.top
  let base : RawTermInterp doc.ResidualDomain := {
    individual := fun _ => topValue
    auxiliary := fun _ _ => topValue
    function := fun _ _ => topValue
  }
  let pin := doc.sharedPin htopActive hconsistent
  let entries := doc.certifiedResidualEntries hfinite hconsistent
  have hsig := doc.checkSignatureClosed_iff.mp hsignature
  have hdirect : modelsRaw
      (materializedCanon (fun concept => concept ∈ doc.active_concepts)
        doc.materialization doc.top doc.bottom closed)
      (pinnedTermInterp base pin) doc.raw_ontology :=
    doc.checkPartitionedNormalization_direct_models_materialized closed hsig
      (pinnedTermInterp base pin) hpartitionedNormalization horigin hcanonical hpartition
  have hvalid : ∀ record ∈ doc.witness_records,
      record.MaterializedValid (bottom := doc.bottom)
        (fun concept => concept ∈ doc.active_concepts)
        doc.materialization doc.ontology :=
    doc.checkWitnessRecords_valid
      (doc.checkFiniteResiduals_witnessRecords hfinite hconsistent)
  have hpins : ∀ record ∈ doc.witness_records,
      record.MaterializedPinCompatible (bottom := doc.bottom)
        (fun concept => concept ∈ doc.active_concepts) doc.materialization pin :=
    doc.checkWitnessRecords_pinCompatible htopActive hconsistent
      (doc.checkFiniteResiduals_functionBindings hfinite hconsistent)
  have hcompatible : ∀ entry ∈ entries, entry.pinCompatible pin := by
    exact doc.certifiedResidualEntries_pinCompatible hfinite hconsistent
  have hcompiled : ∀ entry ∈ entries,
      entry.compiledHolds
        (materializedCanon (fun concept => concept ∈ doc.active_concepts)
          doc.materialization doc.top doc.bottom closed) := by
    exact doc.certifiedResidualEntries_compiled hfinite hconsistent
  have hpartitioned := materialized_partitionedRawOntology_satisfies_source
    (fun concept => concept ∈ doc.active_concepts) doc.ontology
    doc.materialization closed
    (partitionedRawOntology doc.raw_ontology doc.witness_records entries)
    doc.raw_ontology doc.witness_records entries base pin rfl hdirect hvalid hpins
    hcompatible hcompiled
  have hentriesRaw : entries.map ResidualCompilationEntry.raw =
      doc.residualRawOntology :=
    doc.certifiedResidualEntries_raw hfinite hconsistent
  have hpartitionedEq :
      partitionedRawOntology doc.raw_ontology doc.witness_records entries =
        doc.partitionedSourceOntology := by
    unfold partitionedRawOntology residualCompilationRawOntology
      DecodedCertificate.partitionedSourceOntology
    rw [hentriesRaw]
  refine ⟨pinnedTermInterp base pin, ?_⟩
  intro clause hclause
  apply hpartitioned clause
  rw [hpartitionedEq]
  exact (doc.checkSourcePartition_iff.mp hpartition clause).mp hclause

theorem DecodedCertificate.checkV5_entailsSubWithResidual_exact {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true)
    (a b : Fin n) (hactive : a ∈ doc.active_concepts) :
    EntailsSubWithResidual doc.ontology doc.sourceResidualTheory a b ↔
      doc.materialization.sub a doc.bottom ∨ doc.materialization.sub a b := by
  have hcheckV5 := hcheck
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  have hfinite := hcheck.1.1.2
  have hsignature := hcheck.1.2
  have hcore := hcheck.2
  let closed := checkClosedTrace_closed (doc.checkFiniteResiduals_closed hfinite)
  have hsound : SoundState doc.materialization doc.top doc.bottom doc.ontology := by
    simp only [DecodedCertificate.check, Bool.and_eq_true] at hcore
    exact checkedTrace_soundState hcore.1.1.1.1
  have hsig := doc.checkSignatureClosed_iff.mp hsignature
  by_cases hconsistent : ¬doc.materialization.sub doc.top doc.bottom
  · exact entailsSubWithResidual_iff_finiteMaterialized closed hsound
      (fun concept => concept ∈ doc.active_concepts) hsig doc.sourceResidualTheory
      (doc.checkV5_sourceResidual_holds hcheckV5 hconsistent)
      a b hactive
  · have htopBottom : doc.materialization.sub doc.top doc.bottom :=
      Classical.not_not.mp hconsistent
    have hunsat : Unsatisfiable (top := doc.top) (bottom := doc.bottom)
        doc.ontology := (unsat_iff_materialized closed hsound).mpr htopBottom
    have haBottom : doc.materialization.sub a doc.bottom := by
      have hentails : EntailsSub (top := doc.top) (bottom := doc.bottom)
          doc.ontology a doc.bottom := by
        intro Domain I hmodels x _
        letI : Nonempty Domain := ⟨x⟩
        exact False.elim (hunsat I hmodels)
      rcases (entails_iff_materialized closed hsound a doc.bottom).mp hentails with
        hbottom | hbottom
      · exact hbottom
      · exact hbottom
    constructor
    · intro _
      exact Or.inl haBottom
    · intro _
      exact bottom_sound_withResidual (hsound.subSound haBottom)

theorem DecodedCertificate.checkV5_unsatisfiableWithResidual_exact {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true) :
    UnsatisfiableWithResidual doc.ontology doc.sourceResidualTheory ↔
      doc.materialization.sub doc.top doc.bottom := by
  have hcheckV5 := hcheck
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  have hfinite := hcheck.1.1.2
  have hsignature := hcheck.1.2
  have hcore := hcheck.2
  let closed := checkClosedTrace_closed (doc.checkFiniteResiduals_closed hfinite)
  have hsound : SoundState doc.materialization doc.top doc.bottom doc.ontology := by
    simp only [DecodedCertificate.check, Bool.and_eq_true] at hcore
    exact checkedTrace_soundState hcore.1.1.1.1
  have hsig := doc.checkSignatureClosed_iff.mp hsignature
  by_cases hconsistent : ¬doc.materialization.sub doc.top doc.bottom
  · exact unsatisfiableWithResidual_iff_finiteMaterialized closed hsound
      (fun concept => concept ∈ doc.active_concepts) hsig doc.sourceResidualTheory
      (doc.checkV5_sourceResidual_holds hcheckV5 hconsistent)
  · have htopBottom : doc.materialization.sub doc.top doc.bottom :=
      Classical.not_not.mp hconsistent
    constructor
    · intro _
      exact htopBottom
    · intro _
      exact top_bottom_sound_withResidual (hsound.subSound htopBottom)

#print axioms DecodedCertificate.residualCompilation_valid

theorem DecodedCertificate.checkNormalization_models_iff {n : Nat}
    (doc : DecodedCertificate n) (I : Interp Domain (Fin n) (Fin n) doc.top doc.bottom)
    (base : RawTermInterp Domain) (hcheck : doc.checkNormalization = true) :
    (∃ T, modelsRaw I T doc.raw_ontology) ↔ models (extendInterp I) doc.normal_ontology := by
  simp only [DecodedCertificate.checkNormalization] at hcheck
  split at hcheck
  · contradiction
  · rename_i certificate hcertificate
    simp only [Bool.and_eq_true] at hcheck
    rw [certificate.models_iff I base]
    exact (models_iff_of_listSetEq (extendInterp I) hcheck.2).symm

theorem DecodedCertificate.rustFact_iff {n : Nat} (doc : DecodedCertificate n)
    (hagree : doc.checkStateAgreement = true) {fact : Fact (Fin n) (Fin n)}
    (hactive : fact.source ∈ doc.active_concepts) :
    fact ∈ doc.rust_facts ↔
      fact ∈ doc.trace.map (Step.conclusion doc.top doc.bottom) := by
  simp only [DecodedCertificate.checkStateAgreement, DecodedCertificate.checkFactAgreement,
    Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hagree
  constructor
  · intro hrust
    exact (hagree.1.1 fact hrust).1
  · intro hformal
    have h := hagree.1.2 fact hformal
    simp only [hactive, if_true, decide_eq_true_eq] at h
    exact h

theorem DecodedCertificate.rustFact_active {n : Nat} (doc : DecodedCertificate n)
    (hagree : doc.checkStateAgreement = true) {fact : Fact (Fin n) (Fin n)}
    (hfact : fact ∈ doc.rust_facts) : fact.source ∈ doc.active_concepts := by
  simp only [DecodedCertificate.checkStateAgreement, DecodedCertificate.checkFactAgreement,
    Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hagree
  exact (hagree.1.1 fact hfact).2

theorem DecodedCertificate.check_exact {n : Nat} (doc : DecodedCertificate n)
    (hcheck : doc.check = true) :
    (∀ a b, EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b ↔
      (traceMaterialization doc.top doc.bottom doc.trace).sub a doc.bottom ∨
        (traceMaterialization doc.top doc.bottom doc.trace).sub a b) ∧
    (Unsatisfiable (top := doc.top) (bottom := doc.bottom) doc.ontology ↔
      (traceMaterialization doc.top doc.bottom doc.trace).sub doc.top doc.bottom) := by
  simp only [DecodedCertificate.check, Bool.and_eq_true] at hcheck
  exact checkedTrace_exact hcheck.1.1.1.1 hcheck.1.1.1.2

theorem DecodedCertificate.active_subsumption_exact {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true)
    {a b : Fin n} (hactive : a ∈ doc.active_concepts) :
    EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b ↔
      Fact.sub a doc.bottom ∈ doc.rust_facts ∨ Fact.sub a b ∈ doc.rust_facts := by
  have exact := doc.check_exact hcheck
  simp only [DecodedCertificate.check, Bool.and_eq_true] at hcheck
  rw [exact.1 a b]
  constructor
  · intro h
    rcases h with hbottom | hsub
    · exact Or.inl ((doc.rustFact_iff hcheck.1.1.2
        (fact := Fact.sub a doc.bottom) hactive).2 hbottom)
    · exact Or.inr ((doc.rustFact_iff hcheck.1.1.2
        (fact := Fact.sub a b) hactive).2 hsub)
  · intro h
    rcases h with hbottom | hsub
    · exact Or.inl ((doc.rustFact_iff hcheck.1.1.2
        (fact := Fact.sub a doc.bottom) hactive).1 hbottom)
    · exact Or.inr ((doc.rustFact_iff hcheck.1.1.2
        (fact := Fact.sub a b) hactive).1 hsub)

theorem DecodedCertificate.publicSub_iff_expected {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {a b : Fin n} :
    (a, b) ∈ doc.public_subsumptions ↔ (a, b) ∈ doc.expectedPublicOutput := by
  simp only [DecodedCertificate.check, Bool.and_eq_true,
    DecodedCertificate.checkPublicOutput, List.all_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.2.1 (a, b), hcheck.1.2.2 (a, b)⟩

theorem DecodedCertificate.public_subsumption_sound {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {a b : Fin n}
    (hpublic : (a, b) ∈ doc.public_subsumptions) :
    EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b := by
  have hcert := hcheck
  have hexpected := (doc.publicSub_iff_expected hcheck).1 hpublic
  simp only [DecodedCertificate.expectedPublicOutput, List.mem_filterMap] at hexpected
  rcases hexpected with ⟨fact, hfact, hdecoded⟩
  cases fact with
  | edge source role target => simp at hdecoded
  | sub sub sup =>
      simp only at hdecoded
      split at hdecoded
      · simp only [Option.some.injEq, Prod.mk.injEq] at hdecoded
        obtain ⟨hsub, hsup⟩ := hdecoded
        subst sub
        subst sup
        simp only [DecodedCertificate.check, Bool.and_eq_true] at hcheck
        have hactive := doc.rustFact_active hcheck.1.1.2 hfact
        change a ∈ doc.active_concepts at hactive
        rw [doc.active_subsumption_exact hcert hactive]
        exact Or.inr hfact
      · simp at hdecoded

theorem DecodedCertificate.public_subsumption_sound_source {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true) {a b : Fin n}
    (hpublic : (a, b) ∈ doc.public_subsumptions) :
    EntailsSubWithResidual doc.ontology doc.sourceResidualTheory a b := by
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  have hcore := hcheck.2
  have hsound : EntailsSub (top := doc.top) (bottom := doc.bottom)
      doc.ontology a b := doc.public_subsumption_sound hcore hpublic
  intro Domain I hmodels x hsub
  exact hsound I hmodels.1 x hsub

theorem DecodedCertificate.public_subsumption_complete_of_satisfiable {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {a b : Fin n}
    (hactive : a ∈ doc.active_concepts)
    (haTop : a ≠ doc.top) (haBottom : a ≠ doc.bottom)
    (hba : b ≠ a) (hbTop : b ≠ doc.top)
    (hsatisfiable : ¬ EntailsSub (top := doc.top) (bottom := doc.bottom)
      doc.ontology a doc.bottom)
    (hentails : EntailsSub (top := doc.top) (bottom := doc.bottom)
      doc.ontology a b) :
    (a, b) ∈ doc.public_subsumptions := by
  have hrust := (doc.active_subsumption_exact hcheck hactive).1 hentails
  rcases hrust with hbottom | hsub
  · exact False.elim (hsatisfiable
      ((doc.active_subsumption_exact hcheck hactive).2 (Or.inl hbottom)))
  · apply (doc.publicSub_iff_expected hcheck).2
    simp only [DecodedCertificate.expectedPublicOutput, List.mem_filterMap]
    refine ⟨Fact.sub a b, hsub, ?_⟩
    simp [haTop, haBottom, hba, hbTop]

/-- Exact public taxonomy row contract. A public pair is equivalent to semantic
subsumption whenever it is either the distinguished bottom edge (the complete
representation of an unsatisfiable class) or the source class is satisfiable.
This is the classifier-facing partition used by Rust's output format. -/
theorem DecodedCertificate.public_subsumption_exact {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {a b : Fin n}
    (hactive : a ∈ doc.active_concepts)
    (haTop : a ≠ doc.top) (haBottom : a ≠ doc.bottom)
    (hba : b ≠ a) (hbTop : b ≠ doc.top)
    (hcase : b = doc.bottom ∨
      ¬ EntailsSub (top := doc.top) (bottom := doc.bottom)
        doc.ontology a doc.bottom) :
    (a, b) ∈ doc.public_subsumptions ↔
      EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b := by
  constructor
  · exact fun hpublic => doc.public_subsumption_sound hcheck hpublic
  · intro hentails
    rcases hcase with rfl | hsatisfiable
    · have hrust : Fact.sub a doc.bottom ∈ doc.rust_facts := by
        rcases (doc.active_subsumption_exact hcheck hactive).1 hentails with
          hbottom | hbottom
        · exact hbottom
        · exact hbottom
      apply (doc.publicSub_iff_expected hcheck).2
      simp only [DecodedCertificate.expectedPublicOutput, List.mem_filterMap]
      refine ⟨Fact.sub a doc.bottom, hrust, ?_⟩
      simp [haTop, haBottom, hba, doc.top_ne_bottom.symm]
    · exact doc.public_subsumption_complete_of_satisfiable hcheck hactive
        haTop haBottom hba hbTop hsatisfiable hentails

theorem DecodedCertificate.public_subsumption_complete_source_of_satisfiable
    {n : Nat} (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true)
    {a b : Fin n} (hactive : a ∈ doc.active_concepts)
    (haTop : a ≠ doc.top) (haBottom : a ≠ doc.bottom)
    (hba : b ≠ a) (hbTop : b ≠ doc.top)
    (hsatisfiable : ¬ EntailsSubWithResidual doc.ontology
      doc.sourceResidualTheory a doc.bottom)
    (hentails : EntailsSubWithResidual doc.ontology
      doc.sourceResidualTheory a b) :
    (a, b) ∈ doc.public_subsumptions := by
  have hcheckV5 := hcheck
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  have hcore := hcheck.2
  have hexact := doc.checkV5_entailsSubWithResidual_exact hcheckV5
  have hmat := (hexact a b hactive).mp hentails
  have hcoreEntails : EntailsSub (top := doc.top) (bottom := doc.bottom)
      doc.ontology a b := (doc.check_exact hcore).1 a b |>.mpr hmat
  have hcoreSatisfiable : ¬EntailsSub (top := doc.top) (bottom := doc.bottom)
      doc.ontology a doc.bottom := by
    intro hbottom
    apply hsatisfiable
    intro Domain I hmodels x hsub
    exact hbottom I hmodels.1 x hsub
  exact doc.public_subsumption_complete_of_satisfiable hcore hactive
    haTop haBottom hba hbTop hcoreSatisfiable hcoreEntails

/-- Source/residual counterpart of `public_subsumption_exact`. Successful V5
checking therefore gives an exact public taxonomy representation for every
eligible active source: one bottom row for an unsatisfiable source, otherwise
all and only its semantic superclasses. -/
theorem DecodedCertificate.public_subsumption_source_exact
    {n : Nat} (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true)
    {a b : Fin n} (hactive : a ∈ doc.active_concepts)
    (haTop : a ≠ doc.top) (haBottom : a ≠ doc.bottom)
    (hba : b ≠ a) (hbTop : b ≠ doc.top)
    (hcase : b = doc.bottom ∨
      ¬ EntailsSubWithResidual doc.ontology doc.sourceResidualTheory
        a doc.bottom) :
    (a, b) ∈ doc.public_subsumptions ↔
      EntailsSubWithResidual doc.ontology doc.sourceResidualTheory a b := by
  have hcheckV5 := hcheck
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  have hcore := hcheck.2
  constructor
  · exact fun hpublic => doc.public_subsumption_sound_source hcheckV5 hpublic
  · intro hentails
    rcases hcase with rfl | hsatisfiable
    · have hmat := (doc.checkV5_entailsSubWithResidual_exact hcheckV5
          a doc.bottom hactive).mp hentails
      have hcoreEntails : EntailsSub (top := doc.top) (bottom := doc.bottom)
          doc.ontology a doc.bottom := (doc.check_exact hcore).1 a doc.bottom |>.mpr hmat
      exact (doc.public_subsumption_exact hcore hactive haTop haBottom hba hbTop
        (Or.inl rfl)).2 hcoreEntails
    · exact doc.public_subsumption_complete_source_of_satisfiable hcheckV5
        hactive haTop haBottom hba hbTop hsatisfiable hentails

theorem DecodedCertificate.namedSub_iff_expected {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {sub sup : String} :
    (sub, sup) ∈ doc.public_named_subsumptions ↔
      (sub, sup) ∈ doc.expectedNamedOutput := by
  simp only [DecodedCertificate.check, Bool.and_eq_true,
    DecodedCertificate.checkNamedOutput, List.all_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.2.1.1 (sub, sup), hcheck.2.1.2 (sub, sup)⟩

theorem DecodedCertificate.public_named_subsumption_sound {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {sub sup : String}
    (hpublic : (sub, sup) ∈ doc.public_named_subsumptions) :
    ∃ a b, (a, b) ∈ doc.public_subsumptions ∧
      doc.symbols a = sub ∧
      (if b = doc.bottom then "owl:Nothing" else doc.symbols b) = sup ∧
      EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b := by
  have hexpected := (doc.namedSub_iff_expected hcheck).1 hpublic
  simp only [DecodedCertificate.expectedNamedOutput, List.mem_map] at hexpected
  rcases hexpected with ⟨⟨a, b⟩, hab, hnames⟩
  simp only [Prod.mk.injEq] at hnames
  exact ⟨a, b, hab, hnames.1, hnames.2,
    doc.public_subsumption_sound hcheck hab⟩

theorem DecodedCertificate.public_named_subsumption_complete_of_satisfiable {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {a b : Fin n}
    (hactive : a ∈ doc.active_concepts)
    (haTop : a ≠ doc.top) (haBottom : a ≠ doc.bottom)
    (hba : b ≠ a) (hbTop : b ≠ doc.top)
    (hsatisfiable : ¬ EntailsSub (top := doc.top) (bottom := doc.bottom)
      doc.ontology a doc.bottom)
    (hentails : EntailsSub (top := doc.top) (bottom := doc.bottom)
      doc.ontology a b) :
    (doc.symbols a, if b = doc.bottom then "owl:Nothing" else doc.symbols b) ∈
      doc.public_named_subsumptions := by
  apply (doc.namedSub_iff_expected hcheck).2
  simp only [DecodedCertificate.expectedNamedOutput, List.mem_map]
  exact ⟨(a, b), doc.public_subsumption_complete_of_satisfiable hcheck hactive
    haTop haBottom hba hbTop hsatisfiable hentails, rfl⟩

theorem DecodedCertificate.public_named_subsumption_complete_source_of_satisfiable
    {n : Nat} (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true)
    {a b : Fin n} (hactive : a ∈ doc.active_concepts)
    (haTop : a ≠ doc.top) (haBottom : a ≠ doc.bottom)
    (hba : b ≠ a) (hbTop : b ≠ doc.top)
    (hsatisfiable : ¬ EntailsSubWithResidual doc.ontology
      doc.sourceResidualTheory a doc.bottom)
    (hentails : EntailsSubWithResidual doc.ontology
      doc.sourceResidualTheory a b) :
    (doc.symbols a, if b = doc.bottom then "owl:Nothing" else doc.symbols b) ∈
      doc.public_named_subsumptions := by
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  apply (doc.namedSub_iff_expected hcheck.2).2
  simp only [DecodedCertificate.expectedNamedOutput, List.mem_map]
  exact ⟨(a, b), doc.public_subsumption_complete_source_of_satisfiable
    (by simpa only [DecodedCertificate.checkV5, Bool.and_eq_true] using hcheck)
    hactive haTop haBottom hba hbTop hsatisfiable hentails, rfl⟩

theorem DecodedCertificate.top_active {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) :
    doc.top ∈ doc.active_concepts := by
  simp only [DecodedCertificate.check, Bool.and_eq_true] at hcheck
  have hagree := hcheck.1.1.2
  simp only [DecodedCertificate.checkStateAgreement,
    DecodedCertificate.checkActiveConcepts, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hagree
  apply hagree.2.2 doc.top
  simp [DecodedCertificate.expectedActiveConcepts, doc.top_ne_bottom]

theorem DecodedCertificate.public_inconsistent_exact {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) :
    doc.public_inconsistent = true ↔
      Unsatisfiable (top := doc.top) (bottom := doc.bottom) doc.ontology := by
  have hcert := hcheck
  simp only [DecodedCertificate.check, Bool.and_eq_true] at hcheck
  have hagree := hcheck.1.1.2
  have hnamed := hcheck.2
  simp only [DecodedCertificate.checkNamedOutput, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hnamed
  have hactive := doc.top_active hcert
  have hfactActive :
      (Fact.sub doc.top doc.bottom : Fact (Fin n) (Fin n)).source ∈ doc.active_concepts := by
    exact hactive
  have hexact := (doc.check_exact hcert).2
  constructor
  · intro hpublic
    have hdecide : decide (Fact.sub doc.top doc.bottom ∈ doc.rust_facts) = true := by
      rw [← hnamed.2]
      exact hpublic
    have hrust := of_decide_eq_true hdecide
    have htrace := (doc.rustFact_iff hagree hfactActive).1 hrust
    rw [hexact]
    exact htrace
  · intro hunsat
    rw [hexact] at hunsat
    have hrust := (doc.rustFact_iff hagree hfactActive).2 hunsat
    have hdecide : decide (Fact.sub doc.top doc.bottom ∈ doc.rust_facts) = true :=
      decide_eq_true hrust
    rw [hnamed.2, hdecide]

theorem DecodedCertificate.public_inconsistent_source_exact {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true) :
    doc.public_inconsistent = true ↔
      UnsatisfiableWithResidual doc.ontology doc.sourceResidualTheory := by
  have hcheckV5 := hcheck
  simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheck
  have hcore := hcheck.2
  rw [doc.public_inconsistent_exact hcore]
  rw [unsat_iff_materialized
    (checkClosedTrace_closed
      (doc.checkFiniteResiduals_closed hcheck.1.1.2))
    (by
      simp only [DecodedCertificate.check, Bool.and_eq_true] at hcore
      exact checkedTrace_soundState hcore.1.1.1.1)]
  exact (doc.checkV5_unsatisfiableWithResidual_exact hcheckV5).symm

#print axioms DecodedCertificate.checkV5_sourceResidual_holds
#print axioms DecodedCertificate.checkV5_entailsSubWithResidual_exact
#print axioms DecodedCertificate.checkV5_unsatisfiableWithResidual_exact
#print axioms DecodedCertificate.public_subsumption_sound_source
#print axioms DecodedCertificate.public_subsumption_complete_source_of_satisfiable
#print axioms DecodedCertificate.public_subsumption_exact
#print axioms DecodedCertificate.public_subsumption_source_exact
#print axioms DecodedCertificate.public_inconsistent_source_exact

def WireCertificate.check (doc : WireCertificate) : Except String Bool := do
  return (← doc.decode).checkV5

namespace WireExamples

def residualCompilation : WireResidualCompilation where
  variable_count := 2
  origins := [.source 0, .function 2 2]
  raw := {
    body := [.concept 0 (.var 0)]
    head := [.role 1 (.var 0) (.fun 2 (.var 0))]
  }
  body := [.concept 0 0]
  head := [.role 1 0 1]
  pins := [(1, 2)]

example : residualCompilation.check 3 = .ok true := by native_decide

example : { residualCompilation with pins := [(0, 2)] }.check 3 = .ok false := by
  native_decide

example : { residualCompilation with origins := [.source 0] }.check 3 =
    .error "residual origin table has length 1, expected 2" := by native_decide

def empty : WireCertificate where
  version := 5
  symbol_count := 2
  top := 0
  bottom := 1
  variable_count := 0
  source_ontology := []
  raw_ontology := []
  witness_records := []
  residual_compilations := []
  concept_origins := [.source, .source]
  ontology := []
  trace := [.refl 0, .top 0, .refl 1, .top 1]
  active_concepts := [0]
  rust_subsumptions := [{ sub := 0, sup := 0 }]
  rust_edges := []
  public_subsumptions := []
  symbols := ["top", "bottom"]
  public_named_subsumptions := []
  public_inconsistent := false

example : empty.check = .ok true := by native_decide

example : { empty with variable_count := 1, source_ontology := [{
    body := []
    head := [.concept 0 (.var 0)]
  }] }.check = .ok false := by native_decide

example : { empty with version := 4 }.check =
    .error "unsupported ELC certificate version 4" := by native_decide

example : { empty with top := 2 }.check = .error "symbol id 2 is outside [0,2)" := by
  native_decide

end WireExamples

end ContextCalculus.ELCompletion

import ContextCalculus.CBRoleChainGroundCompleteness

/-!
# Finite grounding with a separate source-individual type

The original `CompletenessEq` presentation uses one type both for source
individual names and for the finite Herbrand carrier. Production KM has a
fixed source individual table and a generally larger blocked term universe.
This module separates them by mapping every source name into the carrier,
applies the complete role-chain ground theorem there, and transports the
quotient interpretation back to the original source signature.
-/

namespace ContextCalculus.CBNamedGroundCompleteness

open ContextCalculus Eqv CBRoleChainEncoding
open ContextCalculus.CBRoleChainGroundCompleteness

variable {CN RN Individual Carrier : Type}

def mapIndividualClause (name : Individual → Carrier) :
    OClause CN RN Individual → OClause CN RN Carrier
  | .gci body head => .gci body head
  | .exR source role filler => .exR source role filler
  | .allR source role filler => .allR source role filler
  | .exL role filler conclusion => .exL role filler conclusion
  | .subR sub sup => .subR sub sup
  | .inv role inverse => .inv role inverse
  | .func role => .func role
  | .nom concept individual => .nom concept (name individual)
  | .atMost cardinality role concept => .atMost cardinality role concept

def mapIndividuals (name : Individual → Carrier)
    (source : SourceOntology CN RN Individual) : SourceOntology CN RN Carrier :=
  { clauses := source.clauses.map (mapIndividualClause name)
    chains := source.chains
    roleAxioms := source.roleAxioms }

def restrictIndividualNames (name : Individual → Carrier)
    (interpretation : Interp D CN RN Carrier) : Interp D CN RN Individual where
  c := interpretation.c
  r := interpretation.r
  nm individual := interpretation.nm (name individual)

theorem satO_mapIndividualClause_iff (name : Individual → Carrier)
    (interpretation : Interp D CN RN Carrier) (clause : OClause CN RN Individual) :
    satO interpretation (mapIndividualClause name clause) ↔
      satO (restrictIndividualNames name interpretation) clause := by
  cases clause <;> rfl

theorem models_mapIndividuals_iff (name : Individual → Carrier)
    (interpretation : Interp D CN RN Carrier)
    (source : SourceOntology CN RN Individual) :
    CBRoleChainEncoding.models interpretation (mapIndividuals name source) ↔
      CBRoleChainEncoding.models
        (restrictIndividualNames name interpretation) source := by
  constructor
  · rintro ⟨hclauses, hchains, hroleAxioms⟩
    constructor
    · intro clause hclause
      apply (satO_mapIndividualClause_iff name interpretation clause).mp
      apply hclauses
      exact List.mem_map.mpr ⟨clause, hclause, rfl⟩
    · constructor
      · intro chain hchain
        exact hchains chain (by simpa [mapIndividuals] using hchain)
      · intro roleAxiom hroleAxiom
        exact hroleAxioms roleAxiom (by simpa [mapIndividuals] using hroleAxiom)
  · rintro ⟨hclauses, hchains, hroleAxioms⟩
    constructor
    · intro mapped hmapped
      simp only [mapIndividuals, List.mem_map] at hmapped
      obtain ⟨clause, hclause, rfl⟩ := hmapped
      apply (satO_mapIndividualClause_iff name interpretation clause).mpr
      exact hclauses clause hclause
    · constructor
      · intro chain hchain
        exact hchains chain (by simpa [mapIndividuals] using hchain)
      · intro roleAxiom hroleAxiom
        exact hroleAxioms roleAxiom (by simpa [mapIndividuals] using hroleAxiom)

section FiniteCarrier

variable [DecidableEq CN] [DecidableEq RN] [DecidableEq Carrier]
  [Fintype CN] [Fintype RN] [Fintype Carrier]

def namedGroundSource (name : Individual → Carrier)
    (wit : CN → RN → CN → Carrier → Carrier)
    (source : SourceOntology CN RN Individual) :=
  groundSource wit (mapIndividuals name source)

theorem source_complete_ground_named
    (name : Individual → Carrier)
    (wit : CN → RN → CN → Carrier → Carrier)
    (source : SourceOntology CN RN Individual)
    (hclash : ¬ PropRes.Derivable (namedGroundSource name wit source)
      PropRes.PClause.bot) :
    ∃ (D : Type) (interpretation : Interp D CN RN Individual),
      CBRoleChainEncoding.models interpretation source := by
  obtain ⟨D, carrierInterpretation, hmodels⟩ :=
    source_complete_ground wit (mapIndividuals name source) hclash
  exact ⟨D, restrictIndividualNames name carrierInterpretation,
    (models_mapIndividuals_iff name carrierInterpretation source).mp hmodels⟩

#print axioms satO_mapIndividualClause_iff
#print axioms models_mapIndividuals_iff
#print axioms source_complete_ground_named

end FiniteCarrier

end ContextCalculus.CBNamedGroundCompleteness

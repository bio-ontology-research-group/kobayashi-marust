import ContextCalculus.CBBlockedGroundSaturationWire

/-!
# Query-augmented blocked countermodels for exact CB taxonomy

The production blocked grounding already proves consistency by saturating the
complete finite ground source and constructing its equality-quotient model.
For a negative taxonomy cell we add two exact unit clauses at one blocked
carrier element: the subclass is true and the claimed superclass is false.
If resolution saturation of that augmented grounding remains open, the same
quotient construction gives a source model that refutes the subsumption.
-/

namespace ContextCalculus.CBBlockedTaxonomyCountermodel

open ContextCalculus PropRes Equiv Eqv
open ContextCalculus.CBCert
open ContextCalculus.CBBlockedCarrierWire
open ContextCalculus.CBBlockedGroundSaturationWire
open ContextCalculus.CBFiniteAtomEncoding
open ContextCalculus.CBNamedGroundCompleteness
open ContextCalculus.CBRoleChainGroundCompleteness
open ContextCalculus.CBRoleChainEncoding

def positiveQueryClause (sub : Fin conceptCount) (witness : Fin carrierCount) :
    PClause (GroundAtom conceptCount roleCount carrierCount) :=
  clImp [] [.con sub witness]

def negativeQueryClause (sup : Fin conceptCount) (witness : Fin carrierCount) :
    PClause (GroundAtom conceptCount roleCount carrierCount) :=
  clImp [.con sup witness] []

def blockedQueryGround (carrier : DecodedBlockedCarrierDocument)
    (sub sup : Fin (productionRun carrier.admissibility).source.bounds.concepts)
    (witness : carrier.Carrier) :=
  insert (positiveQueryClause sub witness)
    (insert (negativeQueryClause sup witness) (blockedGround carrier))

def encodedBlockedQueryGround (carrier : DecodedBlockedCarrierDocument)
    (sub sup : Fin (productionRun carrier.admissibility).source.bounds.concepts)
    (witness : carrier.Carrier) :=
  encodeSet (blockedQueryGround carrier sub sup witness)

theorem blockedQueryGround_countermodel
    (carrier : DecodedBlockedCarrierDocument)
    (sub sup : Fin (productionRun carrier.admissibility).source.bounds.concepts)
    (witness : carrier.Carrier)
    (terminal : Finset (PClause (Fin (blockedAtomCount carrier))))
    (saturation : Saturation
      (encodedBlockedQueryGround carrier sub sup witness) terminal)
    (hbot : PClause.bot ∉ terminal) :
    ∃ (D : Type) (interpretation : Interp D
        (Fin (productionRun carrier.admissibility).source.bounds.concepts)
        (Fin (productionRun carrier.admissibility).source.bounds.roles)
        (Fin (productionRun carrier.admissibility).source.bounds.individuals))
        (element : D),
      CBRoleChainEncoding.models interpretation (blockedSource carrier) ∧
      interpretation.c sub element ∧ ¬interpretation.c sup element := by
  have hencodedSat : ¬PropRes.Unsat
      (encodedBlockedQueryGround carrier sub sup witness) := by
    intro hunsat
    exact hbot ((saturation_refutes_iff_unsat saturation).mpr hunsat)
  have hexists : ∃ valuation : Fin (blockedAtomCount carrier) → Prop,
      ∀ clause ∈ encodedBlockedQueryGround carrier sub sup witness,
        clause.sat valuation := by
    by_contra hnone
    exact hencodedSat hnone
  obtain ⟨valuation, hvaluation⟩ := hexists
  have hqueryModels : ∀ clause ∈ blockedQueryGround carrier sub sup witness,
      clause.sat (fun atom => valuation (atomIndex atom)) :=
    (models_encodeSet_iff valuation
      (blockedQueryGround carrier sub sup witness)).mp hvaluation
  have hblockedModels : ∀ clause ∈ blockedGround carrier,
      clause.sat (fun atom => valuation (atomIndex atom)) := by
    intro clause hclause
    exact hqueryModels clause (by
      simp only [blockedQueryGround, Finset.mem_insert]
      exact Or.inr (Or.inr hclause))
  let hbase : ∀ clause ∈ Eqv.ground carrier.witness
      (mapIndividuals carrier.name (blockedSource carrier)).clauses,
      clause.sat (fun atom => valuation (atomIndex atom)) :=
    fun clause hclause => hblockedModels clause
      (mem_groundSource_base hclause)
  let respects := Eqv.respectsEq_of_grounds hbase
    (Eqv.grounds_ground carrier.witness
      (mapIndividuals carrier.name (blockedSource carrier)).clauses)
  let carrierInterpretation := Eqv.congruenceModel
    (fun atom => valuation (atomIndex atom)) respects
  let interpretation := restrictIndividualNames carrier.name carrierInterpretation
  have hcarrierModels : CBRoleChainEncoding.models carrierInterpretation
      (mapIndividuals carrier.name (blockedSource carrier)) :=
    quotient_models_source hblockedModels
  have hsourceModels : CBRoleChainEncoding.models interpretation
      (blockedSource carrier) :=
    (models_mapIndividuals_iff carrier.name carrierInterpretation
      (blockedSource carrier)).mp hcarrierModels
  have hpositiveSat := hqueryModels (positiveQueryClause sub witness) (by
    simp [blockedQueryGround])
  have hpositive : valuation (atomIndex (.con sub witness)) := by
    have himp := (clImp_sat (fun atom => valuation (atomIndex atom))
      [] [.con sub witness]).mp hpositiveSat
    simpa using himp (by simp)
  have hnegativeSat := hqueryModels (negativeQueryClause sup witness) (by
    simp [blockedQueryGround])
  have hnegative : ¬valuation (atomIndex (.con sup witness)) := by
    intro hsuper
    have himp := (clImp_sat (fun atom => valuation (atomIndex atom))
      [.con sup witness] []).mp hnegativeSat
    simpa using himp (by simpa using hsuper)
  refine ⟨Eqv.QDom (fun atom => valuation (atomIndex atom)) respects,
    interpretation, Quotient.mk _ witness, hsourceModels, ?_, ?_⟩
  · exact hpositive
  · exact hnegative

#print axioms blockedQueryGround_countermodel

end ContextCalculus.CBBlockedTaxonomyCountermodel

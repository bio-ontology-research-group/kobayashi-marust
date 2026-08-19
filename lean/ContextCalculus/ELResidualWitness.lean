import ContextCalculus.ELResidualCompilation

/-!
# Canonical-witness refinement for residual ELC certificates

Rust replaces `A ⊑ ∃R.B`'s NF3 target `B` by a dedicated concept `W` and
adds `W ⊑ B`.  Residual occurrences of the source Skolem function are then
pinned to the alive canonical node for `W`.  This file proves that the rewritten
normal forms satisfy both original frontend Skolem clauses under that one
constant-function interpretation.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type} {top bottom : Concept}

def canonicalWitness (active : Concept → Prop) (O : Ontology Concept Role)
    (witness : Concept) (hactive : active witness)
    (halive : ¬Sub top bottom O witness bottom) :
    ActiveAlive active top bottom O :=
  ⟨witness, hactive, halive⟩

/-- The exact NF3/NF1 rewrite used by `compile_residual` validates the two raw
Skolem halves when the function is pinned to its alive canonical witness. -/
theorem canonOn_rewrittenExistential_satisfies_raw
    (active : Concept → Prop) (O : Ontology Concept Role)
    (sub filler witness : Concept) (role : Role) (function : Nat)
    (roleVariable fillerVariable : Nat)
    (hactive : active witness)
    (halive : ¬Sub top bottom O witness bottom)
    (hnf3 : Clause.nf3 sub role witness ∈ O)
    (hnf1 : Clause.nf1 witness filler ∈ O)
    (base : RawTermInterp (ActiveAlive active top bottom O))
    (pin : Nat → ActiveAlive active top bottom O)
    (hpin : pin function = canonicalWitness active O witness hactive halive) :
    let I := canonOn active (top := top) (bottom := bottom) (O := O)
    let T := pinnedTermInterp base pin
    satRawClause I T (rawExistentialRoleClause sub role roleVariable function) ∧
      satRawClause I T
        (rawExistentialFillerClause (Role := Role) sub filler fillerVariable function) := by
  dsimp only
  let canonical := canonicalWitness active O witness hactive halive
  constructor
  · intro env hbody
    have hsub : Sub top bottom O (env roleVariable).1 sub := by
      apply hbody (.concept sub (.var roleVariable))
      simp [rawExistentialRoleClause, satRawAtom, evalRawTerm, canonOn]
    refine ⟨.role role (.var roleVariable) (.fun function (.var roleVariable)), ?_, ?_⟩
    · simp [rawExistentialRoleClause]
    · change Edge top bottom O (env roleVariable).1 role (pin function).1
      rw [hpin]
      exact Edge.nf3 hsub hnf3
  · intro env hbody
    have hsub : Sub top bottom O (env fillerVariable).1 sub := by
      apply hbody (.concept sub (.var fillerVariable))
      simp [rawExistentialFillerClause, satRawAtom, evalRawTerm, canonOn]
    refine ⟨.concept filler (.fun function (.var fillerVariable)), ?_, ?_⟩
    · simp [rawExistentialFillerClause]
    · change Sub top bottom O (pin function).1 filler
      rw [hpin]
      exact Sub.nf1 (Sub.refl witness) hnf1

structure CanonicalWitnessRecord (Concept Role : Type) where
  sub : Concept
  role : Role
  filler : Concept
  witness : Concept
  function : Nat
  roleVariable : Nat
  fillerVariable : Nat
deriving DecidableEq, Repr

def CanonicalWitnessRecord.rawOntology (record : CanonicalWitnessRecord Concept Role) :
    List (RawClause Concept Role) :=
  [rawExistentialRoleClause record.sub record.role record.roleVariable record.function,
    rawExistentialFillerClause (Role := Role) record.sub record.filler
      record.fillerVariable record.function]

def CanonicalWitnessRecord.rewrittenOntology
    (record : CanonicalWitnessRecord Concept Role) : Ontology Concept Role :=
  [.nf3 record.sub record.role record.witness,
    .nf1 record.witness record.filler]

def CanonicalWitnessRecord.Valid (active : Concept → Prop)
    (O : Ontology Concept Role) (record : CanonicalWitnessRecord Concept Role) : Prop :=
  active record.witness ∧
    ¬Sub top bottom O record.witness bottom ∧
    Clause.nf3 record.sub record.role record.witness ∈ O ∧
    Clause.nf1 record.witness record.filler ∈ O

def CanonicalWitnessRecord.PinCompatible (active : Concept → Prop)
    (O : Ontology Concept Role) (pin : Nat → ActiveAlive active top bottom O)
    (record : CanonicalWitnessRecord Concept Role) : Prop :=
  ∀ hactive halive,
    pin record.function =
      canonicalWitness active O record.witness hactive halive

def canonicalWitnessRawOntology
    (records : List (CanonicalWitnessRecord Concept Role)) :
    List (RawClause Concept Role) :=
  records.flatMap CanonicalWitnessRecord.rawOntology

def canonicalWitnessRewrittenOntology
    (records : List (CanonicalWitnessRecord Concept Role)) : Ontology Concept Role :=
  records.flatMap CanonicalWitnessRecord.rewrittenOntology

/-- Every checked witness record is interpreted by the same global pinned term
interpretation, so the complete list of original Skolem pairs holds together. -/
theorem canonOn_witnessRecords_satisfy_raw
    (active : Concept → Prop) (O : Ontology Concept Role)
    (records : List (CanonicalWitnessRecord Concept Role))
    (base : RawTermInterp (ActiveAlive active top bottom O))
    (pin : Nat → ActiveAlive active top bottom O)
    (hvalid : ∀ record ∈ records,
      record.Valid (top := top) (bottom := bottom) active O)
    (hpins : ∀ record ∈ records,
      record.PinCompatible (top := top) (bottom := bottom) active O pin) :
    modelsRaw (canonOn active (top := top) (bottom := bottom) (O := O))
      (pinnedTermInterp base pin) (canonicalWitnessRawOntology records) := by
  intro clause hclause
  simp only [canonicalWitnessRawOntology, List.mem_flatMap] at hclause
  obtain ⟨record, hrecord, hclause⟩ := hclause
  obtain ⟨hactive, halive, hnf3, hnf1⟩ := hvalid record hrecord
  have hpair := canonOn_rewrittenExistential_satisfies_raw
    (top := top) (bottom := bottom) active O record.sub record.filler
    record.witness record.role record.function record.roleVariable
    record.fillerVariable hactive halive hnf3 hnf1 base pin
    (hpins record hrecord hactive halive)
  simp [CanonicalWitnessRecord.rawOntology] at hclause
  rcases hclause with hrole | hfiller
  · rw [hrole]
    exact hpair.1
  · rw [hfiller]
    exact hpair.2

def materializedCanonicalWitness (active : Concept → Prop)
    (m : Materialization Concept Role) (bottom witness : Concept)
    (hactive : active witness) (halive : ¬m.sub witness bottom) :
    MaterializedActiveAlive active m bottom :=
  ⟨witness, hactive, halive⟩

/-- Materialized counterpart of the canonical NF3 witness refinement. It uses
only the checked fixpoint closure, so its domain and interpretation are exactly
those enumerated by the native residual checker. -/
theorem materialized_rewrittenExistential_satisfies_raw
    (active : Concept → Prop) (O : Ontology Concept Role)
    (m : Materialization Concept Role) (closed : ClosedState m top bottom O)
    (sub filler witness : Concept) (role : Role) (function : Nat)
    (roleVariable fillerVariable : Nat)
    (hactive : active witness) (halive : ¬m.sub witness bottom)
    (hnf3 : Clause.nf3 sub role witness ∈ O)
    (hnf1 : Clause.nf1 witness filler ∈ O)
    (base : RawTermInterp (MaterializedActiveAlive active m bottom))
    (pin : Nat → MaterializedActiveAlive active m bottom)
    (hpin : pin function =
      materializedCanonicalWitness active m bottom witness hactive halive) :
    let I := materializedCanon active m top bottom closed
    let T := pinnedTermInterp base pin
    satRawClause I T (rawExistentialRoleClause sub role roleVariable function) ∧
      satRawClause I T
        (rawExistentialFillerClause (Role := Role) sub filler fillerVariable function) := by
  dsimp only
  constructor
  · intro env hbody
    have hsub : m.sub (env roleVariable).1 sub := by
      apply hbody (.concept sub (.var roleVariable))
      simp [rawExistentialRoleClause, satRawAtom, evalRawTerm, materializedCanon]
    refine ⟨.role role (.var roleVariable) (.fun function (.var roleVariable)), ?_, ?_⟩
    · simp [rawExistentialRoleClause]
    · change m.edge (env roleVariable).1 role (pin function).1
      rw [hpin]
      exact closed.closeNf3 hsub hnf3
  · intro env hbody
    have hsub : m.sub (env fillerVariable).1 sub := by
      apply hbody (.concept sub (.var fillerVariable))
      simp [rawExistentialFillerClause, satRawAtom, evalRawTerm, materializedCanon]
    refine ⟨.concept filler (.fun function (.var fillerVariable)), ?_, ?_⟩
    · simp [rawExistentialFillerClause]
    · change m.sub (pin function).1 filler
      rw [hpin]
      exact closed.closeNf1 (closed.initRefl witness) hnf1

def CanonicalWitnessRecord.MaterializedValid (active : Concept → Prop)
    (m : Materialization Concept Role) (O : Ontology Concept Role)
    (record : CanonicalWitnessRecord Concept Role) : Prop :=
  active record.witness ∧ ¬m.sub record.witness bottom ∧
    Clause.nf3 record.sub record.role record.witness ∈ O ∧
    Clause.nf1 record.witness record.filler ∈ O

def CanonicalWitnessRecord.MaterializedPinCompatible (active : Concept → Prop)
    (m : Materialization Concept Role)
    (pin : Nat → MaterializedActiveAlive active m bottom)
    (record : CanonicalWitnessRecord Concept Role) : Prop :=
  ∀ hactive halive, pin record.function =
    materializedCanonicalWitness active m bottom record.witness hactive halive

theorem materialized_witnessRecords_satisfy_raw
    (active : Concept → Prop) (O : Ontology Concept Role)
    (m : Materialization Concept Role) (closed : ClosedState m top bottom O)
    (records : List (CanonicalWitnessRecord Concept Role))
    (base : RawTermInterp (MaterializedActiveAlive active m bottom))
    (pin : Nat → MaterializedActiveAlive active m bottom)
    (hvalid : ∀ record ∈ records,
      record.MaterializedValid (bottom := bottom) active m O)
    (hpins : ∀ record ∈ records,
      record.MaterializedPinCompatible (bottom := bottom) active m pin) :
    modelsRaw (materializedCanon active m top bottom closed)
      (pinnedTermInterp base pin) (canonicalWitnessRawOntology records) := by
  intro clause hclause
  simp only [canonicalWitnessRawOntology, List.mem_flatMap] at hclause
  obtain ⟨record, hrecord, hclause⟩ := hclause
  obtain ⟨hactive, halive, hnf3, hnf1⟩ := hvalid record hrecord
  have hpair := materialized_rewrittenExistential_satisfies_raw
    active O m closed record.sub record.filler record.witness record.role
    record.function record.roleVariable record.fillerVariable hactive halive
    hnf3 hnf1 base pin (hpins record hrecord hactive halive)
  simp [CanonicalWitnessRecord.rawOntology] at hclause
  rcases hclause with hrole | hfiller
  · rw [hrole]
    exact hpair.1
  · rw [hfiller]
    exact hpair.2

def residualCompilationRawOntology
    (entries : List (ResidualCompilationEntry Domain Concept Role)) :
    List (RawResidualClause Concept Role) :=
  entries.map ResidualCompilationEntry.raw

/-- The three fail-closed source partitions: directly normalized clauses,
canonical-witness Skolem pairs, and equality/disjunctive residual clauses. -/
def partitionedRawOntology
    (direct : List (RawClause Concept Role))
    (records : List (CanonicalWitnessRecord Concept Role))
    (entries : List (ResidualCompilationEntry Domain Concept Role)) :
    List (RawResidualClause Concept Role) :=
  direct.map RawClause.toResidual ++
    (canonicalWitnessRawOntology records).map RawClause.toResidual ++
    residualCompilationRawOntology entries

/-- Satisfaction of all three checked partitions composes into satisfaction of
the exact original source stream.  `hsource` is the executable coverage check:
it prevents a frontend clause from being silently omitted or duplicated into a
different clause during routing. -/
theorem canonOn_partitionedRawOntology_satisfies_source
    (active : Concept → Prop) (O : Ontology Concept Role)
    (source : List (RawResidualClause Concept Role))
    (direct : List (RawClause Concept Role))
    (records : List (CanonicalWitnessRecord Concept Role))
    (entries : List
      (ResidualCompilationEntry (ActiveAlive active top bottom O) Concept Role))
    (base : RawTermInterp (ActiveAlive active top bottom O))
    (pin : Nat → ActiveAlive active top bottom O)
    (hsource : source = partitionedRawOntology direct records entries)
    (hdirect : modelsRaw
      (canonOn active (top := top) (bottom := bottom) (O := O))
      (pinnedTermInterp base pin) direct)
    (hvalid : ∀ record ∈ records,
      record.Valid (top := top) (bottom := bottom) active O)
    (hpins : ∀ record ∈ records,
      record.PinCompatible (top := top) (bottom := bottom) active O pin)
    (hcompatible : ∀ entry ∈ entries, entry.pinCompatible pin)
    (hcompiled : ∀ entry ∈ entries,
      entry.compiledHolds
        (canonOn active (top := top) (bottom := bottom) (O := O))) :
    modelsRawResidual
      (canonOn active (top := top) (bottom := bottom) (O := O))
      (pinnedTermInterp base pin) source := by
  rw [hsource]
  intro clause hclause
  change clause ∈ direct.map RawClause.toResidual ++
    (canonicalWitnessRawOntology records).map RawClause.toResidual ++
    entries.map ResidualCompilationEntry.raw at hclause
  rcases List.mem_append.mp hclause with hnormal | hresidualClause
  · rcases List.mem_append.mp hnormal with hdirectClause | hwitnessClause
    · obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hdirectClause
      exact (satRawClause_toResidual_iff _ _ raw).mpr (hdirect raw hraw)
    · obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hwitnessClause
      exact (satRawClause_toResidual_iff _ _ raw).mpr
        (canonOn_witnessRecords_satisfy_raw active O records base pin hvalid hpins raw hraw)
  · obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hresidualClause
    exact residualCompilationTheory_compiled_implies_raw base pin
      (canonOn active (top := top) (bottom := bottom) (O := O)) entries
      hcompatible hcompiled entry hentry

/-- Whole-source composition over the finite executable materialization. -/
theorem materialized_partitionedRawOntology_satisfies_source
    (active : Concept → Prop) (O : Ontology Concept Role)
    (m : Materialization Concept Role) (closed : ClosedState m top bottom O)
    (source : List (RawResidualClause Concept Role))
    (direct : List (RawClause Concept Role))
    (records : List (CanonicalWitnessRecord Concept Role))
    (entries : List
      (ResidualCompilationEntry (MaterializedActiveAlive active m bottom) Concept Role))
    (base : RawTermInterp (MaterializedActiveAlive active m bottom))
    (pin : Nat → MaterializedActiveAlive active m bottom)
    (hsource : source = partitionedRawOntology direct records entries)
    (hdirect : modelsRaw (materializedCanon active m top bottom closed)
      (pinnedTermInterp base pin) direct)
    (hvalid : ∀ record ∈ records,
      record.MaterializedValid (bottom := bottom) active m O)
    (hpins : ∀ record ∈ records,
      record.MaterializedPinCompatible (bottom := bottom) active m pin)
    (hcompatible : ∀ entry ∈ entries, entry.pinCompatible pin)
    (hcompiled : ∀ entry ∈ entries,
      entry.compiledHolds (materializedCanon active m top bottom closed)) :
    modelsRawResidual (materializedCanon active m top bottom closed)
      (pinnedTermInterp base pin) source := by
  rw [hsource]
  intro clause hclause
  change clause ∈ direct.map RawClause.toResidual ++
    (canonicalWitnessRawOntology records).map RawClause.toResidual ++
    entries.map ResidualCompilationEntry.raw at hclause
  rcases List.mem_append.mp hclause with hnormal | hresidualClause
  · rcases List.mem_append.mp hnormal with hdirectClause | hwitnessClause
    · obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hdirectClause
      exact (satRawClause_toResidual_iff _ _ raw).mpr (hdirect raw hraw)
    · obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hwitnessClause
      exact (satRawClause_toResidual_iff _ _ raw).mpr
        (materialized_witnessRecords_satisfy_raw active O m closed records base pin
          hvalid hpins raw hraw)
  · obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hresidualClause
    exact residualCompilationTheory_compiled_implies_raw base pin
      (materializedCanon active m top bottom closed) entries hcompatible hcompiled
      entry hentry

#print axioms canonOn_rewrittenExistential_satisfies_raw
#print axioms canonOn_witnessRecords_satisfy_raw
#print axioms canonOn_partitionedRawOntology_satisfies_source
#print axioms materialized_rewrittenExistential_satisfies_raw
#print axioms materialized_witnessRecords_satisfy_raw
#print axioms materialized_partitionedRawOntology_satisfies_source

end ContextCalculus.ELCompletion

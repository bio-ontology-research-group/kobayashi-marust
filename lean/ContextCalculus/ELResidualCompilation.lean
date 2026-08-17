import ContextCalculus.ELResidualCertificate
import ContextCalculus.ELRawNormalization

/-!
# Refinement of raw residual clauses to pinned finite clauses

Rust's `compile_residual` replaces each supported source slot by a finite
slot and each Skolem term `f(x)` by a slot pinned to a canonical witness. This
file records that translation as proof-carrying evidence and proves that every
model of the compiled clause induces a constant-function model of the original
raw clause. This is the direction required by the fail-closed residual route.
-/

namespace ContextCalculus.ELCompletion

variable {Domain Concept Role Var : Type} {top bottom : Concept}

inductive RawResidualAtom (Concept Role : Type) where
  | concept (concept : Concept) (term : RawTerm)
  | role (role : Role) (source target : RawTerm)
  | eq (left right : RawTerm)
deriving DecidableEq, Repr

structure RawResidualClause (Concept Role : Type) where
  body : List (RawResidualAtom Concept Role)
  head : List (RawResidualAtom Concept Role)
deriving DecidableEq, Repr

def rawAtomToResidual : RawAtom Concept Role → RawResidualAtom Concept Role
  | .concept concept term => .concept concept term
  | .role role source target => .role role source target

def RawClause.toResidual (clause : RawClause Concept Role) :
    RawResidualClause Concept Role := {
  body := clause.body.map rawAtomToResidual
  head := clause.head.map rawAtomToResidual
}

def satRawResidualAtom (I : Interp Domain Concept Role top bottom)
    (T : RawTermInterp Domain) (env : Nat → Domain) :
    RawResidualAtom Concept Role → Prop
  | .concept concept term => I.concept concept (evalRawTerm T env term)
  | .role role source target =>
      I.role role (evalRawTerm T env source) (evalRawTerm T env target)
  | .eq left right => evalRawTerm T env left = evalRawTerm T env right

def satRawResidualClause (I : Interp Domain Concept Role top bottom)
    (T : RawTermInterp Domain) (clause : RawResidualClause Concept Role) : Prop :=
  ∀ env,
    (∀ atom ∈ clause.body, satRawResidualAtom I T env atom) →
    ∃ atom ∈ clause.head, satRawResidualAtom I T env atom

theorem satRawAtom_toResidual_iff
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (env : Nat → Domain) (atom : RawAtom Concept Role) :
    satRawResidualAtom I T env (rawAtomToResidual atom) ↔ satRawAtom I T env atom := by
  cases atom <;> rfl

theorem satRawClause_toResidual_iff
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (clause : RawClause Concept Role) :
    satRawResidualClause I T clause.toResidual ↔ satRawClause I T clause := by
  constructor
  · intro h env hbody
    have hbody' : ∀ atom ∈ clause.body.map rawAtomToResidual,
        satRawResidualAtom I T env atom := by
      intro atom hatom
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hatom
      exact (satRawAtom_toResidual_iff I T env source).mpr (hbody source hsource)
    obtain ⟨atom, hatom, hsatisfied⟩ := h env hbody'
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hatom
    exact ⟨source, hsource, (satRawAtom_toResidual_iff I T env source).mp hsatisfied⟩
  · intro h env hbody
    have hbody' : ∀ atom ∈ clause.body, satRawAtom I T env atom := by
      intro atom hatom
      exact (satRawAtom_toResidual_iff I T env atom).mp
        (hbody (rawAtomToResidual atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
    obtain ⟨atom, hatom, hsatisfied⟩ := h env hbody'
    exact ⟨rawAtomToResidual atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
      (satRawAtom_toResidual_iff I T env atom).mpr hsatisfied⟩

def modelsRawResidual (I : Interp Domain Concept Role top bottom)
    (T : RawTermInterp Domain) (clauses : List (RawResidualClause Concept Role)) : Prop :=
  ∀ clause ∈ clauses, satRawResidualClause I T clause

theorem modelsRaw_toResidual_iff
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (clauses : List (RawClause Concept Role)) :
    modelsRawResidual I T (clauses.map RawClause.toResidual) ↔ modelsRaw I T clauses := by
  constructor
  · intro h clause hclause
    exact (satRawClause_toResidual_iff I T clause).mp
      (h clause.toResidual (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · intro h residual hresidual
    obtain ⟨clause, hclause, rfl⟩ := List.mem_map.mp hresidual
    exact (satRawClause_toResidual_iff I T clause).mpr (h clause hclause)

inductive ResidualVarOrigin (Domain : Type) where
  | source (name : Nat)
  | function (name : Nat) (witness : Domain)

def pinnedTermInterp (base : RawTermInterp Domain) (pin : Nat → Domain) :
    RawTermInterp Domain := {
  base with function := fun function _ => pin function
}

def assignmentOf (origin : Var → ResidualVarOrigin Domain)
    (env : Nat → Domain) : Var → Domain
  | slot => match origin slot with
    | .source name => env name
    | .function _ witness => witness

inductive CompiledResidualTerm (origin : Var → ResidualVarOrigin Domain) :
    RawTerm → Var → Prop where
  | var {name slot} : origin slot = .source name →
      CompiledResidualTerm origin (.var name) slot
  | function {name argument slot witness} :
      origin slot = .function name witness →
      CompiledResidualTerm origin (.fun name (.var argument)) slot

theorem CompiledResidualTerm.eval_eq
    (origin : Var → ResidualVarOrigin Domain) (base : RawTermInterp Domain)
    (pin : Nat → Domain)
    (hpin : ∀ slot name witness, origin slot = .function name witness →
      pin name = witness)
    (env : Nat → Domain) {term : RawTerm} {slot : Var}
    (hterm : CompiledResidualTerm origin term slot) :
    evalRawTerm (pinnedTermInterp base pin) env term = assignmentOf origin env slot := by
  cases hterm with
  | var horigin => simp [evalRawTerm, assignmentOf, horigin]
  | function horigin =>
      simp [evalRawTerm, pinnedTermInterp, assignmentOf, horigin,
        hpin _ _ _ horigin]

inductive CompiledResidualAtomEvidence
    (origin : Var → ResidualVarOrigin Domain) :
    RawResidualAtom Concept Role → CompiledResidualAtom Concept Role Var → Prop where
  | concept {concept term slot} :
      CompiledResidualTerm origin term slot →
      CompiledResidualAtomEvidence origin (.concept concept term) (.concept concept slot)
  | role {role source target sourceVar targetVar} :
      CompiledResidualTerm origin source sourceVar →
      CompiledResidualTerm origin target targetVar →
      CompiledResidualAtomEvidence origin (.role role source target)
        (.role role sourceVar targetVar)
  | eq {left right leftVar rightVar} :
      CompiledResidualTerm origin left leftVar →
      CompiledResidualTerm origin right rightVar →
      CompiledResidualAtomEvidence origin (.eq left right) (.eq leftVar rightVar)

theorem CompiledResidualAtomEvidence.sat_iff
    (origin : Var → ResidualVarOrigin Domain) (base : RawTermInterp Domain)
    (pin : Nat → Domain)
    (hpin : ∀ slot name witness, origin slot = .function name witness →
      pin name = witness)
    (I : Interp Domain Concept Role top bottom) (env : Nat → Domain)
    {raw : RawResidualAtom Concept Role} {compiled : CompiledResidualAtom Concept Role Var}
    (hevidence : CompiledResidualAtomEvidence origin raw compiled) :
    satRawResidualAtom I (pinnedTermInterp base pin) env raw ↔
      satCompiledResidualAtom I (assignmentOf origin env) compiled := by
  cases hevidence with
  | concept hterm => simp [satRawResidualAtom, satCompiledResidualAtom, hterm.eval_eq origin base pin hpin env]
  | role hsource htarget =>
      simp [satRawResidualAtom, satCompiledResidualAtom,
        hsource.eval_eq origin base pin hpin env, htarget.eval_eq origin base pin hpin env]
  | eq hleft hright =>
      simp [satRawResidualAtom, satCompiledResidualAtom,
        hleft.eval_eq origin base pin hpin env, hright.eval_eq origin base pin hpin env]

structure ResidualCompilationEvidence
    (origin : Var → ResidualVarOrigin Domain)
    (raw : RawResidualClause Concept Role)
    (compiled : CompiledResidualClause Domain Concept Role Var) : Prop where
  body : List.Forall₂ (CompiledResidualAtomEvidence origin) raw.body compiled.body
  head : List.Forall₂ (CompiledResidualAtomEvidence origin) raw.head compiled.head
  pins_exact : ∀ slot witness,
    (slot, witness) ∈ compiled.pins ↔
      match origin slot with
      | .source _ => False
      | .function _ expected => expected = witness

def checkCompiledResidualTerm [DecidableEq Domain] [DecidableEq Var]
    (origin : Var → ResidualVarOrigin Domain) (raw : RawTerm) (slot : Var) : Bool :=
  match raw, origin slot with
  | .var name, .source expected => decide (name = expected)
  | .fun name (.var _), .function expected _ => decide (name = expected)
  | _, _ => false

theorem checkCompiledResidualTerm_iff [DecidableEq Domain] [DecidableEq Var]
    (origin : Var → ResidualVarOrigin Domain) (raw : RawTerm) (slot : Var) :
    checkCompiledResidualTerm origin raw slot = true ↔
      CompiledResidualTerm origin raw slot := by
  cases raw with
  | var name =>
      cases horigin : origin slot with
      | source expected =>
          simp only [checkCompiledResidualTerm, horigin, decide_eq_true_eq]
          constructor
          · rintro rfl
            exact .var horigin
          · intro h
            cases h with
            | var hsource => exact (by simpa [horigin] using hsource.symm)
      | function function witness =>
          simp only [checkCompiledResidualTerm, horigin, Bool.false_eq_true]
          constructor
          · intro h; contradiction
          · intro h
            cases h with
            | var hsource => simp [horigin] at hsource
  | ind individual => simp [checkCompiledResidualTerm]; intro h; cases h
  | aux name => simp [checkCompiledResidualTerm]; intro h; cases h
  | «fun» name argument =>
      cases argument with
      | var argumentName =>
          cases horigin : origin slot with
          | source sourceName =>
              simp only [checkCompiledResidualTerm, horigin, Bool.false_eq_true]
              constructor
              · intro h; contradiction
              · intro h
                cases h with
                | function hfunction => simp [horigin] at hfunction
          | function expected witness =>
              simp only [checkCompiledResidualTerm, horigin, decide_eq_true_eq]
              constructor
              · rintro rfl
                exact .function horigin
              · intro h
                cases h with
                | function hfunction =>
                    exact (ResidualVarOrigin.function.inj
                      (horigin.symm.trans hfunction)).1.symm
      | ind individual => simp [checkCompiledResidualTerm]; intro h; cases h
      | aux auxName => simp [checkCompiledResidualTerm]; intro h; cases h
      | «fun» nestedName nestedArgument => simp [checkCompiledResidualTerm]; intro h; cases h

def checkCompiledResidualAtomEvidence [DecidableEq Domain] [DecidableEq Concept]
    [DecidableEq Role] [DecidableEq Var]
    (origin : Var → ResidualVarOrigin Domain) :
    RawResidualAtom Concept Role → CompiledResidualAtom Concept Role Var → Bool
  | .concept rawConcept rawTerm, .concept compiledConcept slot =>
      decide (rawConcept = compiledConcept) && checkCompiledResidualTerm origin rawTerm slot
  | .role rawRole rawSource rawTarget, .role compiledRole source target =>
      decide (rawRole = compiledRole) &&
        checkCompiledResidualTerm origin rawSource source &&
        checkCompiledResidualTerm origin rawTarget target
  | .eq rawLeft rawRight, .eq left right =>
      checkCompiledResidualTerm origin rawLeft left &&
        checkCompiledResidualTerm origin rawRight right
  | _, _ => false

theorem checkCompiledResidualAtomEvidence_iff [DecidableEq Domain]
    [DecidableEq Concept] [DecidableEq Role] [DecidableEq Var]
    (origin : Var → ResidualVarOrigin Domain)
    (raw : RawResidualAtom Concept Role) (compiled : CompiledResidualAtom Concept Role Var) :
    checkCompiledResidualAtomEvidence origin raw compiled = true ↔
      CompiledResidualAtomEvidence origin raw compiled := by
  cases raw <;> cases compiled <;>
    simp only [checkCompiledResidualAtomEvidence, Bool.false_eq_true,
      Bool.and_eq_true, decide_eq_true_eq,
      checkCompiledResidualTerm_iff] <;>
    constructor <;> intro h
  all_goals try { contradiction }
  · rcases h with ⟨rfl, hterm⟩; exact .concept hterm
  · cases h with | concept hterm => exact ⟨rfl, hterm⟩
  · rcases h with ⟨⟨rfl, hsource⟩, htarget⟩; exact .role hsource htarget
  · cases h with | role hsource htarget => exact ⟨⟨rfl, hsource⟩, htarget⟩
  · exact .eq h.1 h.2
  · cases h with | eq hleft hright => exact ⟨hleft, hright⟩

def checkCompiledResidualAtoms [DecidableEq Domain] [DecidableEq Concept]
    [DecidableEq Role] [DecidableEq Var]
    (origin : Var → ResidualVarOrigin Domain) :
    List (RawResidualAtom Concept Role) →
      List (CompiledResidualAtom Concept Role Var) → Bool
  | [], [] => true
  | raw :: raws, compiled :: compileds =>
      checkCompiledResidualAtomEvidence origin raw compiled &&
        checkCompiledResidualAtoms origin raws compileds
  | _, _ => false

theorem checkCompiledResidualAtoms_iff [DecidableEq Domain]
    [DecidableEq Concept] [DecidableEq Role] [DecidableEq Var]
    (origin : Var → ResidualVarOrigin Domain) (raw : List (RawResidualAtom Concept Role))
    (compiled : List (CompiledResidualAtom Concept Role Var)) :
    checkCompiledResidualAtoms origin raw compiled = true ↔
      List.Forall₂ (CompiledResidualAtomEvidence origin) raw compiled := by
  induction raw generalizing compiled with
  | nil => cases compiled <;> simp [checkCompiledResidualAtoms]
  | cons atom atoms ih =>
      cases compiled with
      | nil => simp [checkCompiledResidualAtoms]
      | cons compiledAtom compiledAtoms =>
          simp [checkCompiledResidualAtoms, checkCompiledResidualAtomEvidence_iff, ih]

def checkResidualPins [DecidableEq Domain] (origin : Fin variableCount → ResidualVarOrigin Domain)
    (pins : List (Fin variableCount × Domain)) : Bool :=
  pins.all (fun (slot, witness) =>
    match origin slot with
    | .source _ => false
    | .function _ expected => decide (expected = witness)) &&
  (List.finRange variableCount).all (fun slot =>
    match origin slot with
    | .source _ => true
    | .function _ witness => decide ((slot, witness) ∈ pins))

theorem checkResidualPins_iff [DecidableEq Domain]
    (origin : Fin variableCount → ResidualVarOrigin Domain)
    (pins : List (Fin variableCount × Domain)) :
    checkResidualPins origin pins = true ↔
      ∀ slot witness, (slot, witness) ∈ pins ↔
        match origin slot with
        | .source _ => False
        | .function _ expected => expected = witness := by
  simp only [checkResidualPins, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, decide_eq_true_eq]
  constructor
  · rintro ⟨hsound, hcomplete⟩ slot witness
    cases horigin : origin slot with
    | source name =>
        simp only
        constructor
        · intro hmem
          have := hsound (slot, witness) hmem
          simp [horigin] at this
        · intro h; contradiction
    | function function expected =>
        simp only
        constructor
        · intro hmem
          simpa [horigin] using hsound (slot, witness) hmem
        · intro heq
          subst witness
          simpa [horigin] using hcomplete slot
  · intro hexact
    constructor
    · rintro ⟨slot, witness⟩ hmem
      cases horigin : origin slot with
      | source name =>
          have hfalse := (hexact slot witness).mp hmem
          simp [horigin] at hfalse
      | function function expected =>
          simpa [horigin] using (hexact slot witness).mp hmem
    · intro slot _
      cases horigin : origin slot with
      | source name => simp [horigin]
      | function function witness =>
          simpa [horigin] using (hexact slot witness).mpr (by simp [horigin])

def checkResidualCompilationEvidence [DecidableEq Domain]
    [DecidableEq Concept] [DecidableEq Role]
    (origin : Fin variableCount → ResidualVarOrigin Domain)
    (raw : RawResidualClause Concept Role)
    (compiled : CompiledResidualClause Domain Concept Role (Fin variableCount)) : Bool :=
  checkCompiledResidualAtoms origin raw.body compiled.body &&
    checkCompiledResidualAtoms origin raw.head compiled.head &&
    checkResidualPins origin compiled.pins

theorem checkResidualCompilationEvidence_iff [DecidableEq Domain]
    [DecidableEq Concept] [DecidableEq Role]
    (origin : Fin variableCount → ResidualVarOrigin Domain)
    (raw : RawResidualClause Concept Role)
    (compiled : CompiledResidualClause Domain Concept Role (Fin variableCount)) :
    checkResidualCompilationEvidence origin raw compiled = true ↔
      ResidualCompilationEvidence origin raw compiled := by
  simp only [checkResidualCompilationEvidence, Bool.and_eq_true,
    checkCompiledResidualAtoms_iff, checkResidualPins_iff]
  constructor
  · rintro ⟨⟨hbody, hhead⟩, hpins⟩
    refine ⟨hbody, hhead, ?_⟩
    exact hpins
  · intro h
    refine ⟨⟨h.body, h.head⟩, ?_⟩
    exact h.pins_exact

theorem forall₂_satisfaction_iff
    (origin : Var → ResidualVarOrigin Domain) (base : RawTermInterp Domain)
    (pin : Nat → Domain)
    (hpin : ∀ slot name witness, origin slot = .function name witness →
      pin name = witness)
    (I : Interp Domain Concept Role top bottom) (env : Nat → Domain)
    {raw : List (RawResidualAtom Concept Role)}
    {compiled : List (CompiledResidualAtom Concept Role Var)}
    (hevidence : List.Forall₂ (CompiledResidualAtomEvidence origin) raw compiled) :
    (∀ atom ∈ raw, satRawResidualAtom I (pinnedTermInterp base pin) env atom) ↔
      (∀ atom ∈ compiled, satCompiledResidualAtom I (assignmentOf origin env) atom) := by
  induction hevidence with
  | nil => simp
  | cons hatom _ ih =>
      simp only [List.mem_cons, forall_eq_or_imp]
      rw [hatom.sat_iff origin base pin hpin I env, ih]

theorem forall₂_exists_satisfaction_iff
    (origin : Var → ResidualVarOrigin Domain) (base : RawTermInterp Domain)
    (pin : Nat → Domain)
    (hpin : ∀ slot name witness, origin slot = .function name witness →
      pin name = witness)
    (I : Interp Domain Concept Role top bottom) (env : Nat → Domain)
    {raw : List (RawResidualAtom Concept Role)}
    {compiled : List (CompiledResidualAtom Concept Role Var)}
    (hevidence : List.Forall₂ (CompiledResidualAtomEvidence origin) raw compiled) :
    (∃ atom ∈ raw, satRawResidualAtom I (pinnedTermInterp base pin) env atom) ↔
      (∃ atom ∈ compiled, satCompiledResidualAtom I (assignmentOf origin env) atom) := by
  induction hevidence with
  | nil => simp
  | cons hatom _ ih =>
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [hatom.sat_iff origin base pin hpin I env, ih]

/-- A satisfied compiled clause yields a model of its exact raw source clause. -/
theorem ResidualCompilationEvidence.compiled_implies_raw
    (origin : Var → ResidualVarOrigin Domain) (base : RawTermInterp Domain)
    (pin : Nat → Domain)
    (hpin : ∀ slot name witness, origin slot = .function name witness →
      pin name = witness)
    (I : Interp Domain Concept Role top bottom)
    {raw : RawResidualClause Concept Role}
    {compiled : CompiledResidualClause Domain Concept Role Var}
    (hevidence : ResidualCompilationEvidence origin raw compiled)
    (hcompiled : satCompiledResidualClause I compiled) :
    satRawResidualClause I (pinnedTermInterp base pin) raw := by
  intro env hbody
  let assignment := assignmentOf origin env
  have hpins : ∀ item ∈ compiled.pins, assignment item.1 = item.2 := by
    rintro ⟨slot, witness⟩ hmem
    have hexact := (hevidence.pins_exact slot witness).mp hmem
    cases horigin : origin slot with
    | source name => simp [horigin] at hexact
    | function function expected =>
        simp only [horigin] at hexact
        simp [assignment, assignmentOf, horigin, hexact]
  have hcompiledBody : ∀ atom ∈ compiled.body,
      satCompiledResidualAtom I assignment atom :=
    (forall₂_satisfaction_iff origin base pin hpin I env hevidence.body).mp hbody
  have hhead := hcompiled assignment hpins hcompiledBody
  exact (forall₂_exists_satisfaction_iff origin base pin hpin I env hevidence.head).mpr hhead

/-! ## Whole-theory composition

Each Rust clause owns a small, independently numbered variable table.  The
entries below hide that local slot type while requiring every Skolem-function
slot to agree with one global pin interpretation.  Consequently all source
clauses are satisfied by one shared `RawTermInterp`, rather than by a different
choice of functions for each clause.
-/

structure ResidualCompilationEntry (Domain Concept Role : Type) where
  Var : Type
  origin : Var → ResidualVarOrigin Domain
  raw : RawResidualClause Concept Role
  compiled : CompiledResidualClause Domain Concept Role Var
  evidence : ResidualCompilationEvidence origin raw compiled

def ResidualCompilationEntry.pinCompatible
    (entry : ResidualCompilationEntry Domain Concept Role)
    (pin : Nat → Domain) : Prop :=
  ∀ slot function witness,
    entry.origin slot = .function function witness → pin function = witness

def ResidualCompilationEntry.compiledHolds
    (I : Interp Domain Concept Role top bottom)
    (entry : ResidualCompilationEntry Domain Concept Role) : Prop :=
  satCompiledResidualClause I entry.compiled

def ResidualCompilationEntry.rawHolds
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (entry : ResidualCompilationEntry Domain Concept Role) : Prop :=
  satRawResidualClause I T entry.raw

/-- All independently numbered compiled clauses refine one raw residual theory. -/
theorem residualCompilationTheory_compiled_implies_raw
    (base : RawTermInterp Domain) (pin : Nat → Domain)
    (I : Interp Domain Concept Role top bottom)
    (entries : List (ResidualCompilationEntry Domain Concept Role))
    (hcompatible : ∀ entry ∈ entries, entry.pinCompatible pin)
    (hcompiled : ∀ entry ∈ entries, entry.compiledHolds I) :
    ∀ entry ∈ entries,
      entry.rawHolds I (pinnedTermInterp base pin) := by
  intro entry hentry
  exact entry.evidence.compiled_implies_raw entry.origin base pin
    (hcompatible entry hentry) I (hcompiled entry hentry)

#print axioms ResidualCompilationEvidence.compiled_implies_raw
#print axioms residualCompilationTheory_compiled_implies_raw

end ContextCalculus.ELCompletion

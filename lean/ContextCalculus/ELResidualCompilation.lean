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
      ∃ function, origin slot = .function function witness

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
    obtain ⟨function, horigin⟩ := (hevidence.pins_exact slot witness).mp hmem
    simp [assignment, assignmentOf, horigin]
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

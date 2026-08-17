import ContextCalculus.ELNormalization

/-!
# Executable recognition of raw ELC clauses

This file models the typed fragment of the frontend's `JTerm` / `JAtom` /
`JClause` JSON contract that the pure ELC route accepts.  Recognition checks
variable wiring explicitly. A separate executable recognizer pairs the two
Skolem clauses used for existential introduction, and the semantic section
proves that pair equisatisfiable with the source existential axiom.
-/

namespace ContextCalculus.ELCompletion

/-- The raw terms admitted by the pure ELC recognizer. -/
inductive RawTerm where
  | var (name : Nat)
  | ind (name : Nat)
  | aux (root : Nat) (label : List (Nat × Int))
  | fun (function : Nat) (argument : RawTerm)
deriving DecidableEq, Repr

/-- The equality-free atoms relevant to pure ELC normalization. -/
inductive RawAtom (Concept Role : Type) where
  | concept (concept : Concept) (term : RawTerm)
  | role (role : Role) (source target : RawTerm)
deriving DecidableEq, Repr

/-- A universally quantified frontend Horn clause. -/
structure RawClause (Concept Role : Type) where
  body : List (RawAtom Concept Role)
  head : List (RawAtom Concept Role)
deriving DecidableEq, Repr

/-- Interpretation of the non-logical symbols carried by raw terms. -/
structure RawTermInterp (Domain : Type) where
  individual : Nat → Domain
  auxiliary : Nat → List (Nat × Int) → Domain
  function : Nat → Domain → Domain

def evalRawTerm (T : RawTermInterp Domain) (env : Nat → Domain) : RawTerm → Domain
  | .var name => env name
  | .ind name => T.individual name
  | .aux root label => T.auxiliary root label
  | .fun function argument => T.function function (evalRawTerm T env argument)

def satRawAtom {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (env : Nat → Domain) : RawAtom Concept Role → Prop
  | .concept concept term => I.concept concept (evalRawTerm T env term)
  | .role role source target =>
      I.role role (evalRawTerm T env source) (evalRawTerm T env target)

def holdsRawAtoms {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (env : Nat → Domain) (atoms : List (RawAtom Concept Role)) : Prop :=
  ∀ atom ∈ atoms, satRawAtom I T env atom

def satRawClause {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (clause : RawClause Concept Role) : Prop :=
  ∀ env, holdsRawAtoms I T env clause.body →
    ∃ atom ∈ clause.head, satRawAtom I T env atom

/-- The role half of the frontend's Skolem encoding of `A ⊑ ∃R.B`. -/
def rawExistentialRoleClause (sub : Concept) (role : Role)
    (variableId function : Nat) : RawClause Concept Role := {
  body := [.concept sub (.var variableId)]
  head := [.role role (.var variableId) (.fun function (.var variableId))]
}

/-- The filler half of the frontend's Skolem encoding of `A ⊑ ∃R.B`. -/
def rawExistentialFillerClause (sub filler : Concept)
    (variableId function : Nat) : RawClause Concept Role := {
  body := [.concept sub (.var variableId)]
  head := [.concept filler (.fun function (.var variableId))]
}

/-- Any model of both Skolem halves satisfies the reconstructed existential axiom. -/
theorem rawExistentialPair_sound {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (sub filler : Concept) (role : Role)
    (roleVariable fillerVariable function : Nat)
    (hrole : satRawClause I T
      (rawExistentialRoleClause sub role roleVariable function))
    (hfiller : satRawClause I T
      (rawExistentialFillerClause (Role := Role) sub filler fillerVariable function)) :
    satSourceAxiom I (.existential sub role filler) := by
  intro x hsub
  let env : Nat → Domain := fun _ => x
  refine ⟨T.function function x, ?_, ?_⟩
  · have h := hrole env (by
      intro atom hmem
      simp only [rawExistentialRoleClause, List.mem_singleton] at hmem
      subst atom
      exact hsub)
    simpa [rawExistentialRoleClause, satRawAtom, evalRawTerm, env] using h
  · have h := hfiller env (by
      intro atom hmem
      simp only [rawExistentialFillerClause, List.mem_singleton] at hmem
      subst atom
      exact hsub)
    simpa [rawExistentialFillerClause, satRawAtom, evalRawTerm, env] using h

/-- Every source existential model extends its raw function interpretation to both Skolem halves. -/
theorem rawExistentialPair_complete {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (sub filler : Concept) (role : Role)
    (roleVariable fillerVariable function : Nat)
    (hsource : satSourceAxiom I (.existential sub role filler)) :
    ∃ T : RawTermInterp Domain,
      satRawClause I T (rawExistentialRoleClause sub role roleVariable function) ∧
      satRawClause I T
        (rawExistentialFillerClause (Role := Role) sub filler fillerVariable function) := by
  classical
  let witness : Domain → Domain := fun x =>
    if hx : I.concept sub x then Classical.choose (hsource x hx) else x
  let T : RawTermInterp Domain := {
    base with
    function := fun name argument =>
      if name = function then witness argument else base.function name argument
  }
  refine ⟨T, ?_, ?_⟩
  · intro env hbody
    have hsub : I.concept sub (env roleVariable) := by
      apply hbody (.concept sub (.var roleVariable))
      simp [rawExistentialRoleClause]
    have hspec := Classical.choose_spec (hsource (env roleVariable) hsub)
    refine ⟨.role role (.var roleVariable) (.fun function (.var roleVariable)),
      by simp [rawExistentialRoleClause], ?_⟩
    simpa [satRawAtom, evalRawTerm, T, witness, hsub] using hspec.1
  · intro env hbody
    have hsub : I.concept sub (env fillerVariable) := by
      apply hbody (.concept sub (.var fillerVariable))
      simp [rawExistentialFillerClause]
    have hspec := Classical.choose_spec (hsource (env fillerVariable) hsub)
    refine ⟨.concept filler (.fun function (.var fillerVariable)),
      by simp [rawExistentialFillerClause], ?_⟩
    simpa [satRawAtom, evalRawTerm, T, witness, hsub] using hspec.2

/-- The paired raw Skolem clauses are equisatisfiable with their source existential axiom. -/
theorem rawExistentialPair_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (sub filler : Concept) (role : Role)
    (roleVariable fillerVariable function : Nat) :
    (∃ T : RawTermInterp Domain,
      satRawClause I T (rawExistentialRoleClause sub role roleVariable function) ∧
      satRawClause I T
        (rawExistentialFillerClause (Role := Role) sub filler fillerVariable function)) ↔
      satSourceAxiom I (.existential sub role filler) := by
  constructor
  · rintro ⟨T, hrole, hfiller⟩
    exact rawExistentialPair_sound I T sub filler role roleVariable fillerVariable function
      hrole hfiller
  · intro hsource
    exact rawExistentialPair_complete I base sub filler role roleVariable fillerVariable function
      hsource

def rawConcept : RawAtom Concept Role → Option (Concept × RawTerm)
  | .concept concept term => some (concept, term)
  | .role _ _ _ => none

def rawRole : RawAtom Concept Role → Option (Role × RawTerm × RawTerm)
  | .concept _ _ => none
  | .role role source target => some (role, source, target)

def allConceptsOn (varId : Nat) : List (RawAtom Concept Role) → Option (List Concept)
  | [] => some []
  | .concept concept (.var actual) :: rest =>
      if actual = varId then
        return concept :: (← allConceptsOn varId rest)
      else none
  | _ => none

/-- Recognize a role restriction body in either frontend atom order. -/
def recognizeExistsElimBody (top : Concept) (headVar : Nat) :
    List (RawAtom Concept Role) → Option (Role × Concept)
  | [.role role (.var source) (.var target)] =>
      if headVar = source && source != target then some (role, top) else none
  | [.role role (.var source) (.var target), .concept filler (.var fillerVar)]
  | [.concept filler (.var fillerVar), .role role (.var source) (.var target)] =>
      if headVar = source && source != target && fillerVar = target then
        some (role, filler)
      else none
  | _ => none

/-- Recognize a role inclusion with exact source/target wiring. -/
def recognizeRoleSubBody (headSource headTarget : Nat) :
    List (RawAtom Concept Role) → Option Role
  | [.role role (.var source) (.var target)] =>
      if headSource != headTarget && source = headSource && target = headTarget then
        some role
      else none
  | _ => none

/-- Recognize a length-two role chain, accepting either body atom order. -/
def recognizeRoleChainBody (headSource headTarget : Nat) :
    List (RawAtom Concept Role) → Option (Role × Role)
  | [.role first (.var x) (.var y), .role second (.var y') (.var z)] =>
      if x != y && y != z && x != z &&
          x = headSource && y = y' && z = headTarget then
        some (first, second)
      else if z != y' && y' != x && z != x &&
          z = headSource && y' = y && x = headTarget then
        some (second, first)
      else none
  | _ => none

/--
Reconstruct every single-clause source ELC axiom accepted by Rust's `to_nf`.
The existential-introduction pair `A(x) → R(x,f(x))` and
`A(x) → B(f(x))` is deliberately not accepted here.
-/
def recognizeRawClause (top : Concept) (clause : RawClause Concept Role) :
    Option (SourceAxiom Concept Role) :=
  match clause.head with
  | [] =>
      match clause.body with
      | .concept _ (.var varId) :: _ =>
          return .bottom (← allConceptsOn varId clause.body)
      | _ => none
  | [.concept sup (.var headVar)] =>
      match allConceptsOn headVar clause.body with
      | some body => some (.sub body sup)
      | none =>
          match recognizeExistsElimBody top headVar clause.body with
          | some (role, filler) => some (.existsElim role filler sup)
          | none => none
  | [.role sup (.var headSource) (.var headTarget)] =>
      if clause.body.isEmpty && headSource = headTarget then
        some (.reflexive sup)
      else
        match recognizeRoleSubBody headSource headTarget clause.body with
        | some sub => some (.roleSub sub sup)
        | none =>
            match recognizeRoleChainBody headSource headTarget clause.body with
            | some (first, second) => some (.roleChain first second sup)
            | none => none
  | _ => none

/-- One of the two frontend clauses that jointly encode existential introduction. -/
inductive RawExistentialHalf (Concept Role : Type) where
  | role (sub : Concept) (function : Nat) (role : Role)
  | filler (sub : Concept) (function : Nat) (filler : Concept)
deriving DecidableEq, Repr

/--
Recognize one Skolem half while checking all variable occurrences.  In
particular, the body variable is identical to the role source or filler
function argument.  This is stronger than merely checking that each position
contains some variable.
-/
def recognizeExistentialHalf (clause : RawClause Concept Role) :
    Option (RawExistentialHalf Concept Role) :=
  match clause.body, clause.head with
  | [.concept sub (.var bodyVar)],
      [.role role (.var sourceVar) (.fun function (.var argumentVar))] =>
      if bodyVar = sourceVar && bodyVar = argumentVar then
        some (.role sub function role)
      else none
  | [.concept sub (.var bodyVar)],
      [.concept filler (.fun function (.var argumentVar))] =>
      if bodyVar = argumentVar then
        some (.filler sub function filler)
      else none
  | _, _ => none

/-- Pair exactly one role half and one filler half for the same source and Skolem function. -/
def pairExistentialHalves [DecidableEq Concept] :
    RawExistentialHalf Concept Role → RawExistentialHalf Concept Role →
      Option (SourceAxiom Concept Role)
  | .role sub function role, .filler sub' function' filler
  | .filler sub' function' filler, .role sub function role =>
      if sub = sub' ∧ function = function' then
        some (.existential sub role filler)
      else none
  | _, _ => none

/-- Recognize the existential pair independently of its clause order. -/
def recognizeExistentialPair [DecidableEq Concept]
    (first second : RawClause Concept Role) :
    Option (SourceAxiom Concept Role) := do
  pairExistentialHalves (← recognizeExistentialHalf first)
    (← recognizeExistentialHalf second)

/-- A successfully paired existential has exactly the NF3 source semantics. -/
theorem recognizeExistentialPair_normalize_exact [DecidableEq Concept]
    {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (first second : RawClause Concept Role) (source : SourceAxiom Concept Role)
    (normal : Clause Concept Role)
    (_hrecognize : recognizeExistentialPair first second = some source)
    (hnormalize : normalizeDirect top source = some normal) :
    satSourceAxiom I source ↔ satClause I normal :=
  normalizeDirect_sat_iff I source normal hnormalize

/-- Accepted direct raw forms inherit the semantic exactness of `normalizeDirect`. -/
theorem recognizeRawClause_normalize_exact {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (raw : RawClause Concept Role) (source : SourceAxiom Concept Role)
    (normal : Clause Concept Role)
    (_hrecognize : recognizeRawClause top raw = some source)
    (hnormalize : normalizeDirect top source = some normal) :
    satSourceAxiom I source ↔ satClause I normal :=
  normalizeDirect_sat_iff I source normal hnormalize

namespace RawNormalizationExamples

abbrev C := Fin 5
abbrev R := Fin 4

example : recognizeRawClause (Concept := C) (Role := R) 0 {
    body := [.concept 1 (.var 7), .concept 2 (.var 7)]
    head := [.concept 3 (.var 7)]
  } = some (.sub [1, 2] 3) := by native_decide

example : recognizeRawClause (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 8), .concept 2 (.var 8)]
    head := [.concept 3 (.var 7)]
  } = some (.existsElim 1 2 3) := by native_decide

example : recognizeRawClause (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 8), .role 2 (.var 8) (.var 9)]
    head := [.role 3 (.var 7) (.var 9)]
  } = some (.roleChain 1 2 3) := by native_decide

example : recognizeRawClause (Concept := C) (Role := R) 0 {
    body := [.concept 1 (.var 7), .concept 2 (.var 8)]
    head := [.concept 3 (.var 7)]
  } = none := by native_decide

def existentialRoleHalf : RawClause C R := {
  body := [.concept 1 (.var 7)]
  head := [.role 2 (.var 7) (.fun 41 (.var 7))]
}

def existentialFillerHalf : RawClause C R := {
  body := [.concept 1 (.var 7)]
  head := [.concept 3 (.fun 41 (.var 7))]
}

example : recognizeExistentialPair (Concept := C) (Role := R)
    existentialRoleHalf existentialFillerHalf =
    some (.existential 1 2 3) := by native_decide

example : recognizeExistentialPair (Concept := C) (Role := R)
    existentialFillerHalf existentialRoleHalf =
    some (.existential 1 2 3) := by native_decide

example : recognizeExistentialPair (Concept := C) (Role := R)
    existentialRoleHalf {
      body := [.concept 1 (.var 12)]
      head := [.concept 3 (.fun 41 (.var 12))]
    } = some (.existential 1 2 3) := by native_decide

example : recognizeExistentialPair (Concept := C) (Role := R) {
    body := [.concept 1 (.var 7)]
    head := [.role 2 (.var 8) (.fun 41 (.var 7))]
  } existentialFillerHalf = none := by native_decide

example : recognizeExistentialPair (Concept := C) (Role := R) existentialRoleHalf {
    body := [.concept 1 (.var 7)]
    head := [.concept 3 (.fun 42 (.var 7))]
  } = none := by native_decide

example : recognizeRawClause (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 8), .concept 2 (.var 8)]
    head := [.concept 3 (.var 8)]
  } = none := by native_decide

example : recognizeRawClause (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 7)]
    head := [.role 2 (.var 7) (.var 7)]
  } = none := by native_decide

example : recognizeRawClause (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 7), .role 2 (.var 7) (.var 9)]
    head := [.role 3 (.var 7) (.var 9)]
  } = none := by native_decide

end RawNormalizationExamples

end ContextCalculus.ELCompletion

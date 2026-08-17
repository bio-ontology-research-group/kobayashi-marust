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

/-- A role-half clause depends on its one Skolem function and no other term interpretation. -/
theorem rawExistentialRoleClause_congr {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (left right : RawTermInterp Domain)
    (sub : Concept) (role : Role) (variableId function : Nat)
    (hfunction : ∀ x, left.function function x = right.function function x) :
    satRawClause I left (rawExistentialRoleClause sub role variableId function) ↔
      satRawClause I right (rawExistentialRoleClause sub role variableId function) := by
  constructor
  · intro hleft env hbody
    have hsub := hbody (.concept sub (.var variableId)) (by
      simp [rawExistentialRoleClause])
    have hhead := hleft env (by
      intro atom hmem
      simp only [rawExistentialRoleClause, List.mem_singleton] at hmem
      subst atom
      exact hsub)
    simpa [rawExistentialRoleClause, satRawAtom, evalRawTerm, hfunction] using hhead
  · intro hright env hbody
    have hsub := hbody (.concept sub (.var variableId)) (by
      simp [rawExistentialRoleClause])
    have hhead := hright env (by
      intro atom hmem
      simp only [rawExistentialRoleClause, List.mem_singleton] at hmem
      subst atom
      exact hsub)
    simpa [rawExistentialRoleClause, satRawAtom, evalRawTerm, hfunction] using hhead

/-- A filler-half clause likewise depends only on its named Skolem function. -/
theorem rawExistentialFillerClause_congr {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (left right : RawTermInterp Domain)
    (sub filler : Concept) (variableId function : Nat)
    (hfunction : ∀ x, left.function function x = right.function function x) :
    satRawClause I left
        (rawExistentialFillerClause (Role := Role) sub filler variableId function) ↔
      satRawClause I right
        (rawExistentialFillerClause (Role := Role) sub filler variableId function) := by
  constructor
  · intro hleft env hbody
    have hsub := hbody (.concept sub (.var variableId)) (by
      simp [rawExistentialFillerClause])
    have hhead := hleft env (by
      intro atom hmem
      simp only [rawExistentialFillerClause, List.mem_singleton] at hmem
      subst atom
      exact hsub)
    simpa [rawExistentialFillerClause, satRawAtom, evalRawTerm, hfunction] using hhead
  · intro hright env hbody
    have hsub := hbody (.concept sub (.var variableId)) (by
      simp [rawExistentialFillerClause])
    have hhead := hright env (by
      intro atom hmem
      simp only [rawExistentialFillerClause, List.mem_singleton] at hmem
      subst atom
      exact hsub)
    have hfunction' : ∀ x, right.function function x = left.function function x :=
      fun x => (hfunction x).symm
    simpa [rawExistentialFillerClause, satRawAtom, evalRawTerm, hfunction'] using hhead

/-- One globally paired existential-introduction entry. -/
structure RawExistentialSpec (Concept Role : Type) where
  sub : Concept
  role : Role
  filler : Concept
  roleVariable : Nat
  fillerVariable : Nat
  function : Nat
deriving DecidableEq, Repr

def RawExistentialSpec.source (spec : RawExistentialSpec Concept Role) :
    SourceAxiom Concept Role :=
  .existential spec.sub spec.role spec.filler

def RawExistentialSpec.satisfied {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (spec : RawExistentialSpec Concept Role) : Prop :=
  satRawClause I T
      (rawExistentialRoleClause spec.sub spec.role spec.roleVariable spec.function) ∧
    satRawClause I T
      (rawExistentialFillerClause (Role := Role) spec.sub spec.filler
        spec.fillerVariable spec.function)

def modelsRawExistentials {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (specs : List (RawExistentialSpec Concept Role)) : Prop :=
  ∀ spec ∈ specs, spec.satisfied I T

theorem RawExistentialSpec.satisfied_iff_source {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (spec : RawExistentialSpec Concept Role) :
    (∃ T, spec.satisfied I T) ↔ satSourceAxiom I spec.source := by
  exact rawExistentialPair_sat_iff I base spec.sub spec.filler spec.role
    spec.roleVariable spec.fillerVariable spec.function

/-- Install one source existential's witness function into a shared raw interpretation. -/
noncomputable def RawExistentialSpec.extend {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (spec : RawExistentialSpec Concept Role)
    (hsource : satSourceAxiom I spec.source) : RawTermInterp Domain := by
  classical
  let witness : Domain → Domain := fun x =>
    if hx : I.concept spec.sub x then Classical.choose (hsource x hx) else x
  exact {
    base with
    function := fun name argument =>
      if name = spec.function then witness argument else base.function name argument
  }

theorem RawExistentialSpec.extend_other {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (spec : RawExistentialSpec Concept Role)
    (hsource : satSourceAxiom I spec.source) {other : Nat}
    (hne : other ≠ spec.function) (x : Domain) :
    (spec.extend I base hsource).function other x = base.function other x := by
  simp [RawExistentialSpec.extend, hne]

theorem RawExistentialSpec.extend_satisfies {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (spec : RawExistentialSpec Concept Role)
    (hsource : satSourceAxiom I spec.source) :
    spec.satisfied I (spec.extend I base hsource) := by
  classical
  constructor
  · intro env hbody
    have hsub : I.concept spec.sub (env spec.roleVariable) :=
      hbody (.concept spec.sub (.var spec.roleVariable)) (by
        simp [rawExistentialRoleClause])
    have hspec := Classical.choose_spec (hsource (env spec.roleVariable) hsub)
    refine ⟨.role spec.role (.var spec.roleVariable)
      (.fun spec.function (.var spec.roleVariable)), by simp [rawExistentialRoleClause], ?_⟩
    simpa [satRawAtom, evalRawTerm, RawExistentialSpec.extend, hsub] using hspec.1
  · intro env hbody
    have hsub : I.concept spec.sub (env spec.fillerVariable) :=
      hbody (.concept spec.sub (.var spec.fillerVariable)) (by
        simp [rawExistentialFillerClause])
    have hspec := Classical.choose_spec (hsource (env spec.fillerVariable) hsub)
    refine ⟨.concept spec.filler (.fun spec.function (.var spec.fillerVariable)),
      by simp [rawExistentialFillerClause], ?_⟩
    simpa [satRawAtom, evalRawTerm, RawExistentialSpec.extend, hsub] using hspec.2

/-- A pair's satisfaction depends only on its named Skolem function. -/
theorem RawExistentialSpec.satisfied_congr {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (left right : RawTermInterp Domain)
    (spec : RawExistentialSpec Concept Role)
    (hfunction : ∀ x, left.function spec.function x = right.function spec.function x) :
    spec.satisfied I left ↔ spec.satisfied I right := by
  constructor
  · rintro ⟨hrole, hfiller⟩
    exact ⟨(rawExistentialRoleClause_congr I left right spec.sub spec.role
      spec.roleVariable spec.function hfunction).mp hrole,
      (rawExistentialFillerClause_congr I left right spec.sub spec.filler
        spec.fillerVariable spec.function hfunction).mp hfiller⟩
  · rintro ⟨hrole, hfiller⟩
    exact ⟨(rawExistentialRoleClause_congr I left right spec.sub spec.role
      spec.roleVariable spec.function hfunction).mpr hrole,
      (rawExistentialFillerClause_congr I left right spec.sub spec.filler
        spec.fillerVariable spec.function hfunction).mpr hfiller⟩

/-- Every shared raw model of the pairs is a model of their source axioms. -/
theorem modelsRawExistentials_sound {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (specs : List (RawExistentialSpec Concept Role))
    (hraw : modelsRawExistentials I T specs) :
    modelsSource I (specs.map RawExistentialSpec.source) := by
  intro source hsource
  simp only [List.mem_map] at hsource
  obtain ⟨spec, hspec, rfl⟩ := hsource
  exact rawExistentialPair_sound I T spec.sub spec.filler spec.role
    spec.roleVariable spec.fillerVariable spec.function (hraw spec hspec).1 (hraw spec hspec).2

/-- Distinct Skolem IDs let all source witnesses coexist in one interpretation. -/
theorem modelsRawExistentials_complete {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (specs : List (RawExistentialSpec Concept Role))
    (hunique : (specs.map RawExistentialSpec.function).Nodup)
    (hsource : modelsSource I (specs.map RawExistentialSpec.source)) :
    ∃ T, modelsRawExistentials I T specs := by
  induction specs with
  | nil => exact ⟨base, by simp [modelsRawExistentials]⟩
  | cons head tail ih =>
      rw [List.map_cons, modelsSource_cons] at hsource
      simp only [List.map_cons, List.nodup_cons] at hunique
      obtain ⟨hhead, htail⟩ := hsource
      obtain ⟨hnotmem, htailUnique⟩ := hunique
      obtain ⟨tailInterp, htailRaw⟩ := ih htailUnique htail
      let combined := head.extend I tailInterp hhead
      refine ⟨combined, ?_⟩
      intro spec hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact RawExistentialSpec.extend_satisfies I tailInterp spec hhead
      · have hne : spec.function ≠ head.function := by
          intro heq
          apply hnotmem
          exact List.mem_map.mpr ⟨spec, hmem, heq⟩
        have hfunction : ∀ x, combined.function spec.function x =
            tailInterp.function spec.function x := by
          intro x
          exact RawExistentialSpec.extend_other I tailInterp head hhead hne x
        exact (RawExistentialSpec.satisfied_congr I combined tailInterp spec hfunction).mpr
          (htailRaw spec hmem)

/-- With distinct Skolem IDs, the paired raw list and source list are equisatisfiable. -/
theorem modelsRawExistentials_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (base : RawTermInterp Domain)
    (specs : List (RawExistentialSpec Concept Role))
    (hunique : (specs.map RawExistentialSpec.function).Nodup) :
    (∃ T, modelsRawExistentials I T specs) ↔
      modelsSource I (specs.map RawExistentialSpec.source) := by
  constructor
  · rintro ⟨T, hraw⟩
    exact modelsRawExistentials_sound I T specs hraw
  · exact modelsRawExistentials_complete I base specs hunique

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

/-- Decoding a concept-only body preserves exactly its conjunction semantics. -/
theorem allConceptsOn_holdsRawAtoms_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (env : Nat → Domain) (varId : Nat) (atoms : List (RawAtom Concept Role))
    (concepts : List Concept) (hdecode : allConceptsOn varId atoms = some concepts) :
    holdsRawAtoms I T env atoms ↔ holdsBody I concepts (env varId) := by
  induction atoms generalizing concepts with
  | nil =>
      simp only [allConceptsOn, Option.some.injEq] at hdecode
      subst concepts
      simp [holdsRawAtoms, holdsBody]
  | cons atom rest ih =>
      cases atom with
      | role role source target => simp [allConceptsOn] at hdecode
      | concept concept term =>
          cases term with
          | var actual =>
              simp only [allConceptsOn] at hdecode
              split at hdecode
              next heq =>
                subst actual
                cases hrest : allConceptsOn varId rest with
                | none => simp [hrest] at hdecode
                | some tail =>
                    simp [hrest] at hdecode
                    subst concepts
                    rw [holdsBody_cons, ← ih tail hrest]
                    simp [holdsRawAtoms, satRawAtom, evalRawTerm]
              next hne => simp at hdecode
          | ind name => simp [allConceptsOn] at hdecode
          | aux root label => simp [allConceptsOn] at hdecode
          | «fun» function argument => simp [allConceptsOn] at hdecode

/-- A raw concept-head clause is exactly its reconstructed subclass axiom. -/
theorem rawConceptClause_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (atoms : List (RawAtom Concept Role)) (concepts : List Concept)
    (sup : Concept) (varId : Nat)
    (hdecode : allConceptsOn varId atoms = some concepts) :
    satRawClause I T { body := atoms, head := [.concept sup (.var varId)] } ↔
      satSourceAxiom I (.sub concepts sup) := by
  constructor
  · intro hraw x hbody
    let env : Nat → Domain := fun _ => x
    have hrawBody : holdsRawAtoms I T env atoms :=
      (allConceptsOn_holdsRawAtoms_iff I T env varId atoms concepts hdecode).2 hbody
    have hhead := hraw env hrawBody
    simpa [satRawAtom, evalRawTerm, env] using hhead
  · intro hsource env hbody
    refine ⟨.concept sup (.var varId), by simp, ?_⟩
    exact hsource (env varId)
      ((allConceptsOn_holdsRawAtoms_iff I T env varId atoms concepts hdecode).1 hbody)

/-- A raw empty-head concept clause is exactly its reconstructed bottom axiom. -/
theorem rawBottomClause_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (atoms : List (RawAtom Concept Role)) (concepts : List Concept) (varId : Nat)
    (hdecode : allConceptsOn varId atoms = some concepts) :
    satRawClause I T { body := atoms, head := [] } ↔
      satSourceAxiom I (.bottom concepts) := by
  constructor
  · intro hraw x hbody
    let env : Nat → Domain := fun _ => x
    have hrawBody : holdsRawAtoms I T env atoms :=
      (allConceptsOn_holdsRawAtoms_iff I T env varId atoms concepts hdecode).2 hbody
    simpa using hraw env hrawBody
  · intro hsource env hbody
    have hfalse := hsource (env varId)
      ((allConceptsOn_holdsRawAtoms_iff I T env varId atoms concepts hdecode).1 hbody)
    exact False.elim hfalse

/-- The role-first raw restriction clause is exactly existential elimination. -/
theorem rawExistsElimRoleFirst_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (role : Role) (filler sup : Concept) (source target : Nat)
    (hne : source ≠ target) :
    satRawClause I T {
      body := [.role role (.var source) (.var target),
        .concept filler (.var target)]
      head := [.concept sup (.var source)]
    } ↔ satSourceAxiom I (.existsElim role filler sup) := by
  constructor
  · intro hraw x hexists
    rcases hexists with ⟨y, hrole, hfiller⟩
    let env : Nat → Domain := Function.update (fun _ => x) target y
    have hbody : holdsRawAtoms I T env
        [.role role (.var source) (.var target), .concept filler (.var target)] := by
      simp [holdsRawAtoms, satRawAtom, evalRawTerm, env, hne, hrole, hfiller]
    have hhead := hraw env hbody
    simpa [satRawAtom, evalRawTerm, env, hne] using hhead
  · intro hsource env hbody
    refine ⟨.concept sup (.var source), by simp, ?_⟩
    apply hsource (env source)
    refine ⟨env target, ?_, ?_⟩
    · exact hbody (.role role (.var source) (.var target)) (by simp)
    · exact hbody (.concept filler (.var target)) (by simp)

/-- Atom order does not change existential-elimination semantics. -/
theorem rawExistsElimConceptFirst_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (role : Role) (filler sup : Concept) (source target : Nat)
    (hne : source ≠ target) :
    satRawClause I T {
      body := [.concept filler (.var target),
        .role role (.var source) (.var target)]
      head := [.concept sup (.var source)]
    } ↔ satSourceAxiom I (.existsElim role filler sup) := by
  constructor
  · intro hraw x hexists
    rcases hexists with ⟨y, hrole, hfiller⟩
    let env : Nat → Domain := Function.update (fun _ => x) target y
    have hbody : holdsRawAtoms I T env
        [.concept filler (.var target), .role role (.var source) (.var target)] := by
      simp [holdsRawAtoms, satRawAtom, evalRawTerm, env, hne, hrole, hfiller]
    have hhead := hraw env hbody
    simpa [satRawAtom, evalRawTerm, env, hne] using hhead
  · intro hsource env hbody
    refine ⟨.concept sup (.var source), by simp, ?_⟩
    apply hsource (env source)
    refine ⟨env target, ?_, ?_⟩
    · exact hbody (.role role (.var source) (.var target)) (by simp)
    · exact hbody (.concept filler (.var target)) (by simp)

/-- A lone role body uses semantic top as its existential filler. -/
theorem rawExistsElimTop_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (role : Role) (sup : Concept) (source target : Nat) (hne : source ≠ target) :
    satRawClause I T {
      body := [.role role (.var source) (.var target)]
      head := [.concept sup (.var source)]
    } ↔ satSourceAxiom I (.existsElim role top sup) := by
  constructor
  · intro hraw x hexists
    rcases hexists with ⟨y, hrole, _htop⟩
    let env : Nat → Domain := Function.update (fun _ => x) target y
    have hbody : holdsRawAtoms I T env [.role role (.var source) (.var target)] := by
      simp [holdsRawAtoms, satRawAtom, evalRawTerm, env, hne, hrole]
    have hhead := hraw env hbody
    simpa [satRawAtom, evalRawTerm, env, hne] using hhead
  · intro hsource env hbody
    refine ⟨.concept sup (.var source), by simp, ?_⟩
    apply hsource (env source)
    exact ⟨env target,
      hbody (.role role (.var source) (.var target)) (by simp),
      I.top_true (env target)⟩

/-- A correctly wired raw role implication is exactly role inclusion. -/
theorem rawRoleSub_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (sub sup : Role) (source target : Nat) (hne : source ≠ target) :
    satRawClause I T {
      body := [.role sub (.var source) (.var target)]
      head := [.role sup (.var source) (.var target)]
    } ↔ satSourceAxiom I (.roleSub sub sup) := by
  constructor
  · intro hraw x y hsub
    let env : Nat → Domain := Function.update (fun _ => x) target y
    have hbody : holdsRawAtoms I T env [.role sub (.var source) (.var target)] := by
      simp [holdsRawAtoms, satRawAtom, evalRawTerm, env, hne, hsub]
    have hhead := hraw env hbody
    simpa [satRawAtom, evalRawTerm, env, hne] using hhead
  · intro hsource env hbody
    refine ⟨.role sup (.var source) (.var target), by simp, ?_⟩
    exact hsource (env source) (env target)
      (hbody (.role sub (.var source) (.var target)) (by simp))

/-- An empty-body self-edge fact is exactly role reflexivity. -/
theorem rawReflexive_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (role : Role) (variableId : Nat) :
    satRawClause I T {
      body := []
      head := [.role role (.var variableId) (.var variableId)]
    } ↔ satSourceAxiom I (.reflexive role) := by
  constructor
  · intro hraw x
    let env : Nat → Domain := fun _ => x
    have hhead := hraw env (by simp [holdsRawAtoms])
    simpa [satRawAtom, evalRawTerm, env] using hhead
  · intro hsource env _hbody
    exact ⟨.role role (.var variableId) (.var variableId), by simp,
      hsource (env variableId)⟩

/-- A connected three-variable raw role chain has exactly role-chain semantics. -/
theorem rawRoleChain_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (first second sup : Role) (source middle target : Nat)
    (hsm : source ≠ middle) (hmt : middle ≠ target) (hst : source ≠ target) :
    satRawClause I T {
      body := [.role first (.var source) (.var middle),
        .role second (.var middle) (.var target)]
      head := [.role sup (.var source) (.var target)]
    } ↔ satSourceAxiom I (.roleChain first second sup) := by
  constructor
  · intro hraw x y z hfirst hsecond
    let env : Nat → Domain :=
      Function.update (Function.update (fun _ => x) middle y) target z
    have hbody : holdsRawAtoms I T env
        [.role first (.var source) (.var middle),
          .role second (.var middle) (.var target)] := by
      simp [holdsRawAtoms, satRawAtom, evalRawTerm, env, hsm, hmt, hst,
        hfirst, hsecond]
    have hhead := hraw env hbody
    simpa [satRawAtom, evalRawTerm, env, hsm, hmt, hst] using hhead
  · intro hsource env hbody
    refine ⟨.role sup (.var source) (.var target), by simp, ?_⟩
    exact hsource (env source) (env middle) (env target)
      (hbody (.role first (.var source) (.var middle)) (by simp))
      (hbody (.role second (.var middle) (.var target)) (by simp))

/-- Reversing the two body atoms preserves the same connected chain. -/
theorem rawRoleChainReversed_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (first second sup : Role) (source middle target : Nat)
    (hsm : source ≠ middle) (hmt : middle ≠ target) (hst : source ≠ target) :
    satRawClause I T {
      body := [.role second (.var middle) (.var target),
        .role first (.var source) (.var middle)]
      head := [.role sup (.var source) (.var target)]
    } ↔ satSourceAxiom I (.roleChain first second sup) := by
  constructor
  · intro hraw x y z hfirst hsecond
    let env : Nat → Domain :=
      Function.update (Function.update (fun _ => x) middle y) target z
    have hbody : holdsRawAtoms I T env
        [.role second (.var middle) (.var target),
          .role first (.var source) (.var middle)] := by
      simp [holdsRawAtoms, satRawAtom, evalRawTerm, env, hsm, hmt, hst,
        hfirst, hsecond]
    have hhead := hraw env hbody
    simpa [satRawAtom, evalRawTerm, env, hsm, hmt, hst] using hhead
  · intro hsource env hbody
    refine ⟨.role sup (.var source) (.var target), by simp, ?_⟩
    exact hsource (env source) (env middle) (env target)
      (hbody (.role first (.var source) (.var middle)) (by simp))
      (hbody (.role second (.var middle) (.var target)) (by simp))

/-- Exact accepted shape of a raw existential-elimination body. -/
inductive RawExistsElimBody (Concept Role : Type) where
  | top (role : Role) (source target : Nat)
  | roleFirst (role : Role) (filler : Concept) (source target : Nat)
  | conceptFirst (role : Role) (filler : Concept) (source target : Nat)
deriving DecidableEq, Repr

def RawExistsElimBody.role : RawExistsElimBody Concept Role → Role
  | .top role _ _ | .roleFirst role _ _ _ | .conceptFirst role _ _ _ => role

def RawExistsElimBody.filler (top : Concept) : RawExistsElimBody Concept Role → Concept
  | .top _ _ _ => top
  | .roleFirst _ filler _ _ | .conceptFirst _ filler _ _ => filler

/-- Recognize a role restriction body in either frontend atom order. -/
def recognizeExistsElimBody (headVar : Nat) :
    List (RawAtom Concept Role) → Option (RawExistsElimBody Concept Role)
  | [.role role (.var source) (.var target)] =>
      if headVar = source && source != target then some (.top role source target) else none
  | [.role role (.var source) (.var target), .concept filler (.var fillerVar)]
      =>
      if headVar = source && source != target && fillerVar = target then
        some (.roleFirst role filler source target)
      else none
  | [.concept filler (.var fillerVar), .role role (.var source) (.var target)] =>
      if headVar = source && source != target && fillerVar = target then
        some (.conceptFirst role filler source target)
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
          match recognizeExistsElimBody headVar clause.body with
          | some recognized =>
              some (.existsElim recognized.role (recognized.filler top) sup)
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

/-- The executable empty-head branch returns only a semantically exact bottom axiom. -/
theorem recognizeRawBottom_sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (body : List (RawAtom Concept Role)) (source : SourceAxiom Concept Role)
    (hrecognize : recognizeRawClause top { body := body, head := [] } = some source) :
    satRawClause I T { body := body, head := [] } ↔ satSourceAxiom I source := by
  cases body with
  | nil => simp [recognizeRawClause] at hrecognize
  | cons atom rest =>
      cases atom with
      | role role sourceTerm targetTerm => simp [recognizeRawClause] at hrecognize
      | concept concept term =>
          cases term with
          | var varId =>
              cases hdecode : allConceptsOn varId (.concept concept (.var varId) :: rest) with
              | none => simp [recognizeRawClause, hdecode] at hrecognize
              | some concepts =>
                  simp [recognizeRawClause, hdecode] at hrecognize
                  subst source
                  exact rawBottomClause_sat_iff I T
                    (.concept concept (.var varId) :: rest) concepts varId hdecode
          | ind name => simp [recognizeRawClause] at hrecognize
          | aux root label => simp [recognizeRawClause] at hrecognize
          | «fun» function argument => simp [recognizeRawClause] at hrecognize

/-! ## Proof-producing direct normalization -/

/--
A typed witness for one accepted direct raw clause.  Its indices retain the
exact input clause and reconstructed source axiom, while constructor fields
retain every variable-wiring condition needed by the semantic proof.
-/
inductive RawDirectEvidence (top : Concept) :
    RawClause Concept Role → SourceAxiom Concept Role → Type where
  | sub (body : List (RawAtom Concept Role)) (concepts : List Concept)
      (sup : Concept) (variableId : Nat)
      (hdecode : allConceptsOn variableId body = some concepts) :
      RawDirectEvidence top
        { body := body, head := [.concept sup (.var variableId)] }
        (.sub concepts sup)
  | bottom (body : List (RawAtom Concept Role)) (concepts : List Concept)
      (variableId : Nat)
      (hdecode : allConceptsOn variableId body = some concepts) :
      RawDirectEvidence top { body := body, head := [] } (.bottom concepts)
  | existsTop (role : Role) (sup : Concept) (source target : Nat)
      (hne : source ≠ target) :
      RawDirectEvidence top {
        body := [.role role (.var source) (.var target)]
        head := [.concept sup (.var source)]
      } (.existsElim role top sup)
  | existsRoleFirst (role : Role) (filler sup : Concept) (source target : Nat)
      (hne : source ≠ target) :
      RawDirectEvidence top {
        body := [.role role (.var source) (.var target),
          .concept filler (.var target)]
        head := [.concept sup (.var source)]
      } (.existsElim role filler sup)
  | existsConceptFirst (role : Role) (filler sup : Concept) (source target : Nat)
      (hne : source ≠ target) :
      RawDirectEvidence top {
        body := [.concept filler (.var target),
          .role role (.var source) (.var target)]
        head := [.concept sup (.var source)]
      } (.existsElim role filler sup)
  | roleSub (sub sup : Role) (source target : Nat) (hne : source ≠ target) :
      RawDirectEvidence top {
        body := [.role sub (.var source) (.var target)]
        head := [.role sup (.var source) (.var target)]
      } (.roleSub sub sup)
  | roleChain (first second sup : Role) (source middle target : Nat)
      (hsm : source ≠ middle) (hmt : middle ≠ target) (hst : source ≠ target) :
      RawDirectEvidence top {
        body := [.role first (.var source) (.var middle),
          .role second (.var middle) (.var target)]
        head := [.role sup (.var source) (.var target)]
      } (.roleChain first second sup)
  | roleChainReversed (first second sup : Role) (source middle target : Nat)
      (hsm : source ≠ middle) (hmt : middle ≠ target) (hst : source ≠ target) :
      RawDirectEvidence top {
        body := [.role second (.var middle) (.var target),
          .role first (.var source) (.var middle)]
        head := [.role sup (.var source) (.var target)]
      } (.roleChain first second sup)
  | reflexive (role : Role) (variableId : Nat) :
      RawDirectEvidence top {
        body := []
        head := [.role role (.var variableId) (.var variableId)]
      } (.reflexive role)

/-- Every typed direct-normalization witness carries an exact semantic refinement. -/
theorem RawDirectEvidence.sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    {raw : RawClause Concept Role} {source : SourceAxiom Concept Role}
    (evidence : RawDirectEvidence top raw source) :
    satRawClause I T raw ↔ satSourceAxiom I source := by
  cases evidence with
  | sub body concepts sup variableId hdecode =>
      exact rawConceptClause_sat_iff I T body concepts sup variableId hdecode
  | bottom body concepts variableId hdecode =>
      exact rawBottomClause_sat_iff I T body concepts variableId hdecode
  | existsTop role sup source target hne =>
      exact rawExistsElimTop_sat_iff I T role sup source target hne
  | existsRoleFirst role filler sup source target hne =>
      exact rawExistsElimRoleFirst_sat_iff I T role filler sup source target hne
  | existsConceptFirst role filler sup source target hne =>
      exact rawExistsElimConceptFirst_sat_iff I T role filler sup source target hne
  | roleSub sub sup source target hne =>
      exact rawRoleSub_sat_iff I T sub sup source target hne
  | roleChain first second sup source middle target hsm hmt hst =>
      exact rawRoleChain_sat_iff I T first second sup source middle target hsm hmt hst
  | roleChainReversed first second sup source middle target hsm hmt hst =>
      exact rawRoleChainReversed_sat_iff I T first second sup source middle target hsm hmt hst
  | reflexive role variableId => exact rawReflexive_sat_iff I T role variableId

/-- A source axiom, canonical raw clause, and proof that the input is exactly that clause. -/
structure RawDirectCertificate (top : Concept) (input : RawClause Concept Role) where
  source : SourceAxiom Concept Role
  canonical : RawClause Concept Role
  evidence : RawDirectEvidence top canonical source
  input_eq : input = canonical

theorem RawDirectCertificate.sat_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    {input : RawClause Concept Role} (certificate : RawDirectCertificate top input) :
    satRawClause I T input ↔ satSourceAxiom I certificate.source := by
  cases certificate with
  | mk source canonical evidence input_eq =>
      cases input_eq
      exact evidence.sat_iff I T

/-- Proof-producing normalization for a raw concept-head clause. -/
def certifyRawConceptHead (top : Concept)
    (body : List (RawAtom Concept Role)) (sup : Concept) (headVar : Nat) :
    Option (RawDirectCertificate top
      { body := body, head := [.concept sup (.var headVar)] }) :=
  match hdecode : allConceptsOn headVar body with
  | some concepts => some {
      source := .sub concepts sup
      canonical := { body := body, head := [.concept sup (.var headVar)] }
      evidence := .sub body concepts sup headVar hdecode
      input_eq := rfl
    }
  | none =>
      match body with
      | [.role role (.var source) (.var target)] =>
          if h : headVar = source ∧ source ≠ target then
            some {
              source := .existsElim role top sup
              canonical := {
                body := [.role role (.var source) (.var target)]
                head := [.concept sup (.var source)]
              }
              evidence := .existsTop role sup source target h.2
              input_eq := by simp [h.1]
            }
          else none
      | [.role role (.var source) (.var target), .concept filler (.var fillerVar)] =>
          if h : headVar = source ∧ source ≠ target ∧ fillerVar = target then
            some {
              source := .existsElim role filler sup
              canonical := {
                body := [.role role (.var source) (.var target),
                  .concept filler (.var target)]
                head := [.concept sup (.var source)]
              }
              evidence := .existsRoleFirst role filler sup source target h.2.1
              input_eq := by simp [h.1, h.2.2]
            }
          else none
      | [.concept filler (.var fillerVar), .role role (.var source) (.var target)] =>
          if h : headVar = source ∧ source ≠ target ∧ fillerVar = target then
            some {
              source := .existsElim role filler sup
              canonical := {
                body := [.concept filler (.var target),
                  .role role (.var source) (.var target)]
                head := [.concept sup (.var source)]
              }
              evidence := .existsConceptFirst role filler sup source target h.2.1
              input_eq := by simp [h.1, h.2.2]
            }
          else none
      | _ => none

/-- Proof-producing normalization for a raw empty-head clause. -/
def certifyRawBottom (top : Concept) (body : List (RawAtom Concept Role)) :
    Option (RawDirectCertificate top { body := body, head := [] }) :=
  match body with
  | .concept concept (.var variableId) :: tail =>
      match hdecode : allConceptsOn variableId
          (.concept concept (.var variableId) :: tail) with
      | some concepts => some {
          source := .bottom concepts
          canonical := {
            body := .concept concept (.var variableId) :: tail
            head := []
          }
          evidence := .bottom (.concept concept (.var variableId) :: tail)
            concepts variableId hdecode
          input_eq := rfl
        }
      | none => none
  | _ => none

/-- Proof-producing normalization for a raw role-head clause. -/
def certifyRawRoleHead (top : Concept)
    (body : List (RawAtom Concept Role)) (sup : Role) (headSource headTarget : Nat) :
    Option (RawDirectCertificate top {
      body := body
      head := [.role sup (.var headSource) (.var headTarget)]
    }) :=
  match body with
  | [] =>
      if h : headSource = headTarget then
        some {
          source := .reflexive sup
          canonical := {
            body := []
            head := [.role sup (.var headSource) (.var headSource)]
          }
          evidence := .reflexive sup headSource
          input_eq := by simp [h]
        }
      else none
  | [.role sub (.var bodySource) (.var bodyTarget)] =>
      if h : headSource ≠ headTarget ∧
          bodySource = headSource ∧ bodyTarget = headTarget then
        some {
          source := .roleSub sub sup
          canonical := {
            body := [.role sub (.var headSource) (.var headTarget)]
            head := [.role sup (.var headSource) (.var headTarget)]
          }
          evidence := .roleSub sub sup headSource headTarget h.1
          input_eq := by simp [h.2.1, h.2.2]
        }
      else none
  | [.role first (.var a0) (.var a1), .role second (.var b0) (.var b1)] =>
      if h : a0 ≠ a1 ∧ a1 ≠ b1 ∧ a0 ≠ b1 ∧
          a1 = b0 ∧ headSource = a0 ∧ headTarget = b1 then
        some {
          source := .roleChain first second sup
          canonical := {
            body := [.role first (.var a0) (.var a1),
              .role second (.var a1) (.var b1)]
            head := [.role sup (.var a0) (.var b1)]
          }
          evidence := .roleChain first second sup a0 a1 b1 h.1 h.2.1 h.2.2.1
          input_eq := by simp [h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
        }
      else if h : b0 ≠ b1 ∧ b1 ≠ a1 ∧ b0 ≠ a1 ∧
          b1 = a0 ∧ headSource = b0 ∧ headTarget = a1 then
        some {
          source := .roleChain second first sup
          canonical := {
            body := [.role first (.var b1) (.var a1),
              .role second (.var b0) (.var b1)]
            head := [.role sup (.var b0) (.var a1)]
          }
          evidence := .roleChainReversed second first sup b0 b1 a1
            h.1 h.2.1 h.2.2.1
          input_eq := by simp [h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
        }
      else none
  | _ => none

/--
Total proof-producing normalizer for every single-clause direct ELC form.
Existential introduction remains the separate two-clause certifier above.
-/
def certifyRawDirect (top : Concept) :
    (input : RawClause Concept Role) → Option (RawDirectCertificate top input)
  | { body, head := [] } => certifyRawBottom top body
  | { body, head := [.concept sup (.var headVar)] } =>
      certifyRawConceptHead top body sup headVar
  | { body, head := [.role sup (.var headSource) (.var headTarget)] } =>
      certifyRawRoleHead top body sup headSource headTarget
  | _ => none

/-- Erase proof data when only the executable reconstructed source axiom is needed. -/
def certifiedRawSource (top : Concept) (input : RawClause Concept Role) :
    Option (SourceAxiom Concept Role) :=
  (certifyRawDirect top input).map (RawDirectCertificate.source)

/-! ## Proof-producing direct-list normalization -/

def modelsRaw {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (clauses : List (RawClause Concept Role)) : Prop :=
  ∀ clause ∈ clauses, satRawClause I T clause

theorem modelsRaw_cons {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    (head : RawClause Concept Role) (tail : List (RawClause Concept Role)) :
    modelsRaw I T (head :: tail) ↔ satRawClause I T head ∧ modelsRaw I T tail := by
  simp [modelsRaw]

/-- Pointwise direct certificates for an exact raw list and source ontology. -/
inductive RawDirectListEvidence (top : Concept) :
    List (RawClause Concept Role) → SourceOntology Concept Role → Type where
  | nil : RawDirectListEvidence top [] []
  | cons {raw : RawClause Concept Role} {raws : List (RawClause Concept Role)}
      (head : RawDirectCertificate top raw) {sources : SourceOntology Concept Role}
      (tail : RawDirectListEvidence top raws sources) :
      RawDirectListEvidence top (raw :: raws) (head.source :: sources)

/-- A direct-list witness preserves and reflects the models of the whole list. -/
theorem RawDirectListEvidence.models_iff {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (T : RawTermInterp Domain)
    {raws : List (RawClause Concept Role)} {sources : SourceOntology Concept Role}
    (evidence : RawDirectListEvidence top raws sources) :
    modelsRaw I T raws ↔ modelsSource I sources := by
  induction evidence with
  | nil => simp [modelsRaw, modelsSource]
  | cons head tail ih =>
      rw [modelsRaw_cons, modelsSource_cons, head.sat_iff I T, ih]

/-- Executable proof-producing normalization when every list entry is direct. -/
def certifyRawDirectList (top : Concept) :
    (raws : List (RawClause Concept Role)) →
      Option (Sigma fun sources : SourceOntology Concept Role =>
        RawDirectListEvidence top raws sources)
  | [] => some ⟨[], .nil⟩
  | raw :: raws => do
      let head ← certifyRawDirect top raw
      let tail ← certifyRawDirectList top raws
      return ⟨head.source :: tail.1, .cons head tail.2⟩

def certifiedRawSources (top : Concept) (raws : List (RawClause Concept Role)) :
    Option (SourceOntology Concept Role) :=
  (certifyRawDirectList top raws).map Sigma.fst

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

example : certifiedRawSource (Concept := C) (Role := R) 0 {
    body := [.concept 1 (.var 7), .concept 2 (.var 7)]
    head := [.concept 3 (.var 7)]
  } = some (.sub [1, 2] 3) := by native_decide

example : certifiedRawSource (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 8), .concept 2 (.var 8)]
    head := [.concept 3 (.var 7)]
  } = some (.existsElim 1 2 3) := by native_decide

example : certifiedRawSource (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 8), .role 2 (.var 8) (.var 9)]
    head := [.role 3 (.var 7) (.var 9)]
  } = some (.roleChain 1 2 3) := by native_decide

example : certifiedRawSource (Concept := C) (Role := R) 0 {
    body := [.role 2 (.var 8) (.var 9), .role 1 (.var 7) (.var 8)]
    head := [.role 3 (.var 7) (.var 9)]
  } = some (.roleChain 1 2 3) := by native_decide

example : certifiedRawSource (Concept := C) (Role := R) 0 {
    body := [.role 1 (.var 7) (.var 7)]
    head := [.role 2 (.var 7) (.var 7)]
  } = none := by native_decide

example : certifiedRawSources (Concept := C) (Role := R) 0 [
    { body := [.concept 1 (.var 7)], head := [.concept 2 (.var 7)] },
    { body := [.role 1 (.var 7) (.var 8), .concept 2 (.var 8)],
      head := [.concept 3 (.var 7)] },
    { body := [.role 1 (.var 7) (.var 8), .role 2 (.var 8) (.var 9)],
      head := [.role 3 (.var 7) (.var 9)] }
  ] = some [.sub [1] 2, .existsElim 1 2 3, .roleChain 1 2 3] := by native_decide

example : certifiedRawSources (Concept := C) (Role := R) 0 [
    { body := [.concept 1 (.var 7)], head := [.concept 2 (.var 7)] },
    { body := [.concept 1 (.var 7), .concept 2 (.var 8)],
      head := [.concept 3 (.var 7)] }
  ] = none := by native_decide

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

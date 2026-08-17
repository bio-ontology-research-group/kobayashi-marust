import ContextCalculus.ELCompletion
import Mathlib.Data.List.Forall2

/-!
# Semantic source language for the pure ELC frontend

The Rust frontend emits first-order clauses, while `elcomplete.rs` recognizes
those clauses as EL axioms and interns NF1–NF7.  This module introduces the
semantic source-axiom layer at that boundary.  In particular, existential
introduction is represented as one source axiom even though the JSON frontend
encodes it as a role/filler pair sharing a Skolem function.

`normalizeDirect` covers every source form whose translation needs no fresh
auxiliary concept.  `normalizeDirect_sat_iff` proves that successful
normalization preserves and reflects satisfaction.  N-ary conjunctions are
deliberately returned as `none`; their conservative auxiliary expansion and
the executable raw-clause recognizer are separate refinement obligations.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type}

/-- EL axioms reconstructed from the frontend's normalized Horn clauses. -/
inductive SourceAxiom (Concept Role : Type) where
  | sub (body : List Concept) (sup : Concept)
  | bottom (body : List Concept)
  | existential (sub : Concept) (role : Role) (filler : Concept)
  | existsElim (role : Role) (filler sup : Concept)
  | roleSub (sub sup : Role)
  | roleChain (first second sup : Role)
  | reflexive (role : Role)
deriving DecidableEq

abbrev SourceOntology (Concept Role : Type) := List (SourceAxiom Concept Role)

def holdsBody {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (body : List Concept) (x : Domain) : Prop :=
  ∀ concept ∈ body, I.concept concept x

def satSourceAxiom {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) : SourceAxiom Concept Role → Prop
  | .sub body sup => ∀ x, holdsBody I body x → I.concept sup x
  | .bottom body => ∀ x, holdsBody I body x → False
  | .existential sub role filler =>
      ∀ x, I.concept sub x → ∃ y, I.role role x y ∧ I.concept filler y
  | .existsElim role filler sup =>
      ∀ x, (∃ y, I.role role x y ∧ I.concept filler y) → I.concept sup x
  | .roleSub sub sup => ∀ x y, I.role sub x y → I.role sup x y
  | .roleChain first second sup =>
      ∀ x y z, I.role first x y → I.role second y z → I.role sup x z
  | .reflexive role => ∀ x, I.role role x x

def modelsSource {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (O : SourceOntology Concept Role) : Prop :=
  ∀ ax ∈ O, satSourceAxiom I ax

/--
Translate exactly the source forms that do not introduce conjunction
auxiliaries.  This matches Rust's direct NF1–NF7 branches; conjunctions with
more than two body concepts and bottom conjunctions with more than one body
concept are handled by the auxiliary-expansion layer.
-/
def normalizeDirect (top : Concept) : SourceAxiom Concept Role → Option (Clause Concept Role)
  | .sub [] sup => some (.nf1 top sup)
  | .sub [sub] sup => some (.nf1 sub sup)
  | .sub [left, right] sup => some (.nf2 left right sup)
  | .sub _ _ => none
  | .bottom [sub] => some (.nf5 sub)
  | .bottom _ => none
  | .existential sub role filler => some (.nf3 sub role filler)
  | .existsElim role filler sup => some (.nf4 role filler sup)
  | .roleSub sub sup => some (.nf6 sub sup)
  | .roleChain first second sup => some (.nf7 first second sup)
  | .reflexive role => some (.reflexive role)

theorem holdsBody_nil {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (x : Domain) :
    holdsBody I [] x := by
  intro concept hmem
  contradiction

theorem holdsBody_singleton {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (concept : Concept) (x : Domain) :
    holdsBody I [concept] x ↔ I.concept concept x := by
  simp [holdsBody]

theorem holdsBody_pair {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (left right : Concept) (x : Domain) :
    holdsBody I [left, right] x ↔ I.concept left x ∧ I.concept right x := by
  simp [holdsBody]

/-- Every successful direct frontend normalization is semantically exact. -/
theorem normalizeDirect_sat_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (source : SourceAxiom Concept Role) (normal : Clause Concept Role)
    (hnorm : normalizeDirect top source = some normal) :
    satSourceAxiom I source ↔ satClause I normal := by
  cases source with
  | sub body sup =>
      cases body with
      | nil =>
          simp only [normalizeDirect, Option.some.injEq] at hnorm
          subst normal
          constructor
          · intro hsource x _
            exact hsource x (holdsBody_nil I x)
          · intro hnormal x _
            exact hnormal x (I.top_true x)
      | cons first tail =>
          cases tail with
          | nil =>
              simp only [normalizeDirect, Option.some.injEq] at hnorm
              subst normal
              simp only [satSourceAxiom, satClause]
              constructor
              · intro hsource x hx
                exact hsource x ((holdsBody_singleton I first x).2 hx)
              · intro hnormal x hbody
                exact hnormal x ((holdsBody_singleton I first x).1 hbody)
          | cons second rest =>
              cases rest with
              | nil =>
                  simp only [normalizeDirect, Option.some.injEq] at hnorm
                  subst normal
                  simp only [satSourceAxiom, satClause]
                  constructor
                  · intro hsource x hl hr
                    exact hsource x ((holdsBody_pair I first second x).2 ⟨hl, hr⟩)
                  · intro hnormal x hbody
                    have h := (holdsBody_pair I first second x).1 hbody
                    exact hnormal x h.1 h.2
              | cons third rest => cases hnorm
  | bottom body =>
      cases body with
      | nil => cases hnorm
      | cons first tail =>
          cases tail with
          | nil =>
              simp only [normalizeDirect, Option.some.injEq] at hnorm
              subst normal
              simp only [satSourceAxiom, satClause]
              constructor
              · intro hsource x hx
                exact hsource x ((holdsBody_singleton I first x).2 hx)
              · intro hnormal x hbody
                exact hnormal x ((holdsBody_singleton I first x).1 hbody)
          | cons second rest => cases hnorm
  | existential sub role filler =>
      simp only [normalizeDirect, Option.some.injEq] at hnorm
      subst normal
      rfl
  | existsElim role filler sup =>
      simp only [normalizeDirect, Option.some.injEq] at hnorm
      subst normal
      rfl
  | roleSub sub sup =>
      simp only [normalizeDirect, Option.some.injEq] at hnorm
      subst normal
      rfl
  | roleChain first second sup =>
      simp only [normalizeDirect, Option.some.injEq] at hnorm
      subst normal
      rfl
  | reflexive role =>
      simp only [normalizeDirect, Option.some.injEq] at hnorm
      subst normal
      rfl

/-- Model satisfaction decomposes over a source-ontology head. -/
theorem modelsSource_cons {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (head : SourceAxiom Concept Role)
    (tail : SourceOntology Concept Role) :
    modelsSource I (head :: tail) ↔ satSourceAxiom I head ∧ modelsSource I tail := by
  simp [modelsSource]

/-- Model satisfaction decomposes over a normalized-ontology head. -/
theorem models_cons {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (head : Clause Concept Role)
    (tail : Ontology Concept Role) :
    models I (head :: tail) ↔ satClause I head ∧ models I tail := by
  simp [models]

/-- A list of successful direct translations preserves and reflects models. -/
theorem models_direct_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (source : SourceOntology Concept Role) (normal : Ontology Concept Role)
    (hmap : List.Forall₂ (fun source normal =>
      normalizeDirect top source = some normal) source normal) :
    modelsSource I source ↔ models I normal := by
  induction hmap with
  | nil => simp [modelsSource, models]
  | cons hhead _ ih =>
      rw [modelsSource_cons, models_cons,
        normalizeDirect_sat_iff I _ _ hhead, ih]

/-! ## Conservative expansion of n-ary conjunctions -/

/-- Fresh conjunction auxiliaries are indexed by the exact source prefix. -/
abbrev ExtendedConcept (Concept : Type) := Sum Concept (List Concept)

/--
The NF2 chain used for a conjunction once its first body concept is the
accumulator. Every non-final step names the enlarged prefix; the final step
targets the source superclass (or bottom).
-/
def compileConjTail (pref : List Concept) (acc : ExtendedConcept Concept)
    (remaining : List Concept) (target : ExtendedConcept Concept) :
    Ontology (ExtendedConcept Concept) Role :=
  match remaining with
  | [] => []
  | [last] => [.nf2 acc (.inl last) target]
  | next :: rest =>
      let enlarged := pref ++ [next]
      .nf2 acc (.inl next) (.inr enlarged) ::
        compileConjTail enlarged (.inr enlarged) rest target
termination_by remaining.length

/-- Compile a conjunction of at least two concepts into Rust's NF2 prefix chain. -/
def compileConjunction (body : List Concept) (target : ExtendedConcept Concept) :
    Ontology (ExtendedConcept Concept) Role :=
  match body with
  | first :: second :: rest =>
      compileConjTail [first] (.inl first) (second :: rest) target
  | _ => []

/-- Project an interpretation of the extended signature to source concepts. -/
def projectInterp {Domain : Type} {top bottom : Concept}
    (J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom)) :
    Interp Domain Concept Role top bottom where
  concept concept x := J.concept (.inl concept) x
  role := J.role
  top_true := J.top_true
  bottom_false := J.bottom_false

/-- Extend a source model by interpreting each auxiliary as its prefix intersection. -/
def extendInterp {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) :
    Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom) where
  concept
    | .inl concept => I.concept concept
    | .inr pref => holdsBody I pref
  role := I.role
  top_true := I.top_true
  bottom_false := I.bottom_false

theorem holdsBody_append {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (left right : List Concept) (x : Domain) :
    holdsBody I (left ++ right) x ↔ holdsBody I left x ∧ holdsBody I right x := by
  simp [holdsBody, or_imp, forall_and]

theorem holdsBody_cons {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) (head : Concept) (tail : List Concept)
    (x : Domain) :
    holdsBody I (head :: tail) x ↔ I.concept head x ∧ holdsBody I tail x := by
  simp [holdsBody]

/-- A model of a prefix chain propagates a true accumulator to its target. -/
theorem compileConjTail_derives {Domain : Type} {top bottom : Concept}
    (J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom))
    (pref : List Concept) (acc : ExtendedConcept Concept)
    (remaining : List Concept) (target : ExtendedConcept Concept)
    (hnonempty : remaining ≠ []) (hmodels : models J (compileConjTail pref acc remaining target))
    (x : Domain) (hacc : J.concept acc x)
    (hremaining : ∀ concept ∈ remaining, J.concept (.inl concept) x) :
    J.concept target x := by
  induction remaining generalizing pref acc with
  | nil => exact False.elim (hnonempty rfl)
  | cons next rest ih =>
      cases rest with
      | nil =>
          have hclause := hmodels (.nf2 acc (.inl next) target) (by
            simp [compileConjTail])
          exact hclause x hacc (hremaining next (by simp))
      | cons following tail =>
          let enlarged := pref ++ [next]
          have hparts := (models_cons J
            (.nf2 acc (.inl next) (.inr enlarged))
            (compileConjTail enlarged (.inr enlarged) (following :: tail) target)).1 (by
              simpa [compileConjTail, enlarged] using hmodels)
          have haux : J.concept (.inr enlarged) x :=
            hparts.1 x hacc (hremaining next (by simp))
          apply ih enlarged (.inr enlarged) (by simp) hparts.2 haux
          intro concept hmem
          exact hremaining concept (by simp [hmem])

/-- Every source model extends to a model of the generated prefix chain. -/
theorem compileConjTail_extend_models {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (pref : List Concept) (acc : ExtendedConcept Concept)
    (remaining : List Concept) (target : ExtendedConcept Concept)
    (hnonempty : remaining ≠ [])
    (hacc : ∀ x, (extendInterp I).concept acc x ↔ holdsBody I pref x)
    (htarget : ∀ x, holdsBody I (pref ++ remaining) x →
      (extendInterp I).concept target x) :
    models (extendInterp I) (compileConjTail pref acc remaining target) := by
  induction remaining generalizing pref acc with
  | nil => exact False.elim (hnonempty rfl)
  | cons next rest ih =>
      cases rest with
      | nil =>
          rw [show compileConjTail pref acc [next] target =
            [.nf2 acc (.inl next) target] by simp [compileConjTail]]
          rw [models_cons]
          constructor
          · intro x haccx hnext
            apply htarget x
            rw [holdsBody_append]
            exact ⟨(hacc x).1 haccx,
              (holdsBody_singleton I next x).2 hnext⟩
          · simp [models]
      | cons following tail =>
          let enlarged := pref ++ [next]
          rw [show compileConjTail pref acc (next :: following :: tail) target =
              .nf2 acc (.inl next) (.inr enlarged) ::
                compileConjTail enlarged (.inr enlarged) (following :: tail) target by
            simp [compileConjTail, enlarged], models_cons]
          constructor
          · intro x haccx hnext
            change holdsBody I enlarged x
            rw [holdsBody_append]
            exact ⟨(hacc x).1 haccx,
              (holdsBody_singleton I next x).2 hnext⟩
          · apply ih enlarged (.inr enlarged) (by simp)
            · intro x
              rfl
            · intro x hbody
              apply htarget x
              simpa [enlarged, List.append_assoc] using hbody

/-- NF2 expansion of an n-ary subclass axiom is sound under projection. -/
theorem compileConjunction_sub_reflects {Domain : Type} {top bottom : Concept}
    (J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom))
    (first second : Concept) (rest : List Concept) (sup : Concept)
    (hmodels : models J
      (compileConjunction (first :: second :: rest) (.inl sup))) :
    satSourceAxiom (projectInterp J) (.sub (first :: second :: rest) sup) := by
  intro x hbody
  apply compileConjTail_derives J [first] (.inl first) (second :: rest) (.inl sup)
    (by simp) (by simpa [compileConjunction] using hmodels) x
  · exact (holdsBody_cons (projectInterp J) first (second :: rest) x).1 hbody |>.1
  · intro concept hmem
    exact (holdsBody_cons (projectInterp J) first (second :: rest) x).1 hbody |>.2 concept hmem

/-- Every model of an n-ary subclass axiom extends to its NF2 expansion. -/
theorem compileConjunction_sub_preserves {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (first second : Concept) (rest : List Concept) (sup : Concept)
    (hsource : satSourceAxiom I (.sub (first :: second :: rest) sup)) :
    models (extendInterp I)
      (compileConjunction (first :: second :: rest) (.inl sup)) := by
  apply compileConjTail_extend_models I [first] (.inl first) (second :: rest) (.inl sup)
    (by simp)
  · intro x
    exact (holdsBody_singleton I first x).symm
  · intro x hbody
    exact hsource x (by simpa using hbody)

/-- NF2 expansion of an n-ary bottom axiom is sound under projection. -/
theorem compileConjunction_bottom_reflects {Domain : Type} {top bottom : Concept}
    (J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom))
    (first second : Concept) (rest : List Concept)
    (hmodels : models J
      (compileConjunction (first :: second :: rest) (.inl bottom))) :
    satSourceAxiom (projectInterp J) (.bottom (first :: second :: rest)) := by
  intro x hbody
  have hbottom := compileConjTail_derives J [first] (.inl first) (second :: rest)
    (.inl bottom) (by simp) (by simpa [compileConjunction] using hmodels) x
    ((holdsBody_cons (projectInterp J) first (second :: rest) x).1 hbody).1
    (fun concept hmem =>
      ((holdsBody_cons (projectInterp J) first (second :: rest) x).1 hbody).2 concept hmem)
  exact J.bottom_false x hbottom

/-- Every model of an n-ary bottom axiom extends to its NF2 expansion. -/
theorem compileConjunction_bottom_preserves {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (first second : Concept) (rest : List Concept)
    (hsource : satSourceAxiom I (.bottom (first :: second :: rest))) :
    models (extendInterp I)
      (compileConjunction (first :: second :: rest) (.inl bottom)) := by
  apply compileConjTail_extend_models I [first] (.inl first) (second :: rest) (.inl bottom)
    (by simp)
  · intro x
    exact (holdsBody_singleton I first x).symm
  · intro x hbody
    exact False.elim (hsource x (by simpa using hbody))

theorem projectInterp_extendInterp {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) :
    projectInterp (extendInterp I) = I := by
  rfl

/-- Exact NF2 prefix expansion is equisatisfiable with an n-ary subclass axiom,
while fixing the interpretation of every source concept and role. -/
theorem compileConjunction_sub_sat_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (first second : Concept) (rest : List Concept) (sup : Concept) :
    (∃ J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom),
      projectInterp J = I ∧
        models J (compileConjunction (first :: second :: rest) (.inl sup))) ↔
      satSourceAxiom I (.sub (first :: second :: rest) sup) := by
  constructor
  · rintro ⟨J, hproject, hmodels⟩
    simpa [hproject] using compileConjunction_sub_reflects J first second rest sup hmodels
  · intro hsource
    exact ⟨extendInterp I, projectInterp_extendInterp I,
      compileConjunction_sub_preserves I first second rest sup hsource⟩

/-- Exact NF2 prefix expansion is likewise equisatisfiable with n-ary bottom. -/
theorem compileConjunction_bottom_sat_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (first second : Concept) (rest : List Concept) :
    (∃ J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom),
      projectInterp J = I ∧
        models J (compileConjunction (first :: second :: rest) (.inl bottom))) ↔
      satSourceAxiom I (.bottom (first :: second :: rest)) := by
  constructor
  · rintro ⟨J, hproject, hmodels⟩
    simpa [hproject] using compileConjunction_bottom_reflects J first second rest hmodels
  · intro hsource
    exact ⟨extendInterp I, projectInterp_extendInterp I,
      compileConjunction_bottom_preserves I first second rest hsource⟩

/-- Typed evidence that an exact normal-form list is the deterministic prefix
chain for one genuinely n-ary source conjunction. -/
inductive NaryConjunctionEvidence (bottom : Concept) :
    SourceAxiom Concept Role → Ontology (ExtendedConcept Concept) Role → Type where
  | sub (first second : Concept) (rest : List Concept) (sup : Concept) :
      NaryConjunctionEvidence bottom
        (.sub (first :: second :: rest) sup)
        (compileConjunction (first :: second :: rest) (.inl sup))
  | bottom (first second : Concept) (rest : List Concept) :
      NaryConjunctionEvidence bottom
        (.bottom (first :: second :: rest))
        (compileConjunction (first :: second :: rest) (.inl bottom))

structure NaryConjunctionCertificate (bottom : Concept)
    (normal : Ontology (ExtendedConcept Concept) Role) where
  source : SourceAxiom Concept Role
  canonical : Ontology (ExtendedConcept Concept) Role
  evidence : NaryConjunctionEvidence bottom source canonical
  input_eq : normal = canonical

/-- Executably validate an emitted NF2 list against its complete deterministic chain. -/
def certifyNaryConjunction [DecidableEq Concept] [DecidableEq Role]
    (bottom : Concept) (body : List Concept) (sup : Option Concept)
    (normal : Ontology (ExtendedConcept Concept) Role) :
    Option (NaryConjunctionCertificate bottom normal) :=
  match body, sup with
  | first :: second :: rest, some target =>
      let expected := compileConjunction (Role := Role)
        (first :: second :: rest) (.inl target)
      if h : normal = expected then
        some {
          source := .sub (first :: second :: rest) target
          canonical := expected
          evidence := .sub first second rest target
          input_eq := h }
      else none
  | first :: second :: rest, none =>
      let expected := compileConjunction (Role := Role)
        (first :: second :: rest) (.inl bottom)
      if h : normal = expected then
        some {
          source := .bottom (first :: second :: rest)
          canonical := expected
          evidence := .bottom first second rest
          input_eq := h }
      else none
  | _, _ => none

theorem NaryConjunctionCertificate.sat_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    {normal : Ontology (ExtendedConcept Concept) Role}
    (certificate : NaryConjunctionCertificate bottom normal) :
    (∃ J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom),
      projectInterp J = I ∧ models J normal) ↔ satSourceAxiom I certificate.source := by
  cases certificate with
  | mk source canonical evidence input_eq =>
      subst normal
      cases evidence with
      | sub first second rest sup =>
          exact compileConjunction_sub_sat_iff I first second rest sup
      | bottom first second rest =>
          exact compileConjunction_bottom_sat_iff I first second rest

def certifiedNarySource [DecidableEq Concept] [DecidableEq Role]
    (bottom : Concept) (body : List Concept) (sup : Option Concept)
    (normal : Ontology (ExtendedConcept Concept) Role) :
    Option (SourceAxiom Concept Role) :=
  (certifyNaryConjunction bottom body sup normal).map NaryConjunctionCertificate.source

/-! ## Whole-source-ontology normal-form assembly -/

/-- Embed an ordinary ELC normal form into the collision-free extended signature. -/
def liftClause : Clause Concept Role → Clause (ExtendedConcept Concept) Role
  | .nf1 sub sup => .nf1 (.inl sub) (.inl sup)
  | .nf2 left right sup => .nf2 (.inl left) (.inl right) (.inl sup)
  | .nf3 sub role filler => .nf3 (.inl sub) role (.inl filler)
  | .nf4 role filler sup => .nf4 role (.inl filler) (.inl sup)
  | .nf5 sub => .nf5 (.inl sub)
  | .nf6 sub sup => .nf6 sub sup
  | .nf7 first second sup => .nf7 first second sup
  | .reflexive role => .reflexive role

theorem satClause_liftClause_iff {Domain : Type} {top bottom : Concept}
    (J : Interp Domain (ExtendedConcept Concept) Role (.inl top) (.inl bottom))
    (clause : Clause Concept Role) :
    satClause J (liftClause clause) ↔ satClause (projectInterp J) clause := by
  cases clause <;> rfl

theorem models_append {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (left right : Ontology Concept Role) :
    models I (left ++ right) ↔ models I left ∧ models I right := by
  simp [models, or_imp, forall_and]

theorem compileConjunction_sub_models_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (first second : Concept) (rest : List Concept) (sup : Concept) :
    models (extendInterp I)
        (compileConjunction (first :: second :: rest) (.inl sup)) ↔
      satSourceAxiom I (.sub (first :: second :: rest) sup) := by
  constructor
  · intro hmodels
    simpa using compileConjunction_sub_reflects (extendInterp I) first second rest sup hmodels
  · exact compileConjunction_sub_preserves I first second rest sup

theorem compileConjunction_bottom_models_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (first second : Concept) (rest : List Concept) :
    models (extendInterp I)
        (compileConjunction (first :: second :: rest) (.inl bottom)) ↔
      satSourceAxiom I (.bottom (first :: second :: rest)) := by
  constructor
  · intro hmodels
    simpa using compileConjunction_bottom_reflects (extendInterp I) first second rest hmodels
  · exact compileConjunction_bottom_preserves I first second rest

/-- Exact evidence for flattening every source axiom into one shared extended
normal-form ontology. Prefix auxiliaries are shared by structural identity. -/
inductive SourceOntologyNormalEvidence (top bottom : Concept) :
    SourceOntology Concept Role → Ontology (ExtendedConcept Concept) Role → Type where
  | nil : SourceOntologyNormalEvidence top bottom [] []
  | direct {source : SourceAxiom Concept Role} {clause : Clause Concept Role}
      {sources : SourceOntology Concept Role}
      {normal : Ontology (ExtendedConcept Concept) Role}
      (head : normalizeDirect top source = some clause)
      (tail : SourceOntologyNormalEvidence top bottom sources normal) :
      SourceOntologyNormalEvidence top bottom (source :: sources)
        (liftClause clause :: normal)
  | conjunctionSub (first second : Concept) (rest : List Concept) (sup : Concept)
      {sources : SourceOntology Concept Role}
      {normal : Ontology (ExtendedConcept Concept) Role}
      (tail : SourceOntologyNormalEvidence top bottom sources normal) :
      SourceOntologyNormalEvidence top bottom
        (.sub (first :: second :: rest) sup :: sources)
        (compileConjunction (first :: second :: rest) (.inl sup) ++ normal)
  | conjunctionBottom (first second : Concept) (rest : List Concept)
      {sources : SourceOntology Concept Role}
      {normal : Ontology (ExtendedConcept Concept) Role}
      (tail : SourceOntologyNormalEvidence top bottom sources normal) :
      SourceOntologyNormalEvidence top bottom
        (.bottom (first :: second :: rest) :: sources)
        (compileConjunction (first :: second :: rest) (.inl bottom) ++ normal)

/-- Whole-ontology assembly preserves and reflects all source models. -/
theorem SourceOntologyNormalEvidence.models_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    {sources : SourceOntology Concept Role}
    {normal : Ontology (ExtendedConcept Concept) Role}
    (evidence : SourceOntologyNormalEvidence top bottom sources normal) :
    models (extendInterp I) normal ↔ modelsSource I sources := by
  induction evidence with
  | nil => simp [models, modelsSource]
  | direct head tail ih =>
      rw [models_cons, modelsSource_cons, satClause_liftClause_iff,
        projectInterp_extendInterp, ← normalizeDirect_sat_iff I _ _ head, ih]
  | conjunctionSub first second rest sup tail ih =>
      rw [models_append, modelsSource_cons,
        compileConjunction_sub_models_iff I first second rest sup, ih]
  | conjunctionBottom first second rest tail ih =>
      rw [models_append, modelsSource_cons,
        compileConjunction_bottom_models_iff I first second rest, ih]

structure SourceOntologyNormalCertificate (top bottom : Concept)
    (sources : SourceOntology Concept Role) where
  normal : Ontology (ExtendedConcept Concept) Role
  evidence : SourceOntologyNormalEvidence top bottom sources normal

/-- Build the complete NF1–NF7 ontology or fail closed on an unsupported source shape. -/
def certifySourceOntologyNormal (top bottom : Concept) :
    (sources : SourceOntology Concept Role) →
      Option (SourceOntologyNormalCertificate top bottom sources)
  | [] => some { normal := [], evidence := .nil }
  | .sub (first :: second :: rest) sup :: sources => do
      let tail ← certifySourceOntologyNormal top bottom sources
      return {
        normal := compileConjunction (first :: second :: rest) (.inl sup) ++ tail.normal
        evidence := .conjunctionSub first second rest sup tail.evidence }
  | .bottom (first :: second :: rest) :: sources => do
      let tail ← certifySourceOntologyNormal top bottom sources
      return {
        normal := compileConjunction (first :: second :: rest) (.inl bottom) ++ tail.normal
        evidence := .conjunctionBottom first second rest tail.evidence }
  | source :: sources =>
      match h : normalizeDirect top source with
      | none => none
      | some clause => do
          let tail ← certifySourceOntologyNormal top bottom sources
          return {
            normal := liftClause clause :: tail.normal
            evidence := .direct h tail.evidence }

theorem SourceOntologyNormalCertificate.models_iff {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    {sources : SourceOntology Concept Role}
    (certificate : SourceOntologyNormalCertificate top bottom sources) :
    models (extendInterp I) certificate.normal ↔ modelsSource I sources :=
  certificate.evidence.models_iff I

namespace NormalizationExamples

abbrev C := Fin 5
abbrev R := Fin 1

example :
    compileConjunction (Role := R) ([0, 1, 2, 3] : List C) (.inl 4) =
      [.nf2 (.inl 0) (.inl 1) (.inr [0, 1]),
       .nf2 (.inr [0, 1]) (.inl 2) (.inr [0, 1, 2]),
       .nf2 (.inr [0, 1, 2]) (.inl 3) (.inl 4)] := by
  simp [compileConjunction, compileConjTail]

example : certifiedNarySource (Concept := C) (Role := R) 4 [0, 1, 2, 3] (some 4)
    [.nf2 (.inl 0) (.inl 1) (.inr [0, 1]),
     .nf2 (.inr [0, 1]) (.inl 2) (.inr [0, 1, 2]),
     .nf2 (.inr [0, 1, 2]) (.inl 3) (.inl 4)] =
    some (.sub [0, 1, 2, 3] 4) := by native_decide

example : certifiedNarySource (Concept := C) (Role := R) 4 [0, 1, 2] none
    [.nf2 (.inl 0) (.inl 1) (.inr [0, 1])] = none := by native_decide

end NormalizationExamples

end ContextCalculus.ELCompletion

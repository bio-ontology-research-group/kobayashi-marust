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

end ContextCalculus.ELCompletion

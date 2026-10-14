import ContextCalculus.IncrementalSourceLocality

/-!
# Re-proved rows after source-axiom deletion

An incomplete, sound source proof calculus can certify that a previously exact
query row survives deletion. It need not classify the remaining ontology: the
old exact row is an upper bound, and re-proving all its answers supplies the
lower bound. Roles and all other background constraints stay unchanged.

This module does not bind a Rust/Python graph, source scanner or IRI map to the
proof calculus. Those executable/source obligations remain explicit.
-/
namespace ContextCalculus.IncrementalDeletionSupport
open IncrementalSourceLocality

structure RoleTheory where
  domains : List (Nat × Nat)
  chains : List (Nat × Nat × Nat)

def SatisfiesRoles (m : Model U) (laws : RoleTheory) : Prop :=
  (∀ r c, (r, c) ∈ laws.domains → Domain m r c) ∧
  (∀ r s t, (r, s, t) ∈ laws.chains → ∀ x y z,
    m.roles r x y → m.roles s y z → m.roles t x z)

inductive Proof (theory : List Axiom) (laws : RoleTheory) : Expr → Expr → Prop where
  | source {a b} : (a, b) ∈ theory → Proof theory laws a b
  | refl (a) : Proof theory laws a a
  | top (a) : Proof theory laws a .top
  | bottom (a) : Proof theory laws .bottom a
  | trans {a b c} : Proof theory laws a b → Proof theory laws b c → Proof theory laws a c
  | conjIntro {a b c} : Proof theory laws a b → Proof theory laws a c →
      Proof theory laws a (.conj b c)
  | conjLeft (a b) : Proof theory laws (.conj a b) a
  | conjRight (a b) : Proof theory laws (.conj a b) b
  | someMono (r) {a b} : Proof theory laws a b →
      Proof theory laws (.some r a) (.some r b)
  | someBottom (r) : Proof theory laws (.some r .bottom) .bottom
  | roleDomain {r c} (filler) : (r, c) ∈ laws.domains →
      Proof theory laws (.some r filler) (.atom c)
  | roleChain {r s t a b} : (r, s, t) ∈ laws.chains →
      Proof theory laws a (.some s b) → Proof theory laws (.some r a) (.some t b)

theorem proof_sound {theory : List Axiom} {laws : RoleTheory} {a b : Expr}
    (proof : Proof theory laws a b) (m : Model U) (valid : Satisfies m theory)
    (validRoles : SatisfiesRoles m laws) : ∀ x, eval m a x → eval m b x := by
  induction proof with
  | source member => exact fun x hx => valid _ member x hx
  | refl _ => exact fun _ hx => hx
  | top _ => exact fun _ _ => trivial
  | bottom _ => exact fun _ hx => False.elim hx
  | trans _ _ first second => exact fun x hx => second x (first x hx)
  | conjIntro _ _ first second => exact fun x hx => ⟨first x hx, second x hx⟩
  | conjLeft _ _ => exact fun _ hx => hx.1
  | conjRight _ _ => exact fun _ hx => hx.2
  | someMono _ _ ih =>
    rintro x ⟨y, edge, holds⟩
    exact ⟨y, edge, ih y holds⟩
  | someBottom _ =>
    rintro x ⟨y, _, impossible⟩
    exact impossible
  | roleDomain _ member =>
    rintro x ⟨y, edge, _⟩
    exact validRoles.1 _ _ member x y edge
  | roleChain member _ ih =>
    rintro x ⟨y, first, holds⟩
    rcases ih y holds with ⟨z, second, target⟩
    exact ⟨z, validRoles.2 _ _ _ member x y z first second, target⟩

theorem satisfies_after_deletion {old newer : List Axiom}
    (subset : ∀ ax, ax ∈ newer → ax ∈ old)
    (m : Model U) (valid : Satisfies m old) : Satisfies m newer := by
  intro ax member
  exact valid ax (subset ax member)

def ConsistentWith (background : Model U → Prop) (theory : List Axiom) : Prop :=
  ∃ m, background m ∧ Satisfies m theory

theorem consistency_after_deletion {old newer : List Axiom}
    (subset : ∀ ax, ax ∈ newer → ax ∈ old)
    (background : Model U → Prop) (valid : ConsistentWith background old) :
    ConsistentWith background newer := by
  rcases valid with ⟨m, bg, holds⟩
  exact ⟨m, bg, satisfies_after_deletion subset m holds⟩

/-- Only visibleTarget targets whose prior result is complete may be retained. Missing
or incomplete old answers are not repaired by this implication. -/
theorem rederived_deletion_row {old newer : List Axiom}
    (subset : ∀ ax, ax ∈ newer → ax ∈ old)
    (background : Model U → Prop) (query : Nat) (visibleTarget cached : Nat → Prop)
    (laws : RoleTheory) (background_valid : ∀ m, background m → SatisfiesRoles m laws)
    (exact_old : ∀ target, visibleTarget target →
      (SubsumesWith background old query target ↔ cached target))
    (reproved : ∀ target, visibleTarget target → cached target →
      Proof newer laws (.atom query) (.atom target)) :
    ∀ target, visibleTarget target →
      (SubsumesWith background newer query target ↔ cached target) := by
  intro target visible
  constructor
  · intro entails
    apply (exact_old target visible).mp
    intro m bg valid x holds
    exact entails m bg (satisfies_after_deletion subset m valid) x holds
  · intro cached_answer m bg valid x holds
    exact proof_sound (reproved target visible cached_answer) m valid (background_valid m bg) x holds

def QuerySatWith (background : Model U → Prop) (theory : List Axiom)
    (query : Nat) : Prop :=
  ∃ m, background m ∧ Satisfies m theory ∧ ∃ x, m.classes query x

theorem query_sat_after_deletion {old newer : List Axiom}
    (subset : ∀ ax, ax ∈ newer → ax ∈ old)
    (background : Model U → Prop) (query : Nat)
    (sat : QuerySatWith background old query) :
    QuerySatWith background newer query := by
  rcases sat with ⟨m, bg, valid, x, holds⟩
  exact ⟨m, bg, satisfies_after_deletion subset m valid, x, holds⟩

theorem query_unsat_from_proof {theory : List Axiom}
    (background : Model U → Prop) (query : Nat)
    (laws : RoleTheory) (background_valid : ∀ m, background m → SatisfiesRoles m laws)
    (proof : Proof theory laws (.atom query) .bottom) :
    ¬ QuerySatWith background theory query := by
  rintro ⟨m, bg, valid, x, holds⟩
  exact proof_sound proof m valid (background_valid m bg) x holds

/-- Satisfiable rows survive weakening automatically; previously unsatisfiable
rows require a fresh bottom proof in the remaining source theory. -/
theorem rederived_query_satisfiability {old newer : List Axiom}
    (subset : ∀ ax, ax ∈ newer → ax ∈ old)
    (background : Model U → Prop) (query : Nat)
    (laws : RoleTheory) (background_valid : ∀ m, background m → SatisfiesRoles m laws)
    (reproved : ¬ QuerySatWith background old query →
      Proof newer laws (.atom query) .bottom) :
    QuerySatWith background old query ↔ QuerySatWith background newer query := by
  constructor
  · exact query_sat_after_deletion subset background query
  · intro sat
    by_cases prior : QuerySatWith background old query
    · exact prior
    · exact False.elim (query_unsat_from_proof background query laws background_valid (reproved prior) sat)

#print axioms proof_sound
#print axioms satisfies_after_deletion
#print axioms consistency_after_deletion
#print axioms rederived_deletion_row
#print axioms query_sat_after_deletion
#print axioms query_unsat_from_proof
#print axioms rederived_query_satisfiability
end ContextCalculus.IncrementalDeletionSupport

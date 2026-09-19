/-!
A unary DL-safe rule ranges over the interpretations of source individual
names. Its OWL encoding guards the antecedent with their nominal union.
No unique-name assumption is needed; fresh unnamed query witnesses are not
added to the guard. This is a normalization theorem, not a worker certificate.
-/
namespace ContextCalculus.DLSafeUnaryRuleNormalization

variable {N D : Type}

def namedGuard (names : List N) (denote : N → D) (x : D) : Prop :=
  ∃ name ∈ names, denote name = x

def ruleHolds (names : List N) (denote : N → D)
    (body head : D → Prop) : Prop :=
  ∀ name ∈ names, body (denote name) → head (denote name)

def guardedInclusion (names : List N) (denote : N → D)
    (body head : D → Prop) : Prop :=
  ∀ x, namedGuard names denote x ∧ body x → head x

theorem unary_rule_equivalent (names : List N) (denote : N → D)
    (body head : D → Prop) :
    ruleHolds names denote body head ↔
      guardedInclusion names denote body head := by
  constructor
  · intro source x guard
    rcases guard.1 with ⟨name, member, equal⟩
    subst x
    exact source name member guard.2
  · intro inclusion name member antecedent
    exact inclusion (denote name) ⟨⟨name, member, rfl⟩, antecedent⟩

theorem theory_equivalent (names : List N) (denote : N → D)
    (rules : List ((D → Prop) × (D → Prop))) :
    (∀ rule ∈ rules, ruleHolds names denote rule.1 rule.2) ↔
      (∀ rule ∈ rules, guardedInclusion names denote rule.1 rule.2) := by
  constructor
  · intro source rule member
    exact (unary_rule_equivalent names denote rule.1 rule.2).mp (source rule member)
  · intro normalized rule member
    exact (unary_rule_equivalent names denote rule.1 rule.2).mpr (normalized rule member)

/-- A finite nominal universe makes the source guard universal. In that case
    the rule contributes a genuine TBox inclusion; checking consistency alone
    and then forgetting the rule cannot preserve all class consequences. -/
theorem exhaustive_names_entail_inclusion (names : List N) (denote : N → D)
    (body head : D → Prop) (covers : ∀ x, namedGuard names denote x)
    (rule : ruleHolds names denote body head) :
    ∀ x, body x → head x := by
  intro x antecedent
  exact (unary_rule_equivalent names denote body head).mp rule x ⟨covers x, antecedent⟩

#print axioms unary_rule_equivalent
#print axioms theory_equivalent
#print axioms exhaustive_names_entail_inclusion

/-- A pointwise class-only TBox permits adjoining any unnamed witness type.
    Source names stay in the old component, so all their rule instances remain
    unchanged. Consequently DL-safe rules cannot exclude an otherwise valid
    unnamed counterexample to a class subsumption in this source fragment. -/
theorem pointwise_fresh_extension {T : Type}
    (names : List N) (denote : N → D) (types : D → T) (fresh : T)
    (tbox : T → Prop) (rules : List ((T → Prop) × (T → Prop)))
    (oldTbox : ∀ d, tbox (types d)) (freshTbox : tbox fresh)
    (oldRules : ∀ rule ∈ rules,
      ruleHolds names denote (fun d => rule.1 (types d)) (fun d => rule.2 (types d))) :
    let extended : Option D → T := fun d => d.elim fresh types
    (∀ d, tbox (extended d)) ∧
    (∀ rule ∈ rules,
      ruleHolds names (fun n => some (denote n))
        (fun d => rule.1 (extended d)) (fun d => rule.2 (extended d))) ∧
    extended none = fresh := by
  dsimp
  refine ⟨?_, ?_, rfl⟩
  · intro d
    cases d with
    | none => exact freshTbox
    | some d => exact oldTbox d
  · intro rule member name namedMember body
    exact oldRules rule member name namedMember body

#print axioms pointwise_fresh_extension
end ContextCalculus.DLSafeUnaryRuleNormalization

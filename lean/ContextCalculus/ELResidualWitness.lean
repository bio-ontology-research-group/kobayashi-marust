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

#print axioms canonOn_rewrittenExistential_satisfies_raw

end ContextCalculus.ELCompletion

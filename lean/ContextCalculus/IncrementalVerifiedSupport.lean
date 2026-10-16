/-!
# Publication from an independently verified source support

The incremental source supervisor may propose a small subset of an admitted
NEW source and ask the unchanged production classifier to check it. Only a
complete inconsistent result authorizes publication. The proposal algorithm
is not a trusted reasoner: its only semantic obligation is exact containment
of the independently checked statements in NEW.

This boundary uses arbitrary axiom satisfaction, so it applies to the full
admitted source semantics, including data interpretations. It requires no
locality, masking, unique-name, or consistent-OLD assumption. The executable
binding retains the exact header, all declarations, and original axiom bytes;
checks source admission separately; and rejects failed, incomplete, or timed
out verification. These parser/process obligations remain executable tests.
-/

namespace ContextCalculus.IncrementalVerifiedSupport

universe u v

variable {Ax : Type u} {I : Type v}

/-- The fresh verifier establishes the first premise for the actual proposed
source. Exact source containment supplies the second premise. -/
theorem verified_support_publication (sat : I → Ax → Prop)
    {support newSource : Ax → Prop}
    (verified : ∀ i, ¬ (∀ a, support a → sat i a))
    (contained : ∀ a, support a → newSource a) :
    ∀ i, ¬ (∀ a, newSource a → sat i a) := by
  intro i model
  exact verified i (fun a ha => model a (contained a ha))

/-- Later edits can reuse the same independently verified support when its
exact statements remain present. No containment of the whole old revision
is required. -/
theorem retained_support_publication (sat : I → Ax → Prop)
    {support nextSource : Ax → Prop}
    (verified : ∀ i, ¬ (∀ a, support a → sat i a))
    (retained : ∀ a, support a → nextSource a) :
    ∀ i, ¬ (∀ a, nextSource a → sat i a) :=
  verified_support_publication sat verified retained

#print axioms verified_support_publication
#print axioms retained_support_publication

end ContextCalculus.IncrementalVerifiedSupport

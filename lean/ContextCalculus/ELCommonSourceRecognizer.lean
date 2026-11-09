import ContextCalculus.KMCommonRoutingSource

/-!
# Recognising the pure EL fragment of the common clause source

The routed source of the automatic supervisor is a list of proper-term
clauses (`List FCL`, `KMCommonRoutingSource`).  The EL reference procedure of
v1.6.0 needs that list as an `ELCompletion.Ontology` with distinguished `top`
and `bottom` concepts.  `recognizeEL` reads the clauses back into NF1–NF7 and
reflexive-role clauses and fails closed on anything else; the theorem
`recognizeEL_entails_iff` states that the reading changes no named
subsumption.

Accepted clause shapes (`x = var 0`, `y`, `z` further variables; `C a t` is
`FLit.P (FPred.concept a t)` and `R r s t` is `FLit.P (FPred.role r s t)`):

| common clause | normal form |
|---|---|
| `⟨[C a x], [C b x]⟩` | `nf1 a b` |
| `⟨[C a x, C b x], [C c x]⟩` | `nf2 a b c` |
| `⟨[C a x], [R r x (app f x)]⟩` with `⟨[C a x], [C b (app f x)]⟩` | `nf3 a r b`; both halves share `a` and `f`, `f` is used by exactly one pair |
| `⟨[R r x y, C b y], [C c x]⟩` | `nf4 r b c` |
| `⟨[C a x], []⟩` | `nf5 a` |
| `⟨[R r x y], [R s x y]⟩` | `nf6 r s` |
| `⟨[R r x y, R s y z], [R t x z]⟩` | `nf7 r s t` |
| `⟨[], [R r x x]⟩` | `reflexive r` |
| `⟨[], [C a x]⟩` | `top` candidate; the first such `a` becomes `top`, every further one becomes `nf1 top a` |

Literal order inside a clause does not matter for the semantics
(`sat` is membership-based), so the recogniser must accept both orders of a
two-literal body.  Variables may be any distinct integers, because `valid`
quantifies over all assignments; the recogniser accepts injective renamings
of `x`, `y`, `z` per clause.

`top` and `bottom` are taken from the source when it has a total concept
clause `⟨[], [C a x]⟩` or an nf5 clause whose subject is otherwise unused;
otherwise they are fresh names above every identifier of the source and the
requested list.  A fresh distinguished name is conservative: a model of the
source extends to a model of the source plus `topClause top` and
`bottomClause bottom` by interpreting the fresh names as the total and the
empty concept, and the equivalence `recognizeEL_entails_iff` therefore holds
for every pair of requested names.

Everything in this file except the two obligations is executable; the
theorem is proved by model transport in both directions, reusing
`ELNormalCheckerTermEmbedding.interpOfModel` and `modelOfNormalAndRaw` and
the function-symbol renaming theorems of `CBSourceWire`.
-/

namespace ContextCalculus.ELCommonSourceRecognizer

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.KMCommonRoutingSource

/-- The recognised fragment: distinguished concepts and the normal-form
ontology. -/
structure RecognizedEL where
  top : Nat
  bottom : Nat
  ontology : ELCompletion.Ontology Nat Nat

/-- Concept identifiers occurring in one literal. -/
def literalConcepts : FLit → List Nat
  | .P (.concept iri _) => [iri]
  | _ => []

/-- Concept identifiers occurring in the source. -/
def sourceConcepts (source : List FCL) : List Nat :=
  source.flatMap fun clause =>
    clause.body.flatMap literalConcepts ++ clause.head.flatMap literalConcepts

/-- Read the common clause source as a pure EL ontology.  Fails closed
(`none`) on any clause outside the table above.  The requested names are
needed only to keep fresh distinguished names apart from them.

TODO(v1.6.0 agent): implement.  The placeholder makes the fragment empty, so
every theorem below is vacuous until it is replaced; the brief requires the
unit examples of `ELCommonSourceRecognizerTests` to pass. -/
def recognizeEL (named : List Nat) (source : List FCL) : Option RecognizedEL :=
  none

/-- The semantic obligation of the recogniser: for every pair of requested
names, the common-source entailment and the EL entailment of the reading
agree. -/
theorem recognizeEL_entails_iff (named : List Nat) (source : List FCL)
    (recognized : RecognizedEL)
    (hrecognized : recognizeEL named source = some recognized)
    {sub sup : Nat} (hsub : sub ∈ named) (hsup : sup ∈ named) :
    Entails source sub sup ↔
      ELCompletion.EntailsSub (top := recognized.top) (bottom := recognized.bottom)
        recognized.ontology sub sup := by
  sorry

/-- Inconsistency of the common source agrees with EL inconsistency of the
reading.  `Unsatisfiable source concept` for a concept that is `top` of the
reading is the common-source form of inconsistency. -/
theorem recognizeEL_unsat_iff (named : List Nat) (source : List FCL)
    (recognized : RecognizedEL)
    (hrecognized : recognizeEL named source = some recognized) :
    (∀ (Domain : Type) [Nonempty Domain] (model : TModel Domain),
        (∀ clause ∈ source, valid model clause) → False) ↔
      ELCompletion.Unsatisfiable (top := recognized.top)
        (bottom := recognized.bottom) recognized.ontology := by
  sorry

#print axioms recognizeEL_entails_iff

end ContextCalculus.ELCommonSourceRecognizer

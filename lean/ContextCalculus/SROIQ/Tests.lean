import ContextCalculus.OWLFrontend.SROIQDC2aReference

/-!
# Tests of the regularity check and the role automaton (stage C3)

Small normal-form RBoxes, evaluated with `#guard`:

* the BFO pattern (`partOf` transitive, `locatedIn ∘ partOf ⊑ locatedIn`,
  `partOf ∘ locatedIn ⊑ locatedIn`): regular, automaton closed, the
  expected words accepted;
* the chain of issue E12 (`s ∘ t ∘ t⁻ ⊑ r`): regular, closed;
* `s ∘ r ∘ t ⊑ r`: irregular;
* the gap of design section 2 (`P ⊑ A`, `Q ⊑ B`, `C ∘ B ∘ C ⊑ P`,
  `A ∘ D ⊑ Q`): regular in the sense of the specification, but its
  language is not regular and the automaton listing does not close;
* a reflexive role: the empty word is accepted.

`accB` is a bounded search over runs, a test harness only.
-/

namespace ContextCalculus.SROIQ.Tests

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Clause)
open ContextCalculus.SROIQ.Proc

/-- A bounded search for an accepting run (test harness). -/
def accB {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) :
    Nat → Stack (Fin m) → List (RT m) → Bool
  | 0, _, _ => false
  | k + 1, st, w =>
    (st == [] && w == []) || (succs O st).any fun p =>
      match p.1, w with
      | none, _ => accB O k p.2 w
      | some R, R' :: w' => R == R' && accB O k p.2 w'
      | some _, [] => false

def p : RT 2 := .pos 0
def l : RT 2 := .pos 1

/-- The BFO pattern, with `∀ locatedIn.C`. -/
def bfo : SRIQ.Ontology (Fin 2) (Fin 2) :=
  [.chain [p, p] p, .chain [l, p] l, .chain [p, l] l, .allRight 0 l 1]

#guard regularB bfo
#guard condB bfo
#guard (reachL bfo l).length < 64
#guard accB bfo 40 [(l, false)] [l, p, p]
#guard accB bfo 40 [(l, false)] [p, p, l, p]
#guard accB bfo 40 [(l, false)] [l]
#guard !accB bfo 40 [(l, false)] [p]
#guard !accB bfo 40 [(l, false)] [p, p]
#guard accB bfo 40 [(p, false)] [p, p, p]
#guard accB bfo 40 [(l.flip, false)] [p.flip, l.flip]

def s3 : RT 3 := .pos 0
def t3 : RT 3 := .pos 1
def r3 : RT 3 := .pos 2

/-- Issue E12: `s ∘ t ∘ t⁻ ⊑ r`, `A ⊑ ∀r.C`. -/
def e12 : SRIQ.Ontology (Fin 2) (Fin 3) := [.chain [s3, t3, t3.flip] r3, .allRight 0 r3 1]

#guard regularB e12
#guard condB e12
#guard accB e12 40 [(r3, false)] [s3, t3, t3.flip]
#guard !accB e12 40 [(r3, false)] [s3, t3]
#guard accB e12 40 [(r3.flip, false)] [t3, t3.flip, s3.flip]

/-- `s ∘ r ∘ t ⊑ r`: irregular. -/
def irr : SRIQ.Ontology (Fin 2) (Fin 3) := [.chain [s3, r3, t3] r3]

#guard !regularB irr

def gA : RT 6 := .pos 0
def gB : RT 6 := .pos 1
def gC : RT 6 := .pos 2
def gD : RT 6 := .pos 3
def gP : RT 6 := .pos 4
def gQ : RT 6 := .pos 5

/-- The gap of the specification's regularity condition (design section 2). -/
def gap : SRIQ.Ontology (Fin 2) (Fin 6) :=
  [.chain [gP] gA, .chain [gQ] gB, .chain [gC, gB, gC] gP, .chain [gA, gD] gQ, .allRight 0 gA 1]

#guard regularB gap
#guard !condB gap
#guard accB gap 60 [(gA, false)] [gC, gA, gD, gC]

/-- A reflexive role below a chain: `refl(r)`, `r ∘ s ⊑ q`. -/
def refl : SRIQ.Ontology (Fin 2) (Fin 3) := [.chain [] s3, .chain [s3, t3] r3, .allRight 0 r3 1]

#guard regularB refl
#guard condB refl
#guard accB refl 40 [(s3, false)] []
#guard accB refl 40 [(r3, false)] [t3]
#guard accB refl 40 [(r3, false)] [s3, t3]

end ContextCalculus.SROIQ.Tests

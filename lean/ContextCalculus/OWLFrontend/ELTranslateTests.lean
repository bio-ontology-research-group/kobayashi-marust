import ContextCalculus.OWLFrontend.ELTranslate
import ContextCalculus.ELReferenceSaturation

/-!
# Executable tests for the OWL EL translation

Small ontologies whose translation is checked against hand-computed NF
lists, and end-to-end checks: `ELReference.referenceBit` on the translation
agrees with known entailments (existential round trip, a role chain of
length 3, a disjointness that makes a class unsatisfiable, an inconsistent
ontology read through fresh probe IRIs).
-/

namespace ContextCalculus.OWLFrontend.ELTests

open ContextCalculus.OWL
open ContextCalculus.ELCompletion (Clause)

/-- The reference bit for two requested IRIs, through the translation. -/
def bit (O : Ontology) (requested : List IRI) (a b : IRI) : Option Bool :=
  (translateEL O requested).map fun T =>
    ELReference.referenceBit T.top T.bottom (List.range T.named.length) T.ontology
      (T.named.idxOf a) (T.named.idxOf b)

def r : ObjProp := .named "r"
def s : ObjProp := .named "s"
def t : ObjProp := .named "t"
def u : ObjProp := .named "u"
def A : ClassExpr := .cls "A"
def B : ClassExpr := .cls "B"
def C : ClassExpr := .cls "C"
def D : ClassExpr := .cls "D"
def E : ClassExpr := .cls "E"

/-! ## Hand-computed normal forms -/

/-- `A ⊑ ∃r.B`, `∃r.B ⊑ C`. Names `A, B, C` are `0, 1, 2`, `top = 3`,
`bottom = 4`, definers from 5; role `r` is 0. -/
def roundTrip : Ontology :=
  ⟨[.subClassOf A (.some r B), .subClassOf (.some r B) C]⟩

#guard (translateEL roundTrip ["A", "B", "C"]).map (·.ontology) ==
  some [.nf3 5 0 1, .nf1 0 5, .nf4 0 1 6, .nf1 6 2]
#guard (translateEL roundTrip ["A", "B", "C"]).map (fun T => (T.top, T.bottom)) == some (3, 4)

/- Requested names first (duplicates removed), then the other names in
first-occurrence order. -/
#guard (translateEL roundTrip ["C", "A", "C", "Z"]).map (·.named) == some ["C", "A", "Z"]
#guard (translateEL roundTrip ["C", "A", "C", "Z"]).map (·.ontology) ==
  some [.nf3 6 0 3, .nf1 1 6, .nf4 0 3 7, .nf1 7 0]

/-- Chain of length 3: `r ∘ s ∘ t ⊑ u` splits through the fresh role 4. -/
def chain3Axiom : Ontology := ⟨[.subObjectPropertyOf [r, s, t] u]⟩

#guard (translateEL chain3Axiom []).map (·.ontology) == some [.nf7 0 1 4, .nf7 4 2 3]

/-- Lengths 1 and 2, transitivity, equivalent properties. -/
def roleAxioms : Ontology :=
  ⟨[.subObjectPropertyOf [r] s, .subObjectPropertyOf [r, s] t, .transitive u,
    .equivalentObjectProperties [r, u]]⟩

#guard (translateEL roleAxioms []).map (·.ontology) ==
  some [.nf6 0 1, .nf7 0 1 2, .nf7 3 3 3, .nf6 3 0, .nf6 0 3]

/-- Conjunctions: negative `A ⊓ B ⊓ owl:Thing` is a binary `nf2` chain,
positive `C ⊓ D` one `nf1` per conjunct. Names `A..D` are `0..3`,
`top = 4`, `bottom = 5`. -/
def conj : Ontology := ⟨[.subClassOf (.and [A, B, .thing]) (.and [C, D])]⟩

#guard (translateEL conj ["A", "B", "C", "D"]).map (·.ontology) ==
  some [.nf2 0 1 6, .nf2 6 4 7, .nf1 8 2, .nf1 8 3, .nf1 7 8]

/-- `EquivalentClasses`, `DisjointClasses`, `ObjectPropertyDomain`,
declarations. -/
def classAxioms : Ontology :=
  ⟨[.declareClass "A", .equivalentClasses [A, B], .disjointClasses [A, B, C],
    .domain r C, .declareObjectProperty "r"]⟩

#guard (translateEL classAxioms ["A", "B", "C"]).map (·.ontology) ==
  some [.nf1 0 1, .nf1 1 0, .nf2 0 1 4, .nf2 0 2 4, .nf2 1 2 4, .nf4 0 3 2]

/- Outside OWL EL: `none`. -/
#guard (translateEL ⟨[.subClassOf A (.or [B, C])]⟩ ["A"]).isNone
#guard (translateEL ⟨[.subClassOf A (.some (.inv "r") B)]⟩ ["A"]).isNone
#guard (translateEL ⟨[.range r A]⟩ ["A"]).isNone

/-! ## End to end through `referenceBit` -/

/- `A ⊑ ∃r.B` and `∃r.B ⊑ C` give `A ⊑ C`, not `B ⊑ C`. -/
#guard bit roundTrip ["A", "B", "C"] "A" "C" == some true
#guard bit roundTrip ["A", "B", "C"] "B" "C" == some false
#guard bit roundTrip ["A", "B", "C"] "C" "A" == some false

/-- A role chain of length 3: `A ⊑ ∃r.B`, `B ⊑ ∃s.C`, `C ⊑ ∃t.D`,
`r ∘ s ∘ t ⊑ u`, `∃u.D ⊑ E` give `A ⊑ E`; without the chain axiom they do
not. -/
def chain3 : Ontology :=
  ⟨[.subClassOf A (.some r B), .subClassOf B (.some s C), .subClassOf C (.some t D),
    .subObjectPropertyOf [r, s, t] u, .subClassOf (.some u D) E]⟩

def chain3Without : Ontology :=
  ⟨[.subClassOf A (.some r B), .subClassOf B (.some s C), .subClassOf C (.some t D),
    .subClassOf (.some u D) E]⟩

#guard bit chain3 ["A", "B", "E"] "A" "E" == some true
#guard bit chain3 ["A", "B", "E"] "B" "E" == some false
#guard bit chain3Without ["A", "B", "E"] "A" "E" == some false

/-- Transitivity: `A ⊑ ∃r.B`, `B ⊑ ∃r.C`, `Trans(r)`, `∃r.C ⊑ D` give
`A ⊑ D`. -/
def trans : Ontology :=
  ⟨[.subClassOf A (.some r B), .subClassOf B (.some r C), .transitive r,
    .subClassOf (.some r C) D]⟩

#guard bit trans ["A", "D"] "A" "D" == some true

/- Domain: `A ⊑ ∃r.B` and `Domain(r, C)` give `A ⊑ C`. -/
#guard bit ⟨[.subClassOf A (.some r B), .domain r C]⟩ ["A", "C"] "A" "C" == some true

/- Equivalence and conjunction: `A ≡ B ⊓ C`, `D ⊑ B`, `D ⊑ C` give `D ⊑ A`. -/
#guard bit ⟨[.equivalentClasses [A, .and [B, C]], .subClassOf D B, .subClassOf D C]⟩
  ["A", "D"] "D" "A" == some true

/-- Disjointness makes `A` unsatisfiable: `A ⊑ B`, `A ⊑ ∃r.C`, `C ⊑ D`,
`DisjointClasses(C, D)`. `A` is subsumed by a fresh probe `Q` (the probe
reading of unsatisfiability); `B` is not. -/
def unsatA : Ontology :=
  ⟨[.subClassOf A B, .subClassOf A (.some r C), .subClassOf C D, .disjointClasses [C, D]]⟩

#guard bit unsatA ["A", "B", "Q"] "A" "Q" == some true
#guard bit unsatA ["A", "B", "Q"] "B" "Q" == some false

/-- An inconsistent ontology: `owl:Thing ⊑ A`, `A ⊑ ∃r.B`, `B ⊑ owl:Nothing`.
Fresh probes `P`, `Q` give `P ⊑ Q` exactly when the ontology is
inconsistent. -/
def incons : Ontology :=
  ⟨[.subClassOf .thing A, .subClassOf A (.some r B), .subClassOf B .nothing]⟩

def consistent : Ontology :=
  ⟨[.subClassOf .thing A, .subClassOf A (.some r B)]⟩

#guard bit incons ["P", "Q"] "P" "Q" == some true
#guard bit consistent ["P", "Q"] "P" "Q" == some false
#guard bit consistent ["P", "Q", "A"] "P" "A" == some true

end ContextCalculus.OWLFrontend.ELTests

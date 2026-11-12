import ContextCalculus.OWLFrontend.ALCTranslate
import ContextCalculus.ALCReferenceSaturation

/-!
# Executable tests for the OWL ALC translation

Hand-computed clause lists for every row of the polarity table and every
axiom kind, `none` outside OWL ALC, and end-to-end checks: `alcBit` on the
translation agrees with known entailments (a disjunction, an existential
meeting a universal, a complement, a range, an unsatisfiable class and an
inconsistent ontology read through fresh probe IRIs). The end-to-end
ontologies stay at about 10 concepts after translation, since type
elimination is exponential in the concept count.
-/

namespace ContextCalculus.OWLFrontend.ALCTests

open ContextCalculus.OWL

/-- A clause over `Fin` indices read on `Nat`. -/
def unfin {n m : Nat} : Ctx.Clause (Fin n) (Fin m) → Ctx.Clause Nat Nat
  | .gci b h => .gci (b.map Fin.val) (h.map Fin.val)
  | .exRight a r c => .exRight a.val r.val c.val
  | .exLeft r d c => .exLeft r.val d.val c.val
  | .allRight a r c => .allRight a.val r.val c.val

/-- The translated clauses, on `Nat` indices. -/
def clauses (O : Ontology) (requested : List IRI) : Option (List (Ctx.Clause Nat Nat)) :=
  (translateALC O requested).map fun T => T.ontology.map unfin

/-- The ALC reference bit for two requested IRIs, through the translation. -/
def bit (O : Ontology) (requested : List IRI) (a b : IRI) : Option Bool :=
  (translateALC O requested).bind fun T =>
    let i := T.named.idxOf a
    let j := T.named.idxOf b
    if hi : i < T.conceptCount then
      if hj : j < T.conceptCount then
        some (ALCReference.alcBit T.ontology ⟨i, hi⟩ ⟨j, hj⟩)
      else none
    else none

def r : ObjProp := .named "r"
def A : ClassExpr := .cls "A"
def B : ClassExpr := .cls "B"
def C : ClassExpr := .cls "C"
def D : ClassExpr := .cls "D"
def E : ClassExpr := .cls "E"

/-! ## Hand-computed clause lists, one per table row

Requested names first, then `top` and `bottom` (clauses `gci [] [top]`,
`gci [bottom] []` open every list), then the definers. -/

/- Negative `and`: `A ⊓ B ⊑ C`; `A, B, C = 0, 1, 2`, `top = 3`,
`bottom = 4`, definer `5`. -/
#guard clauses ⟨[.subClassOf (.and [A, B]) C]⟩ ["A", "B", "C"] ==
  some [.gci [] [3], .gci [4] [], .gci [0, 1] [5], .gci [5] [2]]

/- Positive `and`: `C ⊑ A ⊓ B`. -/
#guard clauses ⟨[.subClassOf C (.and [A, B])]⟩ ["A", "B", "C"] ==
  some [.gci [] [3], .gci [4] [], .gci [5] [0], .gci [5] [1], .gci [2] [5]]

/- Negative `or`: `A ⊔ B ⊑ C`. -/
#guard clauses ⟨[.subClassOf (.or [A, B]) C]⟩ ["A", "B", "C"] ==
  some [.gci [] [3], .gci [4] [], .gci [0] [5], .gci [1] [5], .gci [5] [2]]

/- Positive `or`: `C ⊑ A ⊔ B`. -/
#guard clauses ⟨[.subClassOf C (.or [A, B])]⟩ ["A", "B", "C"] ==
  some [.gci [] [3], .gci [4] [], .gci [5] [0, 1], .gci [2] [5]]

/- Negative `not`: `¬A ⊑ C`; `A, C = 0, 1`, `top = 2`, `bottom = 3`,
definer `4`: `gci [] [X, A]`. -/
#guard clauses ⟨[.subClassOf (.not A) C]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .gci [] [4, 0], .gci [4] [1]]

/- Positive `not`: `C ⊑ ¬A`: `gci [X, A] []`. -/
#guard clauses ⟨[.subClassOf C (.not A)]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .gci [4, 0] [], .gci [1] [4]]

/- Negative `some`: `∃r.A ⊑ C`; role `r = 0`. -/
#guard clauses ⟨[.subClassOf (.some r A) C]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .exLeft 0 0 4, .gci [4] [1]]

/- Positive `some`: `C ⊑ ∃r.A`. -/
#guard clauses ⟨[.subClassOf C (.some r A)]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .exRight 4 0 0, .gci [1] [4]]

/- Negative `all`: `∀r.A ⊑ C`; `X = 4`, `W = 5` (for `∃r.¬A`), `N = 6`
(for `¬A`): `gci [] [X, W]`, `exRight W r N`, `gci [N, A] []`. -/
#guard clauses ⟨[.subClassOf (.all r A) C]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .gci [] [4, 5], .exRight 5 0 6, .gci [6, 0] [],
    .gci [4] [1]]

/- Positive `all`: `C ⊑ ∀r.A`. -/
#guard clauses ⟨[.subClassOf C (.all r A)]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .allRight 4 0 0, .gci [1] [4]]

/- `and []` is `top`, `or []` is `bottom`, as are `owl:Thing` and
`owl:Nothing`; no definer. -/
#guard clauses ⟨[.subClassOf (.and []) (.or []), .subClassOf .thing .nothing]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .gci [0] [1], .gci [0] [1]]

/- Nested: `∃r.(A ⊔ ¬B) ⊑ ∀r.C` with both polarities in one axiom. -/
#guard clauses ⟨[.subClassOf (.some r (.or [A, .not B])) (.all r C)]⟩ ["A", "B", "C"] ==
  some [.gci [] [3], .gci [4] [], .gci [] [5, 1], .gci [0] [6], .gci [5] [6],
    .exLeft 0 6 7, .allRight 8 0 2, .gci [7] [8]]

/-! ## Axioms -/

/- `EquivalentClasses` (pairs with equal indices skipped),
`DisjointClasses`, domain, range, declarations (the declared `D` takes
index 3 after the requested names). -/
#guard clauses ⟨[.equivalentClasses [A, B, A], .disjointClasses [A, B, C], .domain r A,
    .range r B, .declareClass "D", .declareObjectProperty "s"]⟩ ["A", "B", "C"] ==
  some [.gci [] [4], .gci [5] [], .gci [0] [1], .gci [1] [0], .gci [1] [0], .gci [0] [1],
    .gci [0, 1] [], .gci [0, 2] [], .gci [1, 2] [], .exLeft 0 4 0, .allRight 4 0 1]

/-! ## Named IRIs, sizes, `none` outside ALC -/

#guard (translateALC ⟨[.subClassOf A B]⟩ ["B", "Z", "B", "A"]).map (·.named) ==
  some ["B", "Z", "A"]
#guard (translateALC ⟨[.subClassOf A (.some r B)]⟩ ["A", "B"]).map
  (fun T => (T.conceptCount, T.roleCount)) == some (5, 1)
#guard (translateALC ⟨[.subClassOf A B, .transitive r]⟩ ["A"]).isNone
#guard (translateALC ⟨[.subObjectPropertyOf [r] (.named "s")]⟩ []).isNone
#guard (translateALC ⟨[.subClassOf A (.some (.inv "r") B)]⟩ ["A"]).isNone
#guard (translateALC ⟨[.domain (.inv "r") A]⟩ ["A"]).isNone

/-! ## End to end through `ALCReference.alcBit` -/

/-- `A ⊑ B ⊔ C`, `B ⊑ D`, `C ⊑ D` entail `A ⊑ D`, not `A ⊑ B`. -/
def disj : Ontology :=
  ⟨[.subClassOf A (.or [B, C]), .subClassOf B D, .subClassOf C D]⟩

#guard bit disj ["A", "B", "C", "D"] "A" "D" == some true
#guard bit disj ["A", "B", "C", "D"] "A" "B" == some false
#guard bit disj ["A", "B", "C", "D"] "D" "A" == some false

/-- `A ⊑ ∀r.B`, `A ⊑ ∃r.C`, `E ≡ ∃r.(B ⊓ C)` entail `A ⊑ E`. -/
def exAll : Ontology :=
  ⟨[.subClassOf A (.all r B), .subClassOf A (.some r C),
    .equivalentClasses [E, .some r (.and [B, C])]]⟩

#guard bit exAll ["A", "B", "C", "E"] "A" "E" == some true
#guard bit exAll ["A", "B", "C", "E"] "E" "A" == some false

/- Without the universal the subsumption fails. -/
#guard bit ⟨[.subClassOf A (.some r C), .equivalentClasses [E, .some r (.and [B, C])]]⟩
  ["A", "B", "C", "E"] "A" "E" == some false

/-- `¬A ⊑ B` and `A ⊑ B` entail `owl:Thing ⊑ B`, read through a fresh IRI
`P`: `P ⊑ B`. -/
def compl : Ontology := ⟨[.subClassOf (.not A) B, .subClassOf A B]⟩

#guard bit compl ["A", "B", "P"] "P" "B" == some true
#guard bit compl ["A", "B", "P"] "B" "A" == some false
#guard bit ⟨[.subClassOf (.not A) B]⟩ ["A", "B", "P"] "P" "B" == some false

/-- `ObjectPropertyRange(r B)`, `C ⊑ ∃r.A`, `∃r.(A ⊓ B) ⊑ D` entail
`C ⊑ D`; without the range they do not. -/
def range : Ontology :=
  ⟨[.range r B, .subClassOf C (.some r A), .subClassOf (.some r (.and [A, B])) D]⟩

#guard bit range ["A", "B", "C", "D"] "C" "D" == some true
#guard bit ⟨range.axioms.tail⟩ ["A", "B", "C", "D"] "C" "D" == some false

/- Domain: `ObjectPropertyDomain(r B)`, `A ⊑ ∃r.C` entail `A ⊑ B`. -/
#guard bit ⟨[.domain r B, .subClassOf A (.some r C)]⟩ ["A", "B", "C"] "A" "B" == some true

/-- Unsatisfiable `A` (`A ⊑ B`, `A ⊑ ¬B`) through the probe reading: with a
fresh `Q`, `A ⊑ Q` holds and `B ⊑ Q` does not. -/
def unsat : Ontology := ⟨[.subClassOf A B, .subClassOf A (.not B)]⟩

#guard bit unsat ["A", "B", "Q"] "A" "Q" == some true
#guard bit unsat ["A", "B", "Q"] "B" "Q" == some false

/-- Inconsistent (`owl:Thing ⊑ ∃r.C`, `C ⊑ owl:Nothing`): fresh `P ⊑ Q`. -/
def incons : Ontology := ⟨[.subClassOf .thing (.some r C), .subClassOf C .nothing]⟩

#guard bit incons ["P", "Q", "C"] "P" "Q" == some true
#guard bit ⟨[.subClassOf .thing (.some r C)]⟩ ["P", "Q", "C"] "P" "Q" == some false

end ContextCalculus.OWLFrontend.ALCTests

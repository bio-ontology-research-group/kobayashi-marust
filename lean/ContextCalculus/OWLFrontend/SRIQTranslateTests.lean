import ContextCalculus.OWLFrontend.SRIQComplete

/-!
# Executable tests for the OWL SHIQ translation

Hand-computed clause lists for the rows of number restrictions and
functionality (`SRIQTranslate`), and the declines of the SHIQ route:
outside the SHIQ part, and on a non-simple role in a number restriction.

Layout as in `SRITranslateTests`: requested names first, then the other
class IRIs, then `top` and `bottom` (clauses `gci [] [top]`,
`gci [bottom] []` open every list), then the definers. Role indices follow
the first occurrence of each property IRI.

The route's answers are checked here on inputs with four concept indices
(a functional property clash, `ObjectExactCardinality` with functionality,
inverse functionality): the star elimination enumerates every record, which
the interpreter of `#guard` runs in seconds only for a handful of indices.
A qualified `max` with a subclass filler (six indices) is checked with the
compiled `km-sriq-probe` on `testdata/sriq/max-subclass-filler.ofn` and
`max-subclass-filler-sat.ofn`.
-/

namespace ContextCalculus.OWLFrontend.SRIQTests

open ContextCalculus.OWL

/-- A role term over `Fin` indices read on `Nat`. -/
def unfinRT {m : Nat} : SRI.RoleT (Fin m) → SRI.RoleT Nat
  | .pos r => .pos r.val
  | .inv r => .inv r.val

/-- A clause over `Fin` indices read on `Nat`. -/
def unfin {n m : Nat} : SRIQ.Clause (Fin n) (Fin m) → SRIQ.Clause Nat Nat
  | .gci b h => .gci (b.map Fin.val) (h.map Fin.val)
  | .exRight a R c => .exRight a.val (unfinRT R) c.val
  | .allRight a R c => .allRight a.val (unfinRT R) c.val
  | .atLeast a k R c => .atLeast a.val k (unfinRT R) c.val
  | .atMost a k R c => .atMost a.val k (unfinRT R) c.val
  | .chain body S => .chain (body.map unfinRT) (unfinRT S)

/-- The translated clauses, on `Nat` indices. -/
def clauses (O : Ontology) (requested : List IRI) : Option (List (SRIQ.Clause Nat Nat)) :=
  (translateSRIQ O requested).map fun T => T.ontology.map unfin

/-- The route's Boolean SHIQ check on the translation. -/
def shiqOK (O : Ontology) (requested : List IRI) : Option Bool :=
  (translateSRIQ O requested).map fun T => isSHIQB T.ontology

def r : ObjProp := .named "r"
def s : ObjProp := .named "s"
def ri : ObjProp := .inv "r"
def A : ClassExpr := .cls "A"
def B : ClassExpr := .cls "B"
def C : ClassExpr := .cls "C"

/-! ## Functionality -/

/- Functional property clash: `A ⊑ ∃r.B`, `A ⊑ ∃r.C`, `B ⊓ C ⊑ ⊥`,
`FunctionalObjectProperty(r)` is `top ⊑ ≤1 r.top`. `A, B, C = 0, 1, 2`,
`top = 3`, `bottom = 4`, definers `5`, `6`. -/
#guard clauses ⟨[.subClassOf A (.some r B), .subClassOf A (.some r C), .disjointClasses [B, C],
    .functional r]⟩ ["A", "B", "C"] ==
  some [.gci [] [3], .gci [4] [], .exRight 5 (.pos 0) 1, .gci [0] [5], .exRight 6 (.pos 0) 2,
    .gci [0] [6], .gci [1, 2] [], .atMost 3 1 (.pos 0) 3]

/- Inverse functionality: `top ⊑ ≤1 r⁻.top`; over `r⁻` it is
`top ⊑ ≤1 r.top`. `top = 0`, `bottom = 1`. -/
#guard clauses ⟨[.inverseFunctional r]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .atMost 0 1 (.inv 0) 0]
#guard clauses ⟨[.inverseFunctional ri]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .atMost 0 1 (.pos 0) 0]

/-! ## Number restrictions (`A, B = 0, 1`, `top = 2`, `bottom = 3`) -/

/- Positive `exact`: `A ⊑ =2 r.B` is `X ⊑ ≥2 r.B` and `X ⊑ ≤2 r.B`, `X = 4`. -/
#guard clauses ⟨[.subClassOf A (.exact 2 r B)]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .atLeast 4 2 (.pos 0) 1, .atMost 4 2 (.pos 0) 1,
    .gci [0] [4]]

/- Negative `exact`: `=2 r.B ⊑ A`; `X = 4`, `W₁ = 5` (`¬ ≥2 r.B`, that is
`≤1 r.B`), `W₂ = 6` (`¬ ≤2 r.B`, that is `≥3 r.B`). -/
#guard clauses ⟨[.subClassOf (.exact 2 r B) A]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .gci [] [4, 5, 6], .atMost 5 1 (.pos 0) 1,
    .atLeast 6 3 (.pos 0) 1, .gci [4] [0]]

/- Negative `exact 0`: `=0 r.B` is `≤0 r.B`, its complement `≥1 r.B`. -/
#guard clauses ⟨[.subClassOf (.exact 0 r B) A]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .gci [] [4, 5], .atLeast 5 1 (.pos 0) 1, .gci [4] [0]]

/- Negative `max`: `≤1 r.B ⊑ A`, complement `≥2 r.B`. -/
#guard clauses ⟨[.subClassOf (.max 1 r B) A]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .gci [] [4, 5], .atLeast 5 2 (.pos 0) 1, .gci [4] [0]]

/- Negative `min`: `≥2 r.B ⊑ A`, complement `≤1 r.B`. -/
#guard clauses ⟨[.subClassOf (.min 2 r B) A]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .gci [] [4, 5], .atMost 5 1 (.pos 0) 1, .gci [4] [0]]

/- `≥0 r.B` is `owl:Thing`: no clause, the index of `top`. -/
#guard clauses ⟨[.subClassOf (.min 0 r B) A]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .gci [2] [0]]

/- Qualified `max` over an inverse: `A ⊑ ≤1 r⁻.B`. -/
#guard clauses ⟨[.subClassOf A (.max 1 ri B)]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .atMost 4 1 (.inv 0) 1, .gci [0] [4]]

/- Qualified `max` with a subclass filler: `A ⊑ ≤1 r.B`, `C ⊑ B`;
`A, B, C = 0, 1, 2`, `top = 3`, `bottom = 4`, `X = 5`. -/
#guard clauses ⟨[.subClassOf A (.max 1 r B), .subClassOf C B]⟩ ["A", "B", "C"] ==
  some [.gci [] [3], .gci [4] [], .atMost 5 1 (.pos 0) 1, .gci [0] [5], .gci [2] [1]]

/- Nested: `A ⊑ ∃s.(≥2 r.B)`; roles `s = 0`, `r = 1`; the inner `min` is
`Y ⊑ ≥2 r.B` (`Y = 4`), the outer `X ⊑ ∃s.Y` (`X = 5`). -/
#guard clauses ⟨[.subClassOf A (.some s (.min 2 r B))]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .atLeast 4 2 (.pos 1) 1, .exRight 5 (.pos 0) 4,
    .gci [0] [5]]

/-! ## Outside SHIQ, and the simple-role check -/

/- `ObjectHasSelf` is outside SHIQ. -/
#guard (clauses ⟨[.subClassOf A (.hasSelf r)]⟩ ["A"]).isNone
#guard (owlSHIQReference ⟨[.subClassOf A (.hasSelf r)]⟩ ["A"]).isNone

/- A transitive role in a number restriction: the translation succeeds, the
route declines (`simpleB` fails). -/
#guard clauses ⟨[.transitive r, .subClassOf A (.max 1 r B)]⟩ ["A", "B"] ==
  some [.gci [] [2], .gci [3] [], .chain [.pos 0, .pos 0] (.pos 0), .atMost 4 1 (.pos 0) 1,
    .gci [0] [4]]
#guard (owlSHIQReference ⟨[.transitive r, .subClassOf A (.max 1 r B)]⟩ ["A", "B"]).isNone

/- A transitive sub-role below the inverse: `s` transitive, `s ⊑ r`,
`A ⊑ ≥1 r⁻.B`. -/
#guard (owlSHIQReference ⟨[.transitive s, .subObjectPropertyOf [s] r,
    .subClassOf A (.min 1 ri B)]⟩ ["A", "B"]).isNone

/- Functionality of a transitive role declines too. -/
#guard (owlSHIQReference ⟨[.transitive r, .functional r]⟩ []).isNone

/- A transitive role that no number restriction uses is fine: the check
passes (the route then classifies). -/
#guard shiqOK ⟨[.transitive s, .subClassOf A (.max 1 r B)]⟩ ["A", "B"] == some true
#guard shiqOK ⟨[.transitive r, .subClassOf A (.max 1 r B)]⟩ ["A", "B"] == some false

/-! ## Answers of the route (`A = 0`, `top = 1`, `bottom = 2`, one definer) -/

/-- The rows of the route as `(sub, unsat, sups)`. -/
def rowsOf (O : Ontology) (requested : List IRI) : Option (List (Nat × Bool × List Nat)) :=
  (owlSHIQReference O requested).map fun a => a.rows.map fun r => (r.sub, r.unsat, r.sups)

/- Functional property clash: `A ⊑ ≥2 r`, `r` functional: `A` is
unsatisfiable. -/
#guard rowsOf ⟨[.subClassOf A (.min 2 r .thing), .functional r]⟩ ["A"] ==
  some [(0, true, [])]

/- `A ⊑ =1 r` with `r` functional: `A` is satisfiable. -/
#guard rowsOf ⟨[.subClassOf A (.exact 1 r .thing), .functional r]⟩ ["A"] ==
  some [(0, false, [0])]

/- `A ⊑ =2 r` with `r` functional: `A` is unsatisfiable. -/
#guard rowsOf ⟨[.subClassOf A (.exact 2 r .thing), .functional r]⟩ ["A"] ==
  some [(0, true, [])]

/- Inverse functionality: `A ⊑ ≥2 r⁻` with `r` inverse functional: `A` is
unsatisfiable. -/
#guard rowsOf ⟨[.subClassOf A (.min 2 ri .thing), .inverseFunctional r]⟩ ["A"] ==
  some [(0, true, [])]

end ContextCalculus.OWLFrontend.SRIQTests

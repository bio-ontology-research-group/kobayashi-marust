import ContextCalculus.DatatypePadding

/-! Executable checking of the complete GCI padding obligation. This checks a
supplied expression list and valuation; it does not certify a source decoder,
datatype interpretations, RBox coverage, or reverse model transport. -/
namespace ContextCalculus.DatatypePadding

open DatatypeClassTransport (Expr)

def paddingEval {Class Role Data : Type}
    (classes : Class → Bool) (data : Data → Bool) : Expr Class Role Data → Bool
  | .atom c => classes c
  | .dataAtom d => data d
  | .neg p => !paddingEval classes data p
  | .conj p q => paddingEval classes data p && paddingEval classes data q
  | .disj p q => paddingEval classes data p || paddingEval classes data q
  | .some _ _ => false
  | .all _ _ => true
  | .min _ n _ => n == 0
  | .max _ _ _ => true

theorem paddingEval_iff {Class Role Data : Type}
    (classes : Class → Bool) (data : Data → Bool) (e : Expr Class Role Data) :
    paddingEval classes data e = true ↔
      paddingHolds (fun c => classes c = true) (fun d => data d = true) e := by
  induction e with
  | neg p ih =>
      simp only [paddingEval, paddingHolds, ← ih]
      cases paddingEval classes data p <;> decide
  | _ => simp_all [paddingEval, paddingHolds]

def checkPadding {Class Role Data : Type}
    (classes : Class → Bool) (data : Data → Bool)
    (axioms : List (Expr Class Role Data × Expr Class Role Data)) : Bool :=
  axioms.all fun ax => !paddingEval classes data ax.1 || paddingEval classes data ax.2

theorem checkPadding_iff {Class Role Data : Type}
    (classes : Class → Bool) (data : Data → Bool)
    (axioms : List (Expr Class Role Data × Expr Class Role Data)) :
    checkPadding classes data axioms = true ↔
      ∀ ax ∈ axioms,
        paddingHolds (fun c => classes c = true) (fun d => data d = true) ax.1 →
        paddingHolds (fun c => classes c = true) (fun d => data d = true) ax.2 := by
  simp only [checkPadding, List.all_eq_true]
  apply forall_congr'
  intro ax
  apply imp_congr Iff.rfl
  rw [← paddingEval_iff, ← paddingEval_iff]
  cases paddingEval classes data ax.1 <;> cases paddingEval classes data ax.2 <;> decide

/-- Accepted valuations discharge the padding half of the extension theorem
for every value node, provided the supplied list is the entire TBox. -/
theorem checked_tbox_extension {Class Role Data O V : Type}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (data : Data → O → Prop) (paddingClasses : Class → Bool)
    (paddingData : Data → Bool)
    (axioms : List (Expr Class Role Data × Expr Class Role Data))
    (accepted : checkPadding paddingClasses paddingData axioms = true)
    (objects : ∀ ax ∈ axioms, ∀ x,
      DatatypeClassTransport.holds classes roles data ax.1 x →
      DatatypeClassTransport.holds classes roles data ax.2 x) :
    ∀ ax ∈ axioms, ∀ node : Sum O V,
      DatatypeClassTransport.holds
        (fun c => extend (classes c) (fun _ => paddingClasses c = true))
        (fun r => objectRole (roles r))
        (fun d => extend (data d) (fun _ => paddingData d = true)) ax.1 node →
      DatatypeClassTransport.holds
        (fun c => extend (classes c) (fun _ => paddingClasses c = true))
        (fun r => objectRole (roles r))
        (fun d => extend (data d) (fun _ => paddingData d = true)) ax.2 node := by
  apply (tbox_extension_iff classes roles data
    (fun c _ => paddingClasses c = true) (fun d _ => paddingData d = true) axioms).mpr
  exact ⟨objects, fun ax member _ => (checkPadding_iff _ _ _).mp accepted ax member⟩

#print axioms paddingEval_iff
#print axioms checkPadding_iff
#print axioms checked_tbox_extension

end ContextCalculus.DatatypePadding

import ContextCalculus.HypertableauSkolemProjection

/-!
# Multi-filler Skolem projection through a fresh definer

`cb_to_ht` combines several singleton filler clauses for one Skolem witness by
introducing a fresh concept, requiring every filler from that concept, and
using the fresh concept in the existential head.  This module represents
freshness structurally with `Option Concept`: `none` is the new definer and
`some c` is an original source concept.
-/

namespace ContextCalculus.Hypertableau

def liftLit (literal : Lit Concept) : Lit (Option Concept) :=
  ⟨some literal.concept, literal.neg⟩

def liftAtom : Atom Variable Concept Role → Atom Variable (Option Concept) Role
  | .concept literal node => .concept (liftLit literal) node
  | .role role source target => .role role source target
  | .exists_ role filler node => .exists_ role (liftLit filler) node
  | .eq left right => .eq left right

def liftClause (clause : Clause Variable Concept Role) :
    Clause Variable (Option Concept) Role := {
  body := clause.body.map liftAtom
  head := clause.head.map liftAtom
}

def restrictDefiner (J : Interp Domain (Option Concept) Role) :
    Interp Domain Concept Role where
  concept concept := J.concept (some concept)
  role := J.role

theorem satLit_lift_iff (J : Interp Domain (Option Concept) Role)
    (literal : Lit Concept) (value : Domain) :
    J.satLit (liftLit literal) value ↔
      (restrictDefiner J).satLit literal value := by
  cases literal
  simp [liftLit, Interp.satLit, restrictDefiner]

theorem satAtom_lift_iff (J : Interp Domain (Option Concept) Role)
    (assignment : Variable → Domain) (atom : Atom Variable Concept Role) :
    J.satAtom assignment (liftAtom atom) ↔
      (restrictDefiner J).satAtom assignment atom := by
  cases atom <;> simp [liftAtom, Interp.satAtom, satLit_lift_iff, restrictDefiner]

theorem modelsClause_lift_iff (J : Interp Domain (Option Concept) Role)
    (clause : Clause Variable Concept Role) :
    J.modelsClause (liftClause clause) ↔
      (restrictDefiner J).modelsClause clause := by
  constructor
  · intro hmodels assignment hbody
    have hliftedBody : ∀ atom ∈ (liftClause clause).body,
        J.satAtom assignment atom := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
      exact (satAtom_lift_iff J assignment sourceAtom).2 (hbody sourceAtom hsource)
    rcases hmodels assignment hliftedBody with ⟨atom, hatom, hsat⟩
    rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
    exact ⟨sourceAtom, hsource, (satAtom_lift_iff J assignment sourceAtom).1 hsat⟩
  · intro hmodels assignment hbody
    have hsourceBody : ∀ atom ∈ clause.body,
        (restrictDefiner J).satAtom assignment atom := by
      intro atom hatom
      apply (satAtom_lift_iff J assignment atom).1
      exact hbody (liftAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩)
    rcases hmodels assignment hsourceBody with ⟨atom, hatom, hsat⟩
    exact ⟨liftAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
      (satAtom_lift_iff J assignment atom).2 hsat⟩

theorem models_lift_iff (J : Interp Domain (Option Concept) Role)
    (ontology : List (Clause Variable Concept Role)) :
    J.models (ontology.map liftClause) ↔
      (restrictDefiner J).models ontology := by
  constructor
  · intro hmodels clause hclause
    exact (modelsClause_lift_iff J clause).1
      (hmodels (liftClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · intro hmodels clause hclause
    rcases List.mem_map.mp hclause with ⟨sourceClause, hsource, rfl⟩
    exact (modelsClause_lift_iff J sourceClause).2 (hmodels sourceClause hsource)

def ModelsSkolemBundle (I : Interp Domain Concept Role)
    (functions : SkolemInterp Domain Function)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (fillers : List (Lit Concept)) : Prop :=
  (∀ assignment, HoldsBody I assignment body →
    I.role role (assignment source) (functions.app function (assignment source))) ∧
  (∀ filler ∈ fillers, ∀ assignment, HoldsBody I assignment body →
    I.satLit filler (functions.app function (assignment source)))

def bundleExtension (I : Interp Domain Concept Role)
    (fillers : List (Lit Concept)) : Interp Domain (Option Concept) Role where
  concept
    | none => fun value => ∀ filler ∈ fillers, I.satLit filler value
    | some concept => I.concept concept
  role := I.role

@[simp] theorem restrictDefiner_bundleExtension
    (I : Interp Domain Concept Role) (fillers : List (Lit Concept)) :
    restrictDefiner (bundleExtension I fillers) = I := by
  rfl

def bundleExistentialClause
    (body : List (Atom Variable Concept Role)) (source : Variable) (role : Role) :
    Clause Variable (Option Concept) Role := {
  body := body.map liftAtom
  head := [.exists_ role (.pos none) source]
}

def bundleDefinerClause (source : Variable) (filler : Lit Concept) :
    Clause Variable (Option Concept) Role := {
  body := [.concept (.pos none) source]
  head := [.concept (liftLit filler) source]
}

def bundleProjectionOntology
    (direct : List (Clause Variable Concept Role))
    (body : List (Atom Variable Concept Role)) (source : Variable) (role : Role)
    (fillers : List (Lit Concept)) :
    List (Clause Variable (Option Concept) Role) :=
  direct.map liftClause ++
    bundleExistentialClause body source role ::
      fillers.map (bundleDefinerClause source)

theorem bundleProjection_sound
    (I : Interp Domain Concept Role) (functions : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (fillers : List (Lit Concept))
    (hdirect : I.models direct)
    (hbundle : ModelsSkolemBundle I functions body source function role fillers) :
    (bundleExtension I fillers).models
      (bundleProjectionOntology direct body source role fillers) := by
  intro clause hclause
  rcases List.mem_append.mp hclause with hdirectClause | hbundleClause
  · rcases List.mem_map.mp hdirectClause with ⟨sourceClause, hsource, rfl⟩
    exact (modelsClause_lift_iff (bundleExtension I fillers) sourceClause).2
      (by simpa using hdirect sourceClause hsource)
  · simp only [List.mem_cons] at hbundleClause
    rcases hbundleClause with rfl | hdefiner
    · intro assignment hliftedBody
      have hsourceBody : HoldsBody I assignment body := by
        intro atom hatom
        exact (satAtom_lift_iff (bundleExtension I fillers) assignment atom).1
          (hliftedBody (liftAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
      refine ⟨.exists_ role (.pos none) source, by simp [bundleExistentialClause], ?_⟩
      refine ⟨functions.app function (assignment source), hbundle.1 assignment hsourceBody, ?_⟩
      simpa [Interp.satLit, bundleExtension] using
        (hbundle.2 · · assignment hsourceBody)
    · rcases List.mem_map.mp hdefiner with ⟨filler, hfiller, rfl⟩
      intro assignment hbody
      have hall := hbody (.concept (.pos none) source) (by simp [bundleDefinerClause])
      refine ⟨.concept (liftLit filler) source, by simp [bundleDefinerClause], ?_⟩
      have := hall filler hfiller
      simpa [Interp.satAtom, satLit_lift_iff] using this

theorem bundleProjection_complete [DecidableEq Function]
    (J : Interp Domain (Option Concept) Role) (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (fillers : List (Lit Concept))
    (htarget : J.models (bundleProjectionOntology direct body source role fillers)) :
    ∃ functions : SkolemInterp Domain Function,
      (restrictDefiner J).models direct ∧
      ModelsSkolemBundle (restrictDefiner J) functions body source function role fillers := by
  have hdirectLift : J.models (direct.map liftClause) := by
    intro clause hclause
    exact htarget clause (List.mem_append_left _ hclause)
  have hdirect : (restrictDefiner J).models direct :=
    (models_lift_iff J direct).1 hdirectLift
  have hexist : J.modelsClause (bundleExistentialClause body source role) := by
    apply htarget
    exact List.mem_append_right _ (by simp)
  have hexist' : J.modelsClause
      (existentialProjectionClause (body.map liftAtom) source role (.pos none)) := by
    simpa [bundleExistentialClause, existentialProjectionClause] using hexist
  rcases skolemPair_complete_preserving J base (body.map liftAtom) source function role
      (.pos none) hexist' with ⟨functions, hpair, _hpreserved⟩
  refine ⟨functions, hdirect, ?_, ?_⟩
  · intro assignment hsourceBody
    have hliftedBody : HoldsBody J assignment (body.map liftAtom) := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
      exact (satAtom_lift_iff J assignment sourceAtom).2 (hsourceBody sourceAtom hsource)
    exact hpair.1 assignment hliftedBody
  · intro filler hfiller assignment hsourceBody
    have hliftedBody : HoldsBody J assignment (body.map liftAtom) := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
      exact (satAtom_lift_iff J assignment sourceAtom).2 (hsourceBody sourceAtom hsource)
    have hdefinerAtWitness := hpair.2 assignment hliftedBody
    have hdefinerClause : J.modelsClause (bundleDefinerClause source filler) := by
      apply htarget
      apply List.mem_append_right
      simp only [List.mem_cons]
      right
      exact List.mem_map.mpr ⟨filler, hfiller, rfl⟩
    let witness := functions.app function (assignment source)
    let witnessAssignment : Variable → Domain := fun _ => witness
    have hbodyAtWitness : ∀ atom ∈ (bundleDefinerClause source filler).body,
        J.satAtom witnessAssignment atom := by
      intro atom hatom
      simp only [bundleDefinerClause, List.mem_singleton] at hatom
      subst atom
      simpa [Interp.satAtom, Interp.satLit, witnessAssignment, witness] using hdefinerAtWitness
    rcases hdefinerClause witnessAssignment hbodyAtWitness with ⟨atom, hatom, hsat⟩
    simp only [bundleDefinerClause, List.mem_singleton] at hatom
    subst atom
    exact (satLit_lift_iff J filler witness).1 (by simpa [Interp.satAtom, witnessAssignment] using hsat)

theorem bundleProjection_sat_iff [DecidableEq Function]
    (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (fillers : List (Lit Concept)) :
    (∃ I : Interp Domain Concept Role, ∃ functions : SkolemInterp Domain Function,
      I.models direct ∧ ModelsSkolemBundle I functions body source function role fillers) ↔
    (∃ J : Interp Domain (Option Concept) Role,
      J.models (bundleProjectionOntology direct body source role fillers)) := by
  constructor
  · rintro ⟨I, functions, hdirect, hbundle⟩
    exact ⟨bundleExtension I fillers,
      bundleProjection_sound I functions direct body source function role fillers hdirect hbundle⟩
  · rintro ⟨J, htarget⟩
    rcases bundleProjection_complete J base direct body source function role fillers htarget with
      ⟨functions, hdirect, hbundle⟩
    exact ⟨restrictDefiner J, functions, hdirect, hbundle⟩

#print axioms bundleProjection_sound
#print axioms bundleProjection_complete
#print axioms bundleProjection_sat_iff

end ContextCalculus.Hypertableau

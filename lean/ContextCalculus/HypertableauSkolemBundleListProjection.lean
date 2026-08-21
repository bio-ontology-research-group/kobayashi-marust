import ContextCalculus.HypertableauSkolemDefinerProjection

/-!
# Simultaneous multi-filler Skolem-bundle projection

The production converter may introduce several fresh filler definers in one
ontology.  This module gives every bundle a structural fresh name `Sum.inl i`
and embeds source concepts as `Sum.inr c`.  It then proves the transformation
for the whole finite family with one shared Skolem interpretation.
-/

namespace ContextCalculus.Hypertableau

structure BundleSpec (Variable Concept Role Function : Type*) where
  body : List (Atom Variable Concept Role)
  source : Variable
  function : Function
  role : Role
  fillers : List (Lit Concept)

def indexedLiftLit (literal : Lit Concept) : Lit (Sum (Fin n) Concept) :=
  ⟨Sum.inr literal.concept, literal.neg⟩

def indexedLiftAtom : Atom Variable Concept Role → Atom Variable (Sum (Fin n) Concept) Role
  | .concept literal node => .concept (indexedLiftLit literal) node
  | .role role source target => .role role source target
  | .exists_ role filler node => .exists_ role (indexedLiftLit filler) node
  | .eq left right => .eq left right

def indexedLiftClause (clause : Clause Variable Concept Role) :
    Clause Variable (Sum (Fin n) Concept) Role := {
  body := clause.body.map indexedLiftAtom
  head := clause.head.map indexedLiftAtom
}

def indexedRestrict (J : Interp Domain (Sum (Fin n) Concept) Role) :
    Interp Domain Concept Role where
  concept concept := J.concept (.inr concept)
  role := J.role

theorem indexed_satLit_lift_iff (J : Interp Domain (Sum (Fin n) Concept) Role)
    (literal : Lit Concept) (value : Domain) :
    J.satLit (indexedLiftLit literal) value ↔
      (indexedRestrict J).satLit literal value := by
  cases literal
  simp [indexedLiftLit, Interp.satLit, indexedRestrict]

theorem indexed_satAtom_lift_iff (J : Interp Domain (Sum (Fin n) Concept) Role)
    (assignment : Variable → Domain) (atom : Atom Variable Concept Role) :
    J.satAtom assignment (indexedLiftAtom atom) ↔
      (indexedRestrict J).satAtom assignment atom := by
  cases atom <;>
    simp [indexedLiftAtom, Interp.satAtom, indexed_satLit_lift_iff, indexedRestrict]

theorem indexed_modelsClause_lift_iff
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (clause : Clause Variable Concept Role) :
    J.modelsClause (indexedLiftClause clause) ↔
      (indexedRestrict J).modelsClause clause := by
  constructor
  · intro hmodels assignment hbody
    have hlifted : ∀ atom ∈ (indexedLiftClause clause).body,
        J.satAtom assignment atom := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
      exact (indexed_satAtom_lift_iff J assignment sourceAtom).2
        (hbody sourceAtom hsource)
    rcases hmodels assignment hlifted with ⟨atom, hatom, hsat⟩
    rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
    exact ⟨sourceAtom, hsource, (indexed_satAtom_lift_iff J assignment sourceAtom).1 hsat⟩
  · intro hmodels assignment hbody
    have hsource : ∀ atom ∈ clause.body,
        (indexedRestrict J).satAtom assignment atom := by
      intro atom hatom
      exact (indexed_satAtom_lift_iff J assignment atom).1
        (hbody (indexedLiftAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
    rcases hmodels assignment hsource with ⟨atom, hatom, hsat⟩
    exact ⟨indexedLiftAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
      (indexed_satAtom_lift_iff J assignment atom).2 hsat⟩

theorem indexed_models_lift_iff
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (ontology : List (Clause Variable Concept Role)) :
    J.models (ontology.map indexedLiftClause) ↔
      (indexedRestrict J).models ontology := by
  constructor
  · intro hmodels clause hclause
    exact (indexed_modelsClause_lift_iff J clause).1
      (hmodels (indexedLiftClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · intro hmodels clause hclause
    rcases List.mem_map.mp hclause with ⟨sourceClause, hsource, rfl⟩
    exact (indexed_modelsClause_lift_iff J sourceClause).2
      (hmodels sourceClause hsource)

def indexedBundlePair (specs : Fin n → BundleSpec Variable Concept Role Function)
    (index : Fin n) :
    SkolemPairSpec Variable (Sum (Fin n) Concept) Role Function := {
  body := (specs index).body.map indexedLiftAtom
  source := (specs index).source
  function := (specs index).function
  role := (specs index).role
  filler := .pos (.inl index)
}

def indexedBundlePairs (specs : Fin n → BundleSpec Variable Concept Role Function) :
    List (SkolemPairSpec Variable (Sum (Fin n) Concept) Role Function) :=
  List.ofFn (indexedBundlePair specs)

def indexedDefinerClause (index : Fin n) (source : Variable) (filler : Lit Concept) :
    Clause Variable (Sum (Fin n) Concept) Role := {
  body := [.concept (.pos (.inl index)) source]
  head := [.concept (indexedLiftLit filler) source]
}

def indexedDefinerClauses
    (specs : Fin n → BundleSpec Variable Concept Role Function) :
    List (Clause Variable (Sum (Fin n) Concept) Role) :=
  (List.ofFn fun index =>
    (specs index).fillers.map (indexedDefinerClause index (specs index).source)).flatten

def indexedBundleOntology
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function) :
    List (Clause Variable (Sum (Fin n) Concept) Role) :=
  direct.map indexedLiftClause ++
    (indexedBundlePairs specs).map (SkolemPairSpec.target) ++
    indexedDefinerClauses specs

def ModelsBundles (I : Interp Domain Concept Role)
    (functions : SkolemInterp Domain Function)
    (specs : Fin n → BundleSpec Variable Concept Role Function) : Prop :=
  ∀ index, ModelsSkolemBundle I functions (specs index).body (specs index).source
    (specs index).function (specs index).role (specs index).fillers

def indexedBundleExtension (I : Interp Domain Concept Role)
    (specs : Fin n → BundleSpec Variable Concept Role Function) :
    Interp Domain (Sum (Fin n) Concept) Role where
  concept
    | .inl index => fun value =>
        ∀ filler ∈ (specs index).fillers, I.satLit filler value
    | .inr concept => I.concept concept
  role := I.role

@[simp] theorem indexedRestrict_bundleExtension
    (I : Interp Domain Concept Role)
    (specs : Fin n → BundleSpec Variable Concept Role Function) :
    indexedRestrict (indexedBundleExtension I specs) = I := by
  rfl

theorem indexedBundleProjection_sound
    (I : Interp Domain Concept Role) (functions : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hdirect : I.models direct) (hbundles : ModelsBundles I functions specs) :
    (indexedBundleExtension I specs).models (indexedBundleOntology direct specs) := by
  intro clause hclause
  rcases List.mem_append.mp hclause with hcore | hdefiner
  · rcases List.mem_append.mp hcore with hdirectClause | hexist
    · rcases List.mem_map.mp hdirectClause with ⟨sourceClause, hsource, rfl⟩
      exact (indexed_modelsClause_lift_iff
        (indexedBundleExtension I specs) sourceClause).2 (hdirect sourceClause hsource)
    · rcases List.mem_map.mp hexist with ⟨pair, hpair, rfl⟩
      rcases List.mem_ofFn.mp hpair with ⟨index, rfl⟩
      apply skolemPair_sound
      constructor
      · intro assignment hbody
        apply (hbundles index).1
        intro atom hatom
        exact (indexed_satAtom_lift_iff
          (indexedBundleExtension I specs) assignment atom).1
          (hbody (indexedLiftAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
      · intro assignment hbody
        have hsourceBody : HoldsBody I assignment (specs index).body := by
          intro atom hatom
          exact (indexed_satAtom_lift_iff
            (indexedBundleExtension I specs) assignment atom).1
            (hbody (indexedLiftAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
        simpa [Interp.satLit, indexedBundleExtension] using
          ((hbundles index).2 · · assignment hsourceBody)
  · simp only [indexedDefinerClauses, List.mem_flatten] at hdefiner
    rcases hdefiner with ⟨clauses, hclauses, hclause⟩
    rcases List.mem_ofFn.mp hclauses with ⟨index, rfl⟩
    rcases List.mem_map.mp hclause with ⟨filler, hfiller, rfl⟩
    intro assignment hbody
    have hall := hbody (.concept (.pos (.inl index)) (specs index).source)
      (by simp [indexedDefinerClause])
    refine ⟨.concept (indexedLiftLit filler) (specs index).source,
      by simp [indexedDefinerClause], ?_⟩
    have := hall filler hfiller
    simpa [Interp.satAtom, indexed_satLit_lift_iff] using this

theorem indexedBundleProjection_complete [DecidableEq Function]
    (J : Interp Domain (Sum (Fin n) Concept) Role)
    (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hunique : (skolemPairFunctions (indexedBundlePairs specs)).Nodup)
    (htarget : J.models (indexedBundleOntology direct specs)) :
    ∃ functions : SkolemInterp Domain Function,
      (indexedRestrict J).models direct ∧
      ModelsBundles (indexedRestrict J) functions specs := by
  have hdirectLift : J.models (direct.map indexedLiftClause) := by
    intro clause hclause
    apply htarget clause
    apply List.mem_append_left
    exact List.mem_append_left _ hclause
  have hdirect : (indexedRestrict J).models direct :=
    (indexed_models_lift_iff J direct).1 hdirectLift
  have hpairs : J.models ((indexedBundlePairs specs).map SkolemPairSpec.target) := by
    intro clause hclause
    apply htarget clause
    apply List.mem_append_left
    exact List.mem_append_right _ hclause
  rcases modelsSkolemPairs_complete J base (indexedBundlePairs specs) hunique hpairs with
    ⟨functions, hpairModels⟩
  refine ⟨functions, hdirect, ?_⟩
  intro index
  have hpairMem : indexedBundlePair specs index ∈ indexedBundlePairs specs := by
    simp [indexedBundlePairs]
  have hpair := hpairModels (indexedBundlePair specs index) hpairMem
  constructor
  · intro assignment hbody
    have hliftedBody : HoldsBody J assignment
        ((specs index).body.map indexedLiftAtom) := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
      exact (indexed_satAtom_lift_iff J assignment sourceAtom).2
        (hbody sourceAtom hsource)
    exact hpair.1 assignment hliftedBody
  · intro filler hfiller assignment hbody
    have hliftedBody : HoldsBody J assignment
        ((specs index).body.map indexedLiftAtom) := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
      exact (indexed_satAtom_lift_iff J assignment sourceAtom).2
        (hbody sourceAtom hsource)
    have hdefinerAtWitness := hpair.2 assignment hliftedBody
    have hdefinerClause : J.modelsClause
        (indexedDefinerClause index (specs index).source filler) := by
      apply htarget
      apply List.mem_append_right
      simp only [indexedDefinerClauses, List.mem_flatten]
      refine ⟨(specs index).fillers.map
        (indexedDefinerClause index (specs index).source), ?_, ?_⟩
      · exact List.mem_ofFn.mpr ⟨index, rfl⟩
      · exact List.mem_map.mpr ⟨filler, hfiller, rfl⟩
    let witness := functions.app (specs index).function (assignment (specs index).source)
    let witnessAssignment : Variable → Domain := fun _ => witness
    have hbodyAtWitness : ∀ atom ∈
        (indexedDefinerClause index (specs index).source filler).body,
        J.satAtom witnessAssignment atom := by
      intro atom hatom
      simp only [indexedDefinerClause, List.mem_singleton] at hatom
      subst atom
      simpa [Interp.satAtom, Interp.satLit, witnessAssignment, witness,
        indexedBundlePair, SkolemPairSpec.models, ModelsSkolemPair] using
        hdefinerAtWitness
    rcases hdefinerClause witnessAssignment hbodyAtWitness with ⟨atom, hatom, hsat⟩
    simp only [indexedDefinerClause, List.mem_singleton] at hatom
    subst atom
    exact (indexed_satLit_lift_iff J filler witness).1
      (by simpa [Interp.satAtom, witnessAssignment] using hsat)

theorem indexedBundleProjection_sat_iff [DecidableEq Function]
    (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (specs : Fin n → BundleSpec Variable Concept Role Function)
    (hunique : (skolemPairFunctions (indexedBundlePairs specs)).Nodup) :
    (∃ I : Interp Domain Concept Role, ∃ functions : SkolemInterp Domain Function,
      I.models direct ∧ ModelsBundles I functions specs) ↔
    (∃ J : Interp Domain (Sum (Fin n) Concept) Role,
      J.models (indexedBundleOntology direct specs)) := by
  constructor
  · rintro ⟨I, functions, hdirect, hbundles⟩
    exact ⟨indexedBundleExtension I specs,
      indexedBundleProjection_sound I functions direct specs hdirect hbundles⟩
  · rintro ⟨J, htarget⟩
    rcases indexedBundleProjection_complete J base direct specs hunique htarget with
      ⟨functions, hdirect, hbundles⟩
    exact ⟨indexedRestrict J, functions, hdirect, hbundles⟩

#print axioms indexedBundleProjection_sound
#print axioms indexedBundleProjection_complete
#print axioms indexedBundleProjection_sat_iff

end ContextCalculus.Hypertableau

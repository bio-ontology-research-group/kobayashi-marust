import ContextCalculus.OWLFrontend.HintEval

/-!
# The negative rows of the witness model (stage H4)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 12. `ckOf W fuel` is the core
knowledge of an accepted witness hint:

* successors of a property: owl:topObjectProperty and
  owl:bottomObjectProperty exactly; on the chain route, a simple property
  (`W.props`) by its labels (exact on the core); every other named property
  or inverse (`W.rprops`) by the product of the labels with its automaton
  (`SROIQ.Proc.succOf`, at most `fuel` states), exact when the listing
  finished and the hint is flat; on the other routes nothing;
* classes: a requested class at a core element by the core type;
* individuals: the core element whose type holds the individual's nominal;
* every element is a core element when the route is the chain route and
  the hint is flat.

`ckOf_spec`: the knowledge is true of the model of `wTabA_model`.
`hintRefute_sound`: `refute (ckOf W fuel) ax = true` certifies that `O`
does not entail `ax`. `hintRefuteR_sound`: the same with keys and rules.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes
open ContextCalculus.SROIQ (Gen Stack)
open ContextCalculus.SROIQ.Proc (LPath succOf succOf_sound succOf_complete)

/-! ## The automaton's moves with a precomputed hierarchy table -/

/-- The moves of a stack, with the hierarchy table computed once. -/
def scOf {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) :
    Stack (Fin m) → List (Option (SROIQ.Proc.RT m) × Stack (Fin m)) :=
  SROIQ.Proc.succsT (SROIQ.rules O) (SROIQ.Proc.leH (Std.HashMap.ofList (SROIQ.Proc.mkTab O)))

theorem scOf_eq {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : scOf O = SROIQ.Proc.succs O := by
  unfold scOf
  rw [SROIQ.Proc.leH_mkTab, SROIQ.Proc.succsT_eq]

/-! ## The knowledge of a witness table -/

/-- The value of the first entry with key `p`. -/
def findR {α β : Type} [BEq α] (L : List (α × β)) (p : α) : Option β :=
  (L.find? fun e => e.1 == p).map Prod.snd

theorem findR_mem {α β : Type} [BEq α] [LawfulBEq α] {L : List (α × β)} {p : α} {b : β}
    (h : findR L p = some b) : (p, b) ∈ L := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  rw [beq_iff_eq] at hp
  rw [← hp]
  exact hm

/-- Successors of a named property or inverse. -/
def ckSuccB (W : WTab) (sc : Stack (Fin W.M) → List (Option (SROIQ.Proc.RT W.M) × Stack (Fin W.M)))
    (fuel : Nat) (p : ObjProp) (w : Fin W.k) : List (Fin W.k) × Bool :=
  if W.chainR then
    match findR W.props p with
    | some R => ((W.adj w).filterMap fun e => if R ∈ e.2 then some e.1 else none, true)
    | none =>
      match findR W.rprops p with
      | some R => let r := succOf sc W.adj fuel R w; (r.1, r.2 && W.flat)
      | none => ([], false)
  else ([], false)

/-- Successors of a property. -/
def ckSucc (W : WTab) (sc : Stack (Fin W.M) → List (Option (SROIQ.Proc.RT W.M) × Stack (Fin W.M)))
    (fuel : Nat) : ObjProp → Fin W.k → List (Fin W.k) × Bool
  | .top, _ => (List.finRange W.k, true)
  | .bot, _ => ([], true)
  | p, w => ckSuccB W sc fuel p w

/-- A requested class at a core element. -/
def ckCls (W : WTab) (A : IRI) (w : Fin W.k) : Option Bool :=
  (findR W.cls A).map fun i => decide (i ∈ W.ty w)

/-- The core element of an individual. -/
def ckInd (W : WTab) (a : IRI) : Option (Fin W.k) :=
  (findR W.inds a).bind fun i => (List.finRange W.k).find? fun w => decide (i ∈ W.ty w)

/-- **The core knowledge of a witness table.** -/
def ckOf (W : WTab) (fuel : Nat) : CK W.k :=
  let sc := scOf W.ob
  { succ := ckSucc W sc fuel, cls := ckCls W, ind := ckInd W, surj := W.chainR && W.flat }

/-- The fuel of the command line (product states listed per start). -/
def ckFuel : Nat := 4000000

section Spec

variable {DM : DatatypeMap} {Dom : Type}

theorem ckCls_spec {W : WTab} {I : Interp DM Dom} {f : Fin W.k → Dom}
    (hcls : ∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w) (A : IRI) (w : Fin W.k) :
    (ckCls W A w = some true → I.cls A (f w)) ∧ (ckCls W A w = some false → ¬ I.cls A (f w)) := by
  unfold ckCls
  cases hf : findR W.cls A with
  | none => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | some i =>
    have hm := hcls A i (findR_mem hf) w
    simp only [Option.map_some, Option.some.injEq, decide_eq_true_eq, decide_eq_false_iff_not]
    exact ⟨hm.2, fun h hc => h (hm.1 hc)⟩

theorem ckInd_spec {W : WTab} {I : Interp DM Dom} {f : Fin W.k → Dom}
    (hind : ∀ a x, (a, x) ∈ W.inds → ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w) (a : IRI)
    (w : Fin W.k) (h : ckInd W a = some w) : I.ind (.named a) = f w := by
  unfold ckInd at h
  obtain ⟨i, hi, hw⟩ := Option.bind_eq_some_iff.1 h
  have := List.find?_some hw
  rw [decide_eq_true_eq] at this
  exact ((hind a i (findR_mem hi) w).2 this).symm

/-- **The core knowledge is true of the witness model.** -/
theorem ckOf_spec (pat : String → String → Prop) {O : Ontology} {req : List IRI} {hint : RawHint}
    {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) :
    ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom),
      OWL.Model O I ∧ CKSpec (ckOf W fuel) I f := by
  by_cases hc : W.chainR = true
  · obtain ⟨Dom, hD, I, f, hM, hinj, hcls, hind, hrole, hadj, hpos, hneg, hsur⟩ := wTabA_rfacts pat hw hc
    have hsc : ∀ st l st', (l, st') ∈ scOf W.ob st ↔ SROIQ.Move W.ob st l st' := by
      intro st l st'; rw [scOf_eq]; exact SROIQ.Proc.mem_succs
    have hB : ∀ (p : ObjProp) (w v : Fin W.k),
        (v ∈ (ckSuccB W (scOf W.ob) fuel p w).1 → I.prop p (f w) (f v)) ∧
        ((ckSuccB W (scOf W.ob) fuel p w).2 = true → I.prop p (f w) (f v) →
          v ∈ (ckSuccB W (scOf W.ob) fuel p w).1) := by
      intro p w v
      unfold ckSuccB
      rw [if_pos hc]
      cases hp : findR W.props p with
      | some R =>
        have hr := hrole p R (findR_mem hp) w v
        refine ⟨fun h => ?_, fun _ h => ?_⟩
        · obtain ⟨e, he, hev⟩ := List.mem_filterMap.1 h
          split_ifs at hev with hR
          cases hev
          exact hr.2 ((hadj w e.1 R).2 ⟨e, he, rfl, hR⟩)
        · obtain ⟨e, he, rfl, hR⟩ := (hadj w v R).1 (hr.1 h)
          exact List.mem_filterMap.2 ⟨e, he, by simp [hR]⟩
      | none =>
        cases hq : findR W.rprops p with
        | none => exact ⟨fun h => absurd h List.not_mem_nil, fun h => (nomatch h)⟩
        | some R =>
          have hmem := findR_mem hq
          dsimp only
          refine ⟨fun h => ?_, fun h h2 => ?_⟩
          · obtain ⟨word, hg, hpth⟩ := succOf_sound (O := W.ob) (lab := W.lab)
              (fun st l st' h => (hsc st l st').1 h)
              (fun x e he R hR => (hadj x e.1 R).2 ⟨e, he, rfl, hR⟩) h
            exact hpos p R hmem w v word hg hpth
          · rw [Bool.and_eq_true] at h
            obtain ⟨word, hg, hpth⟩ := hneg h.2 p R hmem w v h2
            exact succOf_complete (O := W.ob) (lab := W.lab) (fun st l st' h => (hsc st l st').2 h)
              (fun x z R hR => (hadj x z R).1 hR) h.1 hg hpth
    refine ⟨Dom, hD, I, f, hM, ⟨hinj, fun p w v h => ?_, fun p w v hex h => ?_,
      fun A w => (ckCls_spec hcls A w).1, fun A w => (ckCls_spec hcls A w).2,
      fun a w h => ckInd_spec hind a w h, fun h => hsur (by simp_all [ckOf])⟩⟩
    · cases p with
      | top => trivial
      | bot => exact absurd h List.not_mem_nil
      | named e => exact (hB _ w v).1 h
      | inv e => exact (hB _ w v).1 h
    · cases p with
      | top => exact List.mem_finRange _
      | bot => exact h.elim
      | named e => exact (hB _ w v).2 hex h
      | inv e => exact (hB _ w v).2 hex h
  · obtain ⟨Dom, hD, I, f, hM, hinj, hcls, hind, -⟩ := wTabA_model pat hw
    have hB : ∀ (p : ObjProp) (w : Fin W.k), ckSuccB W (scOf W.ob) fuel p w = ([], false) := by
      intro p w; unfold ckSuccB; rw [if_neg hc]
    refine ⟨Dom, hD, I, f, hM, ⟨hinj, fun p w v h => ?_, fun p w v hex h => ?_,
      fun A w => (ckCls_spec hcls A w).1, fun A w => (ckCls_spec hcls A w).2,
      fun a w h => ckInd_spec hind a w h, fun h => ?_⟩⟩
    · cases p with
      | top => trivial
      | bot => exact absurd h List.not_mem_nil
      | named e => simp [ckOf, ckSucc, hB] at h
      | inv e => simp [ckOf, ckSucc, hB] at h
    · cases p with
      | top => exact List.mem_finRange _
      | bot => exact h.elim
      | named e => simp [ckOf, ckSucc, hB] at hex
      | inv e => simp [ckOf, ckSucc, hB] at hex
    · simp only [ckOf, Bool.and_eq_true] at h
      exact absurd h.1 hc

end Spec

/-! ## The rows -/

/-- **A refuted axiom is not entailed.** -/
theorem hintRefute_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) (ax : Axiom)
    (h : refute (ckOf W fuel) ax = true) : ¬ EntailsAt (owl2MapP pat) O ax := by
  obtain ⟨Dom, hD, I, f, hM, hK⟩ := ckOf_spec pat hw fuel
  haveI := hD
  exact fun he => refute_sound hK _ ax h (he Dom I hM)

/-- **A refuted subsumption between class expressions is not entailed.** -/
theorem hintRefuteSub_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) (C D : ClassExpr)
    (h : refute (ckOf W fuel) (.subClassOf C D) = true) :
    ¬ EntailsSubCE (owl2MapP pat) O C D := by
  obtain ⟨Dom, hD, I, f, hM, hK⟩ := ckOf_spec pat hw fuel
  haveI := hD
  exact fun he => refute_sound hK [] _ h (he Dom I hM)

/-- **A refuted axiom is not entailed, with keys and DL-safe rules**, for
every reading of the built-ins. -/
theorem hintRefuteR_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {R : OntologyR} {req : List IRI} {hint : RawHint} {W : WTab} (hw : wTabR R req hint = some W)
    (fuel : Nat) (ax : Axiom) (h : refute (ckOf W fuel) ax = true) :
    ¬ EntailsAtR (owl2MapP pat) bi R ax := by
  obtain ⟨O', hO', hw'⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨Dom, hD, I, f, hM, hK⟩ := ckOf_spec pat hw' fuel
  haveI := hD
  exact fun he => refute_sound hK _ ax h (he Dom I (modelR_of_rulesOntoK bi hO' I hM))

/-- **A refuted subsumption between class expressions is not entailed,
with keys and DL-safe rules.** -/
theorem hintRefuteSubR_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {R : OntologyR} {req : List IRI} {hint : RawHint} {W : WTab} (hw : wTabR R req hint = some W)
    (fuel : Nat) (C D : ClassExpr) (h : refute (ckOf W fuel) (.subClassOf C D) = true) :
    ¬ EntailsSubCER (owl2MapP pat) bi R C D := by
  obtain ⟨O', hO', hw'⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨Dom, hD, I, f, hM, hK⟩ := ckOf_spec pat hw' fuel
  haveI := hD
  exact fun he => refute_sound hK [] _ h (he Dom I (modelR_of_rulesOntoK bi hO' I hM))

/-! ## Successor tables computed once (for the command line) -/

/-- A hash for object property expressions. -/
instance instHashableObjProp : Hashable ObjProp where
  hash
    | .named r => mixHash 1 (hash r)
    | .inv r => mixHash 2 (hash r)
    | .top => 3
    | .bot => 4

/-- `K` with the successors of the properties `ps` computed once. -/
def ckMemo {k : Nat} (K : CK k) (ps : List ObjProp) : CK k :=
  let arr := ps.toArray.map fun p => (p, Array.ofFn (K.succ p))
  let idx : Std.HashMap ObjProp Nat := ps.zipIdx.foldl (fun mp e => mp.insertIfNew e.1 e.2) {}
  { K with succ := fun p w =>
      match idx[p]? with
      | some i =>
        match arr[i]? with
        | some e => if e.1 == p then (e.2[w.val]?).getD (K.succ p w) else K.succ p w
        | none => K.succ p w
      | none => K.succ p w }

/-- **The tables change nothing.** -/
theorem ckMemo_eq {k : Nat} (K : CK k) (ps : List ObjProp) : ckMemo K ps = K := by
  cases K with
  | mk succ cls ind surj =>
  simp only [ckMemo, CK.mk.injEq, and_true]
  funext p w
  split
  · split
    next e he =>
      split_ifs with hp
      · rw [Array.getElem?_map] at he
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 he
        rw [beq_iff_eq] at hp
        dsimp only at hp ⊢
        subst hp
        simp
      · rfl
    · rfl
  · rfl

/-- **A refuted axiom is not entailed** (with the tables of `ckMemo`). -/
theorem hintRefuteM_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) (ps : List ObjProp)
    (ax : Axiom) (h : refute (ckMemo (ckOf W fuel) ps) ax = true) : ¬ EntailsAt (owl2MapP pat) O ax := by
  rw [ckMemo_eq] at h
  exact hintRefute_sound pat hw fuel ax h

/-- **A refuted axiom is not entailed, with keys and rules** (with the
tables of `ckMemo`). -/
theorem hintRefuteMR_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {R : OntologyR} {req : List IRI} {hint : RawHint} {W : WTab} (hw : wTabR R req hint = some W)
    (fuel : Nat) (ps : List ObjProp) (ax : Axiom) (h : refute (ckMemo (ckOf W fuel) ps) ax = true) :
    ¬ EntailsAtR (owl2MapP pat) bi R ax := by
  rw [ckMemo_eq] at h
  exact hintRefuteR_sound pat bi hw fuel ax h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.ckMemo_eq
#print axioms ContextCalculus.OWLFrontend.hintRefuteM_sound
#print axioms ContextCalculus.OWLFrontend.hintRefuteMR_sound
#print axioms ContextCalculus.OWLFrontend.ev_sound
#print axioms ContextCalculus.OWLFrontend.refute_sound
#print axioms ContextCalculus.OWLFrontend.ckOf_spec
#print axioms ContextCalculus.OWLFrontend.hintRefute_sound
#print axioms ContextCalculus.OWLFrontend.hintRefuteSub_sound
#print axioms ContextCalculus.OWLFrontend.hintRefuteR_sound
#print axioms ContextCalculus.OWLFrontend.hintRefuteSubR_sound

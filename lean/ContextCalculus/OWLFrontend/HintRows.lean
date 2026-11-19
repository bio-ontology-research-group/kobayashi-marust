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
  -- the rules and the hierarchy table as data, computed once
  let rs := SROIQ.rules W.ob
  let hm := Std.HashMap.ofList (SROIQ.Proc.mkTab W.ob)
  { succ := ckSucc W (SROIQ.Proc.succsT rs (SROIQ.Proc.leH hm)) fuel, cls := ckCls W, ind := ckInd W,
    surj := W.chainR && W.flat }

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
    have hck : ckOf W fuel = CK.mk (ckSucc W (scOf W.ob) fuel) (ckCls W) (ckInd W)
        (W.chainR && W.flat) := rfl
    rw [hck]
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
    have hck : ckOf W fuel = CK.mk (ckSucc W (scOf W.ob) fuel) (ckCls W) (ckInd W)
        (W.chainR && W.flat) := rfl
    rw [hck]
    refine ⟨Dom, hD, I, f, hM, ⟨hinj, fun p w v h => ?_, fun p w v hex h => ?_,
      fun A w => (ckCls_spec hcls A w).1, fun A w => (ckCls_spec hcls A w).2,
      fun a w h => ckInd_spec hind a w h, fun h => ?_⟩⟩
    · cases p with
      | top => trivial
      | bot => exact absurd h List.not_mem_nil
      | named e => simp [ckSucc, hB] at h
      | inv e => simp [ckSucc, hB] at h
    · cases p with
      | top => exact List.mem_finRange _
      | bot => exact h.elim
      | named e => simp [ckSucc, hB] at hex
      | inv e => simp [ckSucc, hB] at hex
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

/-- First entry of each key in `L`, as a hash map. -/
def mapOfR {α β : Type} [DecidableEq α] [Hashable α] : List (α × β) → Std.HashMap α β
  | [] => ∅
  | e :: L => (mapOfR L).insert e.1 e.2

theorem mapOfR_get {α β : Type} [DecidableEq α] [Hashable α] :
    ∀ (L : List (α × β)) (p : α), (mapOfR L)[p]? = findR L p
  | [], p => by simp [mapOfR, findR]
  | e :: L, p => by
    simp only [mapOfR, Std.HashMap.getElem?_insert, mapOfR_get L p]
    unfold findR
    simp only [List.find?_cons]
    by_cases h : e.1 = p
    · subst h; simp
    · have h1 : (e.1 == p) = false := beq_false_of_ne h
      simp [h1]

/-- Insert `(x, w)` for every concept `x` of `l` that belongs to `inom`
(tail-recursive `foldl` so `m` is updated in place without copying the
hash table on every element). -/
def insTyInom {N k : Nat} (inom : Std.HashSet (Fin N)) (w : Fin k)
    (m : Std.HashMap (Fin N) (Fin k)) (l : List (Fin N)) : Std.HashMap (Fin N) (Fin k) :=
  l.foldl (fun m x => if inom.contains x then m.insert x w else m) m

theorem insTyInom_get {N k : Nat} (inom : Std.HashSet (Fin N)) (w : Fin k) (i : Fin N)
    (hi : inom.contains i = true) :
    ∀ (l : List (Fin N)) (m : Std.HashMap (Fin N) (Fin k)),
      (insTyInom inom w m l)[i]? = if i ∈ l then some w else m[i]?
  | [], m => by simp [insTyInom]
  | x :: l, m => by
    rw [insTyInom, List.foldl_cons, ← insTyInom, insTyInom_get inom w i hi l]
    by_cases h : x = i
    · subst h
      simp [hi, Std.HashMap.getElem?_insert]
    · by_cases hx : inom.contains x = true
      · simp [hx, Std.HashMap.getElem?_insert, h, Ne.symm h]
      · simp [hx, Ne.symm h]

theorem foldr_insTyInom_get {N k : Nat} (inom : Std.HashSet (Fin N))
    (ty : Fin k → Finset (Fin N)) (i : Fin N) (hi : inom.contains i = true) :
    ∀ (ws : List (Fin k)),
      (ws.foldr (fun w m => insTyInom inom w m (SRI.Proc.toL (ty w))) ∅)[i]? =
        ws.find? fun w => decide (i ∈ ty w)
  | [] => by simp
  | w :: ws => by
    simp only [List.foldr_cons, insTyInom_get inom w i hi, SRI.Proc.mem_toL, List.find?_cons]
    by_cases h : i ∈ ty w
    · simp [h]
    · simp [h, foldr_insTyInom_get inom ty i hi ws]

/-- First core element holding each nominal concept index in `W.inds`. -/
def ownerMap (W : WTab) : Std.HashMap (Fin W.N) (Fin W.k) :=
  if W.inds.isEmpty then ∅
  else
    let inom := Std.HashSet.ofList (W.inds.map Prod.snd)
    (List.finRange W.k).reverse.foldl
      (fun m w => insTyInom inom w m (SRI.Proc.toL (W.ty w))) ∅

theorem ownerMap_get (W : WTab) {a : IRI} {i : Fin W.N} (h : (a, i) ∈ W.inds) :
    (ownerMap W)[i]? = (List.finRange W.k).find? fun w => decide (i ∈ W.ty w) := by
  unfold ownerMap
  have hne : W.inds.isEmpty = false := List.isEmpty_eq_false_iff.2 (List.ne_nil_of_mem h)
  rw [if_neg (by simp [hne]), ← List.foldr_eq_foldl_reverse]
  refine foldr_insTyInom_get _ W.ty i ?_ (List.finRange W.k)
  rw [Std.HashSet.contains_ofList]
  exact List.elem_eq_true_of_mem (List.mem_map.2 ⟨(a, i), h, rfl⟩)

def ckSuccBF (W : WTab)
    (pm rm : Std.HashMap ObjProp (SRI.RoleT (Fin W.M)))
    (sc : Stack (Fin W.M) → List (Option (SROIQ.Proc.RT W.M) × Stack (Fin W.M)))
    (br : Fin W.k → SROIQ.Proc.RT W.M → List (Fin W.k))
    (fuel : Nat) (p : ObjProp) (w : Fin W.k) : List (Fin W.k) × Bool :=
  if W.chainR then
    match pm[p]? with
    | some R => (br w R, true)
    | none =>
      match rm[p]? with
      | some R => let r := SROIQ.Proc.succOfR sc br fuel R w; (r.1, r.2 && W.flat)
      | none => ([], false)
  else ([], false)

def ckSuccF (W : WTab)
    (pm rm : Std.HashMap ObjProp (SRI.RoleT (Fin W.M)))
    (sc : Stack (Fin W.M) → List (Option (SROIQ.Proc.RT W.M) × Stack (Fin W.M)))
    (br : Fin W.k → SROIQ.Proc.RT W.M → List (Fin W.k))
    (fuel : Nat) : ObjProp → Fin W.k → List (Fin W.k) × Bool
  | .top, _ => (List.finRange W.k, true)
  | .bot, _ => ([], true)
  | p, w => ckSuccBF W pm rm sc br fuel p w

def ckClsF (W : WTab) (cm : Std.HashMap IRI (Fin W.N)) (A : IRI) (w : Fin W.k) : Option Bool :=
  (cm[A]?).map fun i => decide (i ∈ W.ty w)

def ckIndF (W : WTab) (im : Std.HashMap IRI (Fin W.N))
    (om : Std.HashMap (Fin W.N) (Fin W.k)) (a : IRI) : Option (Fin W.k) :=
  (im[a]?).bind fun i => om[i]?

/-- `ckOf` with the moves table and lookup maps computed once. -/
def ckOfF (W : WTab) (fuel : Nat) : CK W.k :=
  let rs := SROIQ.rules W.ob
  let hm := Std.HashMap.ofList (SROIQ.Proc.mkTab W.ob)
  let le := SROIQ.Proc.leH hm
  let tb := SROIQ.Proc.movesTab rs le
  let br := (SROIQ.Proc.byRoleS W.adj).f
  let pm := mapOfR W.props
  let rm := mapOfR W.rprops
  let cm := mapOfR W.cls
  let im := mapOfR W.inds
  let om := ownerMap W
  { succ := ckSuccF W pm rm (SROIQ.Proc.succsM tb rs le) br fuel
    cls := ckClsF W cm
    ind := ckIndF W im om
    surj := W.chainR && W.flat }

@[csimp] theorem ckOf_eq_F : @ckOf = @ckOfF := by
  funext W fuel
  simp only [ckOf, ckOfF, CK.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · funext p w
    cases p <;> simp [ckSucc, ckSuccF, ckSuccB, ckSuccBF, mapOfR_get, SROIQ.Proc.succsT_eq_M,
      SROIQ.Proc.byRoleS, SROIQ.Proc.succOfR_byRole, SROIQ.Proc.byRole]
  · funext A w
    simp [ckCls, ckClsF, mapOfR_get]
  · funext a
    unfold ckInd ckIndF
    rw [mapOfR_get]
    cases h : findR W.inds a with
    | none => rfl
    | some i =>
      simp only [Option.bind_some]
      exact (ownerMap_get W (findR_mem h)).symm

/-- `K` with the successors of the properties `ps` computed once. -/
def ckMemo {k : Nat} (K : CK k) (ps : List ObjProp) : CK k :=
  let arr := ps.toArray.map fun p => (p, Thunk.mk fun _ => Array.ofFn fun w => Thunk.mk fun _ => K.succ p w)
  let idx : Std.HashMap ObjProp Nat := ps.zipIdx.foldl (fun mp e => mp.insertIfNew e.1 e.2) {}
  { K with succ := fun p w =>
      match idx[p]? with
      | some i =>
        match arr[i]? with
        | some e => if e.1 == p then ((e.2.get[w.val]?).map Thunk.get).getD (K.succ p w) else K.succ p w
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
        dsimp only [Thunk.get, Thunk.mk] at hp ⊢
        subst hp
        simp [Thunk.get]
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
#print axioms ContextCalculus.OWLFrontend.ckOf_eq_F

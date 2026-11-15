import ContextCalculus.OWLFrontend.HintRoles

/-!
# Evaluating axioms over the core of a model (stage H4, items 1 and 2)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 12. A *core knowledge* table
`CK k` says what is known about a model over `k` core elements: for every
object property and core element a list of successors and a flag (the
list is exact on the core), for named classes and core elements a
three-valued membership, the core element of each individual, and whether
every element of the model is a core element. `CKSpec K I f` states that
the table is true of the model `I` with the core map `f`.

* `ev K C w`: three-valued evaluation of a class expression at a core
  element (`cls`, `thing`, `nothing`, `and`, `or`, `not`, `some`, `all`,
  `hasValue`, `hasSelf`, `oneOf`; every other constructor gives `none`).
  `ev_sound`: `some true` means `w` is in `C`, `some false` that it is not.
* `refute K ax`: the model violates the axiom `ax`, found on the core
  (class axioms, domains, ranges, property inclusions and chains,
  equivalent, inverse and disjoint properties, the property
  characteristics, individual axioms and assertions). `refute_sound`: the
  model does not satisfy `ax`.

Every theorem here is about one interpretation; the rows are in
`HintRows.lean`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

/-- What the checker knows about a model over `k` core elements. -/
structure CK (k : Nat) where
  succ : ObjProp → Fin k → List (Fin k) × Bool
  cls : IRI → Fin k → Option Bool
  ind : IRI → Option (Fin k)
  surj : Bool

variable {k : Nat}

/-- The table is true of `I` with the core map `f`. -/
structure CKSpec {DM : DatatypeMap} {Dom : Type} (K : CK k) (I : Interp DM Dom) (f : Fin k → Dom) :
    Prop where
  inj : Function.Injective f
  pos : ∀ p w v, v ∈ (K.succ p w).1 → I.prop p (f w) (f v)
  neg : ∀ p w v, (K.succ p w).2 = true → I.prop p (f w) (f v) → v ∈ (K.succ p w).1
  clsT : ∀ A w, K.cls A w = some true → I.cls A (f w)
  clsF : ∀ A w, K.cls A w = some false → ¬ I.cls A (f w)
  ind : ∀ a w, K.ind a = some w → I.ind (.named a) = f w
  surj : K.surj = true → ∀ y, ∃ w, f w = y

/-! ## Three-valued evaluation -/

def andV : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

def orV : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

theorem andV_true {a b : Option Bool} (h : andV a b = some true) : a = some true ∧ b = some true := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [andV]

theorem andV_false {a b : Option Bool} (h : andV a b = some false) : a = some false ∨ b = some false := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [andV]

theorem orV_true {a b : Option Bool} (h : orV a b = some true) : a = some true ∨ b = some true := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [orV]

theorem orV_false {a b : Option Bool} (h : orV a b = some false) : a = some false ∧ b = some false := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [orV]

/-- One of the listed individuals sits at `w`. -/
def evOne (K : CK k) : List Individual → Fin k → Option Bool
  | [], _ => some false
  | .named a :: as, w =>
    match K.ind a with
    | some v => if v = w then some true else evOne K as w
    | none => if evOne K as w = some true then some true else none
  | .anon _ :: as, w => if evOne K as w = some true then some true else none

mutual

/-- **Three-valued evaluation of a class expression at a core element.** -/
def ev (K : CK k) : ClassExpr → Fin k → Option Bool
  | .cls A, w => K.cls A w
  | .thing, _ => some true
  | .nothing, _ => some false
  | .and cs, w => evAnd K cs w
  | .or cs, w => evOr K cs w
  | .not c, w => (ev K c w).map (!·)
  | .some p c, w =>
    let s := K.succ p w
    if s.1.any (fun v => ev K c v == some true) then some true
    else if s.2 && K.surj && s.1.all (fun v => ev K c v == some false) then some false
    else none
  | .all p c, w =>
    let s := K.succ p w
    if s.1.any (fun v => ev K c v == some false) then some false
    else if s.2 && K.surj && s.1.all (fun v => ev K c v == some true) then some true
    else none
  | .hasValue p (.named a), w =>
    match K.ind a with
    | none => none
    | some v =>
      let s := K.succ p w
      if s.1.contains v then some true else if s.2 then some false else none
  | .hasSelf p, w =>
    let s := K.succ p w
    if s.1.contains w then some true else if s.2 then some false else none
  | .oneOf as, w => evOne K as w
  | .hasValue _ (.anon _), _ => none
  | .min .., _ | .max .., _ | .exact .., _ => none
  | .dataSome .., _ | .dataAll .., _ | .dataHasValue .., _ => none
  | .dataMin .., _ | .dataMax .., _ | .dataExact .., _ => none

def evAnd (K : CK k) : List ClassExpr → Fin k → Option Bool
  | [], _ => some true
  | c :: cs, w => andV (ev K c w) (evAnd K cs w)

def evOr (K : CK k) : List ClassExpr → Fin k → Option Bool
  | [], _ => some false
  | c :: cs, w => orV (ev K c w) (evOr K cs w)

end

section Sound

variable {DM : DatatypeMap} {Dom : Type} {K : CK k} {I : Interp DM Dom} {f : Fin k → Dom}

theorem evOne_sound (hK : CKSpec K I f) : ∀ (as : List Individual) (w : Fin k),
    (evOne K as w = some true → ∃ a ∈ as, f w = I.ind a) ∧
    (evOne K as w = some false → ∀ a ∈ as, f w ≠ I.ind a)
  | [], w => by simp [evOne]
  | .named a :: as, w => by
    have ih := evOne_sound hK as w
    unfold evOne
    split
    next v hv =>
      split_ifs with hvw
      · subst hvw
        refine ⟨fun _ => ⟨_, List.mem_cons_self, (hK.ind a _ hv).symm⟩, fun h => (nomatch h)⟩
      · refine ⟨fun h => ?_, fun h b hb => ?_⟩
        · obtain ⟨b, hb, he⟩ := ih.1 h
          exact ⟨b, List.mem_cons_of_mem _ hb, he⟩
        · rcases List.mem_cons.1 hb with rfl | hb
          · rw [hK.ind a v hv]; exact fun he => hvw (hK.inj he).symm
          · exact ih.2 h b hb
    next hv =>
      split_ifs with h1
      · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
        obtain ⟨b, hb, he⟩ := ih.1 h1
        exact ⟨b, List.mem_cons_of_mem _ hb, he⟩
      · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .anon x :: as, w => by
    have ih := evOne_sound hK as w
    unfold evOne
    split_ifs with h1
    · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
      obtain ⟨b, hb, he⟩ := ih.1 h1
      exact ⟨b, List.mem_cons_of_mem _ hb, he⟩
    · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem ev_some_sound (hK : CKSpec K I f) {p : ObjProp} {c : ClassExpr} {w : Fin k}
    (ih : ∀ v, (ev K c v = some true → I.ext c (f v)) ∧ (ev K c v = some false → ¬ I.ext c (f v))) :
    (ev K (.some p c) w = some true → I.ext (.some p c) (f w)) ∧
    (ev K (.some p c) w = some false → ¬ I.ext (.some p c) (f w)) := by
  rw [ev, Interp.ext]
  dsimp only
  split_ifs with h1 h2
  · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
    obtain ⟨v, hv, he⟩ := List.any_eq_true.1 h1
    exact ⟨f v, hK.pos p w v hv, (ih v).1 (beq_iff_eq.1 he)⟩
  · refine ⟨fun h => (nomatch h), fun _ => ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true] at h2
    obtain ⟨⟨hex, hs⟩, hall⟩ := h2
    rintro ⟨y, hy, hc⟩
    obtain ⟨v, rfl⟩ := hK.surj hs y
    exact (ih v).2 (beq_iff_eq.1 (hall v (hK.neg p w v hex hy))) hc
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem ev_all_sound (hK : CKSpec K I f) {p : ObjProp} {c : ClassExpr} {w : Fin k}
    (ih : ∀ v, (ev K c v = some true → I.ext c (f v)) ∧ (ev K c v = some false → ¬ I.ext c (f v))) :
    (ev K (.all p c) w = some true → I.ext (.all p c) (f w)) ∧
    (ev K (.all p c) w = some false → ¬ I.ext (.all p c) (f w)) := by
  rw [ev, Interp.ext]
  dsimp only
  split_ifs with h1 h2
  · refine ⟨fun h => (nomatch h), fun _ => ?_⟩
    obtain ⟨v, hv, he⟩ := List.any_eq_true.1 h1
    exact fun hall => (ih v).2 (beq_iff_eq.1 he) (hall _ (hK.pos p w v hv))
  · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
    simp only [Bool.and_eq_true, List.all_eq_true] at h2
    obtain ⟨⟨hex, hs⟩, hall⟩ := h2
    intro y hy
    obtain ⟨v, rfl⟩ := hK.surj hs y
    exact (ih v).1 (beq_iff_eq.1 (hall v (hK.neg p w v hex hy)))
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

mutual

/-- **Soundness of the evaluation.** -/
theorem ev_sound (hK : CKSpec K I f) : ∀ (c : ClassExpr) (w : Fin k),
    (ev K c w = some true → I.ext c (f w)) ∧ (ev K c w = some false → ¬ I.ext c (f w))
  | .cls A, w => by
    rw [ev, Interp.ext]; exact ⟨hK.clsT A w, hK.clsF A w⟩
  | .thing, w => by rw [ev, Interp.ext]; exact ⟨fun _ => trivial, fun h => (nomatch h)⟩
  | .nothing, w => by rw [ev, Interp.ext]; exact ⟨fun h => (nomatch h), fun _ h => h⟩
  | .and cs, w => by
    rw [ev, Interp.ext]
    obtain ⟨h1, h2⟩ := evAnd_sound hK cs w
    exact ⟨fun h c hc => h1 h c hc, fun h hall => by
      obtain ⟨c, hc, hn⟩ := h2 h; exact hn (hall c hc)⟩
  | .or cs, w => by
    rw [ev, Interp.ext]
    obtain ⟨h1, h2⟩ := evOr_sound hK cs w
    exact ⟨fun h => by obtain ⟨c, hc, he⟩ := h1 h; exact ⟨c, hc, he⟩,
      fun h ⟨c, hc, he⟩ => h2 h c hc he⟩
  | .not c, w => by
    rw [ev, Interp.ext]
    obtain ⟨h1, h2⟩ := ev_sound hK c w
    constructor
    · intro h
      cases hv : ev K c w with
      | none => rw [hv] at h; cases h
      | some b => rw [hv] at h; cases b <;> simp_all
    · intro h
      cases hv : ev K c w with
      | none => rw [hv] at h; cases h
      | some b => rw [hv] at h; cases b <;> simp_all
  | .some p c, w => ev_some_sound hK fun v => ev_sound hK c v
  | .all p c, w => ev_all_sound hK fun v => ev_sound hK c v
  | .hasValue p (.named a), w => by
    rw [ev, Interp.ext]
    split
    next => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    next v hv =>
      dsimp only
      rw [hK.ind a v hv]
      split_ifs with h1 h2
      · exact ⟨fun _ => hK.pos p w v (List.contains_iff_mem.1 h1), fun h => (nomatch h)⟩
      · exact ⟨fun h => (nomatch h), fun _ hp => by
          have := hK.neg p w v h2 hp
          simp_all⟩
      · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .hasValue p (.anon _), w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .hasSelf p, w => by
    rw [ev, Interp.ext]
    dsimp only
    split_ifs with h1 h2
    · exact ⟨fun _ => hK.pos p w w (List.contains_iff_mem.1 h1), fun h => (nomatch h)⟩
    · exact ⟨fun h => (nomatch h), fun _ hp => by
        have := hK.neg p w w h2 hp
        simp_all⟩
    · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .oneOf as, w => by
    rw [ev, Interp.ext]
    obtain ⟨h1, h2⟩ := evOne_sound hK as w
    exact ⟨h1, fun h ⟨a, ha, he⟩ => h2 h a ha he⟩
  | .min .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .max .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .exact .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .dataSome .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .dataAll .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .dataHasValue .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .dataMin .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .dataMax .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .dataExact .., w => by rw [ev]; exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem evAnd_sound (hK : CKSpec K I f) : ∀ (cs : List ClassExpr) (w : Fin k),
    (evAnd K cs w = some true → ∀ c ∈ cs, I.ext c (f w)) ∧
    (evAnd K cs w = some false → ∃ c ∈ cs, ¬ I.ext c (f w))
  | [], w => by rw [evAnd]; exact ⟨fun _ c hc => absurd hc List.not_mem_nil, fun h => (nomatch h)⟩
  | c :: cs, w => by
    rw [evAnd]
    obtain ⟨h1, h2⟩ := ev_sound hK c w
    obtain ⟨h3, h4⟩ := evAnd_sound hK cs w
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨ha, hb⟩ := andV_true h
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact h1 ha
      · exact h3 hb d hd
    · rcases andV_false h with ha | hb
      · exact ⟨c, List.mem_cons_self, h2 ha⟩
      · obtain ⟨d, hd, hn⟩ := h4 hb
        exact ⟨d, List.mem_cons_of_mem _ hd, hn⟩

theorem evOr_sound (hK : CKSpec K I f) : ∀ (cs : List ClassExpr) (w : Fin k),
    (evOr K cs w = some true → ∃ c ∈ cs, I.ext c (f w)) ∧
    (evOr K cs w = some false → ∀ c ∈ cs, ¬ I.ext c (f w))
  | [], w => by rw [evOr]; exact ⟨fun h => (nomatch h), fun _ c hc => absurd hc List.not_mem_nil⟩
  | c :: cs, w => by
    rw [evOr]
    obtain ⟨h1, h2⟩ := ev_sound hK c w
    obtain ⟨h3, h4⟩ := evOr_sound hK cs w
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases orV_true h with ha | hb
      · exact ⟨c, List.mem_cons_self, h1 ha⟩
      · obtain ⟨d, hd, he⟩ := h3 hb
        exact ⟨d, List.mem_cons_of_mem _ hd, he⟩
    · obtain ⟨ha, hb⟩ := orV_false h
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact h2 ha
      · exact h4 hb d hd

end

end Sound

/-! ## Refuting axioms on the core -/

/-- A table of `g` over the core, read back as a function (computed once). -/
def memo {α : Type} (g : Fin k → α) : Fin k → α :=
  let t := Array.ofFn g
  fun w => t[w.val]'(by simp [t])

@[simp] theorem memo_eq {α : Type} (g : Fin k → α) : memo g = g := by
  funext w
  simp [memo]

/-- The core elements reached from `L` along the chain `rs`. -/
def chainF (K : CK k) (L : List (Fin k)) : List ObjProp → List (Fin k)
  | [] => L
  | r :: rs => chainF K (L.flatMap fun u => (K.succ r u).1).eraseDups rs

/-- Some pair of the listed classes shares a core element. -/
def refDisjC (K : CK k) : List ClassExpr → Bool
  | [] => false
  | c :: cs => cs.any (fun d => (List.finRange k).any fun w =>
      ev K c w == some true && ev K d w == some true) || refDisjC K cs

/-- Some pair of the listed properties shares a pair of core elements. -/
def refDisjP (K : CK k) : List ObjProp → Bool
  | [] => false
  | r :: rs => rs.any (fun t => (List.finRange k).any fun w =>
      (K.succ r w).1.any fun v => (K.succ t w).1.contains v) || refDisjP K rs

/-- `r ⊑ t` fails on the core: an `r`-pair that is exactly no `t`-pair. -/
def refSubP (K : CK k) (r t : ObjProp) : Bool :=
  let st := memo (K.succ t)
  (List.finRange k).any fun w => (st w).2 && (K.succ r w).1.any fun v => !(st w).1.contains v

/-- The element of a listed named individual. -/
def indOf (K : CK k) : Individual → Option (Fin k)
  | .named a => K.ind a
  | .anon _ => none

/-- Two listed individuals sit at different core elements. -/
def refSame (K : CK k) (as : List Individual) : Bool :=
  as.any fun a => as.any fun b => match indOf K a, indOf K b with
    | some w, some v => w != v
    | _, _ => false

/-- Some pair of the listed individuals sits at one core element. -/
def refDiff (K : CK k) : List Individual → Bool
  | [] => false
  | a :: as => as.any (fun b => match indOf K a, indOf K b with
      | some w, some v => w == v
      | _, _ => false) || refDiff K as

/-- **The model violates `ax`**, read off the core. -/
def refute (K : CK k) : Axiom → Bool
  | .subClassOf c d => (List.finRange k).any fun w => ev K c w == some true && ev K d w == some false
  | .equivalentClasses cs => cs.any fun c => cs.any fun d =>
      (List.finRange k).any fun w => ev K c w == some true && ev K d w == some false
  | .disjointClasses cs => refDisjC K cs
  | .domain r c => (List.finRange k).any fun w => !(K.succ r w).1.isEmpty && ev K c w == some false
  | .range r c => (List.finRange k).any fun w => (K.succ r w).1.any fun v => ev K c v == some false
  | .subObjectPropertyOf rs t =>
      let st := memo (K.succ t)
      (List.finRange k).any fun w => (st w).2 && (chainF K [w] rs).any fun v => !(st w).1.contains v
  | .equivalentObjectProperties rs => rs.any fun r => rs.any fun t => refSubP K r t
  | .inverseObjectProperties r t =>
      let sr := memo (K.succ r)
      let st := memo (K.succ t)
      (List.finRange k).any fun w => ((sr w).1.any fun v => (st v).2 && !(st v).1.contains w) ||
        ((st w).1.any fun v => (sr v).2 && !(sr v).1.contains w)
  | .transitive r =>
      let sr := memo (K.succ r)
      (List.finRange k).any fun w => (sr w).2 && (sr w).1.any fun u => (sr u).1.any fun v =>
        !(sr w).1.contains v
  | .symmetric r =>
      let sr := memo (K.succ r)
      (List.finRange k).any fun w => (sr w).1.any fun v => (sr v).2 && !(sr v).1.contains w
  | .disjointObjectProperties rs => refDisjP K rs
  | .functional r => (List.finRange k).any fun w =>
      let L := (K.succ r w).1
      L.any fun v1 => L.any fun v2 => v1 != v2
  | .inverseFunctional r =>
      let sr := memo (K.succ r)
      (List.finRange k).any fun w1 => (List.finRange k).any fun w2 =>
        w1 != w2 && (sr w1).1.any fun y => (sr w2).1.contains y
  | .reflexive r => (List.finRange k).any fun w => (K.succ r w).2 && !(K.succ r w).1.contains w
  | .irreflexive r => (List.finRange k).any fun w => (K.succ r w).1.contains w
  | .asymmetric r =>
      let sr := memo (K.succ r)
      (List.finRange k).any fun w => (sr w).1.any fun v => (sr v).1.contains w
  | .sameIndividual as => refSame K as
  | .differentIndividuals as => refDiff K as
  | .classAssertion c a => match indOf K a with
    | some w => ev K c w == some false
    | none => false
  | .objectPropertyAssertion r a b => match indOf K a, indOf K b with
    | some w, some v => (K.succ r w).2 && !(K.succ r w).1.contains v
    | _, _ => false
  | .negativeObjectPropertyAssertion r a b => match indOf K a, indOf K b with
    | some w, some v => (K.succ r w).1.contains v
    | _, _ => false
  | _ => false

section RefuteSound

variable {DM : DatatypeMap} {Dom : Type} {K : CK k} {I : Interp DM Dom} {f : Fin k → Dom}

theorem indOf_spec (hK : CKSpec K I f) {a : Individual} {w : Fin k} (h : indOf K a = some w) :
    I.ind a = f w := by
  cases a with
  | named a => exact hK.ind a w h
  | anon _ => cases h

theorem chainF_sound (hK : CKSpec K I f) : ∀ (rs : List ObjProp) (L : List (Fin k)) (v : Fin k),
    v ∈ chainF K L rs → ∃ u ∈ L, I.chain rs (f u) (f v)
  | [], L, v, h => ⟨v, h, rfl⟩
  | r :: rs, L, v, h => by
    obtain ⟨u, hu, hc⟩ := chainF_sound hK rs _ v h
    obtain ⟨u0, hu0, hu'⟩ := List.mem_flatMap.1 (List.mem_eraseDups.1 hu)
    exact ⟨u0, hu0, ⟨f u, hK.pos r u0 u hu', hc⟩⟩

theorem refDisjC_sound (hK : CKSpec K I f) : ∀ (cs : List ClassExpr), refDisjC K cs = true →
    ¬ cs.Pairwise fun c d => ∀ x, ¬ (I.ext c x ∧ I.ext d x)
  | [], h, _ => by cases h
  | c :: cs, h, hp => by
    rw [refDisjC, Bool.or_eq_true] at h
    rw [List.pairwise_cons] at hp
    rcases h with h | h
    · obtain ⟨d, hd, h⟩ := List.any_eq_true.1 h
      obtain ⟨w, -, h⟩ := List.any_eq_true.1 h
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
      exact hp.1 d hd (f w) ⟨(ev_sound hK c w).1 h.1, (ev_sound hK d w).1 h.2⟩
    · exact refDisjC_sound hK cs h hp.2

theorem refDisjP_sound (hK : CKSpec K I f) : ∀ (rs : List ObjProp), refDisjP K rs = true →
    ¬ rs.Pairwise fun r s => ∀ x y, ¬ (I.prop r x y ∧ I.prop s x y)
  | [], h, _ => by cases h
  | r :: rs, h, hp => by
    rw [refDisjP, Bool.or_eq_true] at h
    rw [List.pairwise_cons] at hp
    rcases h with h | h
    · obtain ⟨t, ht, h⟩ := List.any_eq_true.1 h
      obtain ⟨w, -, h⟩ := List.any_eq_true.1 h
      obtain ⟨v, hv, h⟩ := List.any_eq_true.1 h
      exact hp.1 t ht (f w) (f v) ⟨hK.pos r w v hv, hK.pos t w v (List.contains_iff_mem.1 h)⟩
    · exact refDisjP_sound hK rs h hp.2

theorem refSubP_sound (hK : CKSpec K I f) {r t : ObjProp} (h : refSubP K r t = true) :
    ¬ ∀ x y, I.prop r x y → I.prop t x y := by
  intro hall
  simp only [refSubP, memo_eq, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
  obtain ⟨w, -, hex, v, hv, hn⟩ := h
  exact hn (hK.neg t w v hex (hall _ _ (hK.pos r w v hv)))

theorem refDiff_sound (hK : CKSpec K I f) : ∀ (as : List Individual), refDiff K as = true →
    ¬ as.Pairwise fun a b => I.ind a ≠ I.ind b
  | [], h, _ => by cases h
  | a :: as, h, hp => by
    rw [refDiff, Bool.or_eq_true] at h
    rw [List.pairwise_cons] at hp
    rcases h with h | h
    · obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
      split at h
      next w v ha hb' =>
        rw [beq_iff_eq] at h
        subst h
        exact hp.1 b hb ((indOf_spec hK ha).trans (indOf_spec hK hb').symm)
      next => cases h
    · exact refDiff_sound hK as h hp.2

/-- **Soundness of the refutation**: the model does not satisfy `ax`. -/
theorem refute_sound (hK : CKSpec K I f) (N : List IRI) (ax : Axiom) (h : refute K ax = true) :
    ¬ I.sat N ax := by
  cases ax with
  | subClassOf c d =>
    simp only [refute, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨w, -, h1, h2⟩ := h
    exact fun hs => (ev_sound hK d w).2 h2 (hs _ ((ev_sound hK c w).1 h1))
  | equivalentClasses cs =>
    simp only [refute, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨c, hc, d, hd, w, -, h1, h2⟩ := h
    exact fun hs => (ev_sound hK d w).2 h2 (hs c hc d hd _ ((ev_sound hK c w).1 h1))
  | disjointClasses cs => exact refDisjC_sound hK cs h
  | domain r c =>
    simp only [refute, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.isEmpty_eq_false_iff] at h
    obtain ⟨w, -, hne, h2⟩ := h
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
    exact fun hs => (ev_sound hK c w).2 h2 (hs _ _ (hK.pos r w v hv))
  | range r c =>
    simp only [refute, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨w, -, v, hv, h2⟩ := h
    exact fun hs => (ev_sound hK c v).2 h2 (hs _ _ (hK.pos r w v hv))
  | subObjectPropertyOf rs t =>
    simp only [refute, memo_eq, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨w, -, hex, v, hv, hn⟩ := h
    obtain ⟨u, hu, hc⟩ := chainF_sound hK rs [w] v hv
    rw [List.mem_singleton.1 hu] at hc
    exact fun hs => hn (hK.neg t w v hex (hs _ _ hc))
  | equivalentObjectProperties rs =>
    simp only [refute, List.any_eq_true] at h
    obtain ⟨r, hr, t, ht, h⟩ := h
    exact fun hs => refSubP_sound hK h (hs r hr t ht)
  | inverseObjectProperties r t =>
    simp only [refute, memo_eq, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨w, -, ⟨v, hv, hex, hn⟩ | ⟨v, hv, hex, hn⟩⟩ := h
    · exact fun hs => hn (hK.neg t v w hex ((hs _ _).1 (hK.pos r w v hv)))
    · exact fun hs => hn (hK.neg r v w hex ((hs _ _).2 (hK.pos t w v hv)))
  | transitive r =>
    simp only [refute, memo_eq, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨w, -, hex, u, hu, v, hv, hn⟩ := h
    exact fun hs => hn (hK.neg r w v hex (hs _ _ _ (hK.pos r w u hu) (hK.pos r u v hv)))
  | symmetric r =>
    simp only [refute, memo_eq, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨w, -, v, hv, hex, hn⟩ := h
    exact fun hs => hn (hK.neg r v w hex (hs _ _ (hK.pos r w v hv)))
  | disjointObjectProperties rs => exact refDisjP_sound hK rs h
  | functional r =>
    simp only [refute, List.any_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨w, -, v1, h1, v2, h2, hne⟩ := h
    exact fun hs => hne (hK.inj (hs _ _ _ (hK.pos r w v1 h1) (hK.pos r w v2 h2)))
  | inverseFunctional r =>
    simp only [refute, memo_eq, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      List.contains_eq_mem, decide_eq_true_eq] at h
    obtain ⟨w1, -, w2, -, hne, y, h1, h2⟩ := h
    exact fun hs => hne (hK.inj (hs _ _ _ (hK.pos r w1 y h1) (hK.pos r w2 y h2)))
  | reflexive r =>
    simp only [refute, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨w, -, hex, hn⟩ := h
    exact fun hs => hn (hK.neg r w w hex (hs _))
  | irreflexive r =>
    simp only [refute, List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
    obtain ⟨w, -, hw⟩ := h
    exact fun hs => hs _ (hK.pos r w w hw)
  | asymmetric r =>
    simp only [refute, memo_eq, List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
    obtain ⟨w, -, v, hv, hw⟩ := h
    exact fun hs => hs _ _ (hK.pos r w v hv) (hK.pos r v w hw)
  | sameIndividual as =>
    simp only [refute, refSame, List.any_eq_true] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    split at h
    next w v h1 h2 =>
      rw [bne_iff_ne] at h
      exact fun hs => h (hK.inj ((indOf_spec hK h1).symm.trans ((hs a ha b hb).trans (indOf_spec hK h2))))
    next => cases h
  | differentIndividuals as => exact refDiff_sound hK as h
  | classAssertion c a =>
    simp only [refute] at h
    split at h
    next w hw =>
      rw [beq_iff_eq] at h
      intro hs
      simp only [Interp.sat] at hs
      rw [indOf_spec hK hw] at hs
      exact (ev_sound hK c w).2 h hs
    next => cases h
  | objectPropertyAssertion r a b =>
    simp only [refute] at h
    split at h
    next w v h1 h2 =>
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
        decide_eq_false_iff_not] at h
      intro hs
      simp only [Interp.sat] at hs
      rw [indOf_spec hK h1, indOf_spec hK h2] at hs
      exact h.2 (hK.neg r w v h.1 hs)
    next => cases h
  | negativeObjectPropertyAssertion r a b =>
    simp only [refute] at h
    split at h
    next w v h1 h2 =>
      simp only [List.contains_eq_mem, decide_eq_true_eq] at h
      intro hs
      simp only [Interp.sat] at hs
      rw [indOf_spec hK h1, indOf_spec hK h2] at hs
      exact hs (hK.pos r w v h)
    next => cases h
  | _ => simp [refute] at h

end RefuteSound

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.ev_sound
#print axioms ContextCalculus.OWLFrontend.refute_sound

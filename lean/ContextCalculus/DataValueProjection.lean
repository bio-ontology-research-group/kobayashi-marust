import ContextCalculus.TwoSortedDL
import ContextCalculus.LinearValueEncoding

/-!
# Object-level projection of data assertions (`docs/DATATYPES.md`)

`engine/src/frontend/value_projection.rs` removes every assertion `u(a, v)` of
an admitted group `G` of data properties and adds, on `a`,

* `D` for every domain `∃q.⊤ ⊑ D` of a super-property `q` of `u`, and
* for every counted slot `s = (C, q, F)` (an axiom `C ⊑ ≤ 1 q.F`, functionality
  being `C = ⊤`, `F = ⊤`) with `u ⊑* q` and `v ∈ F`, the binary index digits of
  the identity class of `v` in `s` as fresh classes, with
  `C ⊓ digit(s,p,0) ⊓ digit(s,p,1) ⊑ ⊥` for every position `p`.

The admitted groups are those whose every axiom has one of the shapes
functionality / `C ⊑ ≤ 1 q.F` / domain / atomic range / sub-property, with no
`G` role inside `C` or the domain class, and whose every asserted literal has
decided memberships (and an identity key where it is counted).

This file proves the two directions over the two-sorted semantics of
`TwoSortedDL`, for any data domain and any interpretation of the data concept
names in which the asserted value names are singletons `{lit v}` and the
oracle's membership and key decisions are sound:

* `projection_sound` (`O ⇒ O'`): every model of `O` extends, by interpreting
  the digit classes, to a model of `O'` with the same interpretation of every
  source symbol;
* `projection_complete` (`O' ⇒ O`): every model of `O'` yields, by edge
  surgery on the `G` edges of asserted subjects, a model of `O` with the same
  objects, classes, object properties, individuals and non-`G` data
  properties.

The gate is the decidable `projGate`; `projGate_spec` turns it into the
semantic facts the proofs use. Fresh digit classes are modelled by the class
type `Cls ⊕ Digit`. The Rust generator (that it emits exactly `Proj`) and the
oracle decisions (`memb`, `key`) are not proved here.
-/

set_option linter.unusedSectionVars false

namespace ContextCalculus.DataValueProjection
open ContextCalculus.TwoSortedDL

variable {Cls OR DR Ind DN K : Type}
variable [DecidableEq Cls] [DecidableEq OR] [DecidableEq DR] [DecidableEq Ind] [DecidableEq DN]

/-! ## Syntax: groups, shapes, slots -/

section Syntax
variable (inG : DR → Bool)

/-- A class expression mentions a role of `G`. -/
def mentionsG : Concept Cls OR DR Ind DN → Bool
  | .not c => mentionsG c
  | .and c d => mentionsG c || mentionsG d
  | .or c d => mentionsG c || mentionsG d
  | .oex _ c => mentionsG c
  | .oall _ c => mentionsG c
  | .oge _ _ c => mentionsG c
  | .ole _ _ c => mentionsG c
  | .dex u _ => inG u
  | .dall u _ => inG u
  | .dge _ u _ => inG u
  | .dle _ u _ => inG u
  | _ => false

def axMentionsG : Axiom Cls OR DR Ind DN → Bool
  | .sub c d => mentionsG inG c || mentionsG inG d
  | .cassert c _ => mentionsG inG c
  | .dassert u _ _ => inG u
  | .dsub u w => inG u || inG w
  | .ddisj u w => inG u || inG w
  | _ => false

end Syntax

/-- `∃q.⊤ ⊑ D` (a data-property domain). -/
def isDomain : Axiom Cls OR DR Ind DN → Option (DR × Concept Cls OR DR Ind DN)
  | .sub (.dex q .top) D => some (q, D)
  | _ => none

/-- `⊤ ⊑ ∀q.R` with `R` a data concept name (an atomic data-property range). -/
def isRange : Axiom Cls OR DR Ind DN → Option (DR × DN)
  | .sub .top (.dall q (.name R)) => some (q, R)
  | _ => none

/-- A counted slot: `C ⊑ ≤ 1 q.F`. -/
structure Slot (Cls OR DR Ind DN : Type) where
  guard : Concept Cls OR DR Ind DN
  role : DR
  filler : DRange DN
  deriving DecidableEq

def isAtMostOne : Axiom Cls OR DR Ind DN → Option (Slot Cls OR DR Ind DN)
  | .sub C (.dle n q F) => if n = 1 then some ⟨C, q, F⟩ else none
  | _ => none

theorem isDomain_eq {ax : Axiom Cls OR DR Ind DN} {q D} (h : isDomain ax = some (q, D)) :
    ax = .sub (.dex q .top) D := by
  unfold isDomain at h
  split at h
  · cases h; rfl
  · cases h

theorem isRange_eq {ax : Axiom Cls OR DR Ind DN} {q R} (h : isRange ax = some (q, R)) :
    ax = .sub .top (.dall q (.name R)) := by
  unfold isRange at h
  split at h
  · cases h; rfl
  · cases h

theorem isAtMostOne_eq {ax : Axiom Cls OR DR Ind DN} {s} (h : isAtMostOne ax = some s) :
    ax = .sub s.guard (.dle 1 s.role s.filler) := by
  unfold isAtMostOne at h
  split at h
  · next C n q F =>
    split at h
    · next hn => cases h; subst hn; rfl
    · cases h
  · cases h

section Gate
variable (inG : DR → Bool)

/-- The shapes the projection admits for an axiom mentioning `G`; every other
axiom must not mention `G`. -/
def allowed (ax : Axiom Cls OR DR Ind DN) : Bool :=
  !(axMentionsG inG ax) ||
  (match isDomain ax with | some (_, D) => !(mentionsG inG D) | none => false) ||
  (isRange ax).isSome ||
  (match isAtMostOne ax with | some s => !(mentionsG inG s.guard) | none => false) ||
  (match ax with
    | .dsub p q => inG p == inG q
    | .dassert _ _ _ => true
    | _ => false)

/-- The asserted data edges of `G`. -/
def gAssertions (O : List (Axiom Cls OR DR Ind DN)) : List (DR × Ind × DN) :=
  O.filterMap fun
    | .dassert u a v => if inG u then some (u, a, v) else none
    | _ => none

def isGAssertion : Axiom Cls OR DR Ind DN → Bool
  | .dassert u _ _ => inG u
  | _ => false

/-- A certificate that every listed role is a super-property of `u`: each is
`u` or a direct super-property of an earlier one. -/
def supCert (O : List (Axiom Cls OR DR Ind DN)) (u : DR) : List DR → List DR → Bool
  | _, [] => true
  | seen, q :: rest =>
    (q == u || seen.any (fun p => O.contains (.dsub p q))) && supCert O u (q :: seen) rest

/-- `v` fits the filler `F` of a slot by the oracle's decision. -/
def fits (memb : DN → DN → Option Bool) (v : DN) : DRange DN → Bool
  | .top => true
  | .name R => memb R v == some true

/-- The oracle decides what the projection needs for the literal `v` under
the super-property `q`: membership in every range of `q`, and for every slot
of `q` either non-membership or membership with an identity key. -/
def literalDecided (O : List (Axiom Cls OR DR Ind DN)) (memb : DN → DN → Option Bool)
    (key : DN → Option K) (q : DR) (v : DN) : Bool :=
  O.all fun ax =>
    (match isRange ax with
      | some (q', R) => !(q' == q) || memb R v == some true
      | none => true) &&
    (match isAtMostOne ax with
      | some s => !(s.role == q) ||
          (match s.filler with
            | .top => (key v).isSome
            | .name R => memb R v == some false || (memb R v == some true && (key v).isSome))
      | none => true)

/-- The projection gate, a decidable predicate on the source and the
certificates `sup`. -/
def projGate (O : List (Axiom Cls OR DR Ind DN)) (sup : DR → List DR)
    (memb : DN → DN → Option Bool) (key : DN → Option K) : Bool :=
  O.all (allowed inG) &&
  (gAssertions inG O).all fun (u, _, v) =>
    (sup u).contains u && supCert O u [] (sup u) &&
    (sup u).all (fun p => O.all fun
      | .dsub p' q => !(p' == p) || (sup u).contains q
      | _ => true) &&
    (sup u).all (fun q => literalDecided O memb key q v)

end Gate

/-! ## The projected ontology -/

/-- Digit class `(slot, position, bit)`. -/
abbrev Digit (Cls OR DR Ind DN : Type) := Slot Cls OR DR Ind DN × Nat × Bool

section Projection
variable (inG : DR → Bool) (O : List (Axiom Cls OR DR Ind DN)) (sup : DR → List DR)
  (memb : DN → DN → Option Bool) (key : DN → Option K)
  (idx : Slot Cls OR DR Ind DN → K → Nat) (npos : Slot Cls OR DR Ind DN → Nat)

open ContextCalculus.LinearValueEncoding (binaryIndex)

def digitAtom (s : Slot Cls OR DR Ind DN) (p : Nat) (b : Bool) :
    Concept (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN :=
  .atom (.inr (s, p, b))

/-- The axioms of `O'`. -/
inductive Proj : Axiom (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN → Prop where
  /-- every axiom of `O` other than an assertion of `G` -/
  | kept (ax) : ax ∈ O → isGAssertion inG ax = false → Proj (ax.mapCls .inl)
  /-- the domains of the super-properties of an asserted property -/
  | domain (u a v q D ax) : (u, a, v) ∈ gAssertions inG O → q ∈ sup u → ax ∈ O →
      isDomain ax = some (q, D) → Proj (.cassert (D.mapCls .inl) a)
  /-- the index digits of an asserted value in every slot it fits -/
  | digit (u a v s k p) : (u, a, v) ∈ gAssertions inG O → s.role ∈ sup u →
      (∃ ax ∈ O, isAtMostOne ax = some s) → fits memb v s.filler = true → key v = some k →
      p < npos s → Proj (.cassert (digitAtom s p (binaryIndex (idx s k) p)) a)
  /-- the clash of the two digits of one position under the slot's guard -/
  | clash (s p) : (∃ ax ∈ O, isAtMostOne ax = some s) → p < npos s →
      Proj (.sub (.and (s.guard.mapCls .inl) (.and (digitAtom s p false) (digitAtom s p true))) .bot)

end Projection

/-! ## Semantic side conditions -/

/-- Asserted value names are singletons `{lit v}`. -/
def ValuesSingleton {Dat : Type} (dcon : DN → Dat → Prop) (lit : DN → Dat) (vals : DN → Prop) : Prop :=
  ∀ v, vals v → ∀ y, dcon v y ↔ y = lit v

/-- The membership decisions are sound for asserted values. -/
def MembSound {Dat : Type} (dcon : DN → Dat → Prop) (lit : DN → Dat)
    (memb : DN → DN → Option Bool) : Prop :=
  ∀ R v b, memb R v = some b → (dcon R (lit v) ↔ b = true)

/-- Identity keys are sound: two keyed values are equal iff their keys are. -/
def KeySound {Dat : Type} (lit : DN → Dat) (key : DN → Option K) : Prop :=
  ∀ v w k l, key v = some k → key w = some l → (k = l ↔ lit v = lit w)

/-- The index separates the keys of every slot on its positions (the Rust
index numbers the identity classes `0 … m-1` and uses `⌈log₂ m⌉` positions;
`indexSeparates_of_injective` derives this from injectivity and the bound). -/
def IndexSeparates (idx : Slot Cls OR DR Ind DN → K → Nat) (npos : Slot Cls OR DR Ind DN → Nat)
    (relevant : Slot Cls OR DR Ind DN → K → Prop) : Prop :=
  ∀ s k l, relevant s k → relevant s l → k ≠ l →
    ∃ p, p < npos s ∧ LinearValueEncoding.binaryIndex (idx s k) p ≠
      LinearValueEncoding.binaryIndex (idx s l) p

theorem indexSeparates_of_injective (idx : Slot Cls OR DR Ind DN → K → Nat)
    (npos : Slot Cls OR DR Ind DN → Nat) (relevant : Slot Cls OR DR Ind DN → K → Prop)
    (hinj : ∀ s k l, relevant s k → relevant s l → idx s k = idx s l → k = l)
    (hbound : ∀ s k, relevant s k → idx s k < 2 ^ npos s) :
    IndexSeparates idx npos relevant := by
  intro s k l hk hl hne
  exact LinearValueEncoding.binaryIndex_separating (npos s) _ _ (hbound s k hk) (hbound s l hl)
    (fun h => hne (hinj s k l hk hl h))

/-! ## Reachability along sub-properties -/

inductive Reach (O : List (Axiom Cls OR DR Ind DN)) (u : DR) : DR → Prop where
  | refl : Reach O u u
  | step {p q} : Reach O u p → .dsub p q ∈ O → Reach O u q

theorem supCert_sound (O : List (Axiom Cls OR DR Ind DN)) (u : DR) :
    ∀ (l seen : List DR), supCert O u seen l = true → (∀ p ∈ seen, Reach O u p) →
      ∀ q ∈ l, Reach O u q := by
  intro l
  induction l with
  | nil => intro _ _ _ q hq; cases hq
  | cons q rest ih =>
    intro seen h hseen
    simp only [supCert, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
      List.contains_iff_mem] at h
    have hq : Reach O u q := by
      rcases h.1 with h1 | ⟨p, hp, hsub⟩
      · subst h1; exact Reach.refl
      · exact Reach.step (hseen p hp) hsub
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hq
    · exact ih (q :: seen) h.2 (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hq
        · exact hseen p hp) r hr

theorem Reach.edge {Obj Dat : Type} {O : List (Axiom Cls OR DR Ind DN)}
    {I : Interp Cls OR DR Ind DN Obj Dat} (hI : Models I O) {u q : DR} (h : Reach O u q) :
    ∀ x y, I.drole u x y → I.drole q x y := by
  induction h with
  | refl => exact fun _ _ h => h
  | step _ hsub ih => exact fun x y h => hI _ hsub x y (ih x y h)

/-! ## What the gate gives -/

section GateSpec
variable {inG : DR → Bool} {O : List (Axiom Cls OR DR Ind DN)} {sup : DR → List DR}
  {memb : DN → DN → Option Bool} {key : DN → Option K}

theorem mem_gAssertions {u a v} :
    (u, a, v) ∈ gAssertions inG O ↔ (Axiom.dassert u a v ∈ O ∧ inG u = true) := by
  unfold gAssertions
  simp only [List.mem_filterMap]
  constructor
  · intro ⟨ax, hax, h⟩
    cases ax with
    | dassert u' a' v' =>
      simp only at h
      split at h
      · next hg => cases h; exact ⟨hax, hg⟩
      · cases h
    | _ => simp at h
  · intro ⟨hax, hg⟩
    exact ⟨_, hax, by simp [hg]⟩

/-- The semantic content of the gate. -/
structure GateFacts (inG : DR → Bool) (O : List (Axiom Cls OR DR Ind DN)) (sup : DR → List DR)
    (memb : DN → DN → Option Bool) (key : DN → Option K) : Prop where
  allowed : ∀ ax ∈ O, allowed inG ax = true
  self : ∀ u a v, (u, a, v) ∈ gAssertions inG O → u ∈ sup u
  reach : ∀ u a v, (u, a, v) ∈ gAssertions inG O → ∀ q ∈ sup u, Reach O u q
  closed : ∀ u a v, (u, a, v) ∈ gAssertions inG O → ∀ p ∈ sup u, ∀ q, .dsub p q ∈ O → q ∈ sup u
  range : ∀ u a v, (u, a, v) ∈ gAssertions inG O → ∀ q ∈ sup u, ∀ ax ∈ O, ∀ R,
    isRange ax = some (q, R) → memb R v = some true
  slot : ∀ u a v, (u, a, v) ∈ gAssertions inG O → ∀ q ∈ sup u, ∀ ax ∈ O, ∀ s,
    isAtMostOne ax = some s → s.role = q →
      (match s.filler with
        | .top => (key v).isSome = true
        | .name R => memb R v = some false ∨ (memb R v = some true ∧ (key v).isSome = true))

theorem projGate_spec (h : projGate inG O sup memb key = true) : GateFacts inG O sup memb key := by
  unfold projGate at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, hA⟩ := h
  have hA' := fun u a v (m : (u, a, v) ∈ gAssertions inG O) => hA (u, a, v) m
  refine ⟨hall, ?_, ?_, ?_, ?_, ?_⟩
  · intro u a v m
    have := (hA' u a v m).1.1.1
    simpa using this
  · intro u a v m q hq
    exact supCert_sound O u (sup u) [] (hA' u a v m).1.1.2 (by intro p hp; cases hp) q hq
  · intro u a v m p hp q hsub
    have := (hA' u a v m).1.2 p hp _ hsub
    simpa using this
  · intro u a v m q hq ax hax R hr
    have := (hA' u a v m).2 q hq
    unfold literalDecided at this
    simp only [List.all_eq_true, Bool.and_eq_true] at this
    have h1 := (this ax hax).1
    rw [hr] at h1
    simpa using h1
  · intro u a v m q hq ax hax s hs hrole
    have := (hA' u a v m).2 q hq
    unfold literalDecided at this
    simp only [List.all_eq_true, Bool.and_eq_true] at this
    have h2 := (this ax hax).2
    rw [hs] at h2
    subst hrole
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or] at h2
    cases hf : s.filler with
    | top => rw [hf] at h2; simpa using h2
    | name R =>
      rw [hf] at h2
      simpa using h2

/-- Every role reachable from an asserted role of `G` is in `G`. -/
theorem reach_inG (hf : GateFacts inG O sup memb key) {u q : DR} (hu : inG u = true)
    (h : Reach O u q) : inG q = true := by
  induction h with
  | refl => exact hu
  | step _ hsub ih =>
    have hal := hf.allowed _ hsub
    simp only [allowed, axMentionsG, isDomain, isRange, isAtMostOne, ih, Bool.true_or,
      Bool.not_true, Bool.false_or, Option.isSome_none, beq_iff_eq] at hal
    exact hal.symm

end GateSpec

/-! ## Evaluation away from `G` -/

section Agree
variable {Obj Dat : Type}

/-- Two interpretations that agree on classes, object roles, individuals,
data labels and every data role outside `G` agree on every class expression
that mentions no `G` role. -/
theorem eval_agree (inG : DR → Bool) (I J : Interp Cls OR DR Ind DN Obj Dat)
    (hc : I.cls = J.cls) (ho : I.orole = J.orole) (hi : I.ind = J.ind) (hd : I.dcon = J.dcon)
    (hr : ∀ r, inG r = false → I.drole r = J.drole r) :
    ∀ C : Concept Cls OR DR Ind DN, mentionsG inG C = false → ∀ x, eval I C x ↔ eval J C x := by
  have hR : ∀ (R : DRange DN) y, evalR I R y ↔ evalR J R y := by
    intro R y; cases R <;> simp [evalR, hd]
  intro C
  induction C with
  | top => intro _ x; exact Iff.rfl
  | bot => intro _ x; exact Iff.rfl
  | atom a => intro _ x; simp [eval, hc]
  | nominal i => intro _ x; simp [eval, hi]
  | oself r => intro _ x; simp [eval, ho]
  | not c ih => intro h x; exact not_congr (ih h x)
  | and c d ihc ihd =>
    intro h x
    simp only [mentionsG, Bool.or_eq_false_iff] at h
    exact and_congr (ihc h.1 x) (ihd h.2 x)
  | or c d ihc ihd =>
    intro h x
    simp only [mentionsG, Bool.or_eq_false_iff] at h
    exact or_congr (ihc h.1 x) (ihd h.2 x)
  | oex r c ih =>
    intro h x
    simp only [eval, ho]
    exact exists_congr fun y => and_congr Iff.rfl (ih h y)
  | oall r c ih =>
    intro h x
    simp only [eval, ho]
    exact forall_congr' fun y => imp_congr Iff.rfl (ih h y)
  | oge n r c ih =>
    intro h x
    simp only [eval, ho]
    exact ⟨AtLeast.mono (fun y hy => ⟨hy.1, (ih h y).1 hy.2⟩),
      AtLeast.mono (fun y hy => ⟨hy.1, (ih h y).2 hy.2⟩)⟩
  | ole n r c ih =>
    intro h x
    simp only [eval, ho]
    exact not_congr ⟨AtLeast.mono (fun y hy => ⟨hy.1, (ih h y).1 hy.2⟩),
      AtLeast.mono (fun y hy => ⟨hy.1, (ih h y).2 hy.2⟩)⟩
  | dex u R =>
    intro h x
    simp only [mentionsG] at h
    simp only [eval, hr u h]
    exact exists_congr fun y => and_congr Iff.rfl (hR R y)
  | dall u R =>
    intro h x
    simp only [mentionsG] at h
    simp only [eval, hr u h]
    exact forall_congr' fun y => imp_congr Iff.rfl (hR R y)
  | dge n u R =>
    intro h x
    simp only [mentionsG] at h
    simp only [eval, hr u h]
    exact ⟨AtLeast.mono (fun y hy => ⟨hy.1, (hR R y).1 hy.2⟩),
      AtLeast.mono (fun y hy => ⟨hy.1, (hR R y).2 hy.2⟩)⟩
  | dle n u R =>
    intro h x
    simp only [mentionsG] at h
    simp only [eval, hr u h]
    exact not_congr ⟨AtLeast.mono (fun y hy => ⟨hy.1, (hR R y).1 hy.2⟩),
      AtLeast.mono (fun y hy => ⟨hy.1, (hR R y).2 hy.2⟩)⟩

theorem sat_agree (inG : DR → Bool) (I J : Interp Cls OR DR Ind DN Obj Dat)
    (hc : I.cls = J.cls) (ho : I.orole = J.orole) (hi : I.ind = J.ind) (hd : I.dcon = J.dcon)
    (hr : ∀ r, inG r = false → I.drole r = J.drole r) :
    ∀ ax : Axiom Cls OR DR Ind DN, axMentionsG inG ax = false → (sat I ax ↔ sat J ax) := by
  intro ax h
  have he := eval_agree inG I J hc ho hi hd hr
  cases ax with
  | sub c d =>
    simp only [axMentionsG, Bool.or_eq_false_iff] at h
    exact forall_congr' fun x => imp_congr (he c h.1 x) (he d h.2 x)
  | cassert c a =>
    simp only [axMentionsG] at h
    simp only [sat, hi]
    exact he c h _
  | oassert r a b => simp [sat, ho, hi]
  | dassert u a v =>
    simp only [axMentionsG] at h
    simp [sat, hr u h, hi, hd]
  | osub r s => simp [sat, ho]
  | dsub u w =>
    simp only [axMentionsG, Bool.or_eq_false_iff] at h
    simp [sat, hr u h.1, hr w h.2]
  | ddisj u w =>
    simp only [axMentionsG, Bool.or_eq_false_iff] at h
    simp [sat, hr u h.1, hr w h.2]
  | same a b => simp [sat, hi]
  | diff a b => simp [sat, hi]

end Agree

/-! ## `O ⇒ O'` -/

section Sound
variable {Obj Dat : Type}
variable (inG : DR → Bool) (O : List (Axiom Cls OR DR Ind DN)) (sup : DR → List DR)
  (memb : DN → DN → Option Bool) (key : DN → Option K)
  (idx : Slot Cls OR DR Ind DN → K → Nat) (npos : Slot Cls OR DR Ind DN → Nat)
  (lit : DN → Dat)

open ContextCalculus.LinearValueEncoding (binaryIndex)

/-- The digit classes read off a model of `O`: the elements with a `q`-value
in `F` that is an asserted value of `G` whose index has bit `b` at `p`. -/
def digitExt (I : Interp Cls OR DR Ind DN Obj Dat) (s : Slot Cls OR DR Ind DN) (p : Nat)
    (b : Bool) (x : Obj) : Prop :=
  ∃ v k, (∃ u a, (u, a, v) ∈ gAssertions inG O) ∧ key v = some k ∧
    binaryIndex (idx s k) p = b ∧ I.drole s.role x (lit v) ∧ evalR I s.filler (lit v)

def extend (I : Interp Cls OR DR Ind DN Obj Dat) :
    Interp (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN Obj Dat :=
  { I with cls := fun
      | .inl c => I.cls c
      | .inr (s, p, b) => digitExt inG O key idx lit I s p b }

theorem comap_extend (I : Interp Cls OR DR Ind DN Obj Dat) :
    (extend inG O key idx lit I).comapCls .inl = I := rfl

/-- **Projection, `O ⇒ O'`.** -/
theorem projection_sound (hg : projGate inG O sup memb key = true)
    (I : Interp Cls OR DR Ind DN Obj Dat)
    (hvals : ValuesSingleton I.dcon lit (fun v => ∃ u a, (u, a, v) ∈ gAssertions inG O))
    (hmemb : MembSound I.dcon lit memb) (hkey : KeySound lit key)
    (hI : Models I O) :
    (∀ ax, Proj inG O sup memb key idx npos ax → sat (extend inG O key idx lit I) ax) ∧
    (extend inG O key idx lit I).comapCls .inl = I := by
  have hf := projGate_spec hg
  refine ⟨?_, rfl⟩
  -- the asserted edge of every assertion of `G`, along every super-property
  have edge : ∀ u a v, (u, a, v) ∈ gAssertions inG O → ∀ q ∈ sup u,
      I.drole q (I.ind a) (lit v) := by
    intro u a v m q hq
    have hax := (mem_gAssertions.1 m).1
    obtain ⟨y, hy, hv⟩ := hI _ hax
    have := (hvals v ⟨u, a, m⟩ y).1 hv
    subst this
    exact Reach.edge hI (hf.reach u a v m q hq) _ _ hy
  intro ax hp
  cases hp with
  | kept ax hax _ =>
    rw [sat_mapCls, comap_extend]
    exact hI ax hax
  | domain u a v q D ax m hq hax hd =>
    show eval _ (D.mapCls Sum.inl) _
    rw [eval_mapCls, comap_extend]
    have hsub := hI ax hax
    rw [isDomain_eq hd] at hsub
    exact hsub _ ⟨lit v, edge u a v m q hq, trivial⟩
  | digit u a v s k p m hq _ hfit hk _ =>
    refine ⟨v, k, ⟨u, a, m⟩, hk, rfl, edge u a v m s.role hq, ?_⟩
    cases hF : s.filler with
    | top => exact trivial
    | name R =>
      rw [hF] at hfit
      simp only [fits, beq_iff_eq] at hfit
      exact (hmemb R v true hfit).2 rfl
  | clash s p hs _ =>
    intro x ⟨hC, h0, h1⟩
    obtain ⟨ax, hax, hs⟩ := hs
    have hat := hI ax hax
    rw [isAtMostOne_eq hs] at hat
    rw [eval_mapCls, comap_extend] at hC
    obtain ⟨v₀, k₀, _, hk₀, hb₀, he₀, hF₀⟩ := h0
    obtain ⟨v₁, k₁, _, hk₁, hb₁, he₁, hF₁⟩ := h1
    have hne : lit v₀ ≠ lit v₁ := by
      intro heq
      have := (hkey v₀ v₁ k₀ k₁ hk₀ hk₁).2 heq
      subst this
      rw [hb₀] at hb₁
      exact Bool.false_ne_true hb₁
    exact hat x hC ((AtLeast.two_iff _).2 ⟨lit v₀, lit v₁, hne, ⟨he₀, hF₀⟩, ⟨he₁, hF₁⟩⟩)

end Sound

/-! ## `O' ⇒ O` -/

section Complete
variable {Obj Dat : Type}
variable (inG : DR → Bool) (O : List (Axiom Cls OR DR Ind DN)) (sup : DR → List DR)
  (memb : DN → DN → Option Bool) (key : DN → Option K)
  (idx : Slot Cls OR DR Ind DN → K → Nat) (npos : Slot Cls OR DR Ind DN → Nat)
  (lit : DN → Dat)

open ContextCalculus.LinearValueEncoding (binaryIndex)

/-- The elements that interpret a subject of an assertion of `G`. -/
def Surgered (J : Interp (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN Obj Dat) (x : Obj) : Prop :=
  ∃ u a v, (u, a, v) ∈ gAssertions inG O ∧ J.ind a = x

/-- Edge surgery: at a surgered element, the `G` edges are exactly the
asserted values along the asserted property's super-properties; everywhere
else the edges of `J` stay. -/
def surgery (J : Interp (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN Obj Dat) :
    Interp Cls OR DR Ind DN Obj Dat :=
  { cls := fun c => J.cls (.inl c), orole := J.orole, ind := J.ind, dcon := J.dcon,
    drole := fun r x y =>
      (inG r = true ∧ Surgered inG O J x ∧
        ∃ u a v, (u, a, v) ∈ gAssertions inG O ∧ J.ind a = x ∧ r ∈ sup u ∧ y = lit v) ∨
      (¬ (inG r = true ∧ Surgered inG O J x) ∧ J.drole r x y) }

/-- Separation, relative to the keys the slot actually indexes. -/
def Relevant (s : Slot Cls OR DR Ind DN) (k : K) : Prop :=
  ∃ u a v, (u, a, v) ∈ gAssertions inG O ∧ s.role ∈ sup u ∧ fits memb v s.filler = true ∧
    key v = some k

/-- **Projection, `O' ⇒ O`.** -/
theorem projection_complete (hg : projGate inG O sup memb key = true)
    (hsep : IndexSeparates idx npos (Relevant inG O sup memb key))
    (J : Interp (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN Obj Dat)
    (hvals : ValuesSingleton J.dcon lit (fun v => ∃ u a, (u, a, v) ∈ gAssertions inG O))
    (hmemb : MembSound J.dcon lit memb) (hkey : KeySound lit key)
    (hJ : ∀ ax, Proj inG O sup memb key idx npos ax → sat J ax) :
    Models (surgery inG O sup lit J) O ∧
    (surgery inG O sup lit J).cls = (J.comapCls Sum.inl).cls ∧
    (surgery inG O sup lit J).orole = J.orole ∧ (surgery inG O sup lit J).ind = J.ind ∧
    (∀ r, inG r = false → (surgery inG O sup lit J).drole r = J.drole r) := by
  have hf := projGate_spec hg
  let S := surgery inG O sup lit J
  let J₀ := J.comapCls (Sum.inl : Cls → Cls ⊕ Digit Cls OR DR Ind DN)
  have hout : ∀ r, inG r = false → S.drole r = J₀.drole r := by
    intro r hr
    funext x y
    apply propext
    simp only [S, J₀, surgery, Interp.comapCls, hr]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · cases h
      · exact h
    · intro h; exact Or.inr ⟨by simp, h⟩
  have hagree := sat_agree inG S J₀ rfl rfl rfl rfl hout
  have hagreeC := eval_agree inG S J₀ rfl rfl rfl rfl hout
  -- the source axioms kept in `O'` hold in `J₀`
  have hkept : ∀ ax ∈ O, isGAssertion inG ax = false → sat J₀ ax := by
    intro ax hax hng
    exact (sat_mapCls _ J ax).1 (hJ _ (Proj.kept ax hax hng))
  -- an edge of the surgery at a surgered element on a `G` role is asserted
  have hsurg : ∀ r x y, S.drole r x y → inG r = true → Surgered inG O J x →
      ∃ u a v, (u, a, v) ∈ gAssertions inG O ∧ J.ind a = x ∧ r ∈ sup u ∧ y = lit v := by
    intro r x y h hr hx
    rcases h with ⟨_, _, h⟩ | ⟨hn, _⟩
    · exact h
    · exact absurd ⟨hr, hx⟩ hn
  -- elsewhere it is an edge of `J`
  have hplain : ∀ r x y, S.drole r x y → ¬ (inG r = true ∧ Surgered inG O J x) →
      J₀.drole r x y := by
    intro r x y h hn
    rcases h with ⟨hr, hx, _⟩ | ⟨_, h⟩
    · exact absurd ⟨hr, hx⟩ hn
    · exact h
  refine ⟨?_, rfl, rfl, rfl, hout⟩
  intro ax hax
  have hal := hf.allowed ax hax
  -- an axiom that mentions no `G` role holds as in `J₀`
  by_cases hm : axMentionsG inG ax = false
  · have hng : isGAssertion inG ax = false := by
      cases ax <;> simp_all [isGAssertion, axMentionsG]
    exact (hagree ax hm).2 (hkept ax hax hng)
  have hm' : axMentionsG inG ax = true := by simpa using hm
  -- otherwise it has one of the admitted shapes
  unfold allowed at hal
  simp only [hm', Bool.not_true, Bool.false_or, Bool.or_eq_true] at hal
  rcases hal with ((hdom | hran) | hat) | hrest
  · -- domain `∃q.⊤ ⊑ D`
    cases hd : isDomain ax with
    | none => rw [hd] at hdom; cases hdom
    | some qD =>
      obtain ⟨q, D⟩ := qD
      rw [hd] at hdom
      simp only [Bool.not_eq_true'] at hdom
      have hax' := isDomain_eq hd
      subst hax'
      intro x ⟨y, hy, _⟩
      by_cases hs : inG q = true ∧ Surgered inG O J x
      · obtain ⟨u, a, v, m, hx, hq, _⟩ := hsurg q x y hy hs.1 hs.2
        have hD := hJ _ (Proj.domain u a v q D _ m hq hax hd)
        change eval J (D.mapCls Sum.inl) (J.ind a) at hD
        rw [eval_mapCls] at hD
        rw [← hx]
        exact (hagreeC D hdom _).2 hD
      · have h0 := hkept _ hax (by simp [isGAssertion])
        exact (hagreeC D hdom x).2 (h0 x ⟨y, hplain q x y hy hs, trivial⟩)
  · -- range `⊤ ⊑ ∀q.R`
    cases hr : isRange ax with
    | none => rw [hr] at hran; cases hran
    | some qR =>
      obtain ⟨q, R⟩ := qR
      have hax' := isRange_eq hr
      subst hax'
      intro x _ y hy
      by_cases hs : inG q = true ∧ Surgered inG O J x
      · obtain ⟨u, a, v, m, _, hq, rfl⟩ := hsurg q x y hy hs.1 hs.2
        exact (hmemb R v true (hf.range u a v m q hq _ hax R hr)).2 rfl
      · exact hkept _ hax (by simp [isGAssertion]) x trivial y (hplain q x y hy hs)
  · -- at most one `C ⊑ ≤ 1 q.F`
    cases hs : isAtMostOne ax with
    | none => rw [hs] at hat; cases hat
    | some s =>
      rw [hs] at hat
      simp only [Bool.not_eq_true'] at hat
      have hax' := isAtMostOne_eq hs
      subst hax'
      intro x hC hc2
      by_cases hsx : inG s.role = true ∧ Surgered inG O J x
      · obtain ⟨y₀, y₁, hne, ⟨he₀, hF₀⟩, ⟨he₁, hF₁⟩⟩ := (AtLeast.two_iff _).1 hc2
        obtain ⟨u₀, a₀, v₀, m₀, hx₀, hq₀, rfl⟩ := hsurg _ x _ he₀ hsx.1 hsx.2
        obtain ⟨u₁, a₁, v₁, m₁, hx₁, hq₁, rfl⟩ := hsurg _ x _ he₁ hsx.1 hsx.2
        -- both values fit the slot and have keys
        have fitkey : ∀ u a v, (u, a, v) ∈ gAssertions inG O → s.role ∈ sup u →
            evalR S s.filler (lit v) → fits memb v s.filler = true ∧ ∃ k, key v = some k := by
          intro u a v m hq hF
          have hsl := hf.slot u a v m s.role hq _ hax s hs rfl
          cases hfl : s.filler with
          | top =>
            rw [hfl] at hsl
            simp only at hsl
            obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hsl
            exact ⟨rfl, k, hk⟩
          | name R =>
            rw [hfl] at hsl hF
            rcases hsl with hno | ⟨hyes, hk⟩
            · exact absurd ((hmemb R v false hno).1 hF) (by decide)
            · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hk
              exact ⟨by simp [fits, hyes], k, hk⟩
        obtain ⟨hfit₀, k₀, hk₀⟩ := fitkey u₀ a₀ v₀ m₀ hq₀ hF₀
        obtain ⟨hfit₁, k₁, hk₁⟩ := fitkey u₁ a₁ v₁ m₁ hq₁ hF₁
        have hkne : k₀ ≠ k₁ := fun h => hne ((hkey v₀ v₁ k₀ k₁ hk₀ hk₁).1 h)
        obtain ⟨p, hp, hbits⟩ := hsep s k₀ k₁ ⟨u₀, a₀, v₀, m₀, hq₀, hfit₀, hk₀⟩
          ⟨u₁, a₁, v₁, m₁, hq₁, hfit₁, hk₁⟩ hkne
        have hslot : ∃ ax ∈ O, isAtMostOne ax = some s := ⟨_, hax, hs⟩
        have hd₀ := hJ _ (Proj.digit u₀ a₀ v₀ s k₀ p m₀ hq₀ hslot hfit₀ hk₀ hp)
        have hd₁ := hJ _ (Proj.digit u₁ a₁ v₁ s k₁ p m₁ hq₁ hslot hfit₁ hk₁ hp)
        have hcl := hJ _ (Proj.clash s p hslot hp)
        change J.cls _ (J.ind a₀) at hd₀
        change J.cls _ (J.ind a₁) at hd₁
        rw [hx₀] at hd₀
        rw [hx₁] at hd₁
        have hCJ : eval J (s.guard.mapCls Sum.inl) x := by
          rw [eval_mapCls]; exact (hagreeC s.guard hat x).1 hC
        apply hcl x
        refine ⟨hCJ, ?_⟩
        cases hb₀ : binaryIndex (idx s k₀) p <;> cases hb₁ : binaryIndex (idx s k₁) p
        · rw [hb₀, hb₁] at hbits; exact absurd rfl hbits
        · rw [hb₀] at hd₀; rw [hb₁] at hd₁; exact ⟨hd₀, hd₁⟩
        · rw [hb₀] at hd₀; rw [hb₁] at hd₁; exact ⟨hd₁, hd₀⟩
        · rw [hb₀, hb₁] at hbits; exact absurd rfl hbits
      · have h0 := hkept _ hax (by simp [isGAssertion])
        apply h0 x ((hagreeC s.guard hat x).1 hC)
        exact AtLeast.mono (fun y hy => ⟨hplain _ x y hy.1 hsx, by
          cases hF : s.filler <;> simp_all [evalR, S, J₀, surgery, Interp.comapCls]⟩) hc2
  · -- sub-property and the assertions themselves
    cases ax with
    | dsub p q =>
      simp only [beq_iff_eq] at hrest
      intro x y hy
      by_cases hs : inG p = true ∧ Surgered inG O J x
      · obtain ⟨u, a, v, m, hx, hp, hy'⟩ := hsurg p x y hy hs.1 hs.2
        refine Or.inl ⟨hrest ▸ hs.1, hs.2, u, a, v, m, hx, hf.closed u a v m p hp q hax, hy'⟩
      · have hq : ¬ (inG q = true ∧ Surgered inG O J x) := by rw [← hrest]; exact hs
        exact Or.inr ⟨hq, hkept _ hax (by simp [isGAssertion]) x y (hplain p x y hy hs)⟩
    | dassert u a v =>
      have hu : inG u = true := by simpa [axMentionsG] using hm'
      have m : (u, a, v) ∈ gAssertions inG O := mem_gAssertions.2 ⟨hax, hu⟩
      refine ⟨lit v, Or.inl ⟨hu, ⟨u, a, v, m, rfl⟩, u, a, v, m, rfl, hf.self u a v m, rfl⟩, ?_⟩
      exact (hvals v ⟨u, a, m⟩ (lit v)).2 rfl
    | _ => simp at hrest

end Complete

/-! ## Consequences -/

/-- Consistency is preserved both ways, and so is every class-name
subsumption (the surgery and the extension keep the source classes). -/
theorem projection_consistency_iff {Obj Dat : Type} (inG : DR → Bool)
    (O : List (Axiom Cls OR DR Ind DN)) (sup : DR → List DR) (memb : DN → DN → Option Bool)
    (key : DN → Option K) (idx : Slot Cls OR DR Ind DN → K → Nat)
    (npos : Slot Cls OR DR Ind DN → Nat) (lit : DN → Dat) (dcon : DN → Dat → Prop)
    (hg : projGate inG O sup memb key = true)
    (hsep : IndexSeparates idx npos (Relevant inG O sup memb key))
    (hvals : ValuesSingleton dcon lit (fun v => ∃ u a, (u, a, v) ∈ gAssertions inG O))
    (hmemb : MembSound dcon lit memb) (hkey : KeySound lit key) :
    (∃ I : Interp Cls OR DR Ind DN Obj Dat, I.dcon = dcon ∧ Models I O) ↔
    (∃ J : Interp (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN Obj Dat, J.dcon = dcon ∧
      ∀ ax, Proj inG O sup memb key idx npos ax → sat J ax) := by
  constructor
  · intro ⟨I, hd, hI⟩
    subst hd
    exact ⟨extend inG O key idx lit I, rfl,
      (projection_sound inG O sup memb key idx npos lit hg I hvals hmemb hkey hI).1⟩
  · intro ⟨J, hd, hJ⟩
    subst hd
    exact ⟨surgery inG O sup lit J, rfl,
      (projection_complete inG O sup memb key idx npos lit hg hsep J hvals hmemb hkey hJ).1⟩

end ContextCalculus.DataValueProjection

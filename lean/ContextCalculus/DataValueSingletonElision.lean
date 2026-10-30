import ContextCalculus.TwoSortedDL

/-!
# Value-singleton elision (`docs/DATATYPES.md`, "Value singletons")

The frontend leaves out the clause `v(y₁) ∧ v(y₂) → y₁ ≈ y₂` for a value `v`
whose relations the datatype oracle decides, when no source construct can force
two data successors of one element apart
(`literal_profiles::distinct_data_successors_forced`; the bridge's
`forced_distinct_data_successors` checks the same on its own input).

We read the clause set `S⁻` as an interpretation `J` with an abstract data
sort `N` (the data nodes), free labels `J.dcon`, the source axioms `O`, and the
oracle's decision clauses (`DecisionClauses`); the singleton clauses are not
assumed at all. The OWL reading has the value space `Val` and the datatype map
`den`.

* `forces` / `gate` are the syntactic gate (G1, G2), as decidable Boolean
  functions mirroring `distinct_data_successors_forced`. G3 (no `HasKey`, no
  rule) is the restriction to the language of `TwoSortedDL`.
* `reading` maps a clause model to an OWL interpretation through a node
  reading `ρ : N → Val`; `reading_models` proves that it is a model of `O`
  under the gate whenever `ρ` respects the labels of every data successor.
* `decidedReading_respects`: for a node that carries a value whose relation
  to *every* data concept name of the vocabulary (ranges and other values) is
  decided, reading the node as that value respects its labels, from the
  decision clauses alone.
* `singleton_elision_sound` / `real_model_satisfies_clauses`: the two
  directions, and `consistency_iff` / `subsumption_iff` the consequences.

The undecided nodes keep the reading the abstraction already needed before the
change (`UndecidedRealizable`, a hypothesis on label sets that do not contain
a decided value); the elision does not touch that obligation.

Finding (recorded in `docs/DATATYPES.md`, "Lean coverage"): the Rust condition
`value_fully_decided` asks for a decided identity key and decided range
memberships, not for decided relations to the other *values*. `val_eq` is
`None` between a keyed value and an opaque one (`"abc"^^xsd:token` against
`"abc"`), so a node can carry both, and the decided reading then does not
respect the opaque label. `decidedReading_respects` needs the stronger
condition `fullyDecided` below.
-/

namespace ContextCalculus.DataValueSingletonElision
open ContextCalculus.TwoSortedDL

variable {Cls OR DR Ind DN : Type}

/-! ## The syntactic gate (G1, G2) -/

/-- `forces p C`: `C`, at polarity `p`, contains a positive `≥ n` with
`n ≥ 2` or a negative `≤ n` with `n ≥ 1` over a data role. Mirrors
`distinct_data_successors_forced::forces` (roles are sorted here; the Rust
`data` test is the sort assignment). -/
def forces : Bool → Concept Cls OR DR Ind DN → Bool
  | p, .not c => forces (!p) c
  | p, .and c d => forces p c || forces p d
  | p, .or c d => forces p c || forces p d
  | p, .oex _ c => forces p c
  | p, .oall _ c => forces p c
  | p, .oge _ _ c => forces p c
  | p, .ole _ _ c => forces (!p) c
  | p, .dge n _ _ => p && decide (2 ≤ n)
  | p, .dle n _ _ => !p && decide (1 ≤ n)
  | _, _ => false

/-- An axiom that can force two data successors apart: a forcing class
expression at its polarity, or a data-property disjointness (G2). -/
def axForces : Axiom Cls OR DR Ind DN → Bool
  | .sub c d => forces false c || forces true d
  | .cassert c _ => forces true c
  | .ddisj _ _ => true
  | _ => false

/-- The gate: no axiom forces two data successors apart. -/
def gate (O : List (Axiom Cls OR DR Ind DN)) : Bool := !(O.any axForces)

theorem gate_axiom {O : List (Axiom Cls OR DR Ind DN)} (h : gate O = true) :
    ∀ ax ∈ O, axForces ax = false := by
  intro ax hax
  unfold gate at h
  cases hf : axForces ax with
  | false => rfl
  | true =>
    have : O.any axForces = true := List.any_eq_true.mpr ⟨ax, hax, hf⟩
    rw [this] at h
    exact absurd h (by decide)

/-! ## Reading a clause model as an OWL interpretation -/

variable {Obj N Val : Type}

/-- The OWL interpretation read off a clause model `J` through `ρ`. -/
def reading (J : Interp Cls OR DR Ind DN Obj N) (ρ : N → Val) (den : DN → Val → Prop) :
    Interp Cls OR DR Ind DN Obj Val :=
  { cls := J.cls, orole := J.orole, ind := J.ind, dcon := den,
    drole := fun u x y => ∃ n, J.drole u x n ∧ ρ n = y }

/-- `ρ` respects the labels of every data successor. -/
def Respects (J : Interp Cls OR DR Ind DN Obj N) (ρ : N → Val) (den : DN → Val → Prop) : Prop :=
  ∀ u x n, J.drole u x n → ∀ d, J.dcon d n ↔ den d (ρ n)

theorem reading_isReal (J : Interp Cls OR DR Ind DN Obj N) (ρ : N → Val) (den : DN → Val → Prop) :
    (reading J ρ den).IsReal den := rfl

theorem reading_sameObjectPart (J : Interp Cls OR DR Ind DN Obj N) (ρ : N → Val)
    (den : DN → Val → Prop) : SameObjectPart (reading J ρ den) J := ⟨rfl, rfl, rfl⟩

section Transfer
variable (J : Interp Cls OR DR Ind DN Obj N) (ρ : N → Val) (den : DN → Val → Prop)

theorem evalR_reading (hr : Respects J ρ den) {u x n} (hn : J.drole u x n) (R : DRange DN) :
    evalR J R n ↔ evalR (reading J ρ den) R (ρ n) := by
  cases R with
  | top => exact Iff.rfl
  | name d => exact hr u x n hn d

/-- Successors in the reading are images of successors in `J`. -/
theorem dsucc_reading (hr : Respects J ρ den) (u : DR) (R : DRange DN) (x : Obj) :
    ∀ y, ((reading J ρ den).drole u x y ∧ evalR (reading J ρ den) R y) →
      ∃ n, (J.drole u x n ∧ evalR J R n) ∧ ρ n = y := by
  intro y ⟨⟨n, hn, hy⟩, hR⟩
  subst hy
  exact ⟨n, ⟨hn, (evalR_reading J ρ den hr hn R).2 hR⟩, rfl⟩

/-- The transfer lemma: at positive polarity truth in `J` gives truth in the
reading, at negative polarity the converse, unless `forces` reports a
construct. -/
theorem eval_transfer (hr : Respects J ρ den) :
    ∀ C : Concept Cls OR DR Ind DN,
      (forces true C = false → ∀ x, eval J C x → eval (reading J ρ den) C x) ∧
      (forces false C = false → ∀ x, eval (reading J ρ den) C x → eval J C x) := by
  intro C
  induction C with
  | top => exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | bot => exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | atom a => exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | nominal i => exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | oself r => exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | not c ih =>
    refine ⟨fun hf x h hc => h (ih.2 hf x hc), fun hf x h hc => h (ih.1 hf x hc)⟩
  | and c d ihc ihd =>
    refine ⟨fun hf x h => ?_, fun hf x h => ?_⟩
    · simp only [forces, Bool.or_eq_false_iff] at hf
      exact ⟨ihc.1 hf.1 x h.1, ihd.1 hf.2 x h.2⟩
    · simp only [forces, Bool.or_eq_false_iff] at hf
      exact ⟨ihc.2 hf.1 x h.1, ihd.2 hf.2 x h.2⟩
  | or c d ihc ihd =>
    refine ⟨fun hf x h => ?_, fun hf x h => ?_⟩
    · simp only [forces, Bool.or_eq_false_iff] at hf
      exact h.elim (fun h => Or.inl (ihc.1 hf.1 x h)) (fun h => Or.inr (ihd.1 hf.2 x h))
    · simp only [forces, Bool.or_eq_false_iff] at hf
      exact h.elim (fun h => Or.inl (ihc.2 hf.1 x h)) (fun h => Or.inr (ihd.2 hf.2 x h))
  | oex r c ih =>
    refine ⟨fun hf x ⟨y, hy, h⟩ => ⟨y, hy, ih.1 hf y h⟩, fun hf x ⟨y, hy, h⟩ => ⟨y, hy, ih.2 hf y h⟩⟩
  | oall r c ih =>
    refine ⟨fun hf x h y hy => ih.1 hf y (h y hy), fun hf x h y hy => ih.2 hf y (h y hy)⟩
  | oge n r c ih =>
    refine ⟨fun hf x h => ?_, fun hf x h => ?_⟩
    · exact AtLeast.mono (fun y hy => ⟨hy.1, ih.1 hf y hy.2⟩) h
    · exact AtLeast.mono (fun y hy => ⟨hy.1, ih.2 hf y hy.2⟩) h
  | ole n r c ih =>
    refine ⟨fun hf x h hc => ?_, fun hf x h hc => ?_⟩
    · exact h (AtLeast.mono (fun y hy => ⟨hy.1, ih.2 hf y hy.2⟩) hc)
    · exact h (AtLeast.mono (fun y hy => ⟨hy.1, ih.1 hf y hy.2⟩) hc)
  | dex u R =>
    refine ⟨fun _ x ⟨n, hn, hR⟩ => ⟨ρ n, ⟨n, hn, rfl⟩, (evalR_reading J ρ den hr hn R).1 hR⟩,
      fun _ x h => ?_⟩
    obtain ⟨y, hy, hR⟩ := h
    obtain ⟨n, ⟨hn, hRn⟩, _⟩ := dsucc_reading J ρ den hr u R x y ⟨hy, hR⟩
    exact ⟨n, hn, hRn⟩
  | dall u R =>
    refine ⟨fun _ x h y ⟨n, hn, hy⟩ => ?_, fun _ x h n hn => ?_⟩
    · subst hy
      exact (evalR_reading J ρ den hr hn R).1 (h n hn)
    · exact (evalR_reading J ρ den hr hn R).2 (h (ρ n) ⟨n, hn, rfl⟩)
  | dge n u R =>
    refine ⟨fun hf x h => ?_, fun _ x h => ?_⟩
    · -- positive `≥ n` is allowed only for `n ≤ 1`
      have hn : n ≤ 1 := by
        simp only [forces, Bool.true_and, decide_eq_false_iff_not] at hf
        omega
      cases n with
      | zero => exact AtLeast.zero _
      | succ m =>
        have : m = 0 := by omega
        subst this
        obtain ⟨k, hk, hR⟩ := (AtLeast.one_iff _).1 h
        exact (AtLeast.one_iff _).2 ⟨ρ k, ⟨k, hk, rfl⟩, (evalR_reading J ρ den hr hk R).1 hR⟩
    · exact AtLeast.of_image ρ (dsucc_reading J ρ den hr u R x) h
  | dle n u R =>
    refine ⟨fun _ x h hc => ?_, fun hf x h hc => ?_⟩
    · exact h (AtLeast.of_image ρ (dsucc_reading J ρ den hr u R x) hc)
    · -- negative `≤ n` is allowed only for `n = 0`
      have hn : n = 0 := by
        simp only [forces, Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at hf
        omega
      subst hn
      obtain ⟨k, hk, hR⟩ := (AtLeast.one_iff _).1 hc
      exact h ((AtLeast.one_iff _).2 ⟨ρ k, ⟨k, hk, rfl⟩, (evalR_reading J ρ den hr hk R).1 hR⟩)

theorem sat_transfer (hr : Respects J ρ den) (ax : Axiom Cls OR DR Ind DN)
    (hf : axForces ax = false) : sat J ax → sat (reading J ρ den) ax := by
  cases ax with
  | sub c d =>
    simp only [axForces, Bool.or_eq_false_iff] at hf
    intro h x hc
    exact (eval_transfer J ρ den hr d).1 hf.2 x (h x ((eval_transfer J ρ den hr c).2 hf.1 x hc))
  | cassert c a =>
    exact (eval_transfer J ρ den hr c).1 hf _
  | oassert r a b => exact id
  | dassert u a v =>
    intro ⟨n, hn, hv⟩
    exact ⟨ρ n, ⟨n, hn, rfl⟩, (hr u _ n hn v).1 hv⟩
  | osub r s => exact id
  | dsub u w =>
    intro h x y ⟨n, hn, hy⟩
    exact ⟨n, h x n hn, hy⟩
  | ddisj u w => simp [axForces] at hf
  | same a b => exact id
  | diff a b => exact id

/-- Under the gate, the reading of a clause model through a label-respecting
`ρ` is an OWL model of `O` with the same object part. No singleton clause is
used. -/
theorem reading_models (O : List (Axiom Cls OR DR Ind DN)) (hg : gate O = true)
    (hJ : Models J O) (hr : Respects J ρ den) : Models (reading J ρ den) O := by
  intro ax hax
  exact sat_transfer J ρ den hr ax (gate_axiom hg ax hax) (hJ ax hax)

end Transfer

/-! ## Decided values -/

/-- The oracle's pairwise decisions: `dec v d = some true` emits `v ⊑ d`,
`some false` emits `v ⊓ d ⊑ ⊥`, `none` emits nothing. `d` ranges over every
data concept name: ranges, finite covers' members and other values (equal
keys give `some true` both ways, different keys `some false`). -/
def DecisionClauses (J : Interp Cls OR DR Ind DN Obj N) (dec : DN → DN → Option Bool) : Prop :=
  ∀ v d n, J.dcon v n → (dec v d = some true → J.dcon d n) ∧ (dec v d = some false → ¬ J.dcon d n)

/-- The oracle is sound for the datatype map. -/
def DecisionSound (den : DN → Val → Prop) (dec : DN → DN → Option Bool) : Prop :=
  ∀ v d y, den v y → (dec v d = some true → den d y) ∧ (dec v d = some false → ¬ den d y)

/-- The decidable condition under which a value's singleton can be left out:
`v` is a value and its relation to every data concept name of the vocabulary
`voc` (other than itself) is decided. This is stronger than the Rust
`value_fully_decided`, which does not look at the other values. -/
def fullyDecided [DecidableEq DN] (voc : List DN) (isValue : DN → Bool)
    (dec : DN → DN → Option Bool) (v : DN) : Bool :=
  isValue v && voc.all (fun d => decide (d = v) || (dec v d).isSome)

/-- Every value denotes a value of the datatype map (its literal). -/
def ValuesDenote (den : DN → Val → Prop) (isValue : DN → Bool) (lit : DN → Val) : Prop :=
  ∀ v, isValue v = true → den v (lit v)

/-- `fullyDecided` gives the semantic decidedness the reading needs. -/
theorem fullyDecided_spec [DecidableEq DN] {voc : List DN} {isValue : DN → Bool}
    {dec : DN → DN → Option Bool} {v : DN} (hvoc : ∀ d, d ∈ voc)
    (h : fullyDecided voc isValue dec v = true) :
    isValue v = true ∧ ∀ d, d = v ∨ ∃ b, dec v d = some b := by
  simp only [fullyDecided, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  refine ⟨h.1, fun d => ?_⟩
  rcases h.2 d (hvoc d) with h' | h'
  · exact Or.inl h'
  · right
    cases hd : dec v d with
    | none => rw [hd] at h'; exact absurd h' (by decide)
    | some b => exact ⟨b, rfl⟩

/-- A node carrying a fully decided value respects its labels when read as
that value: every label is decided by a clause of `S⁻`. -/
theorem decided_node_respects [DecidableEq DN] (J : Interp Cls OR DR Ind DN Obj N)
    (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool) (lit : DN → Val)
    (dec : DN → DN → Option Bool) (hvoc : ∀ d, d ∈ voc)
    (hcl : DecisionClauses J dec) (hsound : DecisionSound den dec)
    (hlit : ValuesDenote den isValue lit) {v : DN} {n : N}
    (hv : fullyDecided voc isValue dec v = true) (hvn : J.dcon v n) :
    ∀ d, J.dcon d n ↔ den d (lit v) := by
  obtain ⟨hval, hdec⟩ := fullyDecided_spec hvoc hv
  have hden := hlit v hval
  intro d
  rcases hdec d with rfl | ⟨b, hb⟩
  · exact ⟨fun _ => hden, fun _ => hvn⟩
  · cases b with
    | true => exact ⟨fun _ => (hsound v d _ hden).1 hb, fun _ => (hcl v d n hvn).1 hb⟩
    | false =>
      exact ⟨fun h => absurd h ((hcl v d n hvn).2 hb), fun h => absurd h ((hsound v d _ hden).2 hb)⟩

/-- A node without a fully decided value. -/
def Undecided [DecidableEq DN] (J : Interp Cls OR DR Ind DN Obj N) (voc : List DN)
    (isValue : DN → Bool) (dec : DN → DN → Option Bool) (n : N) : Prop :=
  ¬ ∃ v, fullyDecided voc isValue dec v = true ∧ J.dcon v n

/-- The pre-existing obligation of the datatype abstraction, unchanged by the
elision: every data successor without a fully decided value has a value that
realizes exactly its labels (`ρ₀`). -/
def UndecidedRealizable [DecidableEq DN] (J : Interp Cls OR DR Ind DN Obj N)
    (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool)
    (dec : DN → DN → Option Bool) (ρ₀ : N → Val) : Prop :=
  ∀ u x n, J.drole u x n → Undecided J voc isValue dec n → ∀ d, J.dcon d n ↔ den d (ρ₀ n)

/-- The node reading `ρ⁻` of the doc: a node carrying a fully decided value is
read as that value (any one: they are all equal by the decision clauses),
every other node as before. -/
noncomputable def decidedReading [DecidableEq DN] (J : Interp Cls OR DR Ind DN Obj N)
    (voc : List DN) (isValue : DN → Bool) (dec : DN → DN → Option Bool) (lit : DN → Val)
    (ρ₀ : N → Val) (n : N) : Val :=
  open Classical in
  if h : ∃ v, fullyDecided voc isValue dec v = true ∧ J.dcon v n then lit (Classical.choose h)
  else ρ₀ n

theorem decidedReading_respects [DecidableEq DN] (J : Interp Cls OR DR Ind DN Obj N)
    (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool) (lit : DN → Val)
    (dec : DN → DN → Option Bool) (ρ₀ : N → Val) (hvoc : ∀ d, d ∈ voc)
    (hcl : DecisionClauses J dec) (hsound : DecisionSound den dec)
    (hlit : ValuesDenote den isValue lit)
    (hund : UndecidedRealizable J den voc isValue dec ρ₀) :
    Respects J (decidedReading J voc isValue dec lit ρ₀) den := by
  intro u x n hn d
  unfold decidedReading
  split
  · next h =>
    exact decided_node_respects J den voc isValue lit dec hvoc hcl hsound hlit
      (Classical.choose_spec h).1 (Classical.choose_spec h).2 d
  · next h => exact hund u x n hn h d

/-! ## The theorem -/

/-- **Singleton elision, `S⁻ ⇒ O`.** Let `J` be a model of the source axioms
and of the decision clauses (the clause set `S⁻`, with no singleton clause for
any value), and let the undecided successors be realizable as before. Under
the gate, `J` read through `ρ⁻` is an OWL model of `O` with the same classes,
object properties and individuals. -/
theorem singleton_elision_sound [DecidableEq DN] (O : List (Axiom Cls OR DR Ind DN))
    (hg : gate O = true) (den : DN → Val → Prop) (voc : List DN) (hvoc : ∀ d, d ∈ voc)
    (isValue : DN → Bool) (lit : DN → Val) (dec : DN → DN → Option Bool)
    (hsound : DecisionSound den dec) (hlit : ValuesDenote den isValue lit)
    (J : Interp Cls OR DR Ind DN Obj N) (hJ : Models J O) (hcl : DecisionClauses J dec)
    (ρ₀ : N → Val) (hund : UndecidedRealizable J den voc isValue dec ρ₀) :
    ∃ I : Interp Cls OR DR Ind DN Obj Val, I.IsReal den ∧ Models I O ∧ SameObjectPart I J :=
  ⟨reading J (decidedReading J voc isValue dec lit ρ₀) den, rfl,
    reading_models J _ den O hg hJ
      (decidedReading_respects J den voc isValue lit dec ρ₀ hvoc hcl hsound hlit hund),
    reading_sameObjectPart J _ den⟩

/-- The value singleton clauses for the values in `keep`. -/
def Singletons (J : Interp Cls OR DR Ind DN Obj N) (keep : DN → Prop) : Prop :=
  ∀ v, keep v → ∀ n₁ n₂, J.dcon v n₁ → J.dcon v n₂ → n₁ = n₂

/-- **`O ⇒ S`.** An OWL model of `O` satisfies the decision clauses and every
singleton clause (each value denotes one literal), so it is a model of the
full clause set `S` and hence of `S⁻`; it is its own undecided reading. -/
theorem real_model_satisfies_clauses [DecidableEq DN] (O : List (Axiom Cls OR DR Ind DN))
    (den : DN → Val → Prop) (voc : List DN) (isValue : DN → Bool)
    (dec : DN → DN → Option Bool) (hsound : DecisionSound den dec)
    (hsingle : ∀ v, isValue v = true → ∀ y₁ y₂, den v y₁ → den v y₂ → y₁ = y₂)
    (I : Interp Cls OR DR Ind DN Obj Val) (hreal : I.IsReal den) (hI : Models I O) :
    Models I O ∧ DecisionClauses I dec ∧ Singletons I (fun v => isValue v = true) ∧
      UndecidedRealizable I den voc isValue dec id := by
  unfold Interp.IsReal at hreal
  refine ⟨hI, ?_, ?_, ?_⟩
  · intro v d n hv
    rw [hreal] at hv ⊢
    exact hsound v d n hv
  · intro v hv n₁ n₂ h₁ h₂
    rw [hreal] at h₁ h₂
    exact hsingle v hv n₁ n₂ h₁ h₂
  · intro _ _ n _ _ d
    rw [hreal]
    exact Iff.rfl

/-- Consistency: `O` has an OWL model iff `S⁻` has a clause model whose
undecided successors are realizable. -/
theorem consistency_iff [DecidableEq DN] (O : List (Axiom Cls OR DR Ind DN))
    (hg : gate O = true) (den : DN → Val → Prop) (voc : List DN) (hvoc : ∀ d, d ∈ voc)
    (isValue : DN → Bool) (lit : DN → Val) (dec : DN → DN → Option Bool)
    (hsound : DecisionSound den dec) (hlit : ValuesDenote den isValue lit) :
    (∃ I : Interp Cls OR DR Ind DN Obj Val, I.IsReal den ∧ Models I O) ↔
    (∃ (J : Interp Cls OR DR Ind DN Obj Val) (ρ₀ : Val → Val), Models J O ∧
      DecisionClauses J dec ∧ UndecidedRealizable J den voc isValue dec ρ₀) := by
  constructor
  · intro ⟨I, hreal, hI⟩
    unfold Interp.IsReal at hreal
    refine ⟨I, id, hI, ?_, ?_⟩
    · intro v d n hv
      rw [hreal] at hv ⊢
      exact hsound v d n hv
    · intro _ _ n _ _ d
      rw [hreal]
      exact Iff.rfl
  · intro ⟨J, ρ₀, hJ, hcl, hund⟩
    obtain ⟨I, hreal, hI, _⟩ :=
      singleton_elision_sound O hg den voc hvoc isValue lit dec hsound hlit J hJ hcl ρ₀ hund
    exact ⟨I, hreal, hI⟩

/-- Class subsumption: `A ⊑ B` holds in every OWL model of `O` iff it holds
in every clause model of `S⁻` with realizable undecided successors (object
type fixed, data nodes of any type). -/
theorem subsumption_iff [DecidableEq DN] (O : List (Axiom Cls OR DR Ind DN))
    (hg : gate O = true) (den : DN → Val → Prop) (voc : List DN) (hvoc : ∀ d, d ∈ voc)
    (isValue : DN → Bool) (lit : DN → Val) (dec : DN → DN → Option Bool)
    (hsound : DecisionSound den dec) (hlit : ValuesDenote den isValue lit) (A B : Cls) :
    (∀ I : Interp Cls OR DR Ind DN Obj Val, I.IsReal den → Models I O → ∀ x, I.cls A x → I.cls B x) ↔
    (∀ (N : Type) (J : Interp Cls OR DR Ind DN Obj N) (ρ₀ : N → Val), Models J O →
      DecisionClauses J dec → UndecidedRealizable J den voc isValue dec ρ₀ →
      ∀ x, J.cls A x → J.cls B x) := by
  constructor
  · intro h N J ρ₀ hJ hcl hund x hA
    obtain ⟨I, hreal, hI, hsame⟩ :=
      singleton_elision_sound O hg den voc hvoc isValue lit dec hsound hlit J hJ hcl ρ₀ hund
    have hc : I.cls = J.cls := hsame.1
    have := h I hreal hI x (by rw [hc]; exact hA)
    rw [hc] at this
    exact this
  · intro h I hreal hI x hA
    unfold Interp.IsReal at hreal
    refine h Val I id hI ?_ ?_ x hA
    · intro v d n hv
      rw [hreal] at hv ⊢
      exact hsound v d n hv
    · intro _ _ n _ _ d
      rw [hreal]
      exact Iff.rfl

end ContextCalculus.DataValueSingletonElision

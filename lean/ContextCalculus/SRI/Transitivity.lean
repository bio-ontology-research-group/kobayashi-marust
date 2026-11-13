import ContextCalculus.SRI.Procedure

/-!
# Transitivity by universal propagation (v1.6.3 plan, section 2d)

SHI clauses have role chains of two shapes: inclusions `[R] ⊑ S` and
transitivity `[T, T] ⊑ T`. `encTrans` drops the transitivity clauses and
adds, for every `allRight a S c` and every transitive role term `T` (or
the flip of one) with `T ⊑* S`, a fresh name `q` with

- `allRight a T q`, `gci [q] [c]`, `allRight q T q`.

The result is ALCHI and has the same subsumptions between old names.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat}

/-- Chains are inclusions or transitivity. -/
def IsSHI (O : Ontology (Fin n) (Fin m)) : Prop :=
  ∀ body S, Clause.chain body S ∈ O → body.length = 1 ∨ body = [S, S]

section Enc

variable (O : Ontology (Fin n) (Fin m))

/-- The transitive role terms, closed under flip. -/
def transTerms : List (RT m) :=
  let base := O.filterMap fun
    | .chain [R, S] T => if R = T ∧ S = T then some T else none
    | _ => none
  (base ++ base.map RoleT.flip).dedup

/-- One fresh name per universal restriction and transitive sub-role. -/
def transPairs : List ((Fin n × RT m × Fin n) × RT m) :=
  (alls O).flatMap fun q =>
    ((transTerms O).filter fun T => decide (q.2.1 ∈ roleUp O T)).map fun T => (q, T)

def liftClause (k : Nat) : Clause (Fin n) (Fin m) → Option (Clause (Fin (n + k)) (Fin m))
  | .gci body head => some (.gci (body.map (Fin.castAdd k)) (head.map (Fin.castAdd k)))
  | .exRight a R b => some (.exRight (Fin.castAdd k a) R (Fin.castAdd k b))
  | .allRight a R b => some (.allRight (Fin.castAdd k a) R (Fin.castAdd k b))
  | .chain [R] S => some (.chain [R] S)
  | .chain _ _ => none

/-- The encoding. -/
def encTrans : Σ k, Ontology (Fin (n + k)) (Fin m) :=
  let P := transPairs O
  ⟨P.length,
    O.filterMap (liftClause P.length) ++
      (P.zipIdx.flatMap fun ⟨⟨⟨a, _, c⟩, T⟩, i⟩ =>
        if h : i < P.length then
          let q : Fin (n + P.length) := Fin.natAdd n ⟨i, h⟩
          [.allRight (Fin.castAdd _ a) T q, .gci [q] [Fin.castAdd _ c], .allRight q T q]
        else [])⟩

end Enc

/-! ## Facts about the encoding -/

section Facts

variable {O : Ontology (Fin n) (Fin m)}

theorem mem_transTerms {T : RT m} :
    T ∈ transTerms O ↔
      Clause.chain [T, T] T ∈ O ∨ Clause.chain [T.flip, T.flip] T.flip ∈ O := by
  unfold transTerms
  simp only [List.mem_dedup, List.mem_append, List.mem_map, List.mem_filterMap]
  constructor
  · rintro (⟨cl, hcl, he⟩ | ⟨U, ⟨cl, hcl, he⟩, rfl⟩)
    · rcases cl with _ | _ | _ | ⟨_ | ⟨R, _ | ⟨S, _ | _⟩⟩, V⟩ <;> simp at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      exact Or.inl hcl
    · rcases cl with _ | _ | _ | ⟨_ | ⟨R, _ | ⟨S, _ | _⟩⟩, V⟩ <;> simp at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      exact Or.inr (by simpa using hcl)
  · rintro (h | h)
    · exact Or.inl ⟨_, h, by simp⟩
    · exact Or.inr ⟨T.flip, ⟨_, h, by simp⟩, by simp⟩

theorem flip_mem_transTerms {T : RT m} (h : T ∈ transTerms O) : T.flip ∈ transTerms O := by
  rw [mem_transTerms] at h ⊢
  rw [RoleT.flip_flip]
  exact h.symm

theorem mem_transPairs {a c : Fin n} {S T : RT m} :
    ((a, S, c), T) ∈ transPairs O ↔
      Clause.allRight a S c ∈ O ∧ T ∈ transTerms O ∧ RoleLe O T S := by
  unfold transPairs
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_roleUp]
  constructor
  · rintro ⟨⟨a', S', c'⟩, hq, T', ⟨hT, hle⟩, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := he
    exact ⟨mem_alls.1 hq, hT, hle⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(a, S, c), mem_alls.2 h1, T, ⟨h2, h3⟩, rfl⟩

theorem mem_encTrans_of_lift {cl0 : Clause (Fin n) (Fin m)}
    {cl : Clause (Fin (n + (transPairs O).length)) (Fin m)} (h : cl0 ∈ O)
    (hl : liftClause (transPairs O).length cl0 = some cl) : cl ∈ (encTrans O).2 :=
  List.mem_append_left _ (List.mem_filterMap.2 ⟨cl0, h, hl⟩)

/-- The three clauses of the fresh name at index `i`. -/
theorem mem_encTrans_fresh {i : Nat} (h : i < (transPairs O).length) {a c : Fin n}
    {S T : RT m} (hp : (transPairs O)[i] = ((a, S, c), T)) :
    Clause.allRight (Fin.castAdd _ a) T (Fin.natAdd n ⟨i, h⟩) ∈ (encTrans O).2 ∧
    Clause.gci [Fin.natAdd n ⟨i, h⟩] [Fin.castAdd _ c] ∈ (encTrans O).2 ∧
    Clause.allRight (Fin.natAdd n ⟨i, h⟩) T (Fin.natAdd n ⟨i, h⟩) ∈ (encTrans O).2 := by
  have hz : (((a, S, c), T), i) ∈ (transPairs O).zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem h, hp]
  refine ⟨?_, ?_, ?_⟩ <;>
    refine List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hz, ?_⟩) <;> simp [h]

/-- Every clause of the encoding is a lifted clause or a clause of a fresh name. -/
theorem mem_encTrans_cases {cl : Clause (Fin (n + (transPairs O).length)) (Fin m)}
    (hcl : cl ∈ (encTrans O).2) :
    (∃ cl0 ∈ O, liftClause (transPairs O).length cl0 = some cl) ∨
    ∃ i, ∃ h : i < (transPairs O).length,
      cl = Clause.allRight (Fin.castAdd _ ((transPairs O)[i]).1.1) ((transPairs O)[i]).2
        (Fin.natAdd n ⟨i, h⟩) ∨
      cl = Clause.gci [Fin.natAdd n ⟨i, h⟩] [Fin.castAdd _ ((transPairs O)[i]).1.2.2] ∨
      cl = Clause.allRight (Fin.natAdd n ⟨i, h⟩) ((transPairs O)[i]).2 (Fin.natAdd n ⟨i, h⟩) := by
  rcases List.mem_append.1 hcl with h0 | h1
  · exact Or.inl (List.mem_filterMap.1 h0)
  · right
    obtain ⟨⟨⟨⟨a, S, c⟩, T⟩, i⟩, hz, hm⟩ := List.mem_flatMap.1 h1
    rw [List.mk_mem_zipIdx_iff_getElem?] at hz
    by_cases h : i < (transPairs O).length
    · rw [List.getElem?_eq_getElem h, Option.some.injEq] at hz
      refine ⟨i, h, ?_⟩
      rw [hz]
      simpa [h] using hm
    · simp [h] at hm

end Facts

theorem encTrans_isALCHI (O : Ontology (Fin n) (Fin m)) : IsALCHI (encTrans O).2 := by
  intro body S hcl
  rcases mem_encTrans_cases hcl with ⟨cl0, _, hl⟩ | ⟨i, h, hc⟩
  · rcases cl0 with _ | _ | _ | ⟨_ | ⟨R, _ | _⟩, S0⟩ <;> simp [liftClause] at hl
    obtain ⟨rfl, rfl⟩ := hl
    rfl
  · rcases hc with hc | hc | hc <;> simp at hc

/-! ## From a model of the input to a model of the encoding -/

section Up

variable {O : Ontology (Fin n) (Fin m)} {D : Type}

/-- The fresh name of the pair `((a, S, c), T)` holds where `c` holds here
and at every `T`-successor. -/
def upI (O : Ontology (Fin n) (Fin m)) (I : Interp D (Fin n) (Fin m)) :
    Interp D (Fin (n + (transPairs O).length)) (Fin m) where
  c := Fin.addCases (motive := fun _ => D → Prop) (fun a => I.c a)
    (fun i y => I.c ((transPairs O)[i.1]'i.2).1.2.2 y ∧
      ∀ z, I.rt ((transPairs O)[i.1]'i.2).2 y z → I.c ((transPairs O)[i.1]'i.2).1.2.2 z)
  r := I.r

theorem upI_rt (I : Interp D (Fin n) (Fin m)) (R : RT m) :
    (upI O I).rt R = I.rt R := by
  cases R <;> rfl

theorem upI_old (I : Interp D (Fin n) (Fin m)) (a : Fin n) (y : D) :
    (upI O I).c (Fin.castAdd _ a) y ↔ I.c a y := by
  simp [upI]

theorem upI_fresh (I : Interp D (Fin n) (Fin m)) {i : Nat} (h : i < (transPairs O).length)
    (y : D) :
    (upI O I).c (Fin.natAdd n ⟨i, h⟩) y ↔
      (I.c ((transPairs O)[i]).1.2.2 y ∧
        ∀ z, I.rt ((transPairs O)[i]).2 y z → I.c ((transPairs O)[i]).1.2.2 z) := by
  simp only [upI]
  rw [Fin.addCases_right]

theorem upI_path (I : Interp D (Fin n) (Fin m)) :
    ∀ (L : List (RT m)) (x y : D), (upI O I).path L x y ↔ I.path L x y
  | [], _, _ => Iff.rfl
  | R :: L, x, y => by
    simp only [Interp.path, upI_rt, upI_path I L]

/-- A transitive role term of `O` is transitive in every model of `O`. -/
theorem trans_of_mem {I : Interp D (Fin n) (Fin m)} (hI : models I O) {T : RT m}
    (hT : T ∈ transTerms O) {x y z : D} (hxy : I.rt T x y) (hyz : I.rt T y z) :
    I.rt T x z := by
  rcases mem_transTerms.1 hT with h | h
  · exact hI _ h x z ⟨y, hxy, z, hyz, rfl⟩
  · have := hI _ h z x ⟨y, (Interp.rt_flip I T z y).2 hyz, x,
      (Interp.rt_flip I T y x).2 hxy, rfl⟩
    exact (Interp.rt_flip I T z x).1 this

theorem upI_models {I : Interp D (Fin n) (Fin m)} (hI : models I O) :
    models (upI O I) (encTrans O).2 := by
  intro cl hcl
  rcases mem_encTrans_cases hcl with ⟨cl0, h0, hl⟩ | ⟨i, h, hc⟩
  · have hs := hI _ h0
    rcases cl0 with ⟨body, head⟩ | ⟨a, R, b⟩ | ⟨a, R, b⟩ | ⟨_ | ⟨R, _ | _⟩, S⟩ <;>
      simp only [liftClause, Option.some.injEq, reduceCtorEq] at hl <;> subst hl
    · intro x hx
      obtain ⟨b, hb, hbx⟩ := hs x (fun a ha => (upI_old I a x).1 (hx _ (List.mem_map_of_mem ha)))
      exact ⟨_, List.mem_map_of_mem hb, (upI_old I b x).2 hbx⟩
    · intro x hx
      obtain ⟨y, hxy, hy⟩ := hs x ((upI_old I a x).1 hx)
      exact ⟨y, by rw [upI_rt]; exact hxy, (upI_old I b y).2 hy⟩
    · intro x hx y hxy
      rw [upI_rt] at hxy
      exact (upI_old I b y).2 (hs x ((upI_old I a x).1 hx) y hxy)
    · intro x y hxy
      rw [upI_path] at hxy
      rw [upI_rt]
      exact hs x y hxy
  · generalize hp : (transPairs O)[i] = p at hc
    obtain ⟨⟨a, S, c⟩, T⟩ := p
    have hmem : ((a, S, c), T) ∈ transPairs O := hp ▸ List.getElem_mem h
    obtain ⟨hall, hT, hle⟩ := mem_transPairs.1 hmem
    have hSO := hI _ hall
    rcases hc with rfl | rfl | rfl
    · intro x hx y hxy
      rw [upI_old] at hx
      rw [upI_rt] at hxy
      rw [upI_fresh, hp]
      refine ⟨hSO x hx y (roleLe_sound hI hle x y hxy), fun z hyz => ?_⟩
      exact hSO x hx z (roleLe_sound hI hle x z (trans_of_mem hI hT hxy hyz))
    · intro x hx
      have hq := (upI_fresh I h x).1 (hx _ (List.mem_singleton_self _))
      rw [hp] at hq
      exact ⟨_, List.mem_singleton_self _, (upI_old I c x).2 hq.1⟩
    · intro x hx y hxy
      rw [upI_fresh, hp] at hx ⊢
      rw [upI_rt] at hxy
      exact ⟨hx.2 y hxy, fun z hyz => hx.2 z (trans_of_mem hI hT hxy hyz)⟩

end Up

/-! ## From a model of the encoding to a model of the input -/

section Down

variable {O : Ontology (Fin n) (Fin m)} {D : Type}

/-- Each role name grows by the transitive closures of its transitive
sub-roles. -/
def downI (O : Ontology (Fin n) (Fin m)) (J : Interp D (Fin (n + (transPairs O).length)) (Fin m)) :
    Interp D (Fin n) (Fin m) where
  c := fun a => J.c (Fin.castAdd _ a)
  r := fun r x y => J.r r x y ∨
    ∃ T ∈ transTerms O, RoleLe O T (.pos r) ∧ Relation.TransGen (J.rt T) x y

theorem transGen_flip {J : Interp D (Fin (n + (transPairs O).length)) (Fin m)} (T : RT m)
    (x y : D) : Relation.TransGen (J.rt T.flip) x y ↔ Relation.TransGen (J.rt T) y x := by
  have : J.rt T.flip = Function.swap (J.rt T) := by
    funext u v
    exact propext (Interp.rt_flip J T u v)
  rw [this, Relation.transGen_swap]

theorem downI_rt (J : Interp D (Fin (n + (transPairs O).length)) (Fin m)) (R : RT m) (x y : D) :
    (downI O J).rt R x y ↔
      J.rt R x y ∨ ∃ T ∈ transTerms O, RoleLe O T R ∧ Relation.TransGen (J.rt T) x y := by
  cases R with
  | pos r => exact Iff.rfl
  | inv r =>
    show J.r r y x ∨ _ ↔ J.r r y x ∨ _
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨T, hT, hle, hp⟩
      exact ⟨T.flip, flip_mem_transTerms hT, roleLe_flip hle, (transGen_flip T x y).2 hp⟩
    · rintro ⟨T, hT, hle, hp⟩
      refine ⟨T.flip, flip_mem_transTerms hT, roleLe_flip hle, ?_⟩
      rw [transGen_flip]
      exact hp

variable {J : Interp D (Fin (n + (transPairs O).length)) (Fin m)}

theorem roleLe_enc {R S : RT m} (h : RoleLe O R S) : RoleLe (encTrans O).2 R S := by
  refine Relation.ReflTransGen.mono (fun U V hst => ?_) h
  rcases hst with h1 | h2
  · exact Or.inl (mem_encTrans_of_lift h1 rfl)
  · exact Or.inr (mem_encTrans_of_lift h2 rfl)

theorem J_le (hJ : models J (encTrans O).2) {R S : RT m} (h : RoleLe O R S) (x y : D)
    (hxy : J.rt R x y) : J.rt S x y :=
  roleLe_sound hJ (roleLe_enc h) x y hxy

theorem downI_mono (hJ : models J (encTrans O).2) {R S : RT m} (h : RoleLe O R S) (x y : D)
    (hxy : (downI O J).rt R x y) : (downI O J).rt S x y := by
  rw [downI_rt] at hxy ⊢
  rcases hxy with hxy | ⟨T, hT, hle, hp⟩
  · exact Or.inl (J_le hJ h x y hxy)
  · exact Or.inr ⟨T, hT, hle.trans h, hp⟩

theorem downI_trans_iff (hJ : models J (encTrans O).2) {T : RT m} (hT : T ∈ transTerms O)
    (x y : D) : (downI O J).rt T x y ↔ Relation.TransGen (J.rt T) x y := by
  rw [downI_rt]
  constructor
  · rintro (hxy | ⟨U, _, hle, hp⟩)
    · exact Relation.TransGen.single hxy
    · exact Relation.TransGen.mono (fun u v huv => J_le hJ hle u v huv) hp
  · intro hp
    exact Or.inr ⟨T, hT, Relation.ReflTransGen.refl, hp⟩

theorem downI_models (hS : IsSHI O) (hJ : models J (encTrans O).2) : models (downI O J) O := by
  intro cl hcl
  cases cl with
  | gci body head =>
    have hs := hJ _ (mem_encTrans_of_lift (cl0 := .gci body head) hcl rfl)
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hs x (fun a ha => by
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
      exact hx a0 ha0)
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
    exact ⟨b0, hb0, hbx⟩
  | exRight a R b =>
    have hs := hJ _ (mem_encTrans_of_lift (cl0 := .exRight a R b) hcl rfl)
    intro x hx
    obtain ⟨y, hxy, hy⟩ := hs x hx
    exact ⟨y, (downI_rt J R x y).2 (Or.inl hxy), hy⟩
  | allRight a S c =>
    have hs := hJ _ (mem_encTrans_of_lift (cl0 := .allRight a S c) hcl rfl)
    intro x hx y hxy
    rcases (downI_rt J S x y).1 hxy with hxy | ⟨T, hT, hle, hp⟩
    · exact hs x hx y hxy
    · obtain ⟨i, h, hpi⟩ := List.getElem_of_mem (mem_transPairs.2 ⟨hcl, hT, hle⟩)
      obtain ⟨h1, h2, h3⟩ := mem_encTrans_fresh h hpi
      have hq : ∀ z, Relation.TransGen (J.rt T) x z → J.c (Fin.natAdd n ⟨i, h⟩) z := by
        intro z hz
        induction hz with
        | single h0 => exact hJ _ h1 x hx _ h0
        | tail _ h0 ih => exact hJ _ h3 _ ih _ h0
      obtain ⟨b, hb, hby⟩ := hJ _ h2 y (by simpa using hq y hp)
      rw [List.mem_singleton] at hb
      subst hb
      exact hby
  | chain body S =>
    rcases hS body S hcl with hlen | rfl
    · match body, hlen, hcl with
      | [R], _, hcl =>
        rintro x y ⟨z, hxz, rfl⟩
        exact downI_mono hJ (Relation.ReflTransGen.single (Or.inl hcl)) x z hxz
    · have hT : S ∈ transTerms O := mem_transTerms.2 (Or.inl hcl)
      rintro x z ⟨y, hxy, z', hyz, rfl⟩
      rw [downI_trans_iff hJ hT] at hxy hyz ⊢
      exact hxy.trans hyz

end Down

/-- **P5.** The encoding keeps subsumption between the old names. -/
theorem encTrans_correct {O : Ontology (Fin n) (Fin m)} (h : IsSHI O) (a b : Fin n) :
    EntailsSub O a b ↔
      EntailsSub (encTrans O).2 (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  constructor
  · intro hO D _ J hJ x hx
    exact hO D (downI O J) (downI_models h hJ) x hx
  · intro hE D _ I hI x hx
    have := hE D (upI O I) (upI_models hI) x ((upI_old I a x).2 hx)
    exact (upI_old I b x).1 this

end ContextCalculus.SRI.Proc

#print axioms ContextCalculus.SRI.Proc.encTrans_isALCHI
#print axioms ContextCalculus.SRI.Proc.encTrans_correct

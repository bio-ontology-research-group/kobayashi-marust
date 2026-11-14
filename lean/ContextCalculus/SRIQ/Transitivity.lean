import ContextCalculus.SRIQ.NormalForm
import ContextCalculus.SRI.Transitivity

/-!
# Transitivity and simple roles for SHIQ (stage C1, design section 5)

SHIQ clauses have role chains of two shapes, inclusions `[R] ⊑ S` and
transitivity `[T, T] ⊑ T`, and the roles of counting clauses are simple:
no transitive role lies below them or below their inverses (`IsSHIQ`,
the OWL 2 DL simple-role restriction).

`encTransQ` applies `SRI.Proc.encTrans` to the clauses without counting
and passes the counting clauses through unchanged (on the old names).
The model constructions of `SRI/Transitivity.lean` change only the roles
above a transitive role, which no counting clause mentions, so the
encoding keeps subsumption between old names (`encTransQ_correct`).
-/

namespace ContextCalculus.SRIQ.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

/-- Chains are inclusions or transitivity, and counting clauses use
simple roles. -/
def IsSHIQ (O : Ontology (Fin n) (Fin m)) : Prop :=
  (∀ body S, Clause.chain body S ∈ O → body.length = 1 ∨ body = [S, S]) ∧
  ∀ a k R b, (Clause.atLeast a k R b ∈ O ∨ Clause.atMost a k R b ∈ O) →
    ∀ T, Clause.chain [T, T] T ∈ O → ¬ RoleLe O T R ∧ ¬ RoleLe O T R.flip

/-- A counting clause on the old names of the encoding. -/
def liftCount (k : Nat) : Clause (Fin n) (Fin m) → Option (Clause (Fin (n + k)) (Fin m))
  | .atLeast a j R b => some (.atLeast (Fin.castAdd k a) j R (Fin.castAdd k b))
  | .atMost a j R b => some (.atMost (Fin.castAdd k a) j R (Fin.castAdd k b))
  | _ => none

/-- `encTrans` of the clauses without counting. -/
def encBase (O : Ontology (Fin n) (Fin m)) :
    Ontology (Fin (n + (SRI.Proc.transPairs (sriPart O)).length)) (Fin m) :=
  (SRI.Proc.encTrans (sriPart O)).2.map ofSRI

/-- The counting clauses on the old names. -/
def countPart (O : Ontology (Fin n) (Fin m)) :
    Ontology (Fin (n + (SRI.Proc.transPairs (sriPart O)).length)) (Fin m) :=
  O.filterMap (liftCount (SRI.Proc.transPairs (sriPart O)).length)

/-- The encoding: `encTrans` on the clauses without counting, and the
counting clauses unchanged. -/
def encTransQ (O : Ontology (Fin n) (Fin m)) :
    Σ k, Ontology (Fin (n + k)) (Fin m) :=
  ⟨(SRI.Proc.transPairs (sriPart O)).length, encBase O ++ countPart O⟩

theorem mem_encTransQ {O : Ontology (Fin n) (Fin m)}
    {cl : Clause (Fin (n + (SRI.Proc.transPairs (sriPart O)).length)) (Fin m)} :
    cl ∈ (encTransQ O).2 ↔ cl ∈ encBase O ∨ cl ∈ countPart O :=
  List.mem_append

theorem isSHI_sriPart {O : Ontology (Fin n) (Fin m)} (h : IsSHIQ O) :
    SRI.Proc.IsSHI (sriPart O) :=
  fun body S hcl => h.1 body S (mem_sriPart.1 hcl)

theorem encTransQ_isALCHIQ (O : Ontology (Fin n) (Fin m)) : IsALCHIQ (encTransQ O).2 := by
  intro body S hcl
  rcases mem_encTransQ.1 hcl with h | h
  · obtain ⟨cl, hcl', he⟩ := List.mem_map.1 h
    cases cl <;> simp only [ofSRI, reduceCtorEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact SRI.Proc.encTrans_isALCHI _ _ _ hcl'
  · obtain ⟨cl, -, he⟩ := List.mem_filterMap.1 h
    cases cl <;> simp [liftCount] at he

section Counting

variable {D : Type}

/-- Counting clauses transfer between interpretations that agree on the
role and the two names. -/
theorem satClause_count_congr {C1 C2 : Type} {I : Interp D C1 (Fin m)} {J : Interp D C2 (Fin m)}
    {R : RoleT (Fin m)} (hR : ∀ x y, I.rt R x y ↔ J.rt R x y) {a b : C1} {a' b' : C2}
    (ha : ∀ x, I.c a x ↔ J.c a' x) (hb : ∀ x, I.c b x ↔ J.c b' x) (k : Nat) :
    (satClause I (.atLeast a k R b) ↔ satClause J (.atLeast a' k R b')) ∧
    (satClause I (.atMost a k R b) ↔ satClause J (.atMost a' k R b')) := by
  refine ⟨?_, ?_⟩ <;> simp only [satClause, hR, ha, hb]

/-- On a simple role, `downI` adds no edges. -/
theorem downI_rt_simple {O : Ontology (Fin n) (Fin m)}
    (J : Interp D (Fin (n + (SRI.Proc.transPairs (sriPart O)).length)) (Fin m))
    {R : RoleT (Fin m)}
    (hs : ∀ T, Clause.chain [T, T] T ∈ O → ¬ RoleLe O T R ∧ ¬ RoleLe O T R.flip) (x y : D) :
    (SRI.Proc.downI (sriPart O) J).rt R x y ↔ J.rt R x y := by
  rw [SRI.Proc.downI_rt]
  refine ⟨fun h => h.resolve_right ?_, Or.inl⟩
  rintro ⟨T, hT, hle, -⟩
  rcases SRI.Proc.mem_transTerms.1 hT with h1 | h1
  · exact (hs T (mem_sriPart.1 h1)).1 hle
  · have := (hs T.flip (mem_sriPart.1 h1)).2
    exact this (roleLe_flip hle)

end Counting

/-- **Transitivity removal.** For SHIQ, the encoding keeps subsumption
between the old names. -/
theorem encTransQ_correct {O : Ontology (Fin n) (Fin m)} (h : IsSHIQ O) (a b : Fin n) :
    EntailsSub O a b ↔
      EntailsSub (encTransQ O).2 (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  constructor
  · intro hO D _ J hJ x hx
    have hJs : SRI.models J (SRI.Proc.encTrans (sriPart O)).2 := by
      intro cl hcl
      rw [← satClause_ofSRI]
      exact hJ _ (mem_encTransQ.2 (Or.inl (List.mem_map_of_mem hcl)))
    have hD : models (SRI.Proc.downI (sriPart O) J) O := by
      intro cl hcl
      cases cl with
      | atLeast a' k R b' =>
        have hJc := hJ _ (mem_encTransQ.2 (Or.inr (List.mem_filterMap.2 ⟨_, hcl, rfl⟩)))
        refine ((satClause_count_congr (downI_rt_simple J (h.2 a' k R b' (Or.inl hcl)))
          (fun _ => Iff.rfl) (fun _ => Iff.rfl) k).1).2 hJc
      | atMost a' k R b' =>
        have hJc := hJ _ (mem_encTransQ.2 (Or.inr (List.mem_filterMap.2 ⟨_, hcl, rfl⟩)))
        refine ((satClause_count_congr (downI_rt_simple J (h.2 a' k R b' (Or.inr hcl)))
          (fun _ => Iff.rfl) (fun _ => Iff.rfl) k).2).2 hJc
      | gci body head =>
        exact (satClause_ofSRI _ (.gci body head)).2
          (SRI.Proc.downI_models (isSHI_sriPart h) hJs _ (mem_sriPart.2 hcl))
      | exRight a' R b' =>
        exact (satClause_ofSRI _ (.exRight a' R b')).2
          (SRI.Proc.downI_models (isSHI_sriPart h) hJs _ (mem_sriPart.2 hcl))
      | allRight a' R b' =>
        exact (satClause_ofSRI _ (.allRight a' R b')).2
          (SRI.Proc.downI_models (isSHI_sriPart h) hJs _ (mem_sriPart.2 hcl))
      | chain body S =>
        exact (satClause_ofSRI _ (.chain body S)).2
          (SRI.Proc.downI_models (isSHI_sriPart h) hJs _ (mem_sriPart.2 hcl))
    exact hO D (SRI.Proc.downI (sriPart O) J) hD x hx
  · intro hE D _ I hI x hx
    have hU : models (SRI.Proc.upI (sriPart O) I) (encTransQ O).2 := by
      intro cl hcl
      rcases mem_encTransQ.1 hcl with h1 | h1
      · obtain ⟨cl', hcl', rfl⟩ := List.mem_map.1 h1
        exact (satClause_ofSRI _ cl').2 (SRI.Proc.upI_models (models_sriPart hI) _ hcl')
      · obtain ⟨cl0, h0, hl⟩ := List.mem_filterMap.1 h1
        have hs := hI _ h0
        cases cl0 <;> simp only [liftCount, Option.some.injEq, reduceCtorEq] at hl <;> subst hl
        · rename_i a' k R b'
          exact ((satClause_count_congr (I := I) (J := SRI.Proc.upI (sriPart O) I)
            (fun x y => by rw [SRI.Proc.upI_rt]) (fun y => (SRI.Proc.upI_old I a' y).symm)
            (fun y => (SRI.Proc.upI_old I b' y).symm) k).1).1 hs
        · rename_i a' k R b'
          exact ((satClause_count_congr (I := I) (J := SRI.Proc.upI (sriPart O) I)
            (fun x y => by rw [SRI.Proc.upI_rt]) (fun y => (SRI.Proc.upI_old I a' y).symm)
            (fun y => (SRI.Proc.upI_old I b' y).symm) k).2).1 hs
    have := hE D (SRI.Proc.upI (sriPart O) I) hU x ((SRI.Proc.upI_old I a x).2 hx)
    exact (SRI.Proc.upI_old I b x).1 this

end ContextCalculus.SRIQ.Proc

#print axioms ContextCalculus.SRIQ.Proc.encTransQ_isALCHIQ
#print axioms ContextCalculus.SRIQ.Proc.encTransQ_correct

import ContextCalculus.OWLFrontend.SRIReference

/-!
# Completeness of the SHI route

`owlSRIReference_complete`: on an ontology of the SHI part of the frontend
fragment (`OWL.Ontology.isSHI`) the SHI route publishes.

The route declines only when a `chain` clause of the translation fails
`chainOK`. The proof shows that every chain clause the translation emits is
an inclusion (body of length 1) or a transitivity clause `[R, R] ⊑ R`:

- class expressions emit no chain clause (`transExpr_noCh`);
- `EquivalentObjectProperties`, `InverseObjectProperties` and
  `SymmetricObjectProperty` emit inclusions, `TransitiveObjectProperty`
  emits `[R, R] ⊑ R`;
- `SubObjectPropertyOf` with one property emits an inclusion, and
  `SubObjectPropertyOf(ObjectPropertyChain(r r) r)` emits `[R, R] ⊑ R`
  because interning an IRI a second time returns the same index
  (`roleT_idem`);
- the conversion to `Fin` indices keeps the shape of a chain
  (`toFin_chainOK`).
-/

namespace ContextCalculus.OWLFrontend.SRIT

open ContextCalculus.OWL

/-! ## Interning twice -/

theorem EL_internR_of_rmap {a : IRI} {b : EL.St} {k : Nat} (h : b.rmap[a]? = some k) :
    EL.internR a b = (k, b) := by
  simp [EL.internR, h]

theorem internR_idem (a : IRI) (s : St) : internR a (internR a s).2 = internR a s := by
  have h := internR_rmap a s
  generalize internR a s = t at h ⊢
  simp only [internR, EL_internR_of_rmap h]

/-- The role term of `r` a second time is the same term, in the same state. -/
theorem roleT_idem (r : ObjProp) (s : St) : roleT r (roleT r s).2 = roleT r s := by
  simp only [roleT, internR_idem]

/-! ## No chain from class expressions -/

/-- `s'` has no chain clause that `s` lacks. -/
def NoCh (s s' : St) : Prop :=
  ∀ body S, SRI.Clause.chain body S ∈ s'.out → SRI.Clause.chain body S ∈ s.out

theorem NoCh.rfl {s : St} : NoCh s s := fun _ _ h => h

theorem NoCh.trans {s t u : St} (h₁ : NoCh s t) (h₂ : NoCh t u) : NoCh s u :=
  fun b S h => h₁ b S (h₂ b S h)

/-- The clause is not a chain. -/
def NotChain : SC → Prop
  | .chain _ _ => False
  | _ => True

theorem internC_noCh (a : IRI) (s : St) : NoCh s (internC a s).2 := fun _ _ h => h
theorem freshC_noCh (e : ClassExpr) (s : St) : NoCh s (freshC e s).2 := fun _ _ h => h
theorem roleT_noCh (r : ObjProp) (s : St) : NoCh s (roleT r s).2 := fun _ _ h => h

theorem roleTs_noCh : ∀ (rs : List ObjProp) (s : St) acc, NoCh s (roleTs rs s acc).2
  | [], _, _ => NoCh.rfl
  | r :: rs, s, _ => (roleT_noCh r s).trans (roleTs_noCh rs _ _)

theorem emit_noCh {c : SC} (hc : NotChain c) (s : St) : NoCh s (emit c s) := by
  intro b S h
  rcases List.mem_cons.1 h with h | h
  · subst h; exact absurd hc id
  · exact h

theorem emitEach_noCh {f : Nat → SC} (hf : ∀ k, NotChain (f k))
    (qs : List (ClassExpr × Nat)) (s : St) : NoCh s (emitEach f qs s) := by
  intro b S h
  rcases (mem_emitEach f qs s _).1 h with h | ⟨q, _, hq⟩
  · exact h
  · have hn := hf q.2
    rw [← hq] at hn
    exact absurd hn id

mutual

theorem transExpr_noCh : ∀ (E : ClassExpr) (p : Bool) (s : St), NoCh s (transExpr E p s).2
  | .cls a, _, s => by simp only [transExpr]; exact internC_noCh a s
  | .thing, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .nothing, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .and [], _, s => by simp only [transExpr]; exact NoCh.rfl
  | .or [], _, s => by simp only [transExpr]; exact NoCh.rfl
  | .and (c :: cs), false, s => by
      simp only [transExpr]
      exact (transList_noCh _ false s []).trans ((freshC_noCh _ _).trans
        (emit_noCh (by trivial) _))
  | .and (c :: cs), true, s => by
      simp only [transExpr]
      exact (transList_noCh _ true s []).trans ((freshC_noCh _ _).trans
        (emitEach_noCh (fun _ => by trivial) _ _))
  | .or (c :: cs), false, s => by
      simp only [transExpr]
      exact (transList_noCh _ false s []).trans ((freshC_noCh _ _).trans
        (emitEach_noCh (fun _ => by trivial) _ _))
  | .or (c :: cs), true, s => by
      simp only [transExpr]
      exact (transList_noCh _ true s []).trans ((freshC_noCh _ _).trans
        (emit_noCh (by trivial) _))
  | .not c, false, s => by
      simp only [transExpr]
      exact (transExpr_noCh c true s).trans ((freshC_noCh _ _).trans (emit_noCh (by trivial) _))
  | .not c, true, s => by
      simp only [transExpr]
      exact (transExpr_noCh c false s).trans ((freshC_noCh _ _).trans (emit_noCh (by trivial) _))
  | .some r c, false, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c false _).trans
        ((freshC_noCh _ _).trans (emit_noCh (by trivial) _)))
  | .some r c, true, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c true _).trans
        ((freshC_noCh _ _).trans (emit_noCh (by trivial) _)))
  | .all r c, false, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c false _).trans
        ((freshC_noCh _ _).trans ((freshC_noCh _ _).trans ((freshC_noCh _ _).trans
        ((emit_noCh (by trivial) _).trans ((emit_noCh (by trivial) _).trans (emit_noCh (by trivial) _)))))))
  | .all r c, true, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c true _).trans
        ((freshC_noCh _ _).trans (emit_noCh (by trivial) _)))

theorem transList_noCh : ∀ (cs : List ClassExpr) (p : Bool) (s : St) acc,
    NoCh s (transList cs p s acc).2
  | [], _, s, acc => by simp only [transList]; exact NoCh.rfl
  | c :: cs, p, s, acc => by
      simp only [transList]
      exact (transExpr_noCh c p s).trans (transList_noCh cs p _ _)

end

/-! ## Every emitted chain is an inclusion or a transitivity clause -/

/-- The shape `chainOK` checks, on `Nat` role terms. -/
def ChainShape (body : List RT) (S : RT) : Prop := body.length = 1 ∨ body = [S, S]

/-- Every chain clause of the state has the SHI shape. -/
def ChainsOK (s : St) : Prop := ∀ body S, SRI.Clause.chain body S ∈ s.out → ChainShape body S

theorem ChainsOK.of_noCh {s s' : St} (hs : ChainsOK s) (h : NoCh s s') : ChainsOK s' :=
  fun b S hm => hs b S (h b S hm)

theorem ChainsOK.emit {s : St} {body : List RT} {S : RT} (hs : ChainsOK s)
    (h : ChainShape body S) : ChainsOK (emit (.chain body S) s) := by
  intro b S' hm
  rcases List.mem_cons.1 hm with hm | hm
  · cases hm; exact h
  · exact hs b S' hm

theorem roleTs_length (rs : List ObjProp) (s : St) : (roleTs rs s []).1.length = rs.length :=
  (roleTs_ok' rs s).length_eq.symm

theorem transAxiom_chainsOK {s : St} (hs : ChainsOK s) (ax : Axiom) (hax : ax.isSHI = true) :
    ChainsOK (transAxiom s ax) := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom]
      exact hs.of_noCh ((transExpr_noCh c false s).trans ((transExpr_noCh d true _).trans
        (emit_noCh (by trivial) _)))
  | equivalentClasses cs =>
      simp only [transAxiom]
      have h := hs.of_noCh ((transList_noCh cs false s []).trans (transList_noCh cs true _ []))
      intro b S hm
      rcases (mem_emitEquiv _ _ _ _).1 hm with hm | ⟨_, _, _, _, _, hc⟩
      · exact h b S hm
      · cases hc
  | disjointClasses cs =>
      simp only [transAxiom]
      have h := hs.of_noCh (transList_noCh cs false s [])
      intro b S hm
      rcases (mem_emitDisjoint _ _ _).1 hm with hm | ⟨_, _, _, hc⟩
      · exact h b S hm
      · cases hc
  | domain r c | range r c =>
      simp only [transAxiom]
      exact hs.of_noCh ((roleT_noCh r s).trans ((transExpr_noCh c true _).trans
        (emit_noCh (by trivial) _)))
  | subObjectPropertyOf rs r =>
      simp only [transAxiom]
      have h := hs.of_noCh ((roleTs_noCh rs s []).trans (roleT_noCh r _))
      refine h.emit ?_
      simp only [Axiom.isSHI, Bool.or_eq_true, beq_iff_eq] at hax
      rcases hax with hl | rfl
      · exact Or.inl (by rw [roleTs_length, hl])
      · right
        simp only [roleTs, roleT_idem, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append]
  | equivalentObjectProperties rs =>
      simp only [transAxiom]
      have h := hs.of_noCh (roleTs_noCh rs s [])
      intro b S hm
      rcases (mem_emitRoleEquiv _ _ _).1 hm with hm | ⟨_, _, _, _, _, hc⟩
      · exact h b S hm
      · cases hc; exact Or.inl rfl
  | inverseObjectProperties r r' =>
      simp only [transAxiom]
      exact ((hs.of_noCh ((roleT_noCh r s).trans (roleT_noCh r' _))).emit (Or.inl rfl)).emit
        (Or.inl rfl)
  | transitive r =>
      simp only [transAxiom]
      exact (hs.of_noCh (roleT_noCh r s)).emit (Or.inr rfl)
  | symmetric r =>
      simp only [transAxiom]
      exact (hs.of_noCh (roleT_noCh r s)).emit (Or.inl rfl)
  | declareClass _ | declareObjectProperty _ =>
      simp only [transAxiom]; exact hs

theorem foldl_trans_chainsOK : ∀ (axs : List Axiom) (s : St), ChainsOK s →
    (∀ ax ∈ axs, ax.isSHI = true) → ChainsOK (axs.foldl transAxiom s)
  | [], _, hs, _ => hs
  | ax :: axs, _, hs, h =>
      foldl_trans_chainsOK axs _ (transAxiom_chainsOK hs ax (h ax List.mem_cons_self))
        (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem start_chainsOK (b : EL.St) : ChainsOK (start b) := by
  intro body S hm
  simp [start] at hm

/-! ## The conversion to `Fin` indices keeps the shape -/

theorem toFin_chainOK {n m : Nat} {c : SC} {c' : SRI.Clause (Fin n) (Fin m)}
    (hc : ∀ body S, c = .chain body S → ChainShape body S) (h : toFin n m c = some c') :
    chainOK c' = true := by
  cases c' with
  | chain b' S' =>
    cases c with
    | gci body head =>
        simp only [toFin] at h
        split at h <;> simp at h
    | exRight a R d =>
        simp only [toFin] at h
        split at h
        · split at h
          · cases hR : finRT m R <;> simp [hR] at h
          · simp at h
        · simp at h
    | allRight a R d =>
        simp only [toFin] at h
        split at h
        · split at h
          · cases hR : finRT m R <;> simp [hR] at h
          · simp at h
        · simp at h
    | chain body S =>
        simp only [toFin] at h
        split at h
        · rename_i b S'' hb hS
          simp only [Option.some.injEq, SRI.Clause.chain.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨L, rfl, hL⟩ := finRTs_spec m body [] b hb
          try simp only [List.reverse_nil, List.nil_append]
          simp only [chainOK, Bool.or_eq_true, beq_iff_eq]
          rcases hc body S rfl with hl | rfl
          · exact Or.inl (by rw [← hL.length_eq, hl])
          · right
            cases hL with
            | cons h₁ hL => cases hL with
              | cons h₂ hL =>
                cases hL
                rw [hS] at h₁ h₂
                cases h₁; cases h₂; rfl
        · simp at h
  | _ => rfl

end ContextCalculus.OWLFrontend.SRIT

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SRIT

/-- On an ontology of the SHI part, every chain clause of the translation
passes the route's check. -/
theorem translateSRI_isSHIB {O : OWL.Ontology} {requested : List OWL.IRI} {T : SRITranslation}
    (hSHI : O.isSHI = true) (h : translateSRI O requested = some T) :
    isSHIB T.ontology = true := by
  simp only [translateSRI] at h
  split at h
  case isFalse => exact absurd h (by simp)
  split at h
  case isFalse => exact absurd h (by simp)
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨b, _, _, _, hF⟩ := SRIT.run_spec O requested
  have hok : ChainsOK (SRIT.run O requested).1 := by
    rw [← hF]
    refine foldl_trans_chainsOK O.axioms _ (start_chainsOK b) ?_
    simpa [OWL.Ontology.isSHI, List.all_eq_true] using hSHI
  simp only [isSHIB, List.all_eq_true, List.mem_filterMap]
  rintro c' ⟨c, hc, hfin⟩
  refine toFin_chainOK (fun body S hcs => ?_) hfin
  subst hcs
  exact hok body S (List.mem_reverse.1 hc)

/-- On every ontology of the SHI part the SHI route publishes, for every
requested list. -/
theorem owlSRIReference_complete {O : OWL.Ontology} (requested : List OWL.IRI)
    (h : O.isSHI = true) : (owlSRIReference O requested).isSome = true := by
  have hs := translateSRI_isSome (requested := requested) (OWL.Ontology.isSRI_of_isSHI h)
  unfold owlSRIReference
  split
  · next hnone => rw [hnone] at hs; exact absurd hs (by simp)
  · next T hT => simp [translateSRI_isSHIB h hT]

#print axioms owlSRIReference_complete

end ContextCalculus.OWLFrontend

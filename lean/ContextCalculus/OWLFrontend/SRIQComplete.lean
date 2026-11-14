import ContextCalculus.OWLFrontend.SRIQReference
import ContextCalculus.OWLFrontend.SRIComplete

/-!
# Completeness of the SHIQ route

`owlSHIQReference_complete`: on an ontology of the SHIQ part of the
frontend fragment (`OWL.Ontology.isSHIQ`) whose translation passes the
simple-role check (`SHIQSimple`) the SHIQ route publishes.

The route declines when a `chain` clause of the translation fails
`chainOKQ` or when the simple-role check `simpleB` fails. The proof that
the first never happens on SHIQ is the one of `SRIComplete`: class
expressions and the two functionality axioms emit no chain clause
(`transExpr_noCh`), the property axioms of SHI emit inclusions and
transitivity clauses, and the conversion to `Fin` indices keeps the shape
of a chain (`toFin_chainOK`). The second is the OWL 2 DL simple-role
restriction, stated on the translated clauses (`SHIQSimple`).
-/

namespace ContextCalculus.OWLFrontend.SRIQT

open ContextCalculus.OWL

/-! ## Interning twice -/

open SRIT (EL_internR_of_rmap finRTs_spec finRT ChainShape)

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
  ∀ body S, SRIQ.Clause.chain body S ∈ s'.out → SRIQ.Clause.chain body S ∈ s.out

theorem NoCh.rfl {s : St} : NoCh s s := fun _ _ h => h

theorem NoCh.trans {s t u : St} (h₁ : NoCh s t) (h₂ : NoCh t u) : NoCh s u :=
  fun b S h => h₁ b S (h₂ b S h)

/-- The clause is not a chain. -/
def NotChain : QC → Prop
  | .chain _ _ => False
  | _ => True

theorem internC_noCh (a : IRI) (s : St) : NoCh s (internC a s).2 := fun _ _ h => h
theorem freshC_noCh (e : ClassExpr) (s : St) : NoCh s (freshC e s).2 := fun _ _ h => h
theorem roleT_noCh (r : ObjProp) (s : St) : NoCh s (roleT r s).2 := fun _ _ h => h

theorem roleTs_noCh : ∀ (rs : List ObjProp) (s : St) acc, NoCh s (roleTs rs s acc).2
  | [], _, _ => NoCh.rfl
  | r :: rs, s, _ => (roleT_noCh r s).trans (roleTs_noCh rs _ _)

theorem emit_noCh {c : QC} (hc : NotChain c) (s : St) : NoCh s (emit c s) := by
  intro b S h
  rcases List.mem_cons.1 h with h | h
  · subst h; exact absurd hc id
  · exact h

theorem emitEach_noCh {f : Nat → QC} (hf : ∀ k, NotChain (f k))
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
  | .oneOf _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .hasValue _ _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .hasSelf _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .min 0 _ _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .min (k + 1) r c, false, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c false _).trans ((freshC_noCh _ _).trans
        ((freshC_noCh _ _).trans ((emit_noCh (by trivial) _).trans (emit_noCh (by trivial) _)))))
  | .min (k + 1) r c, true, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c true _).trans
        ((freshC_noCh _ _).trans (emit_noCh (by trivial) _)))
  | .max k r c, false, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c true _).trans ((freshC_noCh _ _).trans
        ((freshC_noCh _ _).trans ((emit_noCh (by trivial) _).trans (emit_noCh (by trivial) _)))))
  | .max k r c, true, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c false _).trans
        ((freshC_noCh _ _).trans (emit_noCh (by trivial) _)))
  | .exact 0 r c, false, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c true _).trans ((freshC_noCh _ _).trans
        ((freshC_noCh _ _).trans ((emit_noCh (by trivial) _).trans (emit_noCh (by trivial) _)))))
  | .exact (k + 1) r c, false, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c false _).trans
        ((transExpr_noCh c true _).trans ((freshC_noCh _ _).trans ((freshC_noCh _ _).trans
        ((freshC_noCh _ _).trans ((emit_noCh (by trivial) _).trans ((emit_noCh (by trivial) _).trans
        (emit_noCh (by trivial) _))))))))
  | .exact k r c, true, s => by
      simp only [transExpr]
      exact (roleT_noCh r s).trans ((transExpr_noCh c true _).trans
        ((transExpr_noCh c false _).trans ((freshC_noCh _ _).trans
        ((emit_noCh (by trivial) _).trans (emit_noCh (by trivial) _)))))
  | .dataSome _ _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .dataAll _ _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .dataHasValue _ _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .dataMin _ _ _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .dataMax _ _ _, _, s => by simp only [transExpr]; exact NoCh.rfl
  | .dataExact _ _ _, _, s => by simp only [transExpr]; exact NoCh.rfl

theorem transList_noCh : ∀ (cs : List ClassExpr) (p : Bool) (s : St) acc,
    NoCh s (transList cs p s acc).2
  | [], _, s, acc => by simp only [transList]; exact NoCh.rfl
  | c :: cs, p, s, acc => by
      simp only [transList]
      exact (transExpr_noCh c p s).trans (transList_noCh cs p _ _)

end

/-! ## Every emitted chain is an inclusion or a transitivity clause -/

/-- Every chain clause of the state has the SHI shape. -/
def ChainsOK (s : St) : Prop := ∀ body S, SRIQ.Clause.chain body S ∈ s.out → ChainShape body S

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

theorem transAxiom_chainsOK {s : St} (hs : ChainsOK s) (ax : Axiom) (hax : ax.isSHIQ = true) :
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
      simp only [Axiom.isSHIQ, Axiom.isSHI, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hax
      rcases hax.1.1 with hl | rfl
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
  | declareDataProperty _ => simp only [transAxiom]; exact hs
  | declareNamedIndividual _ => simp only [transAxiom]; exact hs
  | declareDatatype _ => simp only [transAxiom]; exact hs
  | declareAnnotationProperty _ => simp only [transAxiom]; exact hs
  | disjointUnion _ _ => simp only [transAxiom]; exact hs
  | disjointObjectProperties _ => simp only [transAxiom]; exact hs
  | functional r | inverseFunctional r =>
      simp only [transAxiom]
      exact hs.of_noCh ((roleT_noCh r s).trans (emit_noCh (by trivial) _))
  | reflexive _ => simp only [transAxiom]; exact hs
  | irreflexive _ => simp only [transAxiom]; exact hs
  | asymmetric _ => simp only [transAxiom]; exact hs
  | subDataPropertyOf _ _ => simp only [transAxiom]; exact hs
  | equivalentDataProperties _ => simp only [transAxiom]; exact hs
  | disjointDataProperties _ => simp only [transAxiom]; exact hs
  | dataDomain _ _ => simp only [transAxiom]; exact hs
  | dataRange _ _ => simp only [transAxiom]; exact hs
  | functionalData _ => simp only [transAxiom]; exact hs
  | datatypeDefinition _ _ => simp only [transAxiom]; exact hs
  | hasKey _ _ _ => simp only [transAxiom]; exact hs
  | sameIndividual _ => simp only [transAxiom]; exact hs
  | differentIndividuals _ => simp only [transAxiom]; exact hs
  | classAssertion _ _ => simp only [transAxiom]; exact hs
  | objectPropertyAssertion _ _ _ => simp only [transAxiom]; exact hs
  | negativeObjectPropertyAssertion _ _ _ => simp only [transAxiom]; exact hs
  | dataPropertyAssertion _ _ _ => simp only [transAxiom]; exact hs
  | negativeDataPropertyAssertion _ _ _ => simp only [transAxiom]; exact hs

theorem foldl_trans_chainsOK : ∀ (axs : List Axiom) (s : St), ChainsOK s →
    (∀ ax ∈ axs, ax.isSHIQ = true) → ChainsOK (axs.foldl transAxiom s)
  | [], _, hs, _ => hs
  | ax :: axs, _, hs, h =>
      foldl_trans_chainsOK axs _ (transAxiom_chainsOK hs ax (h ax List.mem_cons_self))
        (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem start_chainsOK (b : EL.St) : ChainsOK (start b) := by
  intro body S hm
  simp [start] at hm

/-! ## The conversion to `Fin` indices keeps the shape -/

theorem toFin_chainOK {n m : Nat} {c : QC} {c' : SRIQ.Clause (Fin n) (Fin m)}
    (hc : ∀ body S, c = .chain body S → ChainShape body S) (h : toFin n m c = some c') :
    chainOKQ c' = true := by
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
    | atLeast a k R d =>
        simp only [toFin] at h
        split at h
        · split at h
          · cases hR : finRT m R <;> simp [hR] at h
          · simp at h
        · simp at h
    | atMost a k R d =>
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
          simp only [Option.some.injEq, SRIQ.Clause.chain.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨L, rfl, hL⟩ := finRTs_spec m body [] b hb
          try simp only [List.reverse_nil, List.nil_append]
          simp only [chainOKQ, Bool.or_eq_true, beq_iff_eq]
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

end ContextCalculus.OWLFrontend.SRIQT

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SRIQT

/-- On an ontology of the SHIQ part, every chain clause of the translation
passes the route's chain check. -/
theorem translateSRIQ_chainsOK {O : OWL.Ontology} {requested : List OWL.IRI}
    {T : SRIQTranslation} (hSHIQ : O.isSHIQ = true) (h : translateSRIQ O requested = some T) :
    T.ontology.all chainOKQ = true := by
  simp only [translateSRIQ] at h
  split at h
  case isFalse hn => exact absurd hSHIQ hn
  split at h
  case isFalse => exact absurd h (by simp)
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨b, _, _, _, hF⟩ := SRIQT.run_spec O requested
  have hok : ChainsOK (SRIQT.run O requested).1 := by
    rw [← hF]
    refine foldl_trans_chainsOK O.axioms _ (start_chainsOK b) ?_
    simpa [OWL.Ontology.isSHIQ, List.all_eq_true] using hSHIQ
  simp only [List.all_eq_true, List.mem_filterMap]
  rintro c' ⟨c, hc, hfin⟩
  refine toFin_chainOK (fun body S hcs => ?_) hfin
  subst hcs
  exact hok body S (List.mem_reverse.1 hc)

/-- The simple-role restriction of OWL 2 DL, checked on the translated
clauses: no transitive role lies below a role of a counting clause or below
its inverse (`simpleB`). -/
def SHIQSimple (O : OWL.Ontology) (requested : List OWL.IRI) : Prop :=
  ∀ T, translateSRIQ O requested = some T → simpleB T.ontology = true

/-- On every ontology of the SHIQ part that passes the simple-role check,
the SHIQ route publishes. -/
theorem owlSHIQReference_complete {O : OWL.Ontology} (requested : List OWL.IRI)
    (h : O.isSHIQ = true) (hs : SHIQSimple O requested) :
    (owlSHIQReference O requested).isSome = true := by
  have hT := translateSRIQ_isSome (requested := requested) h
  unfold owlSHIQReference
  split
  · next hnone => rw [hnone] at hT; exact absurd hT (by simp)
  · next T hT' =>
      simp [isSHIQB, translateSRIQ_chainsOK h hT', hs T hT']

/-- The SHIQ route publishes exactly on the SHIQ part with the simple-role
check passed: it declines on every other ontology. -/
theorem owlSHIQReference_isSome_iff {O : OWL.Ontology} (requested : List OWL.IRI) :
    (owlSHIQReference O requested).isSome = true ↔ O.isSHIQ = true ∧ SHIQSimple O requested := by
  constructor
  · intro h
    unfold owlSHIQReference at h
    split at h
    · simp at h
    · next T hT =>
        split at h
        · next hS =>
            refine ⟨?_, fun T' hT' => ?_⟩
            · simp only [translateSRIQ] at hT
              split at hT
              · assumption
              · simp at hT
            · rw [hT] at hT'
              cases hT'
              simp only [isSHIQB, Bool.and_eq_true] at hS
              exact hS.2
        · simp at h
  · rintro ⟨h, hs⟩
    exact owlSHIQReference_complete requested h hs

#print axioms translateSRIQ_chainsOK
#print axioms owlSHIQReference_complete
#print axioms owlSHIQReference_isSome_iff

end ContextCalculus.OWLFrontend

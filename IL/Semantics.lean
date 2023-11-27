import IL.Variable
import IL.Formula
import IL.Syntax
import Mathlib.Data.Set.Basic

set_option autoImplicit false

structure KripkeModel (W : Type) where
  R : W → W → Prop
  V : Var → W → Prop
  refl (w : W) : R w w
  trans (w1 w2 w3 : W) : R w1 w2 -> R w2 w3 -> R w1 w3
  monotonicity (v : Var) (w1 w2 : W) : R w1 w2 -> V v w1 -> V v w2

def val {W : Type} (M : KripkeModel W) (w : W) : Formula -> Prop
| Formula.var p => M.V p w
| ⊥ => False
| ϕ ∧∧ ψ => val M w ϕ /\ val M w ψ
| ϕ ∨∨ ψ => val M w ϕ \/ val M w ψ
| (Formula.implication ϕ ψ) =>
  forall (w' : W), M.R w w' /\ val M w' ϕ -> val M w' ψ

def val_neg {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula) : Prop :=
  forall (w' : W), M.R w w' -> ¬ val M w' ϕ

def forces {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula) : Prop :=
  val M w ϕ

def true_in_world {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula) : Prop :=
  forces M w ϕ

def valid_in_model {W : Type} (M : KripkeModel W) (ϕ : Formula) : Prop :=
  forall (w : W), forces M w ϕ

def valid (ϕ : Formula) : Prop :=
  forall (W : Type) (M : KripkeModel W) (w : W), forces M w ϕ

def model_forces_set {W : Type} (M : KripkeModel W) (Γ : Set Formula) (w : W) : Prop :=
  forall (ϕ : Formula), ϕ ∈ Γ -> forces M w ϕ

def sem_conseq (Γ : Set Formula) (ϕ : Formula) : Prop :=
  forall (W : Type) (M : KripkeModel W) (w : W),
  model_forces_set M Γ w -> forces M w ϕ
infix:50 " ⊨ " => sem_conseq

def set_forces_set (Γ Δ : Set Formula) : Prop :=
  forall (ϕ : Formula), ϕ ∈ Δ -> Γ ⊨ ϕ

theorem axioms_valid (ϕ : Formula) (ax : Axiom ϕ) : valid ϕ :=
by
  simp [valid, forces]; intros W M w
  rcases ax
  · intros w' Hww'val
    apply Or.elim (And.right Hww'val)
    repeat {intros; assumption}
  · intros w' Hww'val
    apply And.intro (And.right Hww'val)
    apply And.right Hww'val
  · intros w' Hww'val
    apply Or.inl (And.right Hww'val)
  · intros w' Hww'val
    apply And.left (And.right Hww'val)
  · intros w' Hww'val
    rcases And.right Hww'val with Hvp | Hpsi
    · apply Or.inr Hvp
    · apply Or.inl Hpsi
  · intros w' Hww'val
    apply And.intro (And.right (And.right Hww'val)) (And.left (And.right Hww'val))
  · intros w' Hww'val
    exfalso
    apply And.right Hww'val

theorem elem_sem_conseq (Γ : Set Formula) (ϕ : Formula) : ϕ ∈ Γ -> Γ ⊨ ϕ :=
  by { simp [sem_conseq, model_forces_set]; intros Helem _ _ _  Ha; apply Ha; assumption }

theorem subseteq_sem_conseq (Γ Δ : Set Formula) (ϕ : Formula) : Δ ⊆ Γ -> Δ ⊨ ϕ -> Γ ⊨ ϕ :=
  by { simp [sem_conseq, model_forces_set]; intros Hsubseteq Hdelta _ _ _ Ha; apply Hdelta;
       intros _ Ha'; apply Ha; apply Set.mem_of_mem_of_subset Ha' Hsubseteq; }

theorem valid_sem_conseq (Γ : Set Formula) (ϕ : Formula) : valid ϕ -> Γ ⊨ ϕ :=
  by { simp [sem_conseq, model_forces_set]; intros Hvalid _ _ _ _; apply Hvalid; }

theorem set_conseq (Γ Δ : Set Formula) (ϕ : Formula) : set_forces_set Γ Δ -> Δ ⊨ ϕ -> Γ ⊨ ϕ :=
  by { simp [set_forces_set, sem_conseq, model_forces_set]; intros Hsetforces Hdelta _ M w Ha;
       apply Hdelta; intros; apply Hsetforces; assumption' }

theorem set_conseq_iff (Γ Δ : Set Formula) (ϕ : Formula) :
  set_forces_set Γ Δ -> set_forces_set Δ Γ -> (Δ ⊨ ϕ <-> Γ ⊨ ϕ) :=
  by {
       intros Hsetforcesgd Hsetforcesdg; apply Iff.intro
       · exact set_conseq _ _ _ Hsetforcesgd
       · exact set_conseq _ _ _ Hsetforcesdg
     }

theorem monotonicity_val (W : Type) (M : KripkeModel W) (w1 w2 : W) (ϕ : Formula) :
  M.R w1 w2 -> forces M w1 ϕ -> forces M w2 ϕ :=
  by
    simp [forces]; intros Hw1w2 Hforces
    induction ϕ with
    | var p => apply M.monotonicity p w1 w2 Hw1w2 Hforces
    | bottom => simp [val] at Hforces
    | and ψ χ ih1 ih2 => apply And.intro
                         · eapply ih1 (And.left Hforces)
                         · eapply ih2 (And.right Hforces)
    | or ψ χ ih1 ih2 => rcases Hforces with Hforcespsi | Hforceschi
                        · apply Or.inl; eapply ih1; assumption
                        · apply Or.inr; eapply ih2; assumption
    | implication ψ χ _ _ => simp [val]
                             simp [val] at Hforces
                             intros w3 Hw2w3 Hvalw3psi
                             have Hw1w3 : M.R w1 w3 := (M.trans w1 w2 w3 Hw1w2 Hw2w3)
                             apply Hforces _  Hw1w3 Hvalw3psi

theorem soundness (Γ : Set Formula) (ϕ : Formula) : Γ ⊢ ϕ -> Γ ⊨ ϕ :=
  by
    intros Htheorem
    induction Htheorem with
    | premise Hvp => apply elem_sem_conseq; assumption
    | contractionDisj | contractionConj | weakeningDisj | weakeningConj
      | permutationDisj | permutationConj | exfalso =>
      apply valid_sem_conseq; apply axioms_valid; constructor
    | modusPonens _ _ ih1 ih2 => simp [sem_conseq, forces, val] at ih2
                                 intros _ M _ Hmodelforces
                                 eapply ih2
                                 · assumption
                                 · apply M.refl
                                 · apply ih1; assumption
    | syllogism H1 H2 ih1 ih2 => simp [sem_conseq, forces, val] at *
                                 intros _ _ _ Hmodelforces _ Hr _
                                 eapply ih2
                                 · assumption
                                 · assumption
                                 · apply ih1; apply Hmodelforces; assumption'
    | exportation H ih => simp [sem_conseq, forces, val] at *
                          intros _ M w1 Hmodelforces w2 Hw1w2 _ w3 Hw2w3 _
                          eapply ih
                          · assumption
                          · apply M.trans w1 w2 w3 Hw1w2 Hw2w3
                          · eapply monotonicity_val; assumption'
                          · assumption
    | importation H ih => simp [sem_conseq, forces, val] at *
                          intros _ M w1 Hmodelforces w2 Hw1w2 _ _
                          eapply ih
                          · assumption
                          · assumption
                          · assumption
                          · apply M.refl
                          · assumption
    | expansion H ih => simp [sem_conseq, forces, val] at *
                        intros _ M w1 Hmodelforces w2 Hw1w2 Hvalor
                        rcases Hvalor with Hvalchi | Hvalvp
                        · apply Or.inl; assumption
                        · apply Or.inr
                          eapply ih; assumption'

def canonicalModel : KripkeModel (Proof.setDisjTh) :=
  {
   R := fun (Γ Δ : Proof.setDisjTh) => Γ.1 ⊆ Δ.1,
   V := fun (v : Var) (Γ : Proof.setDisjTh) => Formula.var v ∈ Γ.1,
   refl := fun (Γ : Proof.setDisjTh) => Set.Subset.rfl
   trans := fun (Γ Δ Φ) => Set.Subset.trans
   monotonicity := fun (v Γ Δ) => by intros; apply Set.mem_of_mem_of_subset; assumption'
  }

theorem main_sem_lemma_right (Γ : Proof.setDisjTh) (ϕ : Formula) :
  ϕ ∈ Γ.1 -> forces canonicalModel Γ ϕ :=
  by
    simp [forces]
    intros Helem
    let Hgamma := Γ
    rcases Γ with ⟨Γ, ⟨Hded, ⟨Hcons, Hdisjnonempty⟩⟩⟩
    apply Nonempty.elim Hdisjnonempty
    intros Hdisj
    revert Γ
    induction ϕ with
    | var _ => intros; assumption
    | bottom => intros Γ _ Hcons _ Helem _ _; have Hpremise : Γ ⊢ ⊥ := by apply Proof.premise Helem
                apply Hcons; assumption
    | and ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Helem _ Hdisj
                         have Hconj : Γ ⊢ ψ ∧∧ χ := by apply Proof.premise Helem
                         let Hpsi := Proof.modusPonens Hconj Proof.weakeningConj
                         let Hchi := Proof.modusPonens Hconj Proof.conjElimRight
                         have Hpsielem : ψ ∈ Γ := by apply Hded ψ; assumption
                         have Hchielem : χ ∈ Γ := by apply Hded χ; assumption
                         apply And.intro (ih1 Γ Hded Hcons Hproofdisj Hpsielem Hdisj)
                                         (ih2 Γ Hded Hcons Hproofdisj Hchielem Hdisj)
    | or ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Helem HsetDisj Hdisj'
                        unfold Proof.disjunctive at Hdisj'
                        have Hdisjspec : Γ ⊢ ψ ∨∨ χ := by apply Proof.premise Helem
                        have Hdisj : Sum (Γ ⊢ ψ) (Γ ⊢ χ) := by apply Hdisj' ψ χ Hdisjspec
                        rcases Hdisj with Hpsi | Hchi
                        · have Hpsi : ψ ∈ Γ := by apply Hded ψ; assumption
                          have Hih1 : Γ ⊨ ψ := by apply elem_sem_conseq; assumption
                          apply Or.inl
                          apply ih1; assumption'
                        · have Hpsi : χ ∈ Γ := by apply Hded χ; assumption
                          have Hih2 : Γ ⊨ χ := by apply elem_sem_conseq; assumption
                          apply Or.inr
                          apply ih2; assumption'
    | implication ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Helem _ Hdisj
                                 simp [val]
                                 intros Φ Φdisj Hincl Hpsi
                                 have Helem' : (ψ ⇒ χ) ∈ Φ :=
                                  by eapply Set.mem_of_mem_of_subset Helem Hincl
                                 rcases Φdisj with ⟨Hded', ⟨Hcons', Hdisj'⟩⟩
                                 have Hpremise1 : Φ ⊢ ψ ⇒ χ := by apply Proof.premise Helem'
                                 · by_cases ψ ∈ Φ
                                   · have Hpremise2 : Φ ⊢ ψ := by apply Proof.premise h
                                     have Hchi : Φ ⊢ χ := by apply Proof.modusPonens Hpremise2 Hpremise1
                                     have Hchielem : χ ∈ Φ := by apply Hded' χ; assumption
                                     let Hih2 := ih2 Φ Hded' Hcons' Hdisj' Hchielem
                                     apply Nonempty.elim Hdisj'; assumption
                                   · sorry

theorem main_sem_lemma_left (Γ : Proof.setDisjTh) (ϕ : Formula) :
  forces canonicalModel Γ ϕ -> ϕ ∈ Γ.1 :=
  by
    simp [forces]
    intros Hval
    let Hgamma := Γ
    rcases Γ with ⟨Γ, ⟨Hded, ⟨Hcons, Hdisjnonempty⟩⟩⟩
    apply Nonempty.elim Hdisjnonempty
    intros Hdisj
    revert Γ
    induction ϕ with
    | var _ => intros; assumption
    | bottom => simp [val]
    | and ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Hval _ Hdisj
                         rcases Hval with ⟨Hvalpsi, Hvalchi⟩
                         let Hpsi := Proof.premise (ih1 Γ Hded Hcons Hproofdisj Hvalpsi Hdisj)
                         let Hchi := Proof.premise (ih2 Γ Hded Hcons Hproofdisj Hvalchi Hdisj)
                         let H := Proof.conjIntroRule Hpsi Hchi
                         apply Hded; assumption
    | or ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Hval _ Hdisj
                        rcases Hval with Hvalpsi | Hvalchi
                        · let Hpsi := Proof.premise (ih1 Γ Hded Hcons Hproofdisj Hvalpsi Hdisj)
                          let Hmp := @Proof.modusPonens Γ ψ (ψ ∨∨ χ) Hpsi Proof.weakeningDisj
                          apply Hded; assumption
                        · let Hchi := Proof.premise (ih2 Γ Hded Hcons Hproofdisj Hvalchi Hdisj)
                          let Hmp := @Proof.modusPonens Γ χ (ψ ∨∨ χ) Hchi Proof.disjIntroRight
                          apply Hded; assumption
    | implication ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Hval _ _
                                 simp [val] at Hval
                                 by_cases (ψ ⇒ χ) ∈ Γ
                                 · assumption
                                 · have Hcons' : @Proof.consistentPair (Γ ∪ {ψ}) {χ} :=
                                    by
                                      by_cases Proof.consistentPair
                                      · assumption
                                      · exfalso
                                        unfold Proof.consistentPair at h
                                        push_neg at h
                                        rcases h with ⟨Φ, Ω, h, h', h''⟩
                                        rcases h'' with ⟨w, _⟩
                                        rw [Set.subset_singleton_iff_eq] at h'
                                        rcases h' with Hempty | Hsingleton
                                        · rw [Finset.coe_eq_empty] at Hempty
                                          rw [Hempty] at w
                                          simp at w
                                          let Hexpthded := Proof.deductionTheorem_right_ind (Proof.exportation_ind w)
                                          rw [Set.empty_union] at Hexpthded
                                          unfold Proof.consistent at Hcons
                                          apply Hcons
                                          rw [Finset.toList_toFinset] at Hexpthded
                                          have Hunionconseq : Γ ∪ {ψ} ⊢ ⊥ :=
                                            by apply Proof.subset_proof; assumption'
                                          let Hthded := Proof.deductionTheorem_left Hunionconseq
                                          let Hsyllog := @Proof.syllogism Γ ψ ⊥ χ Hthded Proof.exfalso
                                          let Hdisjspec := Hded (ψ⇒χ) Hsyllog
                                          contradiction
                                        · rw [Finset.coe_eq_singleton] at Hsingleton
                                          rw [Hsingleton] at w
                                          simp at w
                                          let Hsyllog := Proof.syllogism w Proof.orFalse
                                          let Hexp := Proof.exportation_ind Hsyllog
                                          let Hthded := Proof.deductionTheorem_right_ind Hexp
                                          rw [Set.empty_union] at Hthded
                                          rw [Finset.toList_toFinset] at Hthded
                                          have Hunionconseq : Γ ∪ {ψ} ⊢ χ :=
                                            by apply Proof.subset_proof; assumption'
                                          let Hthded := Proof.deductionTheorem_left Hunionconseq
                                          let Hdisjspec := Hded (ψ⇒χ) Hthded
                                          contradiction
                                   let Haux := @Proof.consistent_incl_complete (Γ ∪ {ψ}) {χ} Hcons'
                                   rcases Haux with ⟨Φ, ⟨Ω, ⟨Hincl1, ⟨Hincl2, Hcompl⟩⟩⟩⟩
                                   have Hdisjth' : @Proof.disjunctiveTheory Φ :=
                                    by apply Proof.complete_pair_fst_disj Hcompl
                                   let Hdisjth'' := Hdisjth'
                                   rcases Hdisjth' with ⟨Hcons'', ⟨Hded', Hdisj'⟩⟩
                                   have Hincl : Γ ⊆ Φ :=
                                    by
                                      have Hunionleft : Γ ⊆ Γ ∪ {ψ} := by apply Set.subset_union_left
                                      apply Set.Subset.trans Hunionleft Hincl1
                                   let Hvalspec := Hval Φ Hdisjth'' Hincl
                                   have Hdisjthphi : @Proof.disjunctiveTheory Φ :=
                                      by apply Proof.complete_pair_fst_disj; assumption
                                   let Hdisjthphi' : Proof.setDisjTh := ⟨Φ, by assumption⟩
                                   have Hphipsi : val canonicalModel { val := Φ, property := Hdisjth'' } ψ :=
                                    by
                                      by_cases val canonicalModel { val := Φ, property := Hdisjth'' } ψ
                                      · assumption
                                      · let Hih1 := @ih1 Φ Hcons'' Hded' Hdisj'
                                        simp at Hih1
                                        have Haux : ψ ∈ Φ :=
                                          by
                                            rw [Set.union_subset_iff] at Hincl1
                                            let Hsingleton := And.right Hincl1
                                            rw [Set.singleton_subset_iff] at Hsingleton
                                            assumption
                                        let Hmainsem := main_sem_lemma_right Hdisjthphi' ψ Haux
                                        assumption
                                   have Hphinotchi : val canonicalModel { val := Φ, property := Hdisjth'' } χ -> False :=
                                    by
                                      have Hdisj'' : @Proof.disjunctive Φ :=
                                        by apply Classical.choice Hdisj'
                                      by_cases val canonicalModel { val := Φ, property := Hdisjth'' } χ
                                      · let Hih2 := @ih2 Φ Hcons'' Hded' Hdisj' h Hdisj''
                                        simp at Hih2
                                        unfold Proof.completePair at Hcompl
                                        rcases Hcompl with ⟨_, Hvp⟩
                                        let Hvpchi := Hvp χ
                                        have Hchielem : χ ∈ Ω :=
                                          by rw [Set.singleton_subset_iff] at Hincl2; assumption
                                        rcases Hvpchi with Hphi | Homega
                                        · rcases Hphi; contradiction
                                        · rcases Homega; contradiction
                                      · assumption
                                   let Hvalspecaux := Hvalspec Hphipsi
                                   contradiction

theorem completeness {ϕ : Formula} {Γ : Set Formula} : Γ ⊨ ϕ -> Nonempty (Γ ⊢ ϕ) :=
  by
    intros Hsem
    by_cases (Nonempty (Γ ⊢ ϕ))
    · assumption'
    · have Hcons : @Proof.consistentPair Γ {ϕ} :=
        by
          simp [Proof.consistentPair]
          intros Φ Ω Hincl1 Homega H
          have Homega : Ω = ∅ ∨ Ω = {ϕ} :=
            by
              by_cases Ω = ∅
              · apply Or.inl; assumption
              · apply Or.inr
                rw [Finset.eq_singleton_iff_nonempty_unique_mem]
                apply And.intro
                · apply Finset.nonempty_of_ne_empty; assumption
                · assumption
          rcases Homega with Hempty | Hsingl
          · rw [Hempty] at H
            simp at H
            let Hexpthded := Proof.deductionTheorem_right_ind (Proof.exportation_ind H)
            rw [Set.empty_union] at Hexpthded
            rw [Finset.toList_toFinset] at Hexpthded
            let Hsubsetproof := Proof.subset_proof Hincl1 Hexpthded
            let Hgammavp := @Proof.modusPonens Γ ⊥ ϕ Hsubsetproof Proof.exfalso
            apply h
            apply Nonempty.intro Hgammavp
          · rw [Hsingl] at H
            simp at H
            let Hexfalso := @Proof.exfalso ∅ ϕ
            let Hexpns := @Proof.expansion ∅ ⊥ ϕ ϕ Hexfalso
            have Hself : ∅ ⊢ ϕ ∨∨ ϕ ⇒ ϕ :=
              by
                let Heqv := @Proof.disjEquiv ∅ ϕ
                simp [Formula.equivalence] at Heqv
                let Hweak := @Proof.conjElimRight ∅ (ϕ⇒ϕ∨∨ϕ) (ϕ∨∨ϕ⇒ϕ)
                apply Proof.modusPonens Heqv Hweak
            let Hweak : ∅ ⊢ ϕ ∨∨ ⊥ ⇒ ϕ := by apply Proof.syllogism Hexpns Hself
            let Hsyllog : ∅ ⊢ List.foldr Formula.and (~⊥) (Finset.toList Φ) ⇒ ϕ :=
              by apply Proof.syllogism H Hweak
            let Himpl : ∅ ⊢ List.foldr Formula.implication ϕ (Finset.toList Φ) :=
              by apply Proof.exportation_ind Hsyllog
            let Hded : Φ ⊢ ϕ :=
              by
                let Hded := Proof.deductionTheorem_right_ind Himpl
                rw [Set.empty_union] at Hded
                rw [Finset.toList_toFinset] at Hded
                assumption
            have Hsubsetconseq : Γ ⊢ ϕ := by apply Proof.subset_proof Hincl1 Hded
            apply h
            apply Nonempty.intro Hsubsetconseq
      let Hcompl := @Proof.consistent_incl_complete Γ {ϕ} Hcons
      rcases Hcompl with ⟨Φ, ⟨Ω, ⟨Hincl1, ⟨Hincl2, Hcompl⟩⟩⟩⟩
      let Hcomplete := Hcompl
      simp [Proof.completePair] at Hcompl
      rcases Hcompl with ⟨_, Hvp⟩
      let Hvp := Hvp ϕ
      have Hchielem : ϕ ∈ Ω :=
        by rw [Set.singleton_subset_iff] at Hincl2; assumption
      have Hnotelem : ϕ ∉ Φ :=
        by
          rcases Hvp with Hphi | Homega
          · exfalso; apply And.right Hphi; assumption
          · apply And.right Homega
      have : ¬ϕ ∈ Γ := by apply Set.not_mem_subset Hincl1 Hnotelem
      have Hdisjthphi : @Proof.disjunctiveTheory Φ :=
        by apply Proof.complete_pair_fst_disj; assumption
      let Hdisjthphi' : Proof.setDisjTh := ⟨Φ, by assumption⟩
      let Hnotconseq : ¬forces canonicalModel Hdisjthphi' ϕ :=
        by
          by_cases (forces canonicalModel Hdisjthphi' ϕ)
          · exfalso
            let Hin := @main_sem_lemma_left Hdisjthphi' ϕ h
            rcases Hvp with Hphi | Homega
            · rcases Hphi; contradiction
            · rcases Homega
              have : ϕ ∈ Φ := Hin
              contradiction
          · assumption
      have Hmodelset : model_forces_set canonicalModel Γ Hdisjthphi' :=
        by
          simp [sem_conseq] at Hsem
          simp [model_forces_set]
          intros vp Hvpin
          have Hvpinphi : vp ∈ Φ := by apply Set.mem_of_subset_of_mem Hincl1 Hvpin
          apply elem_sem_conseq Φ
          · assumption
          · unfold model_forces_set
            intros vp Hvpin
            let Hphi : vp ∈ Φ := by assumption
            let Hmainsem := main_sem_lemma_right Hdisjthphi' vp Hphi
            assumption
      simp [sem_conseq] at Hsem
      exfalso
      let Haux := Hsem (@Proof.setDisjTh) canonicalModel Hdisjthphi' Hmodelset
      contradiction

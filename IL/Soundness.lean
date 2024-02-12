import IL.Formula
import IL.Syntax
import IL.Semantics
import Mathlib.Data.Set.Basic

set_option autoImplicit false

lemma axioms_valid (ϕ : Formula) (ax : Axiom ϕ) : valid ϕ :=
  by
    simp [valid, val]; intros W M w
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

lemma monotonicity_val (W : Type) (M : KripkeModel W) (w1 w2 : W) (ϕ : Formula) :
  M.R w1 w2 -> val M w1 ϕ -> val M w2 ϕ :=
  by
    intros Hw1w2 Hval
    induction ϕ with
    | var p => apply M.monotonicity p w1 w2 Hw1w2 Hval
    | bottom => simp [val] at Hval
    | and ψ χ ih1 ih2 => apply And.intro
                         · eapply ih1 (And.left Hval)
                         · eapply ih2 (And.right Hval)
    | or ψ χ ih1 ih2 => rcases Hval with Hvalpsi | Hvalchi
                        · apply Or.inl; eapply ih1; assumption
                        · apply Or.inr; eapply ih2; assumption
    | implication ψ χ _ _ => simp [val]
                             simp [val] at Hval
                             intros w3 Hw2w3 Hvalw3psi
                             have Hw1w3 : M.R w1 w3 := (M.trans w1 w2 w3 Hw1w2 Hw2w3)
                             apply Hval _  Hw1w3 Hvalw3psi

theorem soundness (Γ : Set Formula) (ϕ : Formula) : Γ ⊢ ϕ -> Γ ⊨ ϕ :=
  by
    intros Hlemma
    induction Hlemma with
    | premise Hvp => apply elem_sem_conseq; assumption
    | contractionDisj | contractionConj | weakeningDisj | weakeningConj
      | permutationDisj | permutationConj | exfalso =>
      apply valid_sem_conseq; apply axioms_valid; constructor
    | modusPonens _ _ ih1 ih2 => simp [sem_conseq, val, val] at ih2
                                 intros _ M _ Hmodelval
                                 eapply ih2
                                 · assumption
                                 · apply M.refl
                                 · apply ih1; assumption
    | syllogism H1 H2 ih1 ih2 => simp [sem_conseq, val, val] at *
                                 intros _ _ _ Hmodelval _ Hr _
                                 eapply ih2
                                 · assumption
                                 · assumption
                                 · apply ih1; apply Hmodelval; assumption'
    | exportation H ih => simp [sem_conseq, val, val] at *
                          intros _ M w1 Hmodelval w2 Hw1w2 _ w3 Hw2w3 _
                          eapply ih
                          · assumption
                          · apply M.trans w1 w2 w3 Hw1w2 Hw2w3
                          · eapply monotonicity_val; assumption'
                          · assumption
    | importation H ih => simp [sem_conseq, val, val] at *
                          intros _ M w1 Hmodelval w2 Hw1w2 _ _
                          eapply ih
                          · assumption
                          · assumption
                          · assumption
                          · apply M.refl
                          · assumption
    | expansion H ih => simp [sem_conseq, val, val] at *
                        intros _ M w1 Hmodelval w2 Hw1w2 Hvalor
                        rcases Hvalor with Hvalchi | Hvalvp
                        · apply Or.inl; assumption
                        · apply Or.inr
                          eapply ih; assumption'

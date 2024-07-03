import IL.Formula
import IL.Syntax
import IL.Semantics
import Mathlib.Data.Set.Basic

set_option autoImplicit false

lemma axioms_valid (ϕ : Formula) (ax : Axiom ϕ) : valid ϕ :=
  by
    intros W M w
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

theorem soundness (Γ : Set Formula) (ϕ : Formula) : Γ ⊢ ϕ -> Γ ⊨ ϕ :=
  by
    intros Hlemma
    induction Hlemma with
    | premise Hvp => apply elem_sem_conseq; assumption
    | contractionDisj | contractionConj | weakeningDisj | weakeningConj
      | permutationDisj | permutationConj | exfalso =>
      apply valid_sem_conseq; apply axioms_valid; constructor
    | modusPonens _ _ ih1 ih2 => simp [sem_conseq, val] at ih2
                                 intros _ M _ _
                                 apply ih2
                                 · assumption
                                 · apply M.refl
                                 · apply ih1; assumption
    | syllogism H1 H2 ih1 ih2 => simp [sem_conseq, val] at *
                                 intros _ _ _ Hmodelval _ _ _
                                 apply ih2; assumption'
                                 apply ih1; apply Hmodelval; assumption'
    | exportation H ih => simp [sem_conseq, val] at *
                          intros _ M w1 Hmodelval w2 Hw1w2 _ w3 Hw2w3 _
                          apply ih; assumption'
                          · apply M.trans w1 w2 w3 Hw1w2 Hw2w3
                          · apply monotonicity_val; assumption'
    | importation H ih => simp [sem_conseq, val] at *
                          intros _ M w1 Hmodelval w2 Hw1w2 _ _
                          apply ih; assumption'; apply M.refl
    | expansion H ih => simp [sem_conseq, val] at *
                        intros _ M w1 Hmodelval w2 Hw1w2 Hvalor
                        rcases Hvalor with Hvalchi | Hvalvp
                        · apply Or.inl; assumption
                        · apply Or.inr; apply ih; assumption'

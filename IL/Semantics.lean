import Il.Formula
import Il.Syntax
import Mathlib.Data.Set.Basic

set_option autoImplicit false

structure KripkeModel (W : Type) where
  R : W → W → Prop
  V : Var → W → Prop
  refl (w : W) : R w w
  trans (w1 w2 w3 : W) : R w1 w2 → R w2 w3 → R w1 w3
  monotonicity (v : Var) (w1 w2 : W) : R w1 w2 → V v w1 → V v w2

def val {W : Type} (M : KripkeModel W) (w : W) : Formula → Prop
| Formula.var p => M.V p w
| ⊥ => False
| ϕ ∧∧ ψ => val M w ϕ /\ val M w ψ
| ϕ ∨∨ ψ => val M w ϕ \/ val M w ψ
| ϕ ⇒ ψ => ∀ (w' : W), M.R w w' /\ val M w' ϕ → val M w' ψ

lemma monotonicity_val (W : Type) (M : KripkeModel W) (w1 w2 : W) (ϕ : Formula) :
  M.R w1 w2 → val M w1 ϕ → val M w2 ϕ :=
  by
    intros Hw1w2 Hval
    induction ϕ with
    | var p => apply M.monotonicity p w1 w2 Hw1w2 Hval
    | bottom => simp [val] at Hval
    | and _ _ ih1 ih2 => apply And.intro
                         · apply ih1 (And.left Hval)
                         · apply ih2 (And.right Hval)
    | or _ _ ih1 ih2 => rcases Hval with Hvalpsi | Hvalchi
                        · apply Or.inl; apply ih1; assumption
                        · apply Or.inr; apply ih2; assumption
    | implication => simp [val]
                     simp [val] at Hval
                     intros w3 Hw2w3 Hvalw3psi
                     have Hw1w3 : M.R w1 w3 := (M.trans w1 w2 w3 Hw1w2 Hw2w3)
                     apply Hval _  Hw1w3 Hvalw3psi

lemma val_neg {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula) :
  val M w (~ϕ) ↔ ∀ (w' : W), M.R w w' → ¬ val M w' ϕ :=
  by simp [val]

def true_in_world {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula) : Prop :=
  val M w ϕ

def valid_in_model {W : Type} (M : KripkeModel W) (ϕ : Formula) : Prop :=
  ∀ (w : W), val M w ϕ

def valid (ϕ : Formula) : Prop :=
  ∀ (W : Type) (M : KripkeModel W), valid_in_model M ϕ

def model_sat_set {W : Type} (M : KripkeModel W) (Γ : Set Formula) (w : W) : Prop :=
  ∀ (ϕ : Formula), ϕ ∈ Γ → val M w ϕ

def sem_conseq (Γ : Set Formula) (ϕ : Formula) : Prop :=
  ∀ (W : Type) (M : KripkeModel W) (w : W), model_sat_set M Γ w → val M w ϕ
infix:50 " ⊨ " => sem_conseq

def set_forces_set (Γ Δ : Set Formula) : Prop :=
  ∀ (ϕ : Formula), ϕ ∈ Δ → Γ ⊨ ϕ

lemma elem_sem_conseq (Γ : Set Formula) (ϕ : Formula) : ϕ ∈ Γ → Γ ⊨ ϕ :=
  by { intros Helem _ _ _  Ha; exact (Ha ϕ Helem) }

lemma subseteq_sem_conseq (Γ Δ : Set Formula) (ϕ : Formula) : Δ ⊆ Γ → Δ ⊨ ϕ → Γ ⊨ ϕ :=
  by { intros Hsubseteq Hdelta _ _ _ Ha; apply Hdelta
       intros _ Ha'; apply Ha; apply Set.mem_of_mem_of_subset Ha' Hsubseteq }

lemma valid_sem_conseq (Γ : Set Formula) (ϕ : Formula) : valid ϕ → Γ ⊨ ϕ :=
  by { intros Hvalid _ _ _ _; apply Hvalid }

lemma set_conseq (Γ Δ : Set Formula) (ϕ : Formula) : set_forces_set Γ Δ → Δ ⊨ ϕ → Γ ⊨ ϕ :=
  by { simp [sem_conseq, model_sat_set]; intros Hsetval Hdelta _ _ _ _;
       apply Hdelta; intros; apply Hsetval; assumption' }

lemma set_conseq_iff (Γ Δ : Set Formula) (ϕ : Formula) :
  set_forces_set Γ Δ → set_forces_set Δ Γ → (Δ ⊨ ϕ ↔ Γ ⊨ ϕ) :=
  by {
       intros Hsetvalgd Hsetvaldg; apply Iff.intro
       · exact set_conseq _ _ _ Hsetvalgd
       · exact set_conseq _ _ _ Hsetvaldg
     }

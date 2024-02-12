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
| (Formula.implication ϕ ψ) => forall (w' : W), M.R w w' /\ val M w' ϕ -> val M w' ψ

lemma val_neg {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula) :
  val M w (~ϕ) <-> forall (w' : W), M.R w w' -> ¬ val M w' ϕ :=
  by simp [val]

def true_in_world {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula) : Prop :=
  val M w ϕ

def valid_in_model {W : Type} (M : KripkeModel W) (ϕ : Formula) : Prop :=
  forall (w : W), val M w ϕ

def valid (ϕ : Formula) : Prop :=
  forall (W : Type) (M : KripkeModel W) (w : W), val M w ϕ

def model_sat_set {W : Type} (M : KripkeModel W) (Γ : Set Formula) (w : W) : Prop :=
  forall (ϕ : Formula), ϕ ∈ Γ -> val M w ϕ

def sem_conseq (Γ : Set Formula) (ϕ : Formula) : Prop :=
  forall (W : Type) (M : KripkeModel W) (w : W),
  model_sat_set M Γ w -> val M w ϕ
infix:50 " ⊨ " => sem_conseq

def set_forces_set (Γ Δ : Set Formula) : Prop :=
  forall (ϕ : Formula), ϕ ∈ Δ -> Γ ⊨ ϕ

lemma elem_sem_conseq (Γ : Set Formula) (ϕ : Formula) : ϕ ∈ Γ -> Γ ⊨ ϕ :=
  by { simp [sem_conseq, model_sat_set]; intros Helem _ _ _  Ha; apply Ha; assumption }

lemma subseteq_sem_conseq (Γ Δ : Set Formula) (ϕ : Formula) : Δ ⊆ Γ -> Δ ⊨ ϕ -> Γ ⊨ ϕ :=
  by { simp [sem_conseq, model_sat_set]; intros Hsubseteq Hdelta _ _ _ Ha; apply Hdelta;
       intros _ Ha'; apply Ha; apply Set.mem_of_mem_of_subset Ha' Hsubseteq; }

lemma valid_sem_conseq (Γ : Set Formula) (ϕ : Formula) : valid ϕ -> Γ ⊨ ϕ :=
  by { simp [sem_conseq, model_sat_set]; intros Hvalid _ _ _ _; apply Hvalid; }

lemma set_conseq (Γ Δ : Set Formula) (ϕ : Formula) : set_forces_set Γ Δ -> Δ ⊨ ϕ -> Γ ⊨ ϕ :=
  by { simp [set_forces_set, sem_conseq, model_sat_set]; intros Hsetval Hdelta _ M w Ha;
       apply Hdelta; intros; apply Hsetval; assumption' }

lemma set_conseq_iff (Γ Δ : Set Formula) (ϕ : Formula) :
  set_forces_set Γ Δ -> set_forces_set Δ Γ -> (Δ ⊨ ϕ <-> Γ ⊨ ϕ) :=
  by {
       intros Hsetvalgd Hsetvaldg; apply Iff.intro
       · exact set_conseq _ _ _ Hsetvalgd
       · exact set_conseq _ _ _ Hsetvaldg
     }

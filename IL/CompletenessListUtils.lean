import IL.Formula
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Card
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

set_option autoImplicit false

variable {Γ Δ : Set Formula} {ϕ ψ χ γ : Formula}

@[simp]
def list_indices (Φ : List Formula) (f : Formula -> Nat) : List Nat :=
  match Φ with
  | [] => []
  | h :: t => (f h) :: list_indices t f

lemma perm_list_indices_mem (Φ Ω : List Formula) (Hperm : Φ ~ Ω) (f : Formula -> Nat) :
  ∀ (ϕ : Formula), f ϕ ∈ list_indices Φ f -> f ϕ ∈ list_indices Ω f :=
  by
    induction Hperm with
    | nil => simp
    | @cons x l1' l2' ihperm ihequiv => simp
                                        intros ϕ Hor
                                        cases Hor
                                        · apply Or.inl; assumption
                                        · apply Or.inr; apply ihequiv; assumption
    | swap x y l => simp
                    intros ϕ Hor
                    rcases Hor with _ | H2
                    · apply Or.inr; apply Or.inl; assumption
                    · cases H2
                      · apply Or.inl; assumption
                      · apply Or.inr; apply Or.inr; assumption
    | @trans l1' l2' l3' ihperm12 ihperm23 ihequiv12 ihequiv23 => intros ϕ Hl1
                                                                  exact ihequiv23 ϕ (ihequiv12 ϕ Hl1)

@[simp]
def pf_elem (Φ : Finset Formula) (f : Formula -> Nat) :=
  ∀ (ϕ : Formula), ϕ ∈ Φ.toList -> f ϕ ∈ list_indices Φ.toList f

lemma f_elem_in_list_indices_empty (f : Formula -> Nat) : pf_elem ∅ f := by simp

noncomputable instance {ϕ ψ : Formula} : Decidable (ϕ = ψ) := @default _ (Classical.decidableInhabited _)

noncomputable instance {ϕ : Formula} {Γ : Set Formula} : Decidable (ϕ ∈ Γ) := @default _ (Classical.decidableInhabited _)

lemma f_elem_in_list_indices_insert (Φ : Finset Formula) (f : Formula -> Nat) (Hnotin : ϕ ∉ Φ) (Hprev : pf_elem Φ f) :
  pf_elem (insert ϕ Φ) f :=
    by
      simp
      apply And.intro
      · rw [Finset.insert_eq]
        let Hperm := perm_list_indices_mem (ϕ :: Finset.toList Φ) (Finset.toList ({ϕ} ∪ Φ)) (List.Perm.symm (Finset.toList_insert Hnotin)) f ϕ
        apply Hperm
        simp
      · intros a Hmem
        simp at Hprev
        let Hprev := Hprev a Hmem
        rw [Finset.insert_eq]
        let Hperm := perm_list_indices_mem (ϕ :: Finset.toList Φ) (Finset.toList ({ϕ} ∪ Φ)) (List.Perm.symm (Finset.toList_insert Hnotin)) f a
        apply Hperm
        simp
        apply Or.inr
        assumption

lemma f_elem_in_list_indices (Φ : Finset Formula) (f : Formula -> Nat) : pf_elem Φ f :=
  by
    induction Φ using Finset.induction_on with
    | empty => exact f_elem_in_list_indices_empty f
    | @insert ϕ Φ Hnotin Hprev => exact f_elem_in_list_indices_insert Φ f Hnotin Hprev

noncomputable def pair_finset_indices (Φ Ω : Finset Formula) (f : Formula -> Nat) : (List Nat × List Nat) :=
  (list_indices Φ.toList f, list_indices Ω.toList f)

@[simp]
def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => max h (maximum t)

lemma leq_max (l : List Nat) (x : Nat) (Helem : x ∈ l) : x <= maximum l :=
  by
    unfold maximum
    induction l with
    | nil => simp; exfalso; contradiction
    | cons h t ih => simp; simp at Helem;
                     rcases Helem with Hh | Ht
                     · apply Or.inl; rw [Hh]
                     · apply Or.inr; unfold maximum; apply ih Ht

noncomputable def max_index_mem_local (f : Formula -> Nat) (Φ Ω : Finset Formula) : Nat × Nat :=
  (maximum (pair_finset_indices Φ Ω f).fst, maximum (pair_finset_indices Φ Ω f).snd)

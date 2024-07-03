import IL.Formula
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Card
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

set_option autoImplicit false

variable {ϕ : Formula}

@[simp]
def pf_elem (Φ : Finset Formula) (f : Formula -> Nat) :=
  ∀ (ϕ : Formula), ϕ ∈ Φ.toList -> f ϕ ∈ List.map f Φ.toList

lemma f_elem_in_list_indices_empty (f : Formula -> Nat) : pf_elem ∅ f := by simp

noncomputable instance {ϕ ψ : Formula} : Decidable (ϕ = ψ) := @default _ (Classical.decidableInhabited _)

noncomputable instance {ϕ : Formula} {Γ : Set Formula} : Decidable (ϕ ∈ Γ) := @default _ (Classical.decidableInhabited _)

lemma f_elem_in_list_indices_insert (Φ : Finset Formula) (f : Formula -> Nat) :
  pf_elem (insert ϕ Φ) f :=
    by
      simp
      intro a _
      apply Or.inr
      exists a

lemma f_elem_in_list_indices (Φ : Finset Formula) (f : Formula -> Nat) : pf_elem Φ f :=
  by
    induction Φ using Finset.induction_on with
    | empty => exact f_elem_in_list_indices_empty f
    | @insert ϕ Φ => exact f_elem_in_list_indices_insert Φ f

noncomputable def pair_finset_indices (Φ Ω : Finset Formula) (f : Formula -> Nat) : (List Nat × List Nat) :=
  (List.map f Φ.toList, List.map f Ω.toList)

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

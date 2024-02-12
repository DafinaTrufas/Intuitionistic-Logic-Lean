import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Nat.Pow

set_option autoImplicit false

structure Var where
  val : Nat

inductive Formula where
| var : Var -> Formula
| bottom : Formula
| and : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| implication : Formula -> Formula -> Formula

namespace Formula

infixr:60 "∧∧" => and

infixr:60 "∨∨" => or

infixr:50 "⇒" => implication

notation "⊥" => bottom

def negation (ϕ : Formula) : Formula := ϕ ⇒ ⊥
prefix:70 "~" => negation

def equivalence (ϕ ψ : Formula) := (ϕ ⇒ ψ) ∧∧ (ψ ⇒ ϕ)
infix:50 "⇔" => equivalence

def list2 (l : List (ℕ × ℕ)) := List.map (λ (a, b) => (2^(a+1), 2^(b+1))) l

def list3 (l : List (ℕ × ℕ)) := List.map (λ (a, b) => (3^(a+1), 3^(b+1))) l

def list23 (n m : List (ℕ × ℕ)) : List (ℕ × ℕ) := list2 n ++ list3 m

def encode : Formula -> List (ℕ × ℕ)
  | Formula.bottom => [(0,1)]
  | Formula.var x  => [(x.val + 1,0)]
  | Formula.and ϕ ψ => [(0, 2)] ++ (list23 ϕ.encode ψ.encode)
  | Formula.or ϕ ψ => [(0, 3)] ++ (list23 ϕ.encode ψ.encode)
  | Formula.implication ϕ ψ => [(0, 4)] ++ (list23 ϕ.encode ψ.encode)

lemma prefix_concat {a b n m : List (ℕ × ℕ)} (h1 : a ++ b = n ++ m) (h2 : a.length ≤ n.length) : a <+: n :=
  by
    have Haux := List.prefix_append n m
    rw [<-h1] at Haux
    apply List.prefix_of_prefix_length_le (List.prefix_append a b) Haux h2

lemma split {a b : List (ℕ × ℕ)} (hyp : a <+: b) : ∃ c, c <:+ b ∧ b = a ++ c :=
  by
    rcases hyp with ⟨t, Ht⟩
    exists t
    apply And.intro
    · rw [<-Ht]; simp
    · rw [Ht]

theorem neq_2_3 (n m : Nat) : 3^(n+1) ≠ 2^(m+1) :=
  by sorry

lemma list2inj : list2.Injective :=
  by
    intro l1 l2 hyp
    induction l1 generalizing l2 with
    | nil =>
        cases l2 with
        | nil  => simp at *
        | cons => simp [list2] at hyp
    | cons h t ih =>
        cases l2 with
        | nil  => simp [list2] at hyp
        | cons head tail =>
            simp [list2] at hyp ⊢
            apply And.intro
            . have ⟨eq1, eq2⟩ := hyp.left
              clear ih hyp
              have eq1 := @Nat.pow_right_injective 2 (Nat.le_of_eq (Eq.refl 2)) (h.fst + 1) (head.fst + 1) eq1
              have eq2 := @Nat.pow_right_injective 2 (Nat.le_of_eq (Eq.refl 2)) (h.snd + 1) (head.snd + 1) eq2
              simp [Prod.eq_iff_fst_eq_snd_eq, Nat.succ_inj'] at eq1 eq2 ⊢
              exact ⟨eq1, eq2⟩
            . exact ih hyp.right

theorem list3inj : list3.Injective :=
  by
    intro l1 l2 hyp
    induction l1 generalizing l2 with
    | nil =>
        cases l2 with
        | nil  => simp at *
        | cons => simp [list3] at hyp
    | cons h t ih =>
        cases l2 with
        | nil  => simp [list3] at hyp
        | cons head tail =>
            simp [list3] at hyp ⊢
            apply And.intro
            . have ⟨eq1, eq2⟩ := hyp.left
              clear ih hyp
              have eq1 := @Nat.pow_right_injective 3 (Nat.le_succ 2) (h.fst + 1) (head.fst + 1) eq1
              have eq2 := @Nat.pow_right_injective 3 (Nat.le_succ 2) (h.snd + 1) (head.snd + 1) eq2
              simp [Prod.eq_iff_fst_eq_snd_eq, Nat.succ_inj'] at eq1 eq2 ⊢
              exact ⟨eq1, eq2⟩
            . exact ih hyp.right

lemma pow2 {a : List (ℕ × ℕ)} {x : (ℕ × ℕ)} : x ∈ list2 a -> ∃ n, x.fst = 2^(n+1) :=
  by
    unfold list2
    simp
    intros x1 x2 _ Hpair
    exists x1
    let Hpairsymm := Eq.symm Hpair
    rw [Prod.ext_iff] at Hpairsymm
    rcases Hpairsymm with ⟨Hleft, _⟩
    simp at Hleft
    assumption

lemma mem_suff {a l : List (ℕ × ℕ)} : l <:+ a -> (∀ e, e ∈ l → e ∈ a) :=
  by
    intros Hsuff _ _
    rcases Hsuff with ⟨t, Ht⟩
    rw [<-Ht]
    simp
    apply Or.inr
    assumption

lemma mem_suff_ht {a t : List (ℕ × ℕ)} {h : (ℕ × ℕ)} : h :: t <:+ a -> h ∈ a :=
  by intros Hsuffix; apply mem_suff Hsuffix; simp

lemma suffix_pow2 {a t : List (ℕ × ℕ)} {h : (ℕ × ℕ)} : h :: t <:+ (list2 a) -> ∃ n, h.fst = 2^(n+1) :=
  by intro hyp; exact pow2 (mem_suff_ht hyp)

lemma list23_lemma_wlog {a b n m :  List (ℕ × ℕ)}
  (h : (list2 a).length ≤ (list2 n).length) : list23 a b = list23 n m ->
  (list2 a = list2 n ∧ list3 b = list3 m) :=
  by
    intro hyp
    simp [list23] at hyp
    have by_l1 := prefix_concat hyp h
    have by_l2 := split by_l1
    match by_l2 with
    | ⟨suf, hsuf⟩ =>
        clear h by_l1 by_l2
        simp [hsuf] at hyp
        cases suf
        . simp at hyp hsuf
          exact ⟨Eq.symm hsuf.right, hyp⟩
        . exfalso
          have is_pow_2 := suffix_pow2 hsuf.left
          cases b
          . simp [list3] at hyp
          . simp [list3, Prod.eq_iff_fst_eq_snd_eq] at hyp
            have abs_1 := hyp.left.left
            match is_pow_2 with
            | ⟨n, abs_2⟩ =>
                rw [abs_2] at abs_1
                apply neq_2_3
                apply abs_1

lemma list23_lemma {a b n m :  List (ℕ × ℕ)} : list23 a b = list23 n m -> (list2 a = list2 n ∧ list3 b = list3 m) :=
  by
    by_cases h : (list2 a).length ≤ (list2 n).length
    . exact list23_lemma_wlog h
    . simp at h
      have h := Nat.le_of_lt h
      conv =>
        congr
        . apply Eq.symm
        . congr <;> apply Eq.symm
      let Haux := @list23_lemma_wlog n m a b h
      intros Hlist23
      let Haux := Haux (Eq.symm Hlist23)
      apply And.intro
      · exact Eq.symm (And.left Haux)
      · exact Eq.symm (And.right Haux)

theorem list23_inj {a b n m :  List (ℕ × ℕ)} : list23 a b = list23 n m -> (a = n ∧ b = m) :=
  by
    intro hyp
    have ⟨a_n, b_m⟩ := list23_lemma hyp
    exact ⟨list2inj a_n, list3inj b_m⟩

theorem Inject_Form : Formula.encode.Injective :=
  by
    intro ϕ ψ
    intro h
    induction ϕ generalizing ψ with
    | and a b ih1 ih2 | or a b ih1 ih2 | implication a b ih1 ih2 =>
      cases ψ <;> simp [Formula.encode] at *
      apply And.intro <;> (first | apply ih1 | apply ih2) <;> simp [list23_inj h]
    | _  => induction ψ <;> simp [Formula.encode] at * <;>
            exact congrArg Var.mk h

instance : Countable Formula := Inject_Form.countable

instance : Nonempty Formula := ⟨⊥⟩

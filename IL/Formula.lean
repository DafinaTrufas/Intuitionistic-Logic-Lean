import IL.Variable

set_option autoImplicit false

inductive Formula where
| var : Var -> Formula
| bottom : Formula
| and : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| implication : Formula -> Formula -> Formula
-- | existential : Var -> Formula -> Formula
-- | universal : Var -> Formula -> Formula

namespace Formula

infixr:60 "∧∧" => and

infixr:60 "∨∨" => or

infixr:50 "⇒" => implication

notation "⊥" => bottom

-- notation "∃∃" => existential

-- notation "∀∀" => universal

def negation (ϕ : Formula) : Formula := ϕ ⇒ ⊥
prefix:70 "~" => negation

def equivalence (ϕ ψ : Formula) := (ϕ ⇒ ψ) ∧∧ (ψ ⇒ ϕ)
infix:50 "⇔" => equivalence

def size (ϕ : Formula) : Nat :=
  match ϕ with
  | var _ | bottom => 1
  | and ψ χ | or ψ χ | implication ψ χ => 1 + size ψ + size χ
  termination_by size ϕ => ϕ

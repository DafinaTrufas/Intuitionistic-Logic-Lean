import IL.Term

set_option autoImplicit false

inductive Formula (𝕊 : Type) where
| bottom : Formula 𝕊  
| predicate : Pred -> Nat -> List (Formula 𝕊) -> Formula 𝕊
| and : Formula 𝕊 -> Formula 𝕊 -> Formula 𝕊 
| or : Formula 𝕊 -> Formula 𝕊 -> Formula 𝕊 
| implication : Formula 𝕊 -> Formula 𝕊 -> Formula 𝕊 
| existential : Var -> Formula 𝕊 -> Formula 𝕊 
| universal : Var -> Formula 𝕊 -> Formula 𝕊

infixr:60 "∧∧" => Formula.and

infixr:60 "∨∨" => Formula.or

infixr:50 "⇒" => Formula.implication

notation "⊥" => Formula.bottom

notation "∃∃" => Formula.existential

notation "∀∀" => Formula.universal

variable {𝕊 : Type}

def negation (ϕ : Formula 𝕊) : Formula 𝕊 := ϕ ⇒ ⊥
prefix:70 "¬¬" => Formula.negation

def equivalence {𝕊 : Type} (ϕ ψ : Formula 𝕊) := (ϕ ⇒ ψ) ∧∧ (ψ ⇒ ϕ)
infix:50 "⇔" => equivalence

def isfreeVar {𝕊 : Type} (ϕ : Formula 𝕊) (x : Var) : Bool :=
match ϕ with 
| ϕ ∧∧ ψ | ϕ ∨∨ ψ | ϕ ⇒ ψ => isfreeVar ϕ x ∨ isfreeVar ψ x 
| ∃∃ x ϕ | ∀∀ x ϕ => isfreeVar ϕ x 
| _ => False

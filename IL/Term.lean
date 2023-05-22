import IL.Variable

set_option autoImplicit false

inductive Term (𝕊 : Type) where
| var : Var -> Term 𝕊 
| const : Const -> Term 𝕊 
| function : Func -> Nat -> List (Term 𝕊) -> Term 𝕊 

variable {𝕊 : Type}

instance : Coe Var (Term 𝕊) := ⟨Term.var⟩

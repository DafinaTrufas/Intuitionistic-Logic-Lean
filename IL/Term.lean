import IL.Variable

set_option autoImplicit false

inductive Term where
| var : Var -> Term 
| const : Const -> Term
| function : Func -> Nat -> List Term -> Term 

variable {𝕊 : Type}

instance : Coe Var (Term) := ⟨Term.var⟩

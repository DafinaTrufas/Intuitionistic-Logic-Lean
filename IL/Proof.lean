import IL.Formula

set_option autoImplicit false

abbrev Premises (𝕊 : Type) : Type := List (Formula 𝕊)

inductive Proof {𝕊 : Type} (Γ : Premises 𝕊) : Formula 𝕊 -> Type where
| premise {ϕ : Formula 𝕊} : ϕ ∈ Γ -> Proof Γ ϕ 
| contractionDisj {ϕ} : Proof Γ (ϕ ∨∨ ϕ ⇒ ϕ)
| contractionConj {ϕ} : Proof Γ (ϕ ⇒ ϕ ∧∧ ϕ)
| weakeningDisj {ϕ ψ} : Proof Γ (ϕ ⇒ ϕ ∨∨ ψ)
| weakeningConj {ϕ ψ} : Proof Γ (ϕ ∧∧ ψ ⇒ ϕ)
| permutationODisj {ϕ ψ} : Proof Γ (ϕ ∨∨ ψ ⇒ ψ ∨∨ ϕ)
| permutationConj {ϕ ψ} : Proof Γ (ϕ ∧∧ ψ ⇒ ψ ∧∧ ϕ)
| exfalso {ϕ} : Proof Γ (⊥ ⇒ ϕ)
| modusPonens {ϕ ψ} : Proof Γ ϕ -> Proof Γ (ϕ ⇒ ψ) -> Proof Γ ψ
| syllogism {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) -> Proof Γ (ψ ⇒ χ) -> Proof Γ (ϕ ⇒ χ)
| exportation {ϕ ψ χ} : Proof Γ (ϕ ∧∧ ψ ⇒ χ) -> Proof Γ (ϕ ⇒ ψ ⇒ χ)
| importation {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ ⇒ χ) -> Proof Γ (ϕ ∧∧ ψ ⇒ χ)
| expansion {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) -> Proof Γ (χ ∨∨ ϕ ⇒ χ ∨∨ ψ)
| existGen {ϕ ψ} {x} (not_fv : ¬(isfreeVar ψ x)) : Proof Γ (ϕ ⇒ ψ) -> Proof Γ (∃∃ x ϕ ⇒ ψ)
| forallGen {ϕ ψ} {x} (not_fv : ¬(isfreeVar ψ x)) : Proof Γ (ϕ ⇒ ψ) -> Proof Γ (∀∀ x ϕ ⇒ ψ)

infix:25 " ⊢ " => Proof

namespace Proof

variable {𝕊 : Type} {Γ : Premises 𝕊} {ϕ ψ χ γ : Formula 𝕊}

def disjIntroRight
  : Γ ⊢ ψ ⇒ ϕ ∨∨ ψ :=
  syllogism weakeningDisj permutationODisj

def conjElimRight
  : Γ ⊢ ϕ ∧∧ ψ ⇒ ψ := 
  syllogism permutationConj weakeningConj

def implProjLeft
  : Γ ⊢ ϕ ⇒ (ψ ⇒ ϕ) :=
  exportation weakeningConj

def disjOfAndElimLeft
  : Γ ⊢ (ϕ ∧∧ ψ) ⇒ (ϕ ∨∨ γ) := 
  syllogism weakeningConj weakeningDisj

def implSelf
  : Γ ⊢ ϕ ⇒ ϕ :=
  syllogism contractionConj weakeningConj

def conjIntro
  : Γ ⊢ ϕ ⇒ ψ ⇒ ϕ ∧∧ ψ :=
  exportation implSelf

def modusPonensAndTh1
  : Γ ⊢ (ϕ ⇒ ψ) ∧∧ ϕ ⇒ ψ :=
  let l₁ : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ ψ) := implSelf
  importation l₁

def modusPonensAndTh2
  : Γ ⊢ ϕ ∧∧ (ϕ ⇒ ψ) ⇒ ψ :=
  syllogism permutationConj modusPonensAndTh1

def modusPonensTh 
  : Γ ⊢ ϕ ⇒ (ϕ ⇒ ψ) ⇒ ψ :=
  exportation modusPonensAndTh2

def andElimLeftLeft
  : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ :=
  syllogism weakeningConj weakeningConj

def andElimLeftRight
  : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ψ :=
  syllogism weakeningConj conjElimRight

def andElimRightLeft
  : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ ψ :=
  syllogism conjElimRight weakeningConj

def andElimRightRight
  : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ χ :=
  syllogism conjElimRight conjElimRight

def orIntroRightLeft
  : Γ ⊢ ψ ⇒ (ϕ ∨∨ (ψ ∨∨ χ)) :=
  syllogism weakeningDisj disjIntroRight

def orIntroRightRight
  : Γ ⊢ χ ⇒ (ϕ ∨∨ (ψ ∨∨ χ)) :=
  syllogism disjIntroRight disjIntroRight

def orIntroLeftLeft
  : Γ ⊢ ϕ ⇒ (ϕ ∨∨ ψ) ∨∨ χ :=
  syllogism weakeningDisj weakeningDisj

def orIntroLeftRight
  : Γ ⊢ ψ ⇒ (ϕ ∨∨ ψ) ∨∨ χ :=
  syllogism disjIntroRight weakeningDisj

def conjIntroRule : Γ ⊢ ϕ -> Γ ⊢ ψ -> Γ ⊢ ϕ ∧∧ ψ :=
  fun l₁ : Γ ⊢ ϕ =>
  fun l₂ : Γ ⊢ ψ => 
  let l₃ : Γ ⊢ ϕ ∧∧ ψ ⇒ ϕ ∧∧ ψ := implSelf
  let l₄ : Γ ⊢ ϕ ⇒ ψ ⇒ ϕ ∧∧ ψ := exportation l₃
  let l₅ : Γ ⊢ ψ ⇒ ϕ ∧∧ ψ := modusPonens l₁ l₄
  modusPonens l₂ l₅

def conjImplIntroRule : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ⇒ χ -> Γ ⊢ ϕ ⇒ ψ ∧∧ χ :=
  let l₁ : Γ ⊢ ψ ∧∧ χ ⇒ ψ ∧∧ χ := implSelf
  let l₂ : Γ ⊢ ψ ⇒ χ ⇒ ψ ∧∧ χ := exportation l₁
  fun l₃ : Γ ⊢ ϕ ⇒ ψ =>
  let l₄ : Γ ⊢ ϕ ⇒ χ ⇒ ψ ∧∧ χ := syllogism l₃ l₂
  let l₅ : Γ ⊢ χ ∧∧ ϕ ⇒ ϕ ∧∧ χ := permutationConj
  let l₆ : Γ ⊢ ϕ ∧∧ χ ⇒ ψ ∧∧ χ := importation l₄
  let l₇ : Γ ⊢ χ ∧∧ ϕ ⇒ ψ ∧∧ χ := syllogism l₅ l₆
  fun l₈ : Γ ⊢ ϕ ⇒ χ =>
  let l₉ : Γ ⊢ χ ⇒ ϕ ⇒ ψ ∧∧ χ := exportation l₇
  let l₁₀ : Γ ⊢ ϕ ⇒ ϕ ⇒ ψ ∧∧ χ := syllogism l₈ l₉
  let l₁₁ : Γ ⊢ ϕ ⇒ ϕ ∧∧ ϕ := contractionConj
  let l₁₂ : Γ ⊢ ϕ ∧∧ ϕ ⇒ ψ ∧∧ χ := importation l₁₀
  syllogism l₁₁ l₁₂

def equivIntro : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ψ ⇒ ϕ -> Γ ⊢ ϕ ⇔ ψ :=
  conjIntroRule

def extraPremise : Γ ⊢ ϕ -> Γ ⊢ ψ ⇒ ϕ := fun p =>
  modusPonens p implProjLeft

def conjEquiv
  : Γ ⊢ ϕ ⇔ ϕ ∧∧ ϕ :=
  conjIntroRule contractionConj weakeningConj

def disjEquiv
  : Γ ⊢ ϕ ⇔ ϕ ∨∨ ϕ :=
  conjIntroRule weakeningDisj contractionDisj

def andAssoc1
  : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ ∧∧ (ψ ∧∧ χ) :=
  conjImplIntroRule andElimLeftLeft (conjImplIntroRule andElimLeftRight conjElimRight)

def andAssoc2
  : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ (ϕ ∧∧ ψ) ∧∧ χ :=
  conjImplIntroRule (conjImplIntroRule weakeningConj andElimRightLeft) andElimRightRight

def andAssoc 
  : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇔ (ϕ ∧∧ ψ) ∧∧ χ :=
  conjIntroRule andAssoc2 andAssoc1

def extraPremiseConjIntroLeft1 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ∧∧ χ ⇒ ψ := fun p =>
  syllogism weakeningConj p

def extraPremiseConjIntroLeft2 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ χ ∧∧ ϕ ⇒ ψ := fun p =>
  syllogism conjElimRight p

def implConjElimLeft : Γ ⊢ ϕ ⇒ ψ ∧∧ χ -> Γ ⊢ ϕ ⇒ ψ := fun p =>
  syllogism p weakeningConj

def implConjElimRight : Γ ⊢ ϕ ⇒ ψ ∧∧ χ -> Γ ⊢ ϕ ⇒ χ := fun p =>
  syllogism p conjElimRight

def conjImplComm : Γ ⊢ ϕ ∧∧ ψ ⇒ χ -> Γ ⊢ ψ ∧∧ ϕ ⇒ χ := fun p =>
  syllogism permutationConj p

def importationComm : Γ ⊢ ϕ ⇒ ψ ⇒ χ -> Γ ⊢ ψ ∧∧ ϕ ⇒ χ := fun p =>
  conjImplComm (importation p)

def extraPremiseConjIntroRight1 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ⇒ ϕ ∧∧ ψ := fun p =>
  conjImplIntroRule implSelf p

def extraPremiseConjIntroRight2 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ⇒ ψ ∧∧ ϕ := fun p =>
  conjImplIntroRule p implSelf

def andImplDistrib : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ χ ⇒ γ -> Γ ⊢ ϕ ∧∧ χ ⇒ ψ ∧∧ γ := fun p1 p2 =>
  conjImplIntroRule (extraPremiseConjIntroLeft1 p1) (extraPremiseConjIntroLeft2 p2)

def andOrWeakening : Γ ⊢ ϕ ∧∧ (ϕ ∨∨ ψ) ⇒ ϕ :=
  weakeningConj

def andOrContraction : Γ ⊢ ϕ ⇒ ϕ ∧∧ (ϕ ∨∨ ψ) :=
  conjImplIntroRule implSelf weakeningDisj

def andOrWeakContr : Γ ⊢ ϕ ⇔ ϕ ∧∧ (ϕ ∨∨ ψ) :=
  conjIntroRule andOrContraction andOrWeakening

def orAndWeakening : Γ ⊢ ϕ ∨∨ (ϕ ∧∧ ψ) ⇒ ϕ :=
  syllogism (expansion weakeningConj) contractionDisj

def orAndContraction : Γ ⊢ ϕ ⇒ ϕ ∨∨ (ϕ ∧∧ ψ) :=
  weakeningDisj

def orAndWeakContr : Γ ⊢ ϕ ⇔ ϕ ∨∨ (ϕ ∧∧ ψ) :=
  conjIntroRule orAndContraction orAndWeakening

def permuteHyps : Γ ⊢ ϕ ⇒ ψ ⇒ χ -> Γ ⊢ ψ ⇒ ϕ ⇒ χ := fun p =>
  exportation (importationComm p)

def modusPonensExtraHyp : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ϕ ⇒ χ := fun p1 p2 =>
  syllogism (extraPremiseConjIntroRight1 p1) (importation p2) 

def implExtraHypRev : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) := fun p =>
  exportation (conjImplComm (syllogism (andImplDistrib p implSelf) modusPonensAndTh2))

def implConclTrans : Γ ⊢ ϕ ⇒ ψ ⇒ χ -> Γ ⊢ χ ⇒ γ -> Γ ⊢ ϕ ⇒ ψ ⇒ γ := fun p1 p2 =>
  exportation (syllogism (importation p1) p2)

def implOrExtraHyp : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ χ := fun p =>
  syllogism (syllogism permutationODisj (expansion p)) permutationODisj    

def extraPremiseDisjIntro1 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ∨∨ ψ ⇒ ψ := fun p =>
  syllogism (implOrExtraHyp p) contractionDisj

def extraPremiseDisjIntro2 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ψ ∨∨ ϕ ⇒ ψ := fun p =>
  syllogism (expansion p) contractionDisj

def implOrIntro : Γ ⊢ ϕ ⇒ χ -> Γ ⊢ ψ ⇒ χ -> Γ ⊢ ϕ ∨∨ ψ ⇒ χ := fun p1 p2 =>
  syllogism (expansion p2) (extraPremiseDisjIntro1 p1)

def orImplDistrib : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ χ ⇒ γ -> Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ γ := fun p1 p2 =>
  implOrIntro (syllogism p1 weakeningDisj) (syllogism p2 disjIntroRight)

def orAssoc1 : Γ ⊢ (ϕ ∨∨ ψ) ∨∨ χ ⇒ ϕ ∨∨ (ψ ∨∨ χ) :=
  implOrIntro (implOrIntro weakeningDisj orIntroRightLeft) orIntroRightRight

def orAssoc2 : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ (ϕ ∨∨ ψ) ∨∨ χ :=
  implOrIntro orIntroLeftLeft (implOrIntro orIntroLeftRight disjIntroRight)

def orAssoc : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇔ (ϕ ∨∨ ψ) ∨∨ χ :=
  conjIntroRule orAssoc2 orAssoc1

def implExtraHypRevRule : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation (modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftLeft) andElimLeftRight))

def exportationTh : Γ ⊢ (ϕ ∧∧ ψ ⇒ χ) ⇒ ϕ ⇒ ψ ⇒ χ :=
  exportation (exportation (modusPonensExtraHyp (conjImplIntroRule andElimLeftRight conjElimRight) andElimLeftLeft))

def importationTh : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ := 
  exportation (modusPonensExtraHyp andElimRightRight (modusPonensExtraHyp andElimRightLeft weakeningConj))

def impExpEquiv : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇔ (ϕ ∧∧ ψ ⇒ χ) := 
  conjIntroRule importationTh exportationTh

def permuteHypsTh : Γ ⊢ (ϕ ⇒ (ψ ⇒ χ)) ⇒ (ψ ⇒ (ϕ ⇒ χ)) :=
  exportation (exportation (modusPonensExtraHyp andElimLeftRight (modusPonensExtraHyp conjElimRight andElimLeftLeft)))

def modusPonensExtraHypTh : Γ ⊢ ((ϕ ⇒ (ψ ⇒ χ)) ∧∧ (ϕ ⇒ ψ)) ∧∧ ϕ ⇒ χ :=
  modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftRight) (modusPonensExtraHyp conjElimRight andElimLeftLeft)

def implDistrib1 : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇒ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation modusPonensExtraHypTh)

def conjImplDisj : Γ ⊢ (ϕ ⇒ χ) ∧∧ (ψ ⇒ χ) ⇒ (ϕ ∨∨ ψ ⇒ χ) :=
  permuteHyps (implOrIntro (permuteHyps weakeningConj) (permuteHyps conjElimRight))

def implImplDisj : Γ ⊢ (ϕ ⇒ χ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ∨∨ ψ ⇒ χ) :=
  exportation conjImplDisj

def extraPremiseConjTh : Γ ⊢ (ϕ ∧∧ (ϕ ⇒ ψ) ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ :=
  implExtraHypRev (andImplDistrib implSelf implProjLeft)

def implDistrib2 : Γ ⊢ ((ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ)) ⇒ ϕ ⇒ ψ ⇒ χ :=
  syllogism (syllogism (syllogism permuteHypsTh importationTh) extraPremiseConjTh) exportationTh

def implDistrib : Γ ⊢ ((ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ)) ⇔ (ϕ ⇒ ψ ⇒ χ) :=
  conjIntroRule implDistrib2 implDistrib1

def implDistribRule1 : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) -> Γ ⊢ ϕ ⇒ ψ ⇒ χ := fun p =>
  exportation (modusPonens (conjImplComm (importation p)) extraPremiseConjTh)

def implSyllogism : Γ ⊢ ϕ ⇒ ψ ⇒ χ -> Γ ⊢ ϕ ⇒ χ ⇒ γ -> Γ ⊢ ϕ ⇒ ψ ⇒ γ := fun p1 p2 =>
  implDistribRule1 (syllogism (modusPonens p1 implDistrib1) (modusPonens p2 implDistrib1))

def expRule : Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) -> Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) := fun p =>
  exportation (exportation (syllogism andAssoc1 (importation p)))

def impRule : Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) -> Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) := fun p =>
  exportation (syllogism andAssoc2 (importation (importation p)))

end Proof
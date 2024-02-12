import IL.Formula
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Card
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

set_option autoImplicit false

inductive Axiom : Formula -> Type where
| contractionDisj {ϕ} : Axiom (ϕ ∨∨ ϕ ⇒ ϕ)
| contractionConj {ϕ} : Axiom (ϕ ⇒ ϕ ∧∧ ϕ)
| weakeningDisj {ϕ ψ} : Axiom (ϕ ⇒ ϕ ∨∨ ψ)
| weakeningConj {ϕ ψ} : Axiom (ϕ ∧∧ ψ ⇒ ϕ)
| permutationDisj {ϕ ψ} : Axiom (ϕ ∨∨ ψ ⇒ ψ ∨∨ ϕ)
| permutationConj {ϕ ψ} : Axiom (ϕ ∧∧ ψ ⇒ ψ ∧∧ ϕ)
| exfalso {ϕ} : Axiom (⊥ ⇒ ϕ)

inductive Proof (Γ : Set Formula) : Formula -> Type where
| premise {ϕ} : ϕ ∈ Γ → Proof Γ ϕ
| contractionDisj {ϕ} : Proof Γ (ϕ ∨∨ ϕ ⇒ ϕ)
| contractionConj {ϕ} : Proof Γ (ϕ ⇒ ϕ ∧∧ ϕ)
| weakeningDisj {ϕ ψ} : Proof Γ (ϕ ⇒ ϕ ∨∨ ψ)
| weakeningConj {ϕ ψ} : Proof Γ (ϕ ∧∧ ψ ⇒ ϕ)
| permutationDisj {ϕ ψ} : Proof Γ (ϕ ∨∨ ψ ⇒ ψ ∨∨ ϕ)
| permutationConj {ϕ ψ} : Proof Γ (ϕ ∧∧ ψ ⇒ ψ ∧∧ ϕ)
| exfalso {ϕ} : Proof Γ (⊥ ⇒ ϕ)
| modusPonens {ϕ ψ} : Proof Γ ϕ → Proof Γ (ϕ ⇒ ψ) → Proof Γ ψ
| syllogism {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (ψ ⇒ χ) → Proof Γ (ϕ ⇒ χ)
| exportation {ϕ ψ χ} : Proof Γ (ϕ ∧∧ ψ ⇒ χ) → Proof Γ (ϕ ⇒ ψ ⇒ χ)
| importation {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ ⇒ χ) → Proof Γ (ϕ ∧∧ ψ ⇒ χ)
| expansion {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (χ ∨∨ ϕ ⇒ χ ∨∨ ψ)

infix:25 " ⊢ " => Proof

variable {Γ Δ : Set Formula} {ϕ ψ χ γ : Formula}

namespace Proof

def set_proof_set : Type :=
  forall (ϕ : Formula), ϕ ∈ Δ -> Γ ⊢ ϕ

def disjIntroRight : Γ ⊢ ψ ⇒ ϕ ∨∨ ψ := syllogism weakeningDisj permutationDisj

def conjElimRight : Γ ⊢ ϕ ∧∧ ψ ⇒ ψ := syllogism permutationConj weakeningConj

def implProjLeft : Γ ⊢ ϕ ⇒ (ψ ⇒ ϕ) := exportation weakeningConj

def disjOfAndElimLeft : Γ ⊢ (ϕ ∧∧ ψ) ⇒ (ϕ ∨∨ γ) := syllogism weakeningConj weakeningDisj

def implSelf : Γ ⊢ ϕ ⇒ ϕ := syllogism contractionConj weakeningConj

def conjIntro : Γ ⊢ ϕ ⇒ ψ ⇒ ϕ ∧∧ ψ := exportation implSelf

def modusPonensAndTh1 : Γ ⊢ (ϕ ⇒ ψ) ∧∧ ϕ ⇒ ψ := importation implSelf

def modusPonensAndTh2 : Γ ⊢ ϕ ∧∧ (ϕ ⇒ ψ) ⇒ ψ := syllogism permutationConj modusPonensAndTh1

def modusPonensTh : Γ ⊢ ϕ ⇒ (ϕ ⇒ ψ) ⇒ ψ := exportation modusPonensAndTh2

def andElimLeftLeft : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ := syllogism weakeningConj weakeningConj

def andElimLeftRight : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ψ := syllogism weakeningConj conjElimRight

def andElimRightLeft : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ ψ := syllogism conjElimRight weakeningConj

def andElimRightRight : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ χ := syllogism conjElimRight conjElimRight

def orIntroRightLeft : Γ ⊢ ψ ⇒ (ϕ ∨∨ (ψ ∨∨ χ)) := syllogism weakeningDisj disjIntroRight

def orIntroRightRight : Γ ⊢ χ ⇒ (ϕ ∨∨ (ψ ∨∨ χ)) := syllogism disjIntroRight disjIntroRight

def orIntroLeftLeft : Γ ⊢ ϕ ⇒ (ϕ ∨∨ ψ) ∨∨ χ := syllogism weakeningDisj weakeningDisj

def orIntroLeftRight : Γ ⊢ ψ ⇒ (ϕ ∨∨ ψ) ∨∨ χ := syllogism disjIntroRight weakeningDisj

def conjIntroRule : Γ ⊢ ϕ -> Γ ⊢ ψ -> Γ ⊢ ϕ ∧∧ ψ :=
  fun p1 p2 => modusPonens p2 (modusPonens p1 (exportation implSelf))

def conjImplIntroRule : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ⇒ χ -> Γ ⊢ ϕ ⇒ ψ ∧∧ χ := fun p1 p2 =>
  syllogism contractionConj (importation (syllogism p2 (exportation (syllogism permutationConj
                                                    (importation (syllogism p1 (exportation implSelf)))))))

def equivIntro : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ψ ⇒ ϕ -> Γ ⊢ ϕ ⇔ ψ := conjIntroRule

def extraPremise : Γ ⊢ ϕ -> Γ ⊢ ψ ⇒ ϕ := fun p => modusPonens p implProjLeft

def conjEquiv : Γ ⊢ ϕ ⇔ ϕ ∧∧ ϕ := conjIntroRule contractionConj weakeningConj

def disjEquiv : Γ ⊢ ϕ ⇔ ϕ ∨∨ ϕ := conjIntroRule weakeningDisj contractionDisj

def andAssoc1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ ∧∧ (ψ ∧∧ χ) :=
  conjImplIntroRule andElimLeftLeft (conjImplIntroRule andElimLeftRight conjElimRight)

def andAssoc2 : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ (ϕ ∧∧ ψ) ∧∧ χ :=
  conjImplIntroRule (conjImplIntroRule weakeningConj andElimRightLeft) andElimRightRight

def andAssoc : Γ ⊢ Formula.equivalence (ϕ ∧∧ (ψ ∧∧ χ)) ((ϕ ∧∧ ψ) ∧∧ χ) :=
  conjIntroRule andAssoc2 andAssoc1

def andAssocComm1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ψ ∧∧ (χ ∧∧ ϕ) :=
  conjImplIntroRule andElimLeftRight (conjImplIntroRule conjElimRight andElimLeftLeft)

def andAssocComm2 : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ ψ ∧∧ (ϕ ∧∧ χ) :=
  conjImplIntroRule (syllogism andAssoc2 andElimLeftRight)
                    (syllogism andAssoc2 (conjImplIntroRule andElimLeftLeft conjElimRight))

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

def andOrWeakening : Γ ⊢ ϕ ∧∧ (ϕ ∨∨ ψ) ⇒ ϕ := weakeningConj

def andOrContraction : Γ ⊢ ϕ ⇒ ϕ ∧∧ (ϕ ∨∨ ψ) := conjImplIntroRule implSelf weakeningDisj

def andOrWeakContr : Γ ⊢ ϕ ⇔ ϕ ∧∧ (ϕ ∨∨ ψ) := conjIntroRule andOrContraction andOrWeakening

def orAndWeakening : Γ ⊢ ϕ ∨∨ (ϕ ∧∧ ψ) ⇒ ϕ := syllogism (expansion weakeningConj) contractionDisj

def orAndContraction : Γ ⊢ ϕ ⇒ ϕ ∨∨ (ϕ ∧∧ ψ) := weakeningDisj

def orAndWeakContr : Γ ⊢ ϕ ⇔ ϕ ∨∨ (ϕ ∧∧ ψ) := conjIntroRule orAndContraction orAndWeakening

def permuteHyps : Γ ⊢ ϕ ⇒ ψ ⇒ χ -> Γ ⊢ ψ ⇒ ϕ ⇒ χ := fun p => exportation (importationComm p)

def modusPonensExtraHyp : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ϕ ⇒ χ := fun p1 p2 =>
  syllogism (extraPremiseConjIntroRight1 p1) (importation p2)

def implExtraHypRev : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) := fun p =>
  exportation (conjImplComm (syllogism (andImplDistrib p implSelf) modusPonensAndTh2))

def implConclTrans : Γ ⊢ ϕ ⇒ ψ ⇒ χ -> Γ ⊢ χ ⇒ γ -> Γ ⊢ ϕ ⇒ ψ ⇒ γ := fun p1 p2 =>
  exportation (syllogism (importation p1) p2)

def implOrExtraHyp : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ χ := fun p =>
  syllogism (syllogism permutationDisj (expansion p)) permutationDisj

def extraPremiseDisjIntro1 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ϕ ∨∨ ψ ⇒ ψ := fun p =>
  syllogism (implOrExtraHyp p) contractionDisj

def extraPremiseDisjIntro2 : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ψ ∨∨ ϕ ⇒ ψ := fun p =>
  syllogism (expansion p) contractionDisj

def disjIntroAtHyp : Γ ⊢ ϕ ⇒ χ -> Γ ⊢ ψ ⇒ χ -> Γ ⊢ ϕ ∨∨ ψ ⇒ χ := fun p1 p2 =>
  syllogism (expansion p2) (extraPremiseDisjIntro1 p1)

def orImplDistrib : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ χ ⇒ γ -> Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ γ := fun p1 p2 =>
  disjIntroAtHyp (syllogism p1 weakeningDisj) (syllogism p2 disjIntroRight)

def orAssoc1 : Γ ⊢ (ϕ ∨∨ ψ) ∨∨ χ ⇒ ϕ ∨∨ (ψ ∨∨ χ) :=
  disjIntroAtHyp (disjIntroAtHyp weakeningDisj orIntroRightLeft) orIntroRightRight

def orAssoc2 : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ (ϕ ∨∨ ψ) ∨∨ χ :=
  disjIntroAtHyp orIntroLeftLeft (disjIntroAtHyp orIntroLeftRight disjIntroRight)

def orAssoc : Γ ⊢ Formula.equivalence (ϕ ∨∨ (ψ ∨∨ χ)) ((ϕ ∨∨ ψ) ∨∨ χ) :=
  conjIntroRule orAssoc2 orAssoc1

def orAssocComm1 : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ ψ ∨∨ (χ ∨∨ ϕ) :=
  syllogism permutationDisj orAssoc1

def orAssocComm2 : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ ψ ∨∨ (ϕ ∨∨ χ) :=
  let Hperm := @implOrExtraHyp Γ (ϕ ∨∨ ψ) (ψ ∨∨ ϕ) χ (@permutationDisj Γ ϕ ψ)
  syllogism orAssoc2 (syllogism Hperm orAssoc1)

def implDistrib : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation (modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftLeft) andElimLeftRight))

def exportationTh : Γ ⊢ (ϕ ∧∧ ψ ⇒ χ) ⇒ ϕ ⇒ ψ ⇒ χ :=
  exportation (exportation (modusPonensExtraHyp (conjImplIntroRule andElimLeftRight conjElimRight) andElimLeftLeft))

def importationTh : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ :=
  exportation (modusPonensExtraHyp andElimRightRight (modusPonensExtraHyp andElimRightLeft weakeningConj))

def impExpEquiv : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇔ (ϕ ∧∧ ψ ⇒ χ) := conjIntroRule importationTh exportationTh

def permuteHypsTh : Γ ⊢ (ϕ ⇒ (ψ ⇒ χ)) ⇒ (ψ ⇒ (ϕ ⇒ χ)) :=
  exportation (exportation (modusPonensExtraHyp andElimLeftRight (modusPonensExtraHyp conjElimRight andElimLeftLeft)))

def modusPonensExtraHypTh1 : Γ ⊢ ((ϕ ⇒ (ψ ⇒ χ)) ∧∧ (ϕ ⇒ ψ)) ∧∧ ϕ ⇒ χ :=
  modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftRight) (modusPonensExtraHyp conjElimRight andElimLeftLeft)

def modusPonensExtraHypTh2 : Γ ⊢ ((ϕ ⇒ ψ) ∧∧ (ϕ ⇒ (ψ ⇒ χ))) ∧∧ ϕ ⇒ χ :=
  modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftLeft) (modusPonensExtraHyp conjElimRight andElimLeftRight)

def implDistrib1 : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇒ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation modusPonensExtraHypTh1)

def implDistrib1Perm : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ ψ ⇒ χ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation modusPonensExtraHypTh2)

def conjImplIntroTh : Γ ⊢ (ϕ ⇒ ψ) ∧∧ (ϕ ⇒ χ) ⇒ (ϕ ⇒ ψ ∧∧ χ) :=
  exportation (conjImplIntroRule (modusPonensExtraHyp conjElimRight andElimLeftLeft) (modusPonensExtraHyp conjElimRight andElimLeftRight))

def conjImplIntroThExp : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) ⇒ (ϕ ⇒ ψ ∧∧ χ) := exportation conjImplIntroTh

def conjImplDisj : Γ ⊢ (ϕ ⇒ χ) ∧∧ (ψ ⇒ χ) ⇒ (ϕ ∨∨ ψ ⇒ χ) :=
  permuteHyps (disjIntroAtHyp (permuteHyps weakeningConj) (permuteHyps conjElimRight))

def conjImplDisjExp : Γ ⊢ (ϕ ⇒ χ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ∨∨ ψ ⇒ χ) := exportation conjImplDisj

def orFalse : Γ ⊢ ϕ ∨∨ ⊥ ⇒ ϕ := modusPonens exfalso (modusPonens implSelf conjImplDisjExp)

def extraPremiseConjTh : Γ ⊢ (ϕ ∧∧ (ϕ ⇒ ψ) ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ :=
  implExtraHypRev (andImplDistrib implSelf implProjLeft)

def implDistrib2 : Γ ⊢ ((ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ)) ⇒ ϕ ⇒ ψ ⇒ χ :=
  syllogism (syllogism (syllogism permuteHypsTh importationTh) extraPremiseConjTh) exportationTh

def implDistribEquiv : Γ ⊢ ((ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ)) ⇔ (ϕ ⇒ ψ ⇒ χ) :=
  conjIntroRule implDistrib2 implDistrib1

def implDistribRule1 : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) -> Γ ⊢ ϕ ⇒ ψ ⇒ χ := fun p =>
  exportation (modusPonens (conjImplComm (importation p)) extraPremiseConjTh)

def syllogism_th : Γ ⊢ ϕ ⇒ ψ ⇒ χ -> Γ ⊢ ϕ ⇒ χ ⇒ γ -> Γ ⊢ ϕ ⇒ ψ ⇒ γ := fun p1 p2 =>
  implDistribRule1 (syllogism (modusPonens p1 implDistrib1) (modusPonens p2 implDistrib1))

def exp_extra_hyp : Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) -> Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) := fun p =>
  exportation (exportation (syllogism andAssoc1 (importation p)))

def imp_extra_hyp : Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) -> Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) := fun p =>
  exportation (syllogism andAssoc2 (importation (importation p)))

def dni : Γ ⊢ ϕ ⇒ ~(~ϕ) := modusPonensTh

def dniNeg : Γ ⊢ (~ϕ) ⇒ ~(~(~ϕ)) := dni

def exFalsoImpl : Γ ⊢ ϕ ⇒ (~ϕ ⇒ ψ) := exportation (syllogism modusPonensAndTh2 exfalso)

def exFalsoAnd : Γ ⊢ ϕ ∧∧ ~ ϕ ⇒ ψ := importation exFalsoImpl

def contraposition : Γ ⊢ (ϕ ⇒ ψ) ⇒ (~ψ ⇒ ~ϕ) := implDistrib

def contradictImpl : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ ~ψ) ⇒ ~ϕ := implDistrib1Perm

def notConjContradict : Γ ⊢ ~(ϕ ∧∧ ~ϕ) := modusPonensAndTh2

def deMorgan1 : Γ ⊢ ~ϕ ∧∧ ~ψ ⇒ ~(ϕ ∨∨ ψ) := conjImplDisj

def orContradict1 : Γ ⊢ ϕ ⇒ ϕ ∨∨ (ψ ∧∧ ~ψ) := weakeningDisj

def orContradict2 : Γ ⊢ ϕ ∨∨ (ψ ∧∧ ~ψ) ⇒ ϕ :=
  disjIntroAtHyp implSelf (syllogism notConjContradict exfalso)

def andContradict1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ ~ψ ⇒ ϕ := andElimLeftLeft

def impldef : Γ ⊢ (~ϕ ∨∨ ψ) ⇒ (ϕ ⇒ ψ) := sorry

def vpnotvp_impl_vp : Γ ⊢ (~ϕ ⇒ ϕ) ⇒ ϕ := sorry

def contra : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ~ϕ ⇒ ψ -> Γ ⊢ ψ :=
  by
    intros Hvp Hnvp
    apply modusPonens (syllogism (modusPonens Hvp contraposition) Hnvp) vpnotvp_impl_vp

lemma subset_proof : Δ ⊆ Γ -> Δ ⊢ ϕ -> Γ ⊢ ϕ :=
  by
    intros Hsubseteq Hdelta
    induction Hdelta with
    | premise Hvp => exact (premise (Set.mem_of_mem_of_subset Hvp Hsubseteq))
    | contractionDisj => exact contractionDisj
    | contractionConj => exact contractionConj
    | weakeningDisj => exact weakeningDisj
    | weakeningConj => exact weakeningConj
    | permutationDisj => exact permutationDisj
    | permutationConj => exact permutationConj
    | exfalso => exact exfalso
    | modusPonens _ _ ih1 ih2 => exact (modusPonens ih1 ih2)
    | syllogism _ _ ih1 ih2 => exact (syllogism ih1 ih2)
    | exportation _ ih => exact (exportation ih)
    | importation _ ih => exact (importation ih)
    | expansion _ ih => exact (expansion ih)

lemma empty_proof : ∅ ⊢ ϕ -> Γ ⊢ ϕ :=
  by
    intros Hempty
    eapply subset_proof (Set.empty_subset Γ); assumption

lemma set_conseq_proof (Hset : @set_proof_set Γ Δ) : Δ ⊢ ϕ -> Γ ⊢ ϕ :=
  by
    intros Hdelta
    simp [set_proof_set] at Hset
    induction Hdelta with
    | premise _ => apply Hset; assumption
    | contractionDisj => exact contractionDisj
    | contractionConj => exact contractionConj
    | weakeningDisj => exact weakeningDisj
    | weakeningConj => exact weakeningConj
    | permutationDisj => exact permutationDisj
    | permutationConj => exact permutationConj
    | exfalso => exact exfalso
    | modusPonens _ _ ih1 ih2 => exact (modusPonens ih1 ih2)
    | syllogism _ _ ih1 ih2 => exact (syllogism ih1 ih2)
    | exportation _ ih => exact (exportation ih)
    | importation _ ih => exact (importation ih)
    | expansion _ ih => exact (expansion ih)

noncomputable instance {ϕ ψ : Formula} : Decidable (ϕ = ψ) := @default _ (Classical.decidableInhabited _)

noncomputable def usedPremises {ϕ : Formula} : Proof Γ ϕ -> Finset Formula
  | premise Hvp => {ϕ}
  | contractionDisj => ∅
  | contractionConj => ∅
  | weakeningDisj => ∅
  | weakeningConj => ∅
  | permutationDisj => ∅
  | permutationConj => ∅
  | exfalso => ∅
  | modusPonens p1 p2 => usedPremises p1 ∪ usedPremises p2
  | syllogism p1 p2 => usedPremises p1 ∪ usedPremises p2
  | exportation p => usedPremises p
  | importation p => usedPremises p
  | expansion p => usedPremises p

noncomputable def toFinitePremises {ϕ : Formula} (p : Proof Γ ϕ) : Proof (@usedPremises Γ ϕ p).toSet ϕ :=
  match p with
  | premise Hvp => have Helem : ϕ ∈ ↑(usedPremises (premise Hvp)) := by simp; unfold usedPremises; simp
                   premise Helem
  | contractionDisj => contractionDisj
  | contractionConj => contractionConj
  | weakeningDisj => weakeningDisj
  | weakeningConj => weakeningConj
  | permutationDisj => permutationDisj
  | permutationConj => permutationConj
  | exfalso => exfalso
  | modusPonens p1 p2 => have Hincl1 : usedPremises p1 ⊆ usedPremises (modusPonens p1 p2) :=
                          by
                            simp [usedPremises]
                            apply Finset.subset_union_left
                         let Hsubset1 := subset_proof Hincl1 (toFinitePremises p1)
                         have Hincl2 : usedPremises p2 ⊆ usedPremises (modusPonens p1 p2) :=
                          by
                            simp [usedPremises]
                            apply Finset.subset_union_right
                         let Hsubset2 := subset_proof Hincl2 (toFinitePremises p2)
                         modusPonens Hsubset1 Hsubset2
  | syllogism p1 p2 => have Hincl1 : usedPremises p1 ⊆ usedPremises (syllogism p1 p2) :=
                        by
                          simp [usedPremises]
                          apply Finset.subset_union_left
                       let Hsubset1 := subset_proof Hincl1 (toFinitePremises p1)
                       have Hincl2 : usedPremises p2 ⊆ usedPremises (syllogism p1 p2) :=
                        by
                          simp [usedPremises]
                          apply Finset.subset_union_right
                       let Hsubset2 := subset_proof Hincl2 (toFinitePremises p2)
                       syllogism Hsubset1 Hsubset2
  | exportation p => exportation (toFinitePremises p)
  | importation p => importation (toFinitePremises p)
  | expansion p => expansion (toFinitePremises p)

lemma lemma_finset (p : Proof Γ ϕ) : ∃ (Ω : Finset Formula), Ω.toSet ⊆ Γ /\ Nonempty (Ω.toSet ⊢ ϕ) :=
  by
    exists usedPremises p
    apply And.intro
    · induction p with
      | premise Hvp => unfold usedPremises; simp; assumption
      | contractionDisj | contractionConj | weakeningDisj | weakeningConj
        | permutationDisj | permutationConj | exfalso => unfold usedPremises; simp
      | modusPonens p1 p2 ih1 ih2 | syllogism p1 p2 ih1 ih2 =>
        unfold usedPremises; simp; apply And.intro; assumption'
      | importation p ih | exportation p ih | expansion p ih => unfold usedPremises; assumption
    · apply Nonempty.intro
      apply toFinitePremises

noncomputable instance {ϕ : Formula} {Γ : Set Formula} : Decidable (ϕ ∈ Γ) := @default _ (Classical.decidableInhabited _)

noncomputable def deductionTheorem_left {ϕ ψ : Formula} (p : Γ ∪ {ϕ} ⊢ ψ) : Γ ⊢ ϕ ⇒ ψ :=
  match p with
  | premise Hvp =>
    if Hvpin : ψ ∈ Γ then
      have Hpsi : Γ ⊢ ψ := premise Hvpin
      extraPremise Hpsi
    else
      have Heq : ψ = ϕ :=
      by
        cases Hvp
        · contradiction
        · assumption
      have l : Γ ⊢ ϕ ⇒ ϕ := implSelf
      by rw [Heq]; assumption
  | contractionDisj => extraPremise contractionDisj
  | contractionConj => extraPremise contractionConj
  | weakeningDisj => extraPremise weakeningDisj
  | weakeningConj => extraPremise weakeningConj
  | permutationDisj => extraPremise permutationDisj
  | permutationConj => extraPremise permutationConj
  | exfalso => extraPremise exfalso
  | modusPonens p1 p2 => modusPonensExtraHyp (deductionTheorem_left p1) (deductionTheorem_left p2)
  | syllogism p1 p2 => syllogism_th (deductionTheorem_left p1) (deductionTheorem_left p2)
  | importation p => imp_extra_hyp (deductionTheorem_left p)
  | exportation p => exp_extra_hyp (deductionTheorem_left p)
  | expansion p =>
    permuteHyps (disjIntroAtHyp (exportation disjOfAndElimLeft)
                (implConclTrans (permuteHyps (deductionTheorem_left p)) disjIntroRight))

noncomputable def deductionTheorem_right {ϕ ψ : Formula} (p : Γ ⊢ ϕ ⇒ ψ) : Γ ∪ {ϕ} ⊢ ψ :=
  let p0 : Γ ⊆ Γ ∪ {ϕ} := Set.subset_union_left Γ {ϕ}
  let p1 : Γ ∪ {ϕ} ⊢ ϕ ⇒ ψ := subset_proof p0 p
  let p2 : ϕ ∈ Γ ∪ {ϕ} := by rw [Set.mem_union]; apply Or.inr; apply Set.mem_singleton
  modusPonens (premise p2) p1

lemma deductionTheorem_left_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
  Δ ∪ Γ.toFinset ⊢ ϕ -> Δ ⊢ Γ.foldr Formula.implication ϕ :=
  by
    revert Δ
    induction Γ with
    | nil => intros Δ Hdelta
             simp
             rw [List.toFinset_nil, Finset.coe_empty, Set.union_empty] at Hdelta
             assumption
    | cons h t ih => intros Δ Hdelta
                     have Haux : Δ ∪ {h} ∪ (List.toFinset t).toSet ⊢ ϕ :=
                      by
                        rw [List.toFinset_cons, Finset.insert_eq, Finset.coe_union,
                            Finset.coe_singleton, <-Set.union_assoc] at Hdelta
                        assumption
                     let Hih := @ih (Δ ∪ {h}) Haux
                     let Hthded := deductionTheorem_left Hih
                     unfold List.foldr
                     rcases Hlist : Finset.toList (List.toFinset (h :: t)) with _ | ⟨h', t'⟩
                     · simp at Hlist
                     · simp at Hlist
                       assumption

lemma deductionTheorem_right_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
  Δ ⊢ Γ.foldr Formula.implication ϕ -> Δ ∪ Γ.toFinset ⊢ ϕ :=
  by
    revert Δ
    induction Γ with
    | nil => intros Δ Hdelta
             simp
             simp at Hdelta
             assumption
    | cons h t ih => intros Δ Hdelta
                     unfold List.foldr at Hdelta
                     let Hthded := deductionTheorem_right Hdelta
                     let Hih := @ih (Δ ∪ {h}) Hthded
                     rw [List.toFinset_cons, Finset.insert_eq, Finset.coe_union, Finset.coe_singleton, <-Set.union_assoc]
                     assumption

lemma exportation_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
  Δ ⊢ Γ.foldr Formula.and (~⊥) ⇒ ϕ -> Δ ⊢ Γ.foldr Formula.implication ϕ :=
  by
    revert Δ
    induction Γ with
    | nil => simp
             intros Δ Hnot
             have Htrue : Δ ⊢ ~⊥ := by apply implSelf
             apply modusPonens Htrue Hnot
    | cons h t ih => simp
                     intros Δ Hand
                     let Hexp := exportation Hand
                     let Hded := deductionTheorem_right Hexp
                     let Hih := @ih (Δ ∪ {h}) Hded
                     let Hded' := deductionTheorem_left Hih
                     assumption

lemma importation_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
  Δ ⊢ Γ.foldr Formula.implication ϕ -> Δ ⊢ Γ.foldr Formula.and (~⊥) ⇒ ϕ :=
  by
    revert Δ
    induction Γ with
    | nil => simp
             intros Δ Hdelta
             apply deductionTheorem_left
             have Hincl : Δ ⊆ Δ ∪ {~⊥} := by apply Set.subset_union_left
             apply subset_proof Hincl
             assumption
    | cons h t ih => simp
                     intros Δ Himpl
                     apply importation
                     apply deductionTheorem_left
                     let Hded := deductionTheorem_right Himpl
                     let Hih := @ih (Δ ∪ {h}) Hded
                     assumption

lemma permutationConj_ind (l1 l2 : List Formula) (Hperm : l1 ~ l2) :
  Nonempty (∅ ⊢ List.foldr Formula.and (~⊥) l1 ⇒ List.foldr Formula.and (~⊥) l2) :=
  by
    induction Hperm with
    | nil => simp; apply Nonempty.intro; apply implSelf
    | @cons x l1' l2' ihperm ihequiv => simp; apply Nonempty.intro; let Haux := Classical.choice ihequiv
                                        let Haux' := @conjElimRight ∅ x (List.foldr Formula.and (~⊥) l1')
                                        let Hsyllog := syllogism Haux' Haux
                                        let Haux'' := @weakeningConj ∅ x (List.foldr Formula.and (~⊥) l1')
                                        apply conjImplIntroRule Haux'' Hsyllog
    | swap x y l => simp; apply Nonempty.intro; apply andAssocComm2
    | @trans l1' l2' l3' ihperm12 ihperm23 ihequiv12 ihequiv23 => apply Nonempty.intro;
                                                                  apply syllogism (Classical.choice ihequiv12) (Classical.choice ihequiv23)

lemma permutationDisj_ind (l1 l2 : List Formula) (Hperm : l1 ~ l2) :
  Nonempty (∅ ⊢ List.foldr Formula.or ⊥ l1 ⇒ List.foldr Formula.or ⊥ l2) :=
  by
    induction Hperm with
    | nil => simp; apply Nonempty.intro; apply implSelf
    | @cons x l1' l2' ihperm ihequiv => simp; apply Nonempty.intro; let Haux := Classical.choice ihequiv
                                        apply expansion Haux
    | swap x y l => simp; apply Nonempty.intro; apply orAssocComm2
    | @trans l1' l2' l3' ihperm12 ihperm23 ihequiv12 ihequiv23 => apply Nonempty.intro;
                                                                  apply syllogism (Classical.choice ihequiv12) (Classical.choice ihequiv23)

def pfoldrAndUnion (Φ Ω : Finset Formula) :=
  Nonempty (∅ ⊢ List.foldr Formula.and (~⊥) (Φ ∪ Ω).toList ⇒
  List.foldr Formula.and (~⊥) Φ.toList ∧∧ List.foldr Formula.and (~⊥) Ω.toList)

noncomputable def andTrue : Γ ⊢ ϕ ⇒ (~⊥) ∧∧ ϕ :=
  conjImplIntroRule (deductionTheorem_left implSelf) implSelf

lemma foldrAndUnion_empty (Ω : Finset Formula) :
  pfoldrAndUnion ∅ Ω :=
  by
    unfold pfoldrAndUnion; simp
    apply Nonempty.intro
    apply andTrue

lemma foldrAndUnion_insert (ϕ : Formula) (Φ Ω : Finset Formula) (Hnotin : ϕ ∉ Φ)
  (Hprev : pfoldrAndUnion Φ Ω) : pfoldrAndUnion (insert ϕ Φ) Ω :=
  by
    unfold pfoldrAndUnion; simp
    apply Nonempty.intro
    let Hprev := Classical.choice Hprev
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    let Hperm := Finset.toList_cons Hnotin
    let Haux := Classical.choice (permutationConj_ind (Finset.toList (Finset.cons ϕ Φ Hnotin))
                (ϕ :: Finset.toList Φ) Hperm)
    simp at Haux
    by_cases Hinomega : ϕ ∈ Ω
    · rw [<-Finset.insert_eq]
      rw [<-Finset.insert_eq]
      have Hinsert : insert ϕ (Φ ∪ Ω) = (Φ ∪ Ω) := by simp; apply Or.inr; assumption
      rw [Hinsert]
      have Hh : ∅ ⊢ List.foldr Formula.and (~⊥) (Finset.toList (Φ ∪ Ω)) ⇒ ϕ :=
        by
          apply importation_ind
          apply deductionTheorem_left_ind
          rw [Set.empty_union]
          apply premise
          rw [Finset.toList_toFinset, Finset.mem_coe]
          apply Finset.mem_union_right Φ Hinomega
      have Hconj := conjImplIntroRule Hh Hprev
      let Hperm' := List.Perm.symm (Finset.toList_cons Hnotin)
      let Haux' := Classical.choice (permutationConj_ind (ϕ :: Finset.toList Φ)
                   (Finset.toList (Finset.cons ϕ Φ Hnotin)) Hperm')
      simp at Haux'
      let Hweakconj := @weakeningConj ∅ (ϕ∧∧List.foldr Formula.and (~⊥) (Finset.toList Φ))
                       (List.foldr Formula.and (~⊥) (Finset.toList Ω))
      let Hsyllog := syllogism Hweakconj Haux'
      let Hassoc := @andAssoc2 ∅ ϕ (List.foldr Formula.and (~⊥) (Finset.toList Φ))
                    (List.foldr Formula.and (~⊥) (Finset.toList Ω))
      let Hsyllog := syllogism Hassoc Hsyllog
      let Hweakconj2 := @andElimRightRight ∅ ϕ (List.foldr Formula.and (~⊥) (Finset.toList Φ))
                    (List.foldr Formula.and (~⊥) (Finset.toList Ω))
      let Hconj' := conjImplIntroRule Hsyllog Hweakconj2
      apply syllogism Hconj Hconj'
    · have Hnotinunion : ϕ ∉ Φ ∪ Ω :=
        by
          rw [Finset.not_mem_union]
          apply And.intro; assumption'
      let Hperm' := Finset.toList_cons Hnotinunion
      let Haux' := Classical.choice (permutationConj_ind (Finset.toList (Finset.cons ϕ (Φ ∪ Ω) Hnotinunion))
                   (ϕ :: Finset.toList (Φ ∪ Ω)) Hperm')
      simp at Haux'
      let Hweakconj1 := @weakeningConj ∅ ϕ (List.foldr Formula.and (~⊥) (Finset.toList (Φ ∪ Ω)))
      let Hsyllog1 := syllogism Haux' Hweakconj1
      let Hweakconj2 := @conjElimRight ∅ ϕ (List.foldr Formula.and (~⊥) (Finset.toList (Φ ∪ Ω)))
      let Hsyllog2 := syllogism (syllogism Haux' Hweakconj2) Hprev
      let Hconj := conjImplIntroRule Hsyllog1 Hsyllog2
      let Hassoc := @andAssoc2 ∅ ϕ (List.foldr Formula.and (~⊥) (Finset.toList Φ))
                    (List.foldr Formula.and (~⊥) (Finset.toList Ω))
      let Hsyllog := syllogism Hconj Hassoc
      let Hperm'' := List.Perm.symm (Finset.toList_cons Hnotin)
      let Haux'' := Classical.choice (permutationConj_ind (ϕ :: Finset.toList Φ)
                    (Finset.toList (Finset.cons ϕ Φ Hnotin)) Hperm'')
      simp at Haux''
      let Hweakconj1 := @weakeningConj ∅ (ϕ∧∧List.foldr Formula.and (~⊥) (Finset.toList Φ))
                        (List.foldr Formula.and (~⊥) (Finset.toList Ω))
      let Hsyllog' := syllogism Hweakconj1 Haux''
      let Hweakconj2 := @conjElimRight ∅ (ϕ∧∧List.foldr Formula.and (~⊥) (Finset.toList Φ))
                        (List.foldr Formula.and (~⊥) (Finset.toList Ω))
      let Hconj := conjImplIntroRule Hsyllog' Hweakconj2
      apply syllogism Hsyllog Hconj

lemma foldrAndUnion (Φ Ω : Finset Formula) : pfoldrAndUnion Φ Ω :=
  by
    unfold pfoldrAndUnion
    induction Φ using Finset.induction_on with
    | empty => exact foldrAndUnion_empty Ω
    | @insert ϕ Φ Hnotin Hprev => exact foldrAndUnion_insert ϕ Φ Ω Hnotin Hprev

def pfoldrOrUnion (Φ Ω : Finset Formula) :=
  Nonempty (∅ ⊢ List.foldr Formula.or ⊥ Φ.toList ∨∨ List.foldr Formula.or ⊥ Ω.toList ⇒
  List.foldr Formula.or ⊥ (Φ ∪ Ω).toList)

lemma foldrOrUnion_empty (Ω : Finset Formula) :
  pfoldrOrUnion ∅ Ω :=
  by
    unfold pfoldrOrUnion; simp
    apply Nonempty.intro
    apply syllogism permutationDisj orFalse

lemma foldrOrUnion_insert (ϕ : Formula) (Φ Ω : Finset Formula) (Hnotin : ϕ ∉ Φ)
  (Hprev : pfoldrOrUnion Φ Ω) : pfoldrOrUnion (insert ϕ Φ) Ω :=
  by
    unfold pfoldrOrUnion; simp
    apply Nonempty.intro
    let Hprev := Classical.choice Hprev
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    let Hperm := Finset.toList_cons Hnotin
    let Haux := Classical.choice (permutationDisj_ind (Finset.toList (Finset.cons ϕ Φ Hnotin)) (ϕ :: Finset.toList Φ) Hperm)
    simp at Haux
    let Hexp := @implOrExtraHyp ∅ (List.foldr Formula.or ⊥ (Finset.toList (insert ϕ Φ)))
               (ϕ ∨∨ List.foldr Formula.or ⊥ (Finset.toList Φ)) (List.foldr Formula.or ⊥ (Finset.toList Ω)) Haux
    let Hassoc := @orAssoc1 ∅ ϕ (List.foldr Formula.or ⊥ (Finset.toList Φ)) (List.foldr Formula.or ⊥ (Finset.toList Ω))
    let Hsyllog := syllogism Hexp Hassoc
    let Hexpprev := @expansion ∅ (List.foldr Formula.or ⊥ (Finset.toList Φ)∨∨List.foldr Formula.or ⊥ (Finset.toList Ω))
                    (List.foldr Formula.or ⊥ (Finset.toList (Φ ∪ Ω))) ϕ Hprev
    let Hsyllog := syllogism Hsyllog Hexpprev
    by_cases Hinomega : ϕ ∈ Ω
    · rw [<-Finset.insert_eq]
      rw [<-Finset.insert_eq]
      have Haux : insert ϕ (Φ ∪ Ω) = (Φ ∪ Ω) := by simp; apply Or.inr; assumption
      rw [Haux]
      have Haux : Φ ∪ Ω = {ϕ} ∪ ((Φ ∪ Ω) \ {ϕ}) :=
        by
          simp
          apply Or.inr
          rw [<-Finset.mem_toList]
          simp
          assumption
      have Hnotin : ϕ ∉ (Φ ∪ Ω) \ {ϕ} := by simp
      have Hperm : (Φ ∪ Ω).toList ~ ϕ :: ((Φ ∪ Ω) \ {ϕ}).toList :=
        by
          let Hcons := Finset.toList_cons Hnotin
          simp at Hcons
          rw [Finset.insert_eq] at Hcons
          rw [<-Haux] at Hcons
          assumption
      let Hpermsymm := List.Perm.symm Hperm
      let Hpermequiv := Classical.choice (permutationDisj_ind (ϕ :: Finset.toList ((Φ ∪ Ω) \ {ϕ})) (Finset.toList (Φ ∪ Ω)) Hpermsymm)
      simp at Hpermequiv
      have Hh : ∅ ⊢ ϕ ⇒ List.foldr Formula.or ⊥ (Finset.toList (Φ ∪ Ω)) :=
        by
          let Hweak := @weakeningDisj ∅ ϕ (List.foldr Formula.or ⊥ (Finset.toList ((Φ ∪ Ω) \ {ϕ})))
          apply syllogism Hweak Hpermequiv
      let Hself := @implSelf ∅ (List.foldr Formula.or ⊥ (Finset.toList (Φ ∪ Ω)))
      let Haux := disjIntroAtHyp Hh Hself
      let Hsyllog := syllogism Hsyllog Haux
      assumption
    · have Hnotinunion : ϕ ∉ Φ ∪ Ω :=
        by
          rw [Finset.not_mem_union]
          apply And.intro; assumption'
      let Hperm' := List.Perm.symm (Finset.toList_cons Hnotinunion)
      let Haux' := Classical.choice (permutationDisj_ind (ϕ :: Finset.toList (Φ ∪ Ω)) (Finset.toList (Finset.cons ϕ (Φ ∪ Ω) Hnotinunion)) Hperm')
      simp at Haux'
      let Hsyllog' := syllogism Hsyllog Haux'
      rw [Finset.insert_eq] at Hsyllog'
      rw [Finset.insert_eq] at Hsyllog'
      assumption

lemma foldrOrUnion (Φ Ω : Finset Formula) : pfoldrOrUnion Φ Ω :=
  by
    unfold pfoldrOrUnion
    induction Φ using Finset.induction_on with
    | empty => exact foldrOrUnion_empty Ω
    | @insert ϕ Φ Hnotin Hprev => exact foldrOrUnion_insert ϕ Φ Ω Hnotin Hprev

end Proof

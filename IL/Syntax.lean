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
--| existGen {ϕ ψ} {x} (not_fv : ¬(isfreeVar ψ x)) : Proof Γ (ϕ ⇒ ψ) -> Proof Γ (∃∃ x ϕ ⇒ ψ)
--| forallGen {ϕ ψ} {x} (not_fv : ¬(isfreeVar ψ x)) : Proof Γ (ϕ ⇒ ψ) -> Proof Γ (∀∀ x ϕ ⇒ ψ)

infix:25 " ⊢ " => Proof

namespace Proof

variable {Γ Δ : Set Formula} {ϕ ψ χ γ : Formula}

def set_proof_set : Type :=
  forall (ϕ : Formula), ϕ ∈ Δ -> Γ ⊢ ϕ

theorem subset_proof : Δ ⊆ Γ -> Δ ⊢ ϕ -> Γ ⊢ ϕ :=
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

theorem empty_proof : ∅ ⊢ ϕ -> Γ ⊢ ϕ :=
  by
    intros Hempty
    eapply subset_proof (Set.empty_subset Γ); assumption

theorem set_conseq_proof (Hset : @set_proof_set Γ Δ) : Δ ⊢ ϕ -> Γ ⊢ ϕ :=
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

def proofLength {ϕ : Formula} (p : Proof Γ ϕ) : Nat :=
  match p with
  | premise Hvp => 1
  | contractionDisj | contractionConj | weakeningDisj | weakeningConj
      | permutationDisj | permutationConj | exfalso => 1
  | modusPonens p1 p2 | syllogism p1 p2 => proofLength p1 + proofLength p2 + 1
  | exportation p | importation p | expansion p => proofLength p + 1

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

theorem theorem_finset (p : Proof Γ ϕ) : ∃ (Ω : Finset Formula), Ω.toSet ⊆ Γ /\ Nonempty (Ω.toSet ⊢ ϕ) :=
  by
    exists usedPremises p
    apply And.intro
    · induction p with
      | premise Hvp => unfold usedPremises; simp; assumption
      | contractionDisj => unfold usedPremises; simp
      | contractionConj => unfold usedPremises; simp
      | weakeningDisj => unfold usedPremises; simp
      | weakeningConj => unfold usedPremises; simp
      | permutationDisj => unfold usedPremises; simp
      | permutationConj => unfold usedPremises; simp
      | exfalso => unfold usedPremises; simp
      | modusPonens p1 p2 ih1 ih2 => unfold usedPremises; simp; apply And.intro; assumption'
      | syllogism p1 p2 ih1 ih2 => unfold usedPremises; simp; apply And.intro; assumption'
      | importation p ih => unfold usedPremises; assumption
      | exportation p ih => unfold usedPremises; assumption
      | expansion p ih => unfold usedPremises; assumption
    · apply Nonempty.intro
      apply toFinitePremises

def disjIntroRight
  : Γ ⊢ ψ ⇒ ϕ ∨∨ ψ :=
  syllogism weakeningDisj permutationDisj

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

def conjEquiv : Γ ⊢ ϕ ⇔ ϕ ∧∧ ϕ :=
  conjIntroRule contractionConj weakeningConj

def disjEquiv : Γ ⊢ ϕ ⇔ ϕ ∨∨ ϕ :=
  conjIntroRule weakeningDisj contractionDisj

def andAssoc1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ ∧∧ (ψ ∧∧ χ) :=
  conjImplIntroRule andElimLeftLeft (conjImplIntroRule andElimLeftRight conjElimRight)

def andAssoc2 : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ (ϕ ∧∧ ψ) ∧∧ χ :=
  conjImplIntroRule (conjImplIntroRule weakeningConj andElimRightLeft) andElimRightRight

def andAssoc : Γ ⊢ Formula.equivalence (ϕ ∧∧ (ψ ∧∧ χ)) ((ϕ ∧∧ ψ) ∧∧ χ) :=
  conjIntroRule andAssoc2 andAssoc1

def andAssocComm : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ψ ∧∧ (χ ∧∧ ϕ) :=
  conjImplIntroRule andElimLeftRight (conjImplIntroRule conjElimRight andElimLeftLeft)

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

def orAssocComm
  : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ ψ ∨∨ (χ ∨∨ ϕ) :=
  syllogism permutationDisj orAssoc1

def implDistrib : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation (modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftLeft) andElimLeftRight))

def exportationTh : Γ ⊢ (ϕ ∧∧ ψ ⇒ χ) ⇒ ϕ ⇒ ψ ⇒ χ :=
  exportation (exportation (modusPonensExtraHyp (conjImplIntroRule andElimLeftRight conjElimRight) andElimLeftLeft))

def importationTh : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ :=
  exportation (modusPonensExtraHyp andElimRightRight (modusPonensExtraHyp andElimRightLeft weakeningConj))

def impExpEquiv : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇔ (ϕ ∧∧ ψ ⇒ χ) :=
  conjIntroRule importationTh exportationTh

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

def conjImplIntroThExp : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) ⇒ (ϕ ⇒ ψ ∧∧ χ) :=
  exportation conjImplIntroTh

def conjImplDisj : Γ ⊢ (ϕ ⇒ χ) ∧∧ (ψ ⇒ χ) ⇒ (ϕ ∨∨ ψ ⇒ χ) :=
  permuteHyps (disjIntroAtHyp (permuteHyps weakeningConj) (permuteHyps conjElimRight))

def conjImplDisjExp : Γ ⊢ (ϕ ⇒ χ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ∨∨ ψ ⇒ χ) :=
  exportation conjImplDisj

def orFalse : Γ ⊢ ϕ ∨∨ ⊥ ⇒ ϕ :=
  modusPonens exfalso (modusPonens implSelf conjImplDisjExp)

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

def dni : Γ ⊢ ϕ ⇒ ~(~ϕ) :=
  modusPonensTh

def dniNeg : Γ ⊢ (~ϕ) ⇒ ~(~(~ϕ)) :=
  dni

def exFalsoImpl : Γ ⊢ ϕ ⇒ (~ϕ ⇒ ψ) :=
  exportation (syllogism modusPonensAndTh2 exfalso)

def exFalsoAnd : Γ ⊢ ϕ ∧∧ ~ ϕ ⇒ ψ :=
  importation exFalsoImpl

def contraposition : Γ ⊢ (ϕ ⇒ ψ) ⇒ (~ψ ⇒ ~ϕ) :=
  implDistrib

def contradictImpl : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ ~ψ) ⇒ ~ϕ :=
  implDistrib1Perm

def notConjContradict : Γ ⊢ ~(ϕ ∧∧ ~ϕ) :=
  modusPonensAndTh2

def deMorgan1 : Γ ⊢ ~ϕ ∧∧ ~ψ ⇒ ~(ϕ ∨∨ ψ) :=
  conjImplDisj

def orContradict1 : Γ ⊢ ϕ ⇒ ϕ ∨∨ (ψ ∧∧ ~ψ) :=
  weakeningDisj

def orContradict2 : Γ ⊢ ϕ ∨∨ (ψ ∧∧ ~ψ) ⇒ ϕ :=
  disjIntroAtHyp implSelf (syllogism notConjContradict exfalso)

def andContradict1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ ~ψ ⇒ ϕ :=
  andElimLeftLeft

def impldef : Γ ⊢ (~ϕ ∨∨ ψ) ⇒ (ϕ ⇒ ψ) :=
  sorry

def vpnotvp_impl_vp : Γ ⊢ (~ϕ ⇒ ϕ) ⇒ ϕ :=
  sorry

def contra : Γ ⊢ ϕ ⇒ ψ -> Γ ⊢ ~ϕ ⇒ ψ -> Γ ⊢ ψ :=
  by
    intros Hvp Hnvp
    apply modusPonens (syllogism (modusPonens Hvp contraposition) Hnvp) vpnotvp_impl_vp

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

def dedClosed {Γ : Set Formula} := forall (ϕ : Formula), Γ ⊢ ϕ -> ϕ ∈ Γ

def consistent {Γ : Set Formula} := Γ ⊢ ⊥ -> False

def disjunctive {Γ : Set Formula} := forall (ϕ ψ : Formula), Γ ⊢ ϕ ∨∨ ψ -> Sum (Γ ⊢ ϕ) (Γ ⊢ ψ)

def disjunctiveTheory {Γ : Set Formula} :=
  @dedClosed Γ /\ @consistent Γ /\ Nonempty (@disjunctive Γ)

abbrev setDisjTh := {Γ // @disjunctiveTheory Γ}

def consistentPair {Γ Δ : Set Formula} :=
  forall (Φ Ω : Finset Formula), Φ.toSet ⊆ Γ -> Ω.toSet ⊆ Δ ->
  (∅ ⊢ Φ.toList.foldr Formula.and (~⊥) ⇒ Ω.toList.foldr Formula.or ⊥ -> False)

theorem exportation_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
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

theorem importation_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
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

theorem deductionTheorem_left_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
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

theorem deductionTheorem_right_ind {Γ : List Formula} {Δ : Set Formula} {ϕ : Formula} :
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

theorem disjunctive_ind {Γ : Set Formula} {Δ : List Formula} {Hnempty : Δ ≠ []}:
  @disjunctive Γ -> Γ ⊢ List.foldr Formula.or ⊥ Δ ->
  ∃(χ : Formula), χ ∈ Δ /\ Nonempty (Γ ⊢ χ) :=
  by
    induction Δ with
    | nil => contradiction
    | cons h t ih => simp
                     intros Hdisj Hor
                     let Hdisjspec := Hdisj h (List.foldr Formula.or ⊥ t)
                     rcases Hlist : h :: t with _ | ⟨h', t'⟩
                     · contradiction
                     · rw [List.cons_eq_cons] at Hlist
                       rcases Hlist
                       let Haux := Hdisjspec Hor
                       rcases Haux with Hh | Ht
                       · apply Or.inl
                         apply Nonempty.intro
                         assumption
                       · by_cases ht : t = ∅
                         · rw [ht] at Ht
                           simp at Ht
                           apply Or.inl
                           apply Nonempty.intro
                           apply modusPonens Ht exfalso
                         · apply Or.inr
                           apply ih Hdisj Ht
                           assumption

theorem consistent_snd_empty : @consistent Γ -> @consistentPair Γ ∅ :=
  by
    simp [consistent, consistentPair]
    intros Hgamma Φ Ω Hsubset1 Hsubset2 Hfold
    apply Hgamma
    have Homegaempty : Ω = ∅ :=
      by
        rw [<-Finset.subset_empty]
        rw [<-Finset.coe_empty] at Hsubset2
        assumption
    rw [Homegaempty] at Hfold
    simp at Hfold
    apply subset_proof Hsubset1
    let Hexp := deductionTheorem_right_ind (exportation_ind Hfold)
    rw [Set.empty_union] at Hexp
    simp at Hexp
    assumption

theorem consistent_fst_consistent : @consistentPair Γ Δ -> @consistent Γ :=
  by
    simp [consistent, consistentPair]
    intros Hcpair Hgamma
    rcases (theorem_finset Hgamma) with ⟨Ω, Homega⟩
    eapply Hcpair Ω ∅
    · exact And.left Homega
    · simp
    · simp
      apply deductionTheorem_left
      rcases Homega with ⟨_, Hnonempty⟩
      apply deductionTheorem_right
      apply importation_ind
      apply deductionTheorem_left_ind
      rw [Set.empty_union]
      apply Classical.choice
      simp
      assumption

def completePair {Γ Δ : Set Formula} :=
  @consistentPair Γ Δ /\ forall (ϕ : Formula), (ϕ ∈ Γ /\ ϕ ∉ Δ) ∨ (ϕ ∈ Δ /\ ϕ ∉ Γ)

theorem complete_pair_fst_disj : @completePair Γ Δ -> @disjunctiveTheory Γ :=
  by
    simp [completePair, disjunctiveTheory]
    intros Hcons Hcompl
    have Hded : @dedClosed Γ :=
      by
        unfold dedClosed
        intros vp Hvp
        rcases Hcompl vp with Hgelem | Hdelem
        · exact And.left Hgelem
        · rcases (theorem_finset Hvp) with ⟨Φ, ⟨Hincl, Hnonempty⟩⟩
          apply Hnonempty.elim
          intros Homega
          have Homega' : ∅ ∪ Φ.toList.toFinset ⊢ vp := by rw [Set.empty_union]; simp; assumption
          let Hded := deductionTheorem_left_ind Homega'
          let Himp := importation_ind Hded
          simp [consistentPair] at Hcons
          exfalso
          let Hconsspec := Hcons Φ {vp} Hincl
          simp at Hconsspec
          let Hconsspec' := Hconsspec (And.left Hdelem)
          apply Hconsspec'
          have Horbot : ∅ ⊢ vp ⇒ vp ∨∨ ⊥ := by apply weakeningDisj
          apply syllogism Himp Horbot
    apply And.intro
    · exact Hded
    · apply And.intro
      · apply consistent_fst_consistent Hcons
      · unfold disjunctive
        apply Nonempty.intro
        intros ϕ ψ Hor
        by_cases Nonempty (Γ ⊢ ϕ)
        · apply Sum.inl
          apply Classical.choice
          assumption
        · by_cases h' : Nonempty (Γ ⊢ ψ)
          · apply Sum.inr
            apply Classical.choice
            assumption
          · exfalso
            rcases Hcompl ϕ with Hphi1 | Hphi2
            · let Hpremise := Nonempty.intro (premise (And.left Hphi1))
              contradiction
            · by_cases h'' : ψ ∈ Γ
              · let Hpremise := Nonempty.intro (premise h'')
                contradiction
              · rcases Hcompl ψ with Hpsi1 | Hpsi2
                · let Hpsiin := And.left Hpsi1
                  contradiction
                · unfold consistentPair at Hcons
                  eapply Hcons {ϕ ∨∨ ψ} {ϕ,ψ}
                  · let Hdisj := Hded (ϕ ∨∨ ψ) Hor
                    simp
                    assumption
                  · simp
                    have Hsubset1 : {ϕ} ⊆ Δ ∧ {ψ} ⊆ Δ:=
                      by
                        apply And.intro
                        · let Hvpin := And.left Hphi2
                          rw [<-Finset.singleton_subset_set_iff] at Hvpin
                          rw [<-Finset.coe_singleton]
                          assumption
                        · let Hpsiin := And.left Hpsi2
                          rw [<-Finset.singleton_subset_set_iff] at Hpsiin
                          rw [<-Finset.coe_singleton]
                          assumption
                    apply Set.union_subset (And.left Hsubset1) (And.right Hsubset1)
                  · simp
                    let Htrue := @implSelf (∅ ∪ {ϕ ∨∨ ψ}) ⊥
                    let Hor := deductionTheorem_right (@implSelf ∅ (ϕ ∨∨ ψ))
                    let Hconj := deductionTheorem_left (conjIntroRule Hor Htrue)
                    rcases Hlist : [ϕ, ψ] with nil | ⟨h, t⟩
                    · simp at Hlist
                    · by_cases Heq : ϕ = ψ
                      · rw [Heq]
                        simp
                        apply syllogism (syllogism weakeningConj contractionDisj) weakeningDisj
                      · let Hset := Hlist
                        rw [<-List.doubleton_eq] at Hset
                        · simp at Hlist
                          have Haux : Finset.toList {ϕ, ψ} = [ϕ, ψ] \/ Finset.toList {ϕ, ψ} = [ψ, ϕ] :=
                            by
                              let Hnodup := Finset.nodup_toList {ϕ, ψ}
                              let Hvpelemdoubleton := Finset.mem_insert_self ϕ {ψ}
                              let Hpsielemtail := Finset.mem_singleton_self ψ
                              have Hpsielemdoubleton : ψ = ϕ ∨ ψ ∈ {ψ} := by apply Or.inr; assumption
                              rw [<-Finset.mem_insert] at Hpsielemdoubleton
                              rw [<-Finset.mem_toList] at Hvpelemdoubleton
                              rw [<-Finset.mem_toList] at Hpsielemdoubleton
                              let Hcard := Finset.card_doubleton Heq
                              let Hlengthlist := Finset.length_toList {ϕ, ψ}
                              rw [Hcard] at Hlengthlist
                              rw [List.length_eq_two] at Hlengthlist
                              rcases Hlengthlist with ⟨a, ⟨b, Hab⟩⟩
                              rw [Hab]
                              rw [Hab] at Hvpelemdoubleton
                              rw [Hab] at Hpsielemdoubleton
                              -- let Haux := List.mem_pair Hpsielemdoubleton
                              have Hauxvp : ϕ = a ∨ ϕ = b := by sorry
                              have Hauxpsi : ψ = a ∨ ψ = b := by sorry
                              rcases Hauxvp with Hvpa | Hvpb
                              · rcases Hauxpsi with Hpsia | Hpsib
                                · rw [<-Hpsia] at Hvpa
                                  contradiction
                                · apply Or.inl
                                  rw [Hvpa, Hpsib]
                              · rcases Hauxpsi with Hpsia | Hpsib
                                · apply Or.inr
                                  rw [Hvpb, Hpsia]
                                · rw [<-Hpsib] at Hvpb
                                  contradiction
                          -- rcases Haux
                          by_cases Finset.toList {ϕ, ψ} = [ϕ, ψ]
                          · rw [h]
                            simp
                            apply syllogism weakeningConj (syllogism weakeningDisj orAssoc1)
                          · by_cases h' : Finset.toList {ϕ, ψ} = [ψ, ϕ]
                            · rw [h']
                              simp
                              apply syllogism weakeningConj (syllogism permutationDisj (syllogism weakeningDisj orAssoc1))
                            · sorry
                        · assumption

theorem disjth_completePair : @disjunctiveTheory Γ -> @completePair Γ Γᶜ :=
  by
    simp [disjunctiveTheory, dedClosed, consistent, disjunctive, completePair]
    intros Hded Hcons Hdisj
    apply And.intro
    · unfold consistentPair
      intros Φ Ω Hsubset1 Hsubset2 Hncons
      have Hconj : @set_proof_set Γ {List.foldr Formula.and (~⊥) (Finset.toList Φ)} :=
        by
          simp [set_proof_set]
          intros vp Hin
          have Helemconseq : ∅ ∪ {List.foldr Formula.and (~⊥) (Finset.toList Φ)} ⊢ vp :=
            by
              let Hpremise := premise Hin
              rw [Set.empty_union]
              assumption
          let Hded := deductionTheorem_left Helemconseq
          let Hexp := exportation_ind Hded
          let Hded' := deductionTheorem_right_ind Hexp
          rw [Set.empty_union] at Hded'
          simp at Hded'
          apply subset_proof Hsubset1 Hded'
      let Hdedth := deductionTheorem_right Hncons
      rw [Set.empty_union] at Hdedth
      have Htransconseq : Γ ⊢ List.foldr Formula.or ⊥ (Finset.toList Ω) :=
        by apply set_conseq_proof Hconj Hdedth
      by_cases Ω = ∅
      · rw [h] at Htransconseq
        simp at Htransconseq
        exact Hcons Htransconseq
      by_cases Ω = ∅
      · rw [h] at Htransconseq
        simp at Htransconseq
        exact Hcons Htransconseq
      · have Hi : ∃ vpi ∈ Ω.toList, Nonempty (Γ ⊢ vpi) :=
          by
            have Hlistnempty : Ω.toList ≠ [] :=
              by
                by_cases h' : Ω.toList = []
                · rw [Finset.toList_eq_nil] at h'
                  contradiction
                · assumption
            apply disjunctive_ind Hdisj
            assumption'
        rcases Hi with ⟨vpi, ⟨Helemomega, Hvpigamma⟩⟩
        apply Nonempty.elim Hvpigamma
        clear Hvpigamma
        intros Hvpigamma
        have Helemgamma : vpi ∈ Γ :=
          by apply Hded vpi; assumption
        have Helemcompl : vpi ∈ Γᶜ :=
          have Helemomegaset : vpi ∈ Ω :=
            by rw [Finset.mem_toList] at Helemomega; assumption
          by apply Set.mem_of_subset_of_mem Hsubset2 Helemomegaset
        contradiction
    · intros vp
      apply Classical.em

theorem consistent_disj :
  @consistentPair Γ Δ -> Disjoint Γ Δ :=
  by
    intros Hcons
    by_cases Disjoint Γ Δ
    · assumption
    · exfalso
      rw [Set.not_disjoint_iff_nonempty_inter] at h
      unfold consistentPair at Hcons
      unfold Set.Nonempty at h
      rcases h with ⟨x, Hxin⟩
      have Hxingamma : {x} ⊆ Γ :=
        by simp; apply Set.mem_of_mem_inter_left Hxin
      have Hxindelta : {x} ⊆ Δ :=
        by simp; apply Set.mem_of_mem_inter_right Hxin
      let Haux := Hcons {x} {x}
      rw [Finset.coe_singleton] at Haux
      let Haux' := Haux Hxingamma Hxindelta
      simp at Haux'
      apply Haux'
      apply syllogism weakeningConj weakeningDisj

theorem add_preserves_cons :
  @consistentPair Γ Δ -> forall (ϕ : Formula), @consistentPair ({ϕ} ∪ Γ) Δ ∨ @consistentPair Γ ({ϕ} ∪ Δ) :=
  by
    intros Hcons vp
    by_cases ¬@consistentPair ({vp} ∪ Γ) Δ ∧ ¬@consistentPair Γ ({vp} ∪ Δ)
    · rcases h with ⟨Hncons1, Hncons2⟩
      unfold consistentPair at Hncons1
      unfold consistentPair at Hncons2
      apply Or.inl
      exfalso
      push_neg at Hncons1
      rcases Hncons1 with ⟨Φ1, Ω1, h1, h1', h1''⟩
      rcases h1'' with ⟨w1, h1''⟩
      push_neg at Hncons2
      rcases Hncons2 with ⟨Φ2, Ω2, h2, h2', h2''⟩
      rcases h2'' with ⟨w2, h2''⟩
      have Hvpi1 : vp ∈ Φ1 :=
        by
          by_cases vp ∈ Φ1
          · assumption
          · exfalso
            rw [<-Finset.mem_coe, <-Set.disjoint_singleton_right] at h
            let Hsubset := Disjoint.subset_right_of_subset_union h1 h
            let Hncons := Hcons Φ1 Ω1 Hsubset h1' w1
            assumption
      have Hvpi2 : vp ∈ Ω2 :=
        by
          by_cases vp ∈ Ω2
          · assumption
          · exfalso
            rw [<-Finset.mem_coe, <-Set.disjoint_singleton_right] at h
            let Hsubset := Disjoint.subset_right_of_subset_union h2' h
            let Hncons := Hcons Φ2 Ω2 h2 Hsubset w2
            assumption
      have Hnempty1 : Finset.Nonempty {vp} := by apply Finset.singleton_nonempty
      have Hnemptyunion1 : Finset.Nonempty ({vp} ∪ Φ2) := by apply Finset.Nonempty.inl; assumption
      let Hnemptylist1 := Finset.Nonempty.toList_ne_nil Hnemptyunion1
      have Hnempty2 : Finset.Nonempty {vp} := by apply Finset.singleton_nonempty
      have Hnemptyunion2 : Finset.Nonempty ({vp} ∪ Ω1) := by apply Finset.Nonempty.inl; assumption
      let Hnemptylist2 := Finset.Nonempty.toList_ne_nil Hnemptyunion2
      rcases Hlist2 : Φ1.toList with nil | ⟨head1, t1⟩
      · simp at Hlist2
        let Hnempty := Finset.ne_empty_of_mem Hvpi1
        contradiction
      · rw [Hlist2] at w1
        simp at w1
        have Hnemptyphi1 : Finset.toList Φ1 ≠ [] :=
          by
            have Hnempty : Finset.Nonempty Φ1 := by exists vp
            apply Finset.Nonempty.toList_ne_nil
            assumption
        let Hexp := exportation w1
        let Hperm := permuteHyps Hexp
        let Hweakconj := @weakeningConj ∅ (List.foldr Formula.and (~⊥) t1) (List.foldr Formula.and (~⊥) Φ2.toList ∧∧ List.head Φ1.toList Hnemptyphi1)
        let Hsyllog1 := syllogism Hweakconj Hperm
        let Hded1 := deductionTheorem_right Hsyllog1
        let Hweakdisj := @weakeningDisj (∅ ∪ {List.foldr Formula.and (~⊥) t1∧∧List.foldr Formula.and (~⊥) (Finset.toList Φ2)  ∧∧ List.head Φ1.toList Hnemptyphi1})
                             (List.foldr Formula.or ⊥ (Finset.toList Ω1)) (List.foldr Formula.or ⊥ (Finset.toList Ω2))
        let Hsyllog2 := syllogism Hded1 Hweakdisj
        let Hded' := deductionTheorem_left Hsyllog2
        let Hassocomm := @andAssocComm ∅ (List.head (Finset.toList Φ1) Hnemptyphi1) (List.foldr Formula.and (~⊥) t1) (List.foldr Formula.and (~⊥) (Finset.toList Φ2))
        let Hsyllog2 := deductionTheorem_right (syllogism Hassocomm Hded')
        rw [Set.empty_union] at Hsyllog2
        rcases Hlist1 : Ω2.toList with nil | ⟨head2, t2⟩
        · simp at Hlist1
          let Hnempty := Finset.ne_empty_of_mem Hvpi2
          contradiction
        · rw [Hlist1] at w2
          simp at w2
          have Hnemptyomega2 : Finset.toList Ω2 ≠ [] :=
            by
              have Hnempty : Finset.Nonempty Ω2 := by exists vp
              apply Finset.Nonempty.toList_ne_nil
              assumption
          let Hperm := @permutationDisj ∅ head2 (List.foldr Formula.or ⊥ t2)
          let Hsyllog := syllogism w2 Hperm
          let Hdni := @dni ∅ head2
          let Hexp := @expansion ∅ head2 (~~head2) (List.foldr Formula.or ⊥ t2) Hdni
          let Hperm' := @permutationDisj ∅ (List.foldr Formula.or ⊥ t2) (~~head2)
          let Hsyllog' := syllogism Hexp Hperm'
          let Himpldef := @impldef ∅ (~head2) (List.foldr Formula.or ⊥ t2)
          let Hsyllog'' := syllogism Hsyllog' Himpldef
          let Hsyllog''' := syllogism Hsyllog Hsyllog''
          let Hded2 := deductionTheorem_right Hsyllog'''
          let Hded3 := deductionTheorem_left Hded2
          let Hweakconj := @weakeningConj ∅ (List.foldr Formula.and (~⊥) Φ2.toList) (List.foldr Formula.and (~⊥) (Finset.toList Φ1))
          let Hsyllog3 := syllogism Hweakconj Hded3
          let Hded4 := deductionTheorem_right Hsyllog3
          let Hweakdisj := @weakeningDisj (∅ ∪ {List.foldr Formula.and (~⊥) (Finset.toList Φ2)∧∧List.foldr Formula.and (~⊥) (Finset.toList Φ1)})
                               (List.foldr Formula.or ⊥ t2) (List.foldr Formula.or ⊥ (Finset.toList Ω1) ∨∨ List.head Ω2.toList Hnemptyomega2)
          let Hsyllog4 := syllogism Hded4 Hweakdisj
          let Hded' := deductionTheorem_left Hsyllog4
          let Hassocomm := @orAssocComm (∅ ∪ {List.foldr Formula.and (~⊥) (Finset.toList Φ2)∧∧List.foldr Formula.and (~⊥) (Finset.toList Φ1)}) (List.foldr Formula.or ⊥ t2) (List.foldr Formula.or ⊥ (Finset.toList Ω1)) (List.head (Finset.toList Ω2) Hnemptyomega2)
          let Hded'' := deductionTheorem_right Hded'
          let Hsyllog4 := deductionTheorem_left (deductionTheorem_right (syllogism Hded'' Hassocomm))
          rw [Set.empty_union] at Hsyllog4
          have Hcontra' : ∅ ∪ {List.foldr Formula.and (~⊥) (Finset.toList Φ2)} ⊢ List.foldr Formula.or ⊥ (Finset.toList Ω1) :=
            by sorry
          let Hded := deductionTheorem_left Hcontra'
          let Hconsspec := Hcons Φ2 Ω1 h2 h1' Hded
          assumption
    · by_cases h' : @consistentPair ({vp} ∪ Γ) Δ
      · apply Or.inl; assumption
      · apply Or.inr
        simp at h
        rw [<-Set.insert_eq]
        rw [<-Set.insert_eq] at h'
        apply h h'

theorem consistent_incl_complete :
  @consistentPair Γ Δ -> (∃ (Γ' Δ' : Set Formula), Γ ⊆ Γ' ∧ Δ ⊆ Δ' ∧ @completePair Γ' Δ') :=
  by sorry

end Proof

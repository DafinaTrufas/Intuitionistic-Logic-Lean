import IL.HeytingAlgebraUtils
import IL.Formula
import IL.Semantics

variable {α : Type u} [HeytingAlgebra α]

def AlgInterpretation {α : Type} [HeytingAlgebra α] (I : Var -> α) : Formula -> α
| Formula.var p => I p
| Formula.bottom => ⊥
| ϕ ∧∧ ψ => AlgInterpretation I ϕ ⊓ AlgInterpretation I ψ
| ϕ ∨∨ ψ => AlgInterpretation I ϕ ⊔ AlgInterpretation I ψ
| ϕ ⇒ ψ => AlgInterpretation I ϕ ⇨ AlgInterpretation I ψ

def alg_univ_true (ϕ : Formula) : Prop :=
  forall (α : Type) [HeytingAlgebra α] (I : Var -> α), AlgInterpretation I ϕ = ⊤

def closed {W : Type} (M : KripkeModel W) (A : Set W) : Prop :=
  ∀ (w w' : W), w ∈ A -> M.R w w' -> w' ∈ A

def all_closed {W : Type} (M : KripkeModel W) := {A // @closed W M A}

def all_closed_subset {W : Type} (M : KripkeModel W) (A B : all_closed M) :=
  {X | @closed W M X /\ X ⊆ ((@Set.univ W) \ A.1) ∪ B.1}

def himp_closed {W : Type} {M : KripkeModel W} (A B : all_closed M) :=
  Set.sUnion (@all_closed_subset W M A B)

lemma himp_closed_prop {W : Type} {M : KripkeModel W} (A B X : all_closed M) :
  X.1 ⊆ himp_closed A B <-> X.1 ∩ A.1 ⊆ B.1 :=
  by
    apply Iff.intro
    · intro Hsubset
      unfold himp_closed at Hsubset
      unfold all_closed_subset at Hsubset
      have Haux1 : X.1 ⊆ ((@Set.univ W) \ A.1) ∪ B.1 :=
        by
          rw [Set.sUnion] at Hsubset
          apply Set.Subset.trans Hsubset
          simp
      have Haux2 : A.1 ∩ X.1 ⊆ A.1 ∩ (((@Set.univ W) \ A.1) ∪ B.1) :=
        by apply Set.inter_subset_inter_right; assumption
      have Haux3 : A.1 ∩ (((@Set.univ W) \ A.1) ∪ B.1) = A.1 ∩ B.1 :=
        by rw [Set.inter_union_distrib_left]; simp
      rw [Haux3] at Haux2
      have Haux3 : A.1 ∩ X.1 ⊆ B.1 := by apply Set.Subset.trans Haux2; simp
      rw [Set.inter_comm]
      assumption
    · intro Hsubset
      have Haux1 : (X.1 ∩ A.1) ∪ (X.1 \ A.1) ⊆ B.1 ∪ (X.1 \ A.1) :=
        by apply Set.union_subset_union_left; assumption
      simp at Haux1
      have Haux2 : X.1 ⊆ B.1 ∪ ((@Set.univ W) \ A.1) :=
        by
          apply Set.Subset.trans Haux1
          apply Set.union_subset_union_right
          apply Set.diff_subset_diff_left
          simp
      have Haux3 : X.1 ∈ all_closed_subset M A B :=
        by
          apply And.intro
          · exact X.2
          · rw [Set.union_comm] at Haux2; assumption
      apply Set.subset_sUnion_of_mem
      assumption

lemma union_preserves_closed {W : Type} {M : KripkeModel W} (A B : all_closed M) :
  closed M (A.1 ∪ B.1) :=
  by
    intro w w' Hwin Hr
    rw [Set.mem_union] at Hwin
    rcases Hwin with HA | HB
    · apply Or.inl; exact A.2 w w' HA Hr
    · apply Or.inr; exact B.2 w w' HB Hr

lemma inter_preserves_closed {W : Type} {M : KripkeModel W} (A B : all_closed M) :
  closed M (A.1 ∩ B.1) :=
  by
    intro w w' Hwin Hr
    rw [Set.mem_inter_iff] at Hwin
    exact And.intro (A.2 w w' Hwin.left Hr) (B.2 w w' Hwin.right Hr)

lemma univ_closed {W : Type} {M : KripkeModel W} : closed M (@Set.univ W) :=
  by intro w w' _ _; simp

lemma empty_closed {W : Type} {M : KripkeModel W} : closed M ∅:=
  by intro w w' Hwin _; exfalso; exact (Set.not_mem_empty w) Hwin

lemma himp_is_closed {W : Type} {M : KripkeModel W} (A B : all_closed M) :
  closed M (himp_closed A B) :=
  by
    intro w w' Hwin Hr
    rcases Hwin with ⟨t, Ht⟩
    exists t
    apply And.intro
    · exact Ht.left
    · rcases Ht with ⟨Ht, Hmem⟩
      apply Ht.left
      assumption'

lemma antisymm'' {W : Type} {M : KripkeModel W} (A B : all_closed M) :
  A.1 ⊆ B.1 -> B.1 ⊆ A.1 -> A.1 = B.1 :=
  by
    intro HAB HBA
    apply Set.Subset.antisymm HAB HBA

instance {W : Type} (M : KripkeModel W) : HeytingAlgebra (all_closed M) :=
  { sup := λ X Y => {val := X.1 ∪ Y.1, property := union_preserves_closed X Y}
    le := λ X Y => X.1 ⊆ Y.1
    le_refl := λ _ => Set.Subset.rfl
    le_trans := λ _ _ _ => Set.Subset.trans
    le_antisymm := λ _ _ => by rw [Subtype.ext_iff]; apply Set.Subset.antisymm
    le_sup_left := λ X Y => Set.subset_union_left X.1 Y.1
    le_sup_right := λ X Y => Set.subset_union_right X.1 Y.1
    sup_le := λ _ _ _ => Set.union_subset
    inf := λ X Y => {val := X.1 ∩ Y.1, property := inter_preserves_closed X Y}
    inf_le_left := λ X Y => Set.inter_subset_left X.1 Y.1
    inf_le_right := λ X Y => Set.inter_subset_right X.1 Y.1
    le_inf := λ _ _ _ => Set.subset_inter
    top := {val := @Set.univ W, property := univ_closed}
    le_top := λ X => Set.subset_univ X.1
    himp := λ X Y => {val := himp_closed X Y, property := himp_is_closed X Y}
    le_himp_iff := λ X Y Z => himp_closed_prop Y Z X
    bot := {val := ∅, property := empty_closed}
    bot_le := λ X => Set.empty_subset X.1
    compl := λ X => {val := himp_closed X {val := ∅, property := empty_closed},
                     property := himp_is_closed X {val := ∅, property := empty_closed}}
    himp_bot := by simp }

def h_var {W : Type} {M : KripkeModel W} (v : Var) : all_closed M :=
  {val := {w | M.V v w}, property := by intro w w' Hwin Hr; apply M.monotonicity; assumption'}

def h {W : Type} {M : KripkeModel W} (ϕ : Formula) : all_closed M :=
  {val := {w | val M w ϕ}, property := by intro w w' Hwin Hr; apply monotonicity_val; assumption'}

lemma h_interpretation {W : Type} {M : KripkeModel W} :
  ∀ (ϕ : Formula), @h W M ϕ = @AlgInterpretation (all_closed M) _ (@h_var W M) ϕ :=
  by
    intro ϕ
    induction ϕ with
    | var v | bottom => rfl
    | and ψ χ ih1 ih2 | or ψ χ ih1 ih2 => unfold AlgInterpretation
                                          rw [<-ih1, <-ih2, Subtype.ext_iff, Set.ext_iff]
                                          unfold h
                                          intro x
                                          apply Iff.intro
                                          · intro Hxin; assumption
                                          · intro Hxin; assumption
    | implication ψ χ ih1 ih2 => have Haux : ∀ (A : all_closed M), A.1 ⊆ (@h W M (ψ ⇒ χ)).1 <->
                                                A.1 ∩ (@h W M ψ).1 ⊆ (@h W M χ).1 :=
                                  by
                                    intro A
                                    apply Iff.intro
                                    · intro Hsubset
                                      rw [Set.subset_def]
                                      intro w Hwin
                                      have Hwin' : w ∈ (@h W M (ψ ⇒ χ)).1 :=
                                        by exact Set.mem_of_mem_of_subset Hwin
                                                  (Set.Subset.trans (Set.inter_subset_left A.1 (@h W M ψ).1) Hsubset)
                                      have Hwin'' : w ∈ (@h W M ψ).1 :=
                                        by apply Set.inter_subset_right; assumption'
                                      apply Hwin'
                                      apply And.intro (M.refl w)
                                      assumption
                                    · intro Hsubset
                                      rw [Set.subset_def]
                                      intro w Hwin
                                      intro w' ⟨Hr, Hvalpsi⟩
                                      have Hw'in : w' ∈ (@h W M χ).1 :=
                                        by
                                          apply Set.Subset.trans
                                          assumption'
                                          exact Set.Subset.rfl
                                          · apply Set.mem_inter
                                            · apply A.2; assumption'
                                            · assumption
                                      assumption
                                 unfold AlgInterpretation
                                 rw [<-ih1, <-ih2, Subtype.ext_iff]
                                 have Haux' : ∀ (A : all_closed M), A.1 ⊆ (@h W M (ψ ⇒ χ)).1 <->
                                                 A.1 ⊆ himp_closed (@h W M ψ) (@h W M χ) :=
                                  by
                                    intro A
                                    let Haux := Haux A
                                    rw [Haux]
                                    rw [<-himp_closed_prop]
                                 have Haux'' : Set.powerset (@h W M (ψ ⇒ χ)).1 = Set.powerset (himp_closed (@h W M ψ) (@h W M χ)) :=
                                  by
                                    unfold Set.powerset
                                    rw [Set.ext_iff]
                                    intro X
                                    simp
                                    by_cases Hclosed : closed M X
                                    · exact Haux' {val := X, property := Hclosed}
                                    · apply Iff.intro
                                      · sorry
                                      · sorry
                                 rw [Set.Subset.antisymm_iff] at Haux''
                                 rw [Set.powerset_mono, Set.powerset_mono] at Haux''
                                 rw [Set.Subset.antisymm_iff]
                                 assumption

def prime_filters_closed {W : Type} {M : KripkeModel W} := {F | @prime_filter (all_closed M) _ F}

def prime_filters_model {W : Type} {M : KripkeModel W} :
  KripkeModel (@prime_filters_closed W M) :=
  {
   R := λ (F1 F2) => F1.1 ⊆ F2.1,
   V := λ (v F) => h (Formula.var v) ∈ F.1,
   refl := λ (F) => Set.Subset.rfl
   trans := λ (F1 F2 Φ) => Set.Subset.trans
   monotonicity := λ (v F1 F2) => by intros; apply Set.mem_of_mem_of_subset; assumption'
  }

def Vh_var {W : Type} {M : KripkeModel W} (v : Var) (F : @prime_filters_closed W M) : Prop :=
  h (Formula.var v) ∈ F.1

def Vh {W : Type} {M : KripkeModel W} (ϕ : Formula) (F : @prime_filters_closed W M) : Prop :=
  h ϕ ∈ F.1

lemma Vh_valuation :
  ∀ (ϕ : Formula) (F : @prime_filters_closed W M), Vh ϕ F = val prime_filters_model F ϕ :=
  by
    intro ϕ
    induction ϕ with
    | var v => intro F; rfl
    | bottom => intro F
                unfold Vh
                have Hbot_notin : Bot.bot ∉ F.1 := by exact F.2.1.2
                unfold val
                simp
                assumption
    | and ψ χ ih1 ih2 => intro F
                         unfold Vh
                         have Hsplit : AlgInterpretation h_var ψ ⊓ AlgInterpretation h_var χ ∈ F.1 <->
                                       AlgInterpretation h_var ψ ∈ F.1 ∧ AlgInterpretation h_var χ ∈ F.1 :=
                          by
                            apply Iff.intro
                            · intro Hglb
                              exact And.intro (F.2.1.1.2.2 _ _ Hglb inf_le_left) (F.2.1.1.2.2 _ _ Hglb inf_le_right)
                            · intro Hand
                              exact F.2.1.1.2.1 _ _ Hand.left Hand.right
                         unfold val
                         unfold Vh at ih1
                         unfold Vh at ih2
                         rw [h_interpretation]
                         rw [h_interpretation] at ih1
                         rw [h_interpretation] at ih2
                         rw [<-ih1, <-ih2]
                         simp
                         assumption
    | or ψ χ ih1 ih2 => intro F
                        unfold Vh
                        have Hsplit : AlgInterpretation h_var ψ ⊔ AlgInterpretation h_var χ ∈ F.1 <->
                                      AlgInterpretation h_var ψ ∈ F.1 ∨ AlgInterpretation h_var χ ∈ F.1 :=
                          by
                            apply Iff.intro
                            · intro Hlub
                              exact F.2.2 _ _ Hlub
                            · intro Hor
                              rcases Hor with Hpsi | Hchi
                              · exact F.2.1.1.2.2 _ _ Hpsi le_sup_left
                              · exact F.2.1.1.2.2 _ _ Hchi le_sup_right
                        unfold val
                        unfold Vh at ih1
                        unfold Vh at ih2
                        rw [h_interpretation]
                        rw [h_interpretation] at ih1
                        rw [h_interpretation] at ih2
                        rw [<-ih1, <-ih2]
                        simp
                        assumption
    | implication ψ χ ih1 ih2 => intro F
                                 simp
                                 apply Iff.intro
                                 · intro Hvh
                                   unfold Vh at Hvh
                                   intro F' ⟨Hr, Hvalpsi⟩
                                   rw [<-ih1] at Hvalpsi
                                   unfold Vh at Hvalpsi
                                   let HF'filter := F'.2.1.1
                                   rw [filter_dedsyst_equiv] at HF'filter
                                   let Hvh : AlgInterpretation h_var ψ ⇨ AlgInterpretation h_var χ ∈ F'.1 :=
                                    by
                                      apply Set.mem_of_subset_of_mem Hr
                                      rw [h_interpretation] at Hvh
                                      assumption
                                   rw [h_interpretation] at Hvalpsi
                                   let Haux := HF'filter.2 (AlgInterpretation h_var ψ) (AlgInterpretation h_var χ) Hvalpsi Hvh
                                   · have Haux : Vh χ F' :=
                                      by
                                        unfold Vh
                                        rw [<-h_interpretation] at Haux
                                        assumption
                                     rw [ih2] at Haux
                                     assumption
                                   · exists (@h W M ψ).1; exact (@h W M ψ).2
                                   · exists (@h W M ψ).1; exact (@h W M ψ).2
                                 · intro Hval
                                   unfold val at Hval
                                   by_cases Hvh : Vh (ψ ⇒ χ) F
                                   · assumption
                                   · exfalso
                                     unfold Vh at Hvh
                                     have Hnotin : AlgInterpretation h_var χ ∉ X_gen_filter (F.1 ∪ {h ψ}) :=
                                      by
                                        apply himp_not_mem
                                        · exists (@h W M ψ).1; exact (@h W M ψ).2
                                        · exact F.2.1.1
                                        · rw [h_interpretation]
                                          rw [h_interpretation] at Hvh
                                          unfold AlgInterpretation at Hvh
                                          assumption
                                     unfold X_gen_filter at Hnotin
                                     have Hnotin : AlgInterpretation h_var χ ∉ F.1 ∪ {h ψ} :=
                                      by
                                        let Hsubset := X_subset_X_gen_filter (F.1 ∪ {h ψ})
                                        apply Set.not_mem_subset
                                        assumption'
                                     let Haux := @super_prime_filter (all_closed M) _ (h χ) (F ∪ {h ψ})
                                     have Hins_filter : filter (F.1 ∪ {h ψ}) :=
                                      by
                                        sorry
                                     have Hnotin : AlgInterpretation h_var χ ∉ F.1 :=
                                      by
                                        apply Set.not_mem_subset
                                        assumption'
                                        apply Set.subset_union_left
                                     rw [<-h_interpretation] at Hnotin
                                     let Haux := @super_prime_filter (all_closed M) _ (h χ) F F.2.1.1 Hnotin
                                     rcases Haux with ⟨F', ⟨Hprime, ⟨Hsubset, Hnotval_chi⟩⟩⟩
                                     simp at Hval
                                     unfold KripkeModel.R at Hval
                                     let Haux := Hval F' Hprime Hsubset
                                     sorry

theorem soundness_alg (ϕ : Formula) : Nonempty (∅ ⊢ ϕ) -> alg_univ_true ϕ :=
  by
    intro Htheorem
    let Htheorem' := Classical.choice Htheorem
    induction Htheorem' with
    | premise Hin => simp at Hin
    | @contractionDisj ψ => intro α H I
                            unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∨∨ ψ) = AlgInterpretation I ψ ⊔ AlgInterpretation I ψ := by rfl
                            rw [Haux]
                            simp
    | @contractionConj ψ => intro α H I
                            unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∧∧ ψ) = AlgInterpretation I ψ ⊓ AlgInterpretation I ψ := by rfl
                            rw [Haux]
                            simp
    | @weakeningDisj ψ χ => intro α H I
                            unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∨∨ χ) = AlgInterpretation I ψ ⊔ AlgInterpretation I χ := by rfl
                            rw [Haux]
                            simp
    | @weakeningConj ψ χ => intro α H I
                            unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∧∧ χ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ := by rfl
                            rw [Haux]
                            simp
    | @permutationDisj ψ χ => intro α H I
                              unfold AlgInterpretation
                              have Haux : AlgInterpretation I (ψ ∨∨ χ) = AlgInterpretation I ψ ⊔ AlgInterpretation I χ := by rfl
                              rw [Haux]
                              have Haux : AlgInterpretation I (χ ∨∨ ψ) = AlgInterpretation I χ ⊔ AlgInterpretation I ψ := by rfl
                              rw [Haux]
                              simp
    | @permutationConj ψ χ => intro α H I
                              unfold AlgInterpretation
                              have Haux : AlgInterpretation I (ψ ∧∧ χ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ := by rfl
                              rw [Haux]
                              have Haux : AlgInterpretation I (χ ∧∧ ψ) = AlgInterpretation I χ ⊓ AlgInterpretation I ψ := by rfl
                              rw [Haux]
                              simp
    | @exfalso ψ => intro α H I
                    unfold AlgInterpretation
                    have Haux : AlgInterpretation I ⊥ = Bot.bot := by rfl
                    rw [Haux]
                    simp
    | @modusPonens ψ χ p1 p2 ih1 ih2 => intro α H I
                                        simp at ih1; simp at ih2
                                        let ih2 := ih2 p2 α I
                                        unfold AlgInterpretation at ih2
                                        let ih1 := ih1 p1 α I
                                        rw [ih1] at ih2
                                        simp at ih2
                                        assumption
    | @syllogism ψ χ γ p1 p2 ih1 ih2 => intro α H I
                                        simp at ih1; simp at ih2
                                        let ih1 := ih1 p1 α I
                                        unfold AlgInterpretation at ih1
                                        let ih2 := ih2 p2 α I
                                        unfold AlgInterpretation at ih2
                                        simp at ih1; simp at ih2
                                        unfold AlgInterpretation
                                        simp
                                        apply le_trans
                                        assumption'
    | @exportation ψ χ γ p ih => intro α H I
                                 simp at ih
                                 let ih := ih p α I
                                 unfold AlgInterpretation at ih
                                 have Haux : AlgInterpretation I (ψ ∧∧ χ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ := by rfl
                                 rw [Haux] at ih
                                 simp at ih
                                 rw [<-le_himp_iff, <-himp_eq_top_iff] at ih
                                 unfold AlgInterpretation
                                 have Haux : AlgInterpretation I (χ ⇒ γ) = AlgInterpretation I χ ⇨ AlgInterpretation I γ := by rfl
                                 rw [Haux]
                                 assumption
    | @importation ψ χ γ p ih => intro α H I
                                 simp at ih
                                 let ih := ih p α I
                                 unfold AlgInterpretation at ih
                                 simp at ih
                                 have Haux : AlgInterpretation I (χ ⇒ γ) = AlgInterpretation I χ ⇨ AlgInterpretation I γ := by rfl
                                 rw [Haux, le_himp_iff, <-himp_eq_top_iff] at ih
                                 unfold AlgInterpretation
                                 have Haux : AlgInterpretation I (ψ ∧∧ χ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ := by rfl
                                 rw [Haux]
                                 assumption
    | @expansion ψ χ γ p ih => intro α H I
                               simp at ih
                               let ih := ih p α I
                               unfold AlgInterpretation at ih
                               simp at ih
                               let ih := sup_le_sup_left ih (AlgInterpretation I γ)
                               have Haux : AlgInterpretation I γ ⊔ AlgInterpretation I ψ = AlgInterpretation I (γ ∨∨ ψ) := by rfl
                               rw [Haux] at ih
                               have Haux : AlgInterpretation I γ ⊔ AlgInterpretation I χ = AlgInterpretation I (γ ∨∨ χ) := by rfl
                               rw [Haux] at ih
                               unfold AlgInterpretation
                               simp
                               assumption

def equiv (ϕ ψ : Formula) := Nonempty (∅ ⊢ ϕ ⇒ ψ) /\ Nonempty (∅ ⊢ ψ ⇒ ϕ)
infix:50 "∼" => equiv

instance setoid_formula : Setoid Formula :=
  { r := equiv,
    iseqv := ⟨λ _ => And.intro (Nonempty.intro Proof.implSelf) (Nonempty.intro Proof.implSelf),
              λ _ => by unfold equiv; rw [And.comm]; assumption,
              λ H12 H23 => by
                              unfold equiv; unfold equiv at H12; unfold equiv at H23;
                              apply And.intro
                              · apply Nonempty.intro
                                exact Proof.syllogism (Classical.choice H12.left) (Classical.choice H23.left)
                              · apply Nonempty.intro
                                exact Proof.syllogism (Classical.choice H23.right) (Classical.choice H12.right)
                              ⟩ }

def Formula.le (ϕ ψ : Formula) : Prop := Nonempty (∅ ⊢ ϕ ⇒ ψ)

lemma le_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : ϕ ∼ ϕ' -> ψ ∼ ψ' -> (Formula.le ϕ ψ = Formula.le ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    simp
    apply Iff.intro
    · intro Hvppsi
      apply Nonempty.intro
      exact Proof.syllogism (Proof.syllogism (Classical.choice Heqvp.right) (Classical.choice Hvppsi))
                            (Classical.choice Heqpsi.left)
    · intro Hvp'psi'
      apply Nonempty.intro
      exact Proof.syllogism (Proof.syllogism (Classical.choice Heqvp.left) (Classical.choice Hvp'psi'))
                            (Classical.choice Heqpsi.right)

def le_quot (ϕ ψ : Quotient setoid_formula) : Prop :=
  Quotient.lift₂ Formula.le le_preserves_equiv ϕ ψ
infix:50 "≤" => le_quot

def Formula.or_quot (ϕ ψ : Formula) := Quotient.mk setoid_formula (ϕ ∨∨ ψ)

lemma or_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : ϕ ∼ ϕ' -> ψ ∼ ψ' ->
  (Formula.or_quot ϕ ψ = Formula.or_quot ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    unfold Formula.or_quot
    simp
    apply And.intro
    · apply Nonempty.intro
      exact Proof.orImplDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.orImplDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.right)

def or_quot (ϕ ψ : Quotient setoid_formula) : Quotient setoid_formula :=
  Quotient.lift₂ Formula.or_quot or_quot_preserves_equiv ϕ ψ

def Formula.and_quot (ϕ ψ : Formula) := Quotient.mk setoid_formula (ϕ ∧∧ ψ)

lemma and_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : ϕ ∼ ϕ' -> ψ ∼ ψ' ->
  (Formula.and_quot ϕ ψ = Formula.and_quot ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    unfold Formula.and_quot
    simp
    apply And.intro
    · apply Nonempty.intro
      exact Proof.andImplDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.andImplDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.right)

def and_quot (ϕ ψ : Quotient setoid_formula) : Quotient setoid_formula :=
  Quotient.lift₂ Formula.and_quot and_quot_preserves_equiv ϕ ψ

def Formula.to_quot (ϕ ψ : Formula) := Quotient.mk setoid_formula (ϕ ⇒ ψ)

lemma to_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : ϕ ∼ ϕ' -> ψ ∼ ψ' ->
  (Formula.to_quot ϕ ψ = Formula.to_quot ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    unfold Formula.to_quot
    simp
    apply And.intro
    · apply Nonempty.intro
      unfold equiv at Heqvp
      exact Proof.equivDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.equivDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.right)

def to_quot (ϕ ψ : Quotient setoid_formula) : Quotient setoid_formula :=
  Quotient.lift₂ Formula.to_quot to_quot_preserves_equiv ϕ ψ

instance quotient_formula_heyting : HeytingAlgebra (Quotient setoid_formula) :=
  { sup := or_quot
    le := le_quot
    le_refl := λ q => by
                        induction q using Quotient.ind
                        apply Nonempty.intro
                        exact Proof.implSelf
    le_trans := λ q1 q2 q3 H12 H23 => by
                                        induction q1 using Quotient.ind
                                        induction q2 using Quotient.ind
                                        induction q3 using Quotient.ind
                                        apply Nonempty.intro
                                        exact Proof.syllogism (Classical.choice H12) (Classical.choice H23)
    le_antisymm := λ q1 q2 H12 H21 => by
                                        induction q1 using Quotient.ind
                                        induction q2 using Quotient.ind
                                        simp
                                        exact And.intro H12 H21
    le_sup_left := λ q1 q2 => by
                                induction q1 using Quotient.ind
                                induction q2 using Quotient.ind
                                apply Nonempty.intro
                                exact Proof.weakeningDisj
    le_sup_right := λ q1 q2 => by
                                induction q1 using Quotient.ind
                                induction q2 using Quotient.ind
                                apply Nonempty.intro
                                exact Proof.disjIntroRight
    sup_le := λ q1 q2 q3 H13 H23 => by
                                      induction q1 using Quotient.ind
                                      induction q2 using Quotient.ind
                                      induction q3 using Quotient.ind
                                      apply Nonempty.intro
                                      exact Proof.disjIntroAtHyp (Classical.choice H13) (Classical.choice H23)
    inf := and_quot
    inf_le_left := λ q1 q2 => by
                                induction q1 using Quotient.ind
                                induction q2 using Quotient.ind
                                apply Nonempty.intro
                                exact Proof.weakeningConj
    inf_le_right := λ q1 q2 => by
                                induction q1 using Quotient.ind
                                induction q2 using Quotient.ind
                                apply Nonempty.intro
                                exact Proof.conjElimRight
    le_inf := λ q1 q2 q3 H13 H23 => by
                                      induction q1 using Quotient.ind
                                      induction q2 using Quotient.ind
                                      induction q3 using Quotient.ind
                                      apply Nonempty.intro
                                      exact Proof.conjImplIntroRule (Classical.choice H13) (Classical.choice H23)
    top := Quotient.mk setoid_formula (Formula.negation ((⊥ ⇒ ⊥) ∧∧ (Formula.negation (⊥ ⇒ ⊥))))
    himp := to_quot
    le_himp_iff := λ q1 q2 q3 => by
                                  induction q1 using Quotient.ind
                                  induction q2 using Quotient.ind
                                  induction q3 using Quotient.ind
                                  apply Iff.intro
                                  · intro Hle
                                    apply Nonempty.intro
                                    exact Proof.importation (Classical.choice Hle)
                                  · intro Hle
                                    apply Nonempty.intro
                                    exact Proof.exportation (Classical.choice Hle)
    le_top := λ q => by
                      induction q using Quotient.ind
                      apply Nonempty.intro
                      exact Proof.extraPremise Proof.exFalsoAnd
    bot := Quotient.mk setoid_formula ((⊥ ⇒ ⊥) ∧∧ (Formula.negation (⊥ ⇒ ⊥)))
    bot_le := λ q => by
                      induction q using Quotient.ind
                      apply Nonempty.intro
                      exact Proof.exFalsoAnd
    compl := λ q => to_quot q (Quotient.mk setoid_formula ((⊥ ⇒ ⊥) ∧∧ (Formula.negation (⊥ ⇒ ⊥))))
    himp_bot := by simp }

lemma equiv_top (ϕ : Formula)  :
  Nonempty (∅ ⊢ ϕ) <-> Quotient.mk setoid_formula ϕ = ⊤ :=
  by
    simp only [Top.top]
    simp
    apply Iff.intro
    · intro Hnempty
      apply And.intro
      · apply Nonempty.intro
        exact Proof.extraPremise Proof.notConjContradict
      · apply Nonempty.intro
        exact Proof.extraPremise (Classical.choice Hnempty)
    · intro Hequiv
      apply Nonempty.intro
      rcases Hequiv with ⟨_, Hr⟩
      exact Proof.modusPonens Proof.notConjContradict (Classical.choice Hr)

def h_quot_var (v : Var) : Quotient setoid_formula := Quotient.mk setoid_formula (Formula.var v)

def h_quot (ϕ : Formula) : Quotient setoid_formula := Quotient.mk setoid_formula ϕ

lemma h_quot_interpretation :
  ∀ (ϕ : Formula),  h_quot ϕ = (@AlgInterpretation (Quotient setoid_formula) _ h_quot_var ϕ) :=
  by
    intro ϕ
    induction ϕ with
    | var v => rfl
    | bottom => unfold h_quot; unfold AlgInterpretation
                simp only [Bot.bot]; simp
                apply And.intro
                · apply Nonempty.intro
                  exact Proof.exfalso
                · apply Nonempty.intro
                  exact Proof.exFalsoAnd
    | and ψ χ ih1 ih2 => unfold h_quot; unfold AlgInterpretation
                         have Haux : Quotient.mk setoid_formula (ψ∧∧χ) =
                          and_quot (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) :=
                          by rfl
                         rw [Haux]
                         unfold h_quot at ih1
                         unfold h_quot at ih2
                         rw [<-ih1, <-ih2]
                         simp only [Inf.inf]
    | or ψ χ ih1 ih2 => unfold h_quot; unfold AlgInterpretation
                        have Haux : Quotient.mk setoid_formula (ψ∨∨χ) =
                          or_quot (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) :=
                          by rfl
                        rw [Haux]
                        unfold h_quot at ih1
                        unfold h_quot at ih2
                        rw [<-ih1, <-ih2]
                        simp only [Sup.sup]
    | implication ψ χ ih1 ih2 => unfold h_quot; unfold AlgInterpretation
                                 have Haux : Quotient.mk setoid_formula (ψ⇒χ) =
                                  to_quot (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) :=
                                  by rfl
                                 rw [Haux]
                                 unfold h_quot at ih1
                                 unfold h_quot at ih2
                                 rw [<-ih1, <-ih2]
                                 simp only [himp]

theorem completeness_alg (ϕ : Formula) :
  alg_univ_true ϕ -> Nonempty (∅ ⊢ ϕ) :=
  by
    intro Halg
    by_cases Hth : Nonempty (∅ ⊢ ϕ)
    · assumption
    · exfalso
      rw [equiv_top] at Hth
      let Halg := Halg (Quotient setoid_formula) h_quot_var
      rw [<-h_quot_interpretation] at Halg
      exact Hth Halg

theorem alg_true_kripke (ϕ : Formula) :
  alg_univ_true ϕ -> valid ϕ :=
  by
    intro Halg
    by_cases Hv : valid ϕ
    · assumption
    · exfalso
      unfold valid at Hv
      push_neg at Hv
      rcases Hv with ⟨W, ⟨M, ⟨w, Hnval⟩⟩⟩
      let Halg := Halg (all_closed M) h_var
      rw [<-h_interpretation] at Halg
      simp only [Top.top] at Halg
      rw [Subtype.ext_iff] at Halg
      rw [Set.ext_iff] at Halg
      simp at Halg
      exact Hnval (Halg w)

theorem kripke_alg_true (ϕ : Formula) {W : Type} {M : KripkeModel W} :
  valid ϕ -> alg_univ_true ϕ :=
  by
    intro Hvalid
    by_cases Halg : alg_univ_true ϕ
    · assumption
    · exfalso
      unfold alg_univ_true at Halg
      push_neg at Halg
      rcases Halg with ⟨α, ⟨H, ⟨I, Hnint⟩⟩⟩
      unfold valid at Hvalid
      let Hvalid := Hvalid (@prime_filters_closed W M) (prime_filters_model)
      have Hcompl : AlgInterpretation I (Formula.negation ϕ) = compl (AlgInterpretation I ϕ) :=
        by
          unfold Formula.negation
          have Haux : AlgInterpretation I (ϕ⇒⊥) = AlgInterpretation I ϕ ⇨ AlgInterpretation I ⊥ := by rfl
          rw [Haux]
          have Haux : AlgInterpretation I ⊥ = Bot.bot := by rfl
          rw [Haux]
          simp
      have Hneqbot : AlgInterpretation I (~ϕ) ≠ ⊥ :=
        by
          rw [Hcompl]
          simp
          rw [<-compl_top]
          intro Hcompl
          simp at Hnint
          apply Hnint
          have Haux : (AlgInterpretation I ϕ)ᶜ = AlgInterpretation I ϕ ⇨ ⊥ := by simp
          sorry
      sorry

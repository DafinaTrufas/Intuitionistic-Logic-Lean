import IL.HeytingAlgebraUtils
import IL.Formula
import IL.Semantics
import IL.Soundness

variable {α : Type} [HeytingAlgebra α]

def AlgInterpretation (I : Var → α) : Formula → α
| Formula.var p => I p
| Formula.bottom => ⊥
| ϕ ∧∧ ψ => AlgInterpretation I ϕ ⊓ AlgInterpretation I ψ
| ϕ ∨∨ ψ => AlgInterpretation I ϕ ⊔ AlgInterpretation I ψ
| ϕ ⇒ ψ => AlgInterpretation I ϕ ⇨ AlgInterpretation I ψ

lemma alg_compl (I : Var → α) : AlgInterpretation I (Formula.negation ϕ) = (AlgInterpretation I ϕ)ᶜ :=
  by
    unfold Formula.negation
    have Haux : AlgInterpretation I (ϕ⇒⊥) = AlgInterpretation I ϕ ⇨ AlgInterpretation I ⊥ := by rfl
    rw [Haux]
    have Haux : AlgInterpretation I ⊥ = Bot.bot := by rfl
    rw [Haux]
    simp

lemma alg_top (I : Var → α) : AlgInterpretation I Formula.top = Top.top :=
  by
    have Haux : AlgInterpretation I ⊤ = AlgInterpretation I ⊥ ⇨ AlgInterpretation I ⊥ := by rfl
    rw [Haux]
    have Haux : AlgInterpretation I ⊥ = Bot.bot := by rfl
    rw [Haux]
    simp

def true_in_alg_model (I : Var → α) (ϕ : Formula) : Prop := AlgInterpretation I ϕ = Top.top

def valid_in_alg (ϕ : Formula) : Prop := ∀ (I : Var → α), true_in_alg_model I ϕ

def alg_valid (ϕ : Formula) : Prop := ∀ (α : Type) [HeytingAlgebra α], @valid_in_alg α _ ϕ

def set_true_in_alg_model (I : Var → α) (Γ : Set Formula) : Prop :=
  ∀ (ϕ : Formula), ϕ ∈ Γ → AlgInterpretation I ϕ = Top.top

def set_valid_in_alg (Γ : Set Formula) : Prop := ∀ (I : Var → α), set_true_in_alg_model I Γ

def set_alg_valid (Γ : Set Formula) : Prop :=
  ∀ (α : Type) [HeytingAlgebra α], @set_valid_in_alg α _ Γ

def alg_sem_conseq (Γ : Set Formula) (ϕ : Formula) : Prop :=
  ∀ (α : Type) [HeytingAlgebra α] (I : Var → α),
  set_true_in_alg_model I Γ → true_in_alg_model I ϕ
infix:50 " ⊨ₐ " => alg_sem_conseq

lemma empty_conseq_alg_valid (ϕ : Formula) :
  ∅ ⊨ₐ ϕ ↔ alg_valid ϕ :=
  by
    apply Iff.intro
    · intro Hconseq α _ I
      simp only [alg_sem_conseq, set_true_in_alg_model] at Hconseq
      simp at Hconseq
      exact Hconseq α I
    · intro Halgvalid α _ I _
      exact Halgvalid α I

lemma elem_alg_sem_conseq (Γ : Set Formula) (ϕ : Formula) : ϕ ∈ Γ → Γ ⊨ₐ ϕ :=
  by
    intro Hin α _ _ Hsettrue
    exact Hsettrue ϕ Hin

lemma alg_valid_sem_conseq (Γ : Set Formula) (ϕ : Formula) : alg_valid ϕ → Γ ⊨ₐ ϕ :=
  by
    intro Halgvalid α _ I _
    exact Halgvalid α I

def closed {W : Type} (M : KripkeModel W) (A : Set W) : Prop :=
  ∀ (w w' : W), w ∈ A → M.R w w' → w' ∈ A

def all_closed {W : Type} (M : KripkeModel W) := {A // @closed W M A}

def all_closed_subset {W : Type} (M : KripkeModel W) (A B : all_closed M) :=
  {X | @closed W M X /\ X ⊆ ((@Set.univ W) \ A.1) ∪ B.1}

def himp_closed {W : Type} {M : KripkeModel W} (A B : all_closed M) :=
  Set.sUnion (@all_closed_subset W M A B)

lemma himp_closed_prop {W : Type} {M : KripkeModel W} (A B X : all_closed M) :
  X.1 ⊆ himp_closed A B ↔ X.1 ∩ A.1 ⊆ B.1 :=
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
  A.1 ⊆ B.1 → B.1 ⊆ A.1 → A.1 = B.1 :=
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
    | implication ψ χ ih1 ih2 => have Haux : ∀ (A : all_closed M), A.1 ⊆ (@h W M (ψ ⇒ χ)).1 ↔
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
                                 have Haux' : ∀ (A : all_closed M), A.1 ⊆ (@h W M (ψ ⇒ χ)).1 ↔
                                                 A.1 ⊆ himp_closed (@h W M ψ) (@h W M χ) :=
                                  by
                                    intro A
                                    let Haux := Haux A
                                    rw [Haux]
                                    rw [<-himp_closed_prop]
                                 rw [Set.ext_iff]
                                 intro w
                                 apply Iff.intro
                                 · intro Hwin
                                   exists (@h W M (ψ⇒χ)).1
                                   apply And.intro
                                   · apply And.intro
                                     · exact (@h W M (ψ⇒χ)).2
                                     · let Haux' := Haux' (@h W M (ψ⇒χ))
                                       unfold himp_closed at Haux'
                                       rcases Haux' with ⟨hl, _⟩
                                       let Haux' := hl Set.Subset.rfl
                                       apply Set.Subset.trans Haux'
                                       rw [Set.sUnion_subset_iff]
                                       intro t Htin
                                       exact Htin.right
                                   · assumption
                                 · intro Hwin
                                   rcases Hwin with ⟨t, ⟨⟨Hwint, Htclosed⟩, Htsubset⟩⟩
                                   let Haux' := Haux' {val := t, property := Hwint}
                                   have Haux'' : t ⊆ @himp_closed W M (h ψ) (h χ) :=
                                    by
                                      apply Set.subset_sUnion_of_mem
                                      apply And.intro
                                      assumption'
                                   rw [<-Haux'] at Haux''
                                   apply Set.mem_of_subset_of_mem Haux'' Htsubset

lemma kripke_alg {W : Type} {M : KripkeModel W} (ϕ : Formula) :
  valid_in_model M ϕ ↔ @true_in_alg_model (all_closed M) _ h_var ϕ :=
  by
    apply Iff.intro
    · intro Hvalid
      unfold true_in_alg_model
      rw [<-h_interpretation]
      simp only [Top.top]
      rw [Subtype.ext_iff, Set.ext_iff]
      simp
      assumption
    · intro Htruealg
      unfold true_in_alg_model at Htruealg
      rw [<-h_interpretation] at Htruealg
      simp only [Top.top] at Htruealg
      rw [Subtype.ext_iff, Set.ext_iff] at Htruealg
      simp at Htruealg
      assumption

def prime_filters_frame (I : Var → α) :
  KripkeModel (@prime_filters α _) :=
  {
   R := λ (F1 F2) => F1.1 ⊆ F2.1,
   V := λ (v F) => I v ∈ F.1,
   refl := λ (F) => Set.Subset.rfl
   trans := λ (F1 F2 Φ) => Set.Subset.trans
   monotonicity := λ (v F1 F2) => by intros; apply Set.mem_of_mem_of_subset; assumption'
  }

def Vh_var (v : Var) (F : @prime_filters α _) (I : Var → α) : Prop :=
  I v ∈ F.1

def Vh (ϕ : Formula) (F : @prime_filters α _) (I : Var → α) : Prop :=
  AlgInterpretation I ϕ ∈ F.1

lemma Vh_valuation (I : Var → α) :
  ∀ (ϕ : Formula) (F : @prime_filters α _), Vh ϕ F I = val (prime_filters_frame I) F ϕ :=
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
                         have Hsplit : AlgInterpretation I ψ ⊓ AlgInterpretation I χ ∈ F.1 ↔
                                       AlgInterpretation I ψ ∈ F.1 ∧ AlgInterpretation I χ ∈ F.1 :=
                          by
                            apply Iff.intro
                            · intro Hglb
                              exact And.intro (F.2.1.1.2.2 _ _ Hglb inf_le_left) (F.2.1.1.2.2 _ _ Hglb inf_le_right)
                            · intro Hand
                              exact F.2.1.1.2.1 _ _ Hand.left Hand.right
                         unfold val
                         unfold Vh at ih1
                         unfold Vh at ih2
                         rw [<-ih1, <-ih2]
                         simp
                         assumption
    | or ψ χ ih1 ih2 => intro F
                        unfold Vh
                        have Hsplit : AlgInterpretation I ψ ⊔ AlgInterpretation I χ ∈ F.1 ↔
                                      AlgInterpretation I ψ ∈ F.1 ∨ AlgInterpretation I χ ∈ F.1 :=
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
                                   rw [@filter_dedsyst_equiv α _ (@AlgInterpretation α _ I ψ) (@AlgInterpretation α _ I ψ)] at HF'filter
                                   have Hvh : AlgInterpretation I ψ ⇨ AlgInterpretation I χ ∈ F'.1 :=
                                    by
                                      apply Set.mem_of_subset_of_mem Hr
                                      assumption
                                   let Haux := HF'filter.2 (AlgInterpretation I ψ) (AlgInterpretation I χ) Hvalpsi Hvh
                                   rw [<-ih2]
                                   assumption
                                 · intro Hval
                                   unfold val at Hval
                                   by_cases Hvh : Vh (ψ ⇒ χ) F I
                                   · assumption
                                   · exfalso
                                     unfold Vh at Hvh
                                     have Hnotin : AlgInterpretation I χ ∉ X_gen_filter (F.1 ∪ {AlgInterpretation I ψ}) :=
                                      by
                                        apply himp_not_mem
                                        · exact F.2.1.1
                                        · unfold AlgInterpretation at Hvh
                                          assumption
                                     have Hnempty : Set.Nonempty (F.1 ∪ {AlgInterpretation I ψ}) :=
                                      by
                                        rw [Set.union_comm, Set.singleton_union]
                                        apply Set.insert_nonempty
                                     let Haux := @super_prime_filter α _ (AlgInterpretation I χ) (X_gen_filter (F.1 ∪ {AlgInterpretation I ψ}))
                                                  (X_gen_filter_filter ((F.1 ∪ {AlgInterpretation I ψ})) Hnempty) Hnotin
                                     rcases Haux with ⟨P, ⟨Hprime, ⟨Hsubset, Hchinotin⟩⟩⟩
                                     have Hsubset' : F.1 ⊆ P :=
                                      by
                                        apply Set.Subset.trans (Set.subset_union_left F.1 {AlgInterpretation I ψ})
                                        apply Set.Subset.trans (X_subset_X_gen_filter (F.1 ∪ {AlgInterpretation I ψ})) Hsubset
                                     simp at Hval
                                     let Hval := Hval P Hprime Hsubset'
                                     rw [<-ih1, <-ih2] at Hval
                                     apply Hchinotin
                                     apply Hval
                                     have Hpsiin : AlgInterpretation I ψ ∈ X_gen_filter (F.1 ∪ {AlgInterpretation I ψ}) :=
                                      by
                                        unfold X_gen_filter
                                        simp
                                        intro F'' _ Hsubset''
                                        rw [Set.insert_subset_iff] at Hsubset''
                                        exact Hsubset''.left
                                     apply Set.mem_of_subset_of_mem Hsubset Hpsiin

lemma alg_kripke (I : Var → α) (ϕ : Formula) :
  true_in_alg_model I ϕ ↔ valid_in_model (prime_filters_frame I) ϕ :=
  by
    apply Iff.intro
    · intro Htruealg
      intro Hprime
      rcases Hprime with ⟨F, ⟨⟨Hfilter, _⟩, _⟩⟩
      rw [<-Vh_valuation]
      unfold Vh
      rw [Htruealg]
      exact @top_mem_filter α _ F Hfilter
    · intro Hvalid
      have Haux : (∀ (w : ↑prime_filters), val (prime_filters_frame I) w ϕ) →
                  (∀ (w : ↑prime_filters), Vh ϕ w I) :=
      by
        intro _ _
        rw [Vh_valuation]
        apply Hvalid
      let Hvalid := Haux Hvalid
      unfold Vh at Hvalid
      simp at Hvalid
      rw [<-Set.mem_sInter, super_prime_filter_cor2] at Hvalid
      assumption

variable {Γ : Set Formula}

def equiv (ϕ ψ : Formula) := Nonempty (Γ ⊢ ϕ ⇔ ψ)
infix:50 "∼" => equiv

lemma equiv_and (ϕ ψ : Formula) : @equiv Γ ϕ ψ ↔ Nonempty (Γ ⊢ ϕ ⇒ ψ) ∧ Nonempty (Γ ⊢ ψ ⇒ ϕ) :=
  by
    unfold equiv
    apply Iff.intro
    · intro Hequiv
      unfold Formula.equivalence at Hequiv
      apply Proof.conjIntroRule' (Classical.choice Hequiv)
    · intro Hand
      apply Nonempty.intro
      apply Proof.conjIntroRule (Classical.choice Hand.left) (Classical.choice Hand.right)

@[simp]
instance setoid_formula : Setoid Formula :=
  { r := @equiv Γ,
    iseqv := ⟨λ _ => by rw [equiv_and]; exact And.intro (Nonempty.intro Proof.implSelf) (Nonempty.intro Proof.implSelf),
              λ H12 => by rw [equiv_and, And.comm]; rw [equiv_and] at H12; assumption,
              λ H12 H23 => by
                              rw [equiv_and]; rw [equiv_and] at H12; rw [equiv_and] at H23
                              apply And.intro
                              · apply Nonempty.intro
                                exact Proof.syllogism (Classical.choice H12.left) (Classical.choice H23.left)
                              · apply Nonempty.intro
                                exact Proof.syllogism (Classical.choice H23.right) (Classical.choice H12.right)
                              ⟩ }

def Formula.le (ϕ ψ : Formula) : Prop := Nonempty (Γ ⊢ ϕ ⇒ ψ)

lemma le_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ ψ' → (@Formula.le Γ ϕ ψ = @Formula.le Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    simp
    apply Iff.intro
    · intro Hvppsi
      apply Nonempty.intro
      rw [equiv_and] at Heqvp; rw [equiv_and] at Heqpsi
      exact Proof.syllogism (Proof.syllogism (Classical.choice Heqvp.right) (Classical.choice Hvppsi))
                            (Classical.choice Heqpsi.left)
    · intro Hvp'psi'
      apply Nonempty.intro
      rw [equiv_and] at Heqvp; rw [equiv_and] at Heqpsi
      exact Proof.syllogism (Proof.syllogism (Classical.choice Heqvp.left) (Classical.choice Hvp'psi'))
                            (Classical.choice Heqpsi.right)

def le_quot (ϕ ψ : Quotient (@setoid_formula Γ)) : Prop :=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.le le_preserves_equiv ϕ ψ
infix:50 "≤" => le_quot

def Formula.or_quot (ϕ ψ : Formula) := Quotient.mk (@setoid_formula Γ) (ϕ ∨∨ ψ)

lemma or_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ ψ' →
  (@Formula.or_quot Γ ϕ ψ = @Formula.or_quot Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    apply Quotient.sound
    rw [equiv_and] at Heqvp
    rw [equiv_and] at Heqpsi
    simp [HasEquiv.Equiv, Setoid.r]
    rw [equiv_and]
    apply And.intro
    · apply Nonempty.intro
      exact Proof.orImplDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.orImplDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.right)

def or_quot (ϕ ψ : Quotient (@setoid_formula Γ)) : Quotient (@setoid_formula Γ) :=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.or_quot or_quot_preserves_equiv ϕ ψ

def Formula.and_quot (ϕ ψ : Formula) := Quotient.mk (@setoid_formula Γ) (ϕ ∧∧ ψ)

lemma and_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ ψ' →
  (@Formula.and_quot Γ ϕ ψ = @Formula.and_quot Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    apply Quotient.sound
    rw [equiv_and] at Heqvp
    rw [equiv_and] at Heqpsi
    simp [HasEquiv.Equiv, Setoid.r]
    rw [equiv_and]
    apply And.intro
    · apply Nonempty.intro
      exact Proof.andImplDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.andImplDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.right)

def and_quot (ϕ ψ : Quotient (@setoid_formula Γ)) : Quotient (@setoid_formula Γ) :=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.and_quot and_quot_preserves_equiv ϕ ψ

def Formula.to_quot (ϕ ψ : Formula) := Quotient.mk (@setoid_formula Γ) (ϕ ⇒ ψ)

lemma to_quot_preserves_equiv (ϕ ψ ϕ' ψ' : Formula) : @equiv Γ ϕ ϕ' → @equiv Γ ψ  ψ' →
  (@Formula.to_quot Γ ϕ ψ = @Formula.to_quot Γ ϕ' ψ') :=
  by
    intro Heqvp Heqpsi
    apply Quotient.sound
    rw [equiv_and] at Heqvp
    rw [equiv_and] at Heqpsi
    simp [HasEquiv.Equiv, Setoid.r]
    rw [equiv_and]
    apply And.intro
    · apply Nonempty.intro
      exact Proof.equivDistrib (Classical.choice Heqvp.right) (Classical.choice Heqpsi.left)
    · apply Nonempty.intro
      exact Proof.equivDistrib (Classical.choice Heqvp.left) (Classical.choice Heqpsi.right)

def to_quot (ϕ ψ : Quotient (@setoid_formula Γ)) : Quotient (@setoid_formula Γ):=
  Quotient.lift₂ (s₁ := @setoid_formula Γ) (s₂ := @setoid_formula Γ) Formula.to_quot to_quot_preserves_equiv ϕ ψ

instance lt_heyting : HeytingAlgebra (Quotient (@setoid_formula Γ)) :=
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
                                        apply Quotient.sound
                                        simp [HasEquiv.Equiv, Setoid.r]
                                        rw [equiv_and]
                                        apply And.intro H12 H21
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
    top := Quotient.mk setoid_formula Formula.top
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
                      exact Proof.extraPremise Proof.exfalso
    bot := Quotient.mk setoid_formula Formula.bottom
    bot_le := λ q => by
                      induction q using Quotient.ind
                      apply Nonempty.intro
                      exact Proof.exfalso
    compl := λ q => to_quot q (Quotient.mk setoid_formula Formula.bottom)
    himp_bot := by simp }

lemma equiv_top (ϕ : Formula)  :
  Nonempty (Γ ⊢ ϕ) ↔ Quotient.mk (@setoid_formula Γ) ϕ = Top.top :=
  by
    simp only [Top.top]
    apply Iff.intro
    · intro Hnempty
      apply Quotient.sound
      simp [HasEquiv.Equiv, Setoid.r]
      rw [equiv_and]
      apply And.intro
      · apply Nonempty.intro
        exact Proof.extraPremise Proof.exfalso
      · apply Nonempty.intro
        exact Proof.extraPremise (Classical.choice Hnempty)
    · intro Hequiv
      apply Nonempty.intro
      let Hequiv := Quotient.exact Hequiv
      simp [HasEquiv.Equiv, Setoid.r] at Hequiv
      rw [equiv_and] at Hequiv
      rcases Hequiv with ⟨_, Hr⟩
      exact Proof.modusPonens Proof.exfalso (Classical.choice Hr)

def h_quot_var (v : Var) : Quotient (@setoid_formula Γ) := Quotient.mk setoid_formula (Formula.var v)

def h_quot (ϕ : Formula) : Quotient (@setoid_formula Γ) := Quotient.mk setoid_formula ϕ

lemma h_quot_interpretation :
  ∀ (ϕ : Formula),  h_quot ϕ = (@AlgInterpretation (Quotient (@setoid_formula Γ)) _ h_quot_var ϕ) :=
  by
    intro ϕ
    induction ϕ with
    | var v => rfl
    | bottom => unfold h_quot; unfold AlgInterpretation
                simp only [Bot.bot]
    | and ψ χ ih1 ih2 => unfold h_quot; unfold AlgInterpretation
                         have Haux : Quotient.mk (@setoid_formula Γ) (ψ∧∧χ) =
                          and_quot (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) :=
                          by rfl
                         rw [Haux]
                         unfold h_quot at ih1
                         unfold h_quot at ih2
                         rw [<-ih1, <-ih2]
                         simp only [Inf.inf]
    | or ψ χ ih1 ih2 => unfold h_quot; unfold AlgInterpretation
                        have Haux : Quotient.mk (@setoid_formula Γ) (ψ∨∨χ) =
                          or_quot (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) :=
                          by rfl
                        rw [Haux]
                        unfold h_quot at ih1
                        unfold h_quot at ih2
                        rw [<-ih1, <-ih2]
                        simp only [Sup.sup]
    | implication ψ χ ih1 ih2 => unfold h_quot; unfold AlgInterpretation
                                 have Haux : Quotient.mk (@setoid_formula Γ) (ψ⇒χ) =
                                  to_quot (Quotient.mk setoid_formula ψ) (Quotient.mk setoid_formula χ) :=
                                  by rfl
                                 rw [Haux]
                                 unfold h_quot at ih1
                                 unfold h_quot at ih2
                                 rw [<-ih1, <-ih2]
                                 simp only [himp]

lemma set_true_in_lt :
  @set_true_in_alg_model (Quotient (@setoid_formula Γ)) _ h_quot_var Γ :=
  by
    intro ϕ Hin
    rw [<-h_quot_interpretation]
    unfold h_quot
    rw [<-equiv_top]
    apply Nonempty.intro
    exact Proof.premise Hin

lemma true_in_lt (ϕ : Formula) :
  @true_in_alg_model (Quotient (@setoid_formula Γ)) _ h_quot_var ϕ ↔ Nonempty (Γ ⊢ ϕ) :=
  by
    apply Iff.intro
    · intro Htruelt
      apply Nonempty.intro
      unfold true_in_alg_model at Htruelt
      rw [<-h_quot_interpretation] at Htruelt
      unfold h_quot at Htruelt
      rw [<-equiv_top] at Htruelt
      exact Classical.choice Htruelt
    · intro Hnempty
      rw [equiv_top] at Hnempty
      unfold true_in_alg_model
      rw [<-h_quot_interpretation]
      assumption

theorem soundness_alg (ϕ : Formula) : Nonempty (Γ ⊢ ϕ) → alg_sem_conseq Γ ϕ :=
  by
    intro Htheorem
    let Htheorem' := Classical.choice Htheorem
    induction Htheorem' with
    | @premise ϕ Hin => intro _ _ _ Hsettrue
                        exact Hsettrue ϕ Hin
    | @contractionDisj ψ => intro _ _ I _
                            unfold true_in_alg_model; unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∨∨ ψ) = AlgInterpretation I ψ ⊔ AlgInterpretation I ψ := by rfl
                            rw [Haux, himp_eq_top_iff, sup_idem]
    | @contractionConj ψ => intro _ _ I _
                            unfold true_in_alg_model; unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∧∧ ψ) = AlgInterpretation I ψ ⊓ AlgInterpretation I ψ := by rfl
                            rw [Haux, himp_eq_top_iff, inf_idem]
    | @weakeningDisj ψ χ => intro _ _ I _
                            unfold true_in_alg_model; unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∨∨ χ) = AlgInterpretation I ψ ⊔ AlgInterpretation I χ := by rfl
                            rw [Haux, himp_eq_top_iff]
                            exact le_sup_left
    | @weakeningConj ψ χ => intro _ _ I _
                            unfold true_in_alg_model; unfold AlgInterpretation
                            have Haux : AlgInterpretation I (ψ ∧∧ χ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ := by rfl
                            rw [Haux, himp_eq_top_iff]
                            exact inf_le_left
    | @permutationDisj ψ χ => intro _ _ I _
                              unfold true_in_alg_model; unfold AlgInterpretation
                              have Haux : AlgInterpretation I (ψ ∨∨ χ) = AlgInterpretation I ψ ⊔ AlgInterpretation I χ := by rfl
                              rw [Haux]
                              have Haux : AlgInterpretation I (χ ∨∨ ψ) = AlgInterpretation I χ ⊔ AlgInterpretation I ψ := by rfl
                              rw [Haux, himp_eq_top_iff, sup_comm]
    | @permutationConj ψ χ => intro _ _ I _
                              unfold true_in_alg_model; unfold AlgInterpretation
                              have Haux : AlgInterpretation I (ψ ∧∧ χ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ := by rfl
                              rw [Haux]
                              have Haux : AlgInterpretation I (χ ∧∧ ψ) = AlgInterpretation I χ ⊓ AlgInterpretation I ψ := by rfl
                              rw [Haux, himp_eq_top_iff, inf_comm]
    | @exfalso ψ => intro _ _ I _
                    unfold true_in_alg_model; unfold AlgInterpretation
                    have Haux : AlgInterpretation I ⊥ = Bot.bot := by rfl
                    rw [Haux, himp_eq_top_iff]
                    exact bot_le
    | @modusPonens ψ χ p1 p2 ih1 ih2 => intro α _ I Hsettrue
                                        simp at ih1; simp at ih2
                                        let ih2 := ih2 p2
                                        let ih1 := ih1 p1
                                        have Haux : AlgInterpretation I (ψ ⇒ χ) = AlgInterpretation I ψ ⇨ AlgInterpretation I χ := by rfl
                                        let ih2 := ih2 α I Hsettrue
                                        unfold true_in_alg_model at ih2
                                        rw [Haux, ih1, top_himp] at ih2
                                        assumption'
    | @syllogism ψ χ γ p1 p2 ih1 ih2 => intro α _ I Hsettrue
                                        simp at ih1; simp at ih2
                                        let ih1 := ih1 p1
                                        let ih2 := ih2 p2
                                        have Haux1 : AlgInterpretation I (ψ ⇒ χ) = AlgInterpretation I ψ ⇨ AlgInterpretation I χ := by rfl
                                        have Haux2 : AlgInterpretation I (χ ⇒ γ) = AlgInterpretation I χ ⇨ AlgInterpretation I γ := by rfl
                                        let ih1 := ih1 α I Hsettrue; let ih2 := ih2 α I Hsettrue
                                        unfold true_in_alg_model at ih1; unfold true_in_alg_model at ih2
                                        rw [Haux1, himp_eq_top_iff] at ih1
                                        rw [Haux2, himp_eq_top_iff] at ih2
                                        unfold true_in_alg_model; unfold AlgInterpretation
                                        rw [himp_eq_top_iff]
                                        apply le_trans
                                        assumption'
    | @exportation ψ χ γ p ih => intro α _ I Hsettrue
                                 simp at ih
                                 let ih := ih p
                                 have Haux : AlgInterpretation I (ψ ∧∧ χ ⇒ γ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ ⇨ AlgInterpretation I γ := by rfl
                                 let ih := ih α I Hsettrue
                                 unfold true_in_alg_model at ih
                                 rw [Haux] at ih
                                 rw [himp_eq_top_iff] at ih
                                 unfold true_in_alg_model; unfold AlgInterpretation
                                 have Haux : AlgInterpretation I (χ ⇒ γ) = AlgInterpretation I χ ⇨ AlgInterpretation I γ := by rfl
                                 rw [Haux, himp_eq_top_iff, le_himp_iff]
                                 assumption
    | @importation ψ χ γ p ih => intro α _ I Hsettrue
                                 simp at ih
                                 let ih := ih p
                                 have Haux : AlgInterpretation I (ψ ⇒ χ ⇒ γ) = AlgInterpretation I ψ ⇨ AlgInterpretation I χ ⇨ AlgInterpretation I γ := by rfl
                                 let ih := ih α I Hsettrue
                                 unfold true_in_alg_model at ih
                                 rw [Haux, himp_eq_top_iff] at ih
                                 unfold true_in_alg_model; unfold AlgInterpretation
                                 have Haux : AlgInterpretation I (ψ ∧∧ χ) = AlgInterpretation I ψ ⊓ AlgInterpretation I χ := by rfl
                                 rw [Haux, himp_eq_top_iff, <-le_himp_iff]
                                 assumption
    | @expansion ψ χ γ p ih => intro α _ I Hsettrue
                               simp at ih
                               let ih := ih p
                               have Haux : AlgInterpretation I (ψ ⇒ χ) = AlgInterpretation I ψ ⇨ AlgInterpretation I χ := by rfl
                               let ih := ih α I Hsettrue
                               unfold true_in_alg_model at ih
                               rw [Haux, himp_eq_top_iff] at ih
                               let ih := sup_le_sup_left ih (AlgInterpretation I γ)
                               have Haux : AlgInterpretation I γ ⊔ AlgInterpretation I ψ = AlgInterpretation I (γ ∨∨ ψ) := by rfl
                               rw [Haux] at ih
                               have Haux : AlgInterpretation I γ ⊔ AlgInterpretation I χ = AlgInterpretation I (γ ∨∨ χ) := by rfl
                               rw [Haux] at ih
                               unfold true_in_alg_model; unfold AlgInterpretation
                               rw [himp_eq_top_iff]
                               assumption

theorem completeness_alg (ϕ : Formula) :
  alg_sem_conseq Γ ϕ ↔ Nonempty (Γ ⊢ ϕ) :=
  by
    apply Iff.intro
    · intro Halg
      rw [<-true_in_lt]
      exact Halg (Quotient (@setoid_formula Γ)) h_quot_var set_true_in_lt
    · exact soundness_alg ϕ

theorem alg_true_kripke (ϕ : Formula) :
  alg_valid ϕ → valid ϕ :=
  by
    intro Halg _ _
    rw [kripke_alg]
    apply Halg

theorem kripke_alg_true (ϕ : Formula) :
  valid ϕ → alg_valid ϕ :=
  by
    intro Hvalid _ _ _
    rw [alg_kripke]
    apply Hvalid

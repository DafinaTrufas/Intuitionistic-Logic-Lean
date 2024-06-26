import IL.Formula
import IL.Syntax
import IL.Semantics
import IL.CompletenessListUtils
import Mathlib.Data.Set.Basic

set_option autoImplicit false

variable {Γ Δ : Set Formula} {ϕ ψ χ γ : Formula}

def dedClosed {Γ : Set Formula} := forall (ϕ : Formula), Γ ⊢ ϕ -> ϕ ∈ Γ

def consistent {Γ : Set Formula} := Γ ⊢ ⊥ -> False

def disjunctive {Γ : Set Formula} := forall (ϕ ψ : Formula), Γ ⊢ ϕ ∨∨ ψ -> Sum (Γ ⊢ ϕ) (Γ ⊢ ψ)

def disjunctiveTheory {Γ : Set Formula} :=
  @dedClosed Γ /\ @consistent Γ /\ Nonempty (@disjunctive Γ)

abbrev setDisjTh := {Γ // @disjunctiveTheory Γ}

def canonicalModel : KripkeModel (setDisjTh) :=
  {
   R := fun (Γ Δ) => Γ.1 ⊆ Δ.1,
   V := fun (v Γ) => Formula.var v ∈ Γ.1,
   refl := fun (Γ) => Set.Subset.rfl
   trans := fun (Γ Δ Φ) => Set.Subset.trans
   monotonicity := fun (v Γ Δ) => by intros; apply Set.mem_of_mem_of_subset; assumption'
  }

def consistentPair {Γ Δ : Set Formula} :=
  forall (Φ Ω : Finset Formula), Φ.toSet ⊆ Γ -> Ω.toSet ⊆ Δ ->
  (∅ ⊢ Φ.toList.foldr Formula.and (~⊥) ⇒ Ω.toList.foldr Formula.or ⊥ -> False)

def completePair {Γ Δ : Set Formula} :=
  @consistentPair Γ Δ /\ forall (ϕ : Formula), (ϕ ∈ Γ /\ ϕ ∉ Δ) ∨ (ϕ ∈ Δ /\ ϕ ∉ Γ)

noncomputable instance {Γ Δ : Set Formula} : Decidable (@consistentPair Γ Δ) := @default _ (Classical.decidableInhabited _)

lemma disjunctive_ind {Γ : Set Formula} {Δ : List Formula} {Hnempty : Δ ≠ []} :
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
                           apply Proof.modusPonens Ht Proof.exfalso
                         · apply Or.inr
                           apply ih Hdisj Ht
                           assumption

lemma consistent_snd_empty : @consistent Γ -> @consistentPair Γ ∅ :=
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
    apply Proof.subset_proof Hsubset1
    let Hexp := Proof.deductionTheorem_right_ind (Proof.exportation_ind Hfold)
    rw [Set.empty_union] at Hexp
    simp at Hexp
    assumption

lemma consistent_fst_consistent : @consistentPair Γ Δ -> @consistent Γ :=
  by
    simp [consistent, consistentPair]
    intros Hcpair Hgamma
    rcases (Proof.lemma_finset Hgamma) with ⟨Ω, Homega⟩
    eapply Hcpair Ω ∅
    · exact And.left Homega
    · simp
    · simp
      apply Proof.deductionTheorem_left
      rcases Homega with ⟨_, Hnonempty⟩
      apply Proof.deductionTheorem_right
      apply Proof.importation_ind
      apply Proof.deductionTheorem_left_ind
      rw [Set.empty_union]
      apply Classical.choice
      simp
      assumption

lemma complete_pair_fst_disj : @completePair Γ Δ -> @disjunctiveTheory Γ :=
  by
    simp [completePair, disjunctiveTheory]
    intros Hcons Hcompl
    have Hded : @dedClosed Γ :=
      by
        unfold dedClosed
        intros vp Hvp
        rcases Hcompl vp with Hgelem | Hdelem
        · exact And.left Hgelem
        · rcases (Proof.lemma_finset Hvp) with ⟨Φ, ⟨Hincl, Hnonempty⟩⟩
          apply Hnonempty.elim
          intros Homega
          have Homega' : ∅ ∪ Φ.toList.toFinset ⊢ vp := by rw [Set.empty_union]; simp; assumption
          let Hded := Proof.deductionTheorem_left_ind Homega'
          let Himp := Proof.importation_ind Hded
          simp [consistentPair] at Hcons
          exfalso
          let Hconsspec := Hcons Φ {vp} Hincl
          simp at Hconsspec
          let Hconsspec' := Hconsspec (And.left Hdelem)
          apply Hconsspec'
          have Horbot : ∅ ⊢ vp ⇒ vp ∨∨ ⊥ := by apply Proof.weakeningDisj
          apply Proof.syllogism Himp Horbot
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
            · let Hpremise := Nonempty.intro (Proof.premise (And.left Hphi1))
              contradiction
            · by_cases h'' : ψ ∈ Γ
              · let Hpremise := Nonempty.intro (Proof.premise h'')
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
                    have Hsubset1 : {ϕ} ⊆ Δ ∧ {ψ} ⊆ Δ :=
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
                    rcases Hlist : [ϕ, ψ] with nil | ⟨h, t⟩
                    · simp at Hlist
                    · by_cases Heq : ϕ = ψ
                      · rw [Heq]
                        simp
                        apply Proof.syllogism (Proof.syllogism Proof.weakeningConj Proof.contractionDisj) Proof.weakeningDisj
                      · let Hset := Hlist
                        rw [<-List.doubleton_eq] at Hset
                        · simp at Hlist
                          have Haux : Finset.toList {ϕ, ψ} = [ϕ, ψ] \/ Finset.toList {ϕ, ψ} = [ψ, ϕ] :=
                            by
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
                              simp at Hvpelemdoubleton
                              simp at Hpsielemdoubleton
                              rcases Hvpelemdoubleton with Hvpa | Hvpb
                              · rcases Hpsielemdoubleton with Hpsia | Hpsib
                                · rw [<-Hpsia] at Hvpa
                                  contradiction
                                · apply Or.inl
                                  rw [Hvpa, Hpsib]
                              · rcases Hpsielemdoubleton with Hpsia | Hpsib
                                · apply Or.inr
                                  rw [Hvpb, Hpsia]
                                · rw [<-Hpsib] at Hvpb
                                  contradiction
                          apply Classical.choice
                          rcases Haux with Hperm1 | Hperm2
                          · apply Nonempty.intro
                            rw [Hperm1]
                            simp
                            apply Proof.syllogism Proof.weakeningConj (Proof.syllogism Proof.weakeningDisj Proof.orAssoc1)
                          · apply Nonempty.intro
                            rw [Hperm2]
                            simp
                            apply Proof.syllogism Proof.weakeningConj (Proof.syllogism Proof.permutationDisj (Proof.syllogism Proof.weakeningDisj Proof.orAssoc1))
                        · assumption

lemma disjth_completePair : @disjunctiveTheory Γ -> @completePair Γ Γᶜ :=
  by
    simp [disjunctiveTheory, dedClosed, consistent, disjunctive, completePair]
    intros Hded Hcons Hdisj
    apply And.intro
    · unfold consistentPair
      intros Φ Ω Hsubset1 Hsubset2 Hncons
      have Hconj : @Proof.set_proof_set Γ {List.foldr Formula.and (~⊥) (Finset.toList Φ)} :=
        by
          simp [Proof.set_proof_set]
          intros vp Hin
          have Helemconseq : ∅ ∪ {List.foldr Formula.and (~⊥) (Finset.toList Φ)} ⊢ vp :=
            by
              let Hpremise := Proof.premise Hin
              rw [Set.empty_union]
              assumption
          let Hded := Proof.deductionTheorem_left Helemconseq
          let Hexp := Proof.exportation_ind Hded
          let Hded' := Proof.deductionTheorem_right_ind Hexp
          rw [Set.empty_union] at Hded'
          simp at Hded'
          apply Proof.subset_proof Hsubset1 Hded'
      let Hdedth := Proof.deductionTheorem_right Hncons
      rw [Set.empty_union] at Hdedth
      have Htransconseq : Γ ⊢ List.foldr Formula.or ⊥ (Finset.toList Ω) :=
        by apply Proof.set_conseq_proof Hconj Hdedth
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

lemma consistent_disj :
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
      apply Proof.syllogism Proof.weakeningConj Proof.weakeningDisj

lemma add_preserves_cons :
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
      have Hvp1 : vp ∈ Φ1 :=
        by
          by_cases vp ∈ Φ1
          · assumption
          · exfalso
            rw [<-Finset.mem_coe, <-Set.disjoint_singleton_right] at h
            let Hsubset := Disjoint.subset_right_of_subset_union h1 h
            let Hncons := Hcons Φ1 Ω1 Hsubset h1' w1
            assumption
      have Hauxvp1 : Φ1 = {vp} ∪ Φ1 \ {vp} := by simp; assumption
      rw [Hauxvp1] at w1
      have Hvpi2 : vp ∈ Ω2 :=
        by
          by_cases vp ∈ Ω2
          · assumption
          · exfalso
            rw [<-Finset.mem_coe, <-Set.disjoint_singleton_right] at h
            let Hsubset := Disjoint.subset_right_of_subset_union h2' h
            let Hncons := Hcons Φ2 Ω2 h2 Hsubset w2
            assumption
      have Hauxvp2 : Ω2 = {vp} ∪ Ω2 \ {vp} := by simp; assumption
      rw [Hauxvp2] at w2
      have Haux : vp ∉ Φ1 \ {vp} := by simp
      let Hperm := List.Perm.symm (Finset.toList_cons Haux)
      let Hpermconjequiv := Classical.choice (Proof.permutationConj_ind (vp :: Finset.toList (Φ1 \ {vp})) (Finset.toList (Finset.cons vp (Φ1 \ {vp}) Haux)) Hperm)
      simp at Hpermconjequiv
      let Hweakconj := @Proof.weakeningConj ∅ (vp ∧∧ List.foldr Formula.and (~⊥) (Φ1 \ {vp}).toList) (List.foldr Formula.and (~⊥) Φ2.toList)
      let Hsyllog1 := Proof.syllogism Hweakconj (Proof.syllogism Hpermconjequiv w1)
      let Hweakdisj := @Proof.weakeningDisj ∅ (List.foldr Formula.or ⊥ Ω1.toList) (List.foldr Formula.or ⊥ (Ω2 \ {vp}).toList)
      let Hsyllog1 := Proof.syllogism Proof.permutationConj (Proof.syllogism Proof.andAssoc2 (Proof.syllogism Hsyllog1 Hweakdisj))
      have Haux : vp ∉ Ω2 \ {vp} := by simp
      let Hperm := Finset.toList_cons Haux
      let Hpermdisjequiv := Classical.choice (Proof.permutationDisj_ind (Finset.toList (Finset.cons vp (Ω2 \ {vp}) Haux)) (vp :: Finset.toList (Ω2 \ {vp}))  Hperm)
      simp at Hpermdisjequiv
      let Hperm := @Proof.permutationDisj ∅ vp (List.foldr Formula.or ⊥ (Ω2 \ {vp}).toList)
      let Hweakconj := @Proof.weakeningConj ∅ (List.foldr Formula.and (~⊥) (Finset.toList Φ2)) (List.foldr Formula.and (~⊥) (Finset.toList (Φ1 \ {vp})))
      let Hweakdisj := @Proof.weakeningDisj ∅ (List.foldr Formula.or ⊥ (Finset.toList (Ω2 \ {vp}))∨∨vp) (List.foldr Formula.or ⊥ (Finset.toList (Ω1)))
      let Hcontra := Proof.nconsContra Hsyllog1 (Proof.syllogism Proof.permutationConj (Proof.syllogism (Proof.syllogism (Proof.syllogism (Proof.syllogism Hweakconj
                    (Proof.syllogism (Proof.syllogism w2 Hpermdisjequiv) Hperm)) Hweakdisj) Proof.permutationDisj) Proof.orAssoc2))
      let Hfoldr := Proof.syllogism (Classical.choice (Proof.foldrAndUnion (Φ1 \ {vp}) Φ2)) Hcontra
      let Hcontra' := Proof.syllogism Hfoldr (Classical.choice (Proof.foldrOrUnion Ω1 (Ω2 \ {vp})))
      have Hauxunionphi : ↑((Φ1 \ {vp}) ∪ Φ2) ⊆ Γ := by simp; apply And.intro; rw [Set.insert_eq]; assumption'
      have Hauxunionomega : ↑(Ω1 ∪ (Ω2 \ {vp})) ⊆ Δ := by simp; apply And.intro; assumption; rw [Set.insert_eq]; assumption
      let Hconsspec := Hcons ((Φ1 \ {vp}) ∪ Φ2) (Ω1 ∪ (Ω2 \ {vp})) Hauxunionphi Hauxunionomega Hcontra'
      assumption
    · by_cases h' : @consistentPair ({vp} ∪ Γ) Δ
      · apply Or.inl; assumption
      · apply Or.inr
        simp at h
        rw [<-Set.insert_eq]
        rw [<-Set.insert_eq] at h'
        apply h h'

@[simp]
def add_next (ϕ : Formula) : Set Formula × Set Formula :=
  if @consistentPair ({ϕ} ∪ Γ) Δ then (({ϕ} ∪ Γ), Δ)
  else (Γ, {ϕ} ∪ Δ)

lemma add_consistent_next (Hcons : @consistentPair Γ Δ) (ϕ : Formula) :
  Γ ⊆ (@add_next Γ Δ ϕ).fst ∧ Δ ⊆ (@add_next Γ Δ ϕ).snd ∧
  @consistentPair (@add_next Γ Δ ϕ).fst (@add_next Γ Δ ϕ).snd :=
  by
    let Hconsor := add_preserves_cons Hcons ϕ
    by_cases Hconsadd : @consistentPair ({ϕ} ∪ Γ) Δ
    · apply And.intro
      · simp; simp_rw [Hconsadd]; simp
      · apply And.intro
        · simp; simp_rw [Hconsadd]; simp; apply Set.Subset.rfl
        · simp; simp_rw [Hconsadd]
    · cases Hconsor
      · contradiction
      · apply And.intro
        · simp; simp_rw [Hconsadd]; simp; apply Set.Subset.rfl
        · apply And.intro
          · simp; simp_rw [Hconsadd]; simp
          · simp; simp_rw [Hconsadd]; simp; assumption

@[simp]
def add_family (nf : Nat -> Formula) (n : Nat) :
  Set Formula × Set Formula :=
  match n with
  | .zero => @add_next Γ Δ (nf 0)
  | .succ n => let prev := add_family nf n
               @add_next prev.fst prev.snd (nf (n + 1))

lemma nf_in_ΓiΔi (nf : Nat -> Formula) (n : Nat) :
  nf n ∈ (@add_family Γ Δ nf n).fst \/ nf n ∈ (@add_family Γ Δ nf n).snd :=
  by
    induction n with
    | zero => simp
              by_cases Hcons : @consistentPair ({nf 0} ∪ Γ) Δ
              · apply Or.inl
                simp_rw [Hcons]; simp
              · apply Or.inr
                simp_rw [Hcons]; simp
    | succ n => simp
                by_cases Hcons : @consistentPair (insert (nf (n + 1)) (@add_family Γ Δ nf n).fst) (@add_family Γ Δ nf n).snd
                repeat simp_rw [Hcons]; simp

lemma vp_in_ΓiΔi (ϕ : Formula) (fn : Formula -> Nat) (fn_inj : fn.Injective) (nf : Nat -> Formula) (nf_inv : nf = fn.invFun) :
  ϕ ∈ (@add_family Γ Δ nf (fn ϕ)).fst \/ ϕ ∈ (@add_family Γ Δ nf (fn ϕ)).snd :=
  by
    have Hleftinv : ∀ (ϕ : Formula), nf (fn ϕ) = ϕ := by intros ϕ; simp [fn.leftInverse_invFun fn_inj ϕ, nf_inv]
    conv =>
      congr
      repeat {lhs; rw [<-Hleftinv ϕ]}
    exact nf_in_ΓiΔi nf (fn ϕ)

lemma add_consistent_family (Hcons : @consistentPair Γ Δ) (nf : Nat -> Formula) (n : Nat) :
  @consistentPair (@add_family Γ Δ nf n).fst (@add_family Γ Δ nf n).snd :=
  by
    induction n with
    | zero => simp
              let Hconsor := add_preserves_cons Hcons (nf 0)
              by_cases Hconsadd : @consistentPair ({nf 0} ∪ Γ) Δ
              · simp_rw [Hconsadd]
              · rcases Hconsor with Hgamma | Hdelta
                · contradiction
                · simp_rw [Hconsadd]; simp; assumption
    | succ n ih => let Haux := And.right (And.right (add_consistent_next ih (nf (n + 1))))
                   simp_rw [Haux]

lemma ΓΔ_in_family {nf : Nat -> Formula} {i : Nat} : Γ ⊆ (@add_family Γ Δ nf i).fst /\ Δ ⊆ (@add_family Γ Δ nf i).snd :=
  by
    apply And.intro
    · induction i with
      | zero => simp
                by_cases @consistentPair (insert (nf 0) Γ) Δ
                · simp_rw [h]; simp
                · simp_rw [h]; simp; apply Set.Subset.rfl
      | succ n ih => simp
                     by_cases @consistentPair (insert (nf (n + 1)) (@add_family Γ Δ nf n).fst) (@add_family Γ Δ nf n).snd
                     · simp_rw [h]; simp; apply Set.subset_union_of_subset_right ih
                     · simp_rw [h]; simp; assumption
    · induction i with
      | zero => simp
                by_cases @consistentPair (insert (nf 0) Γ) Δ
                · simp_rw [h]; simp; apply Set.Subset.rfl
                · simp_rw [h]; simp
      | succ n ih => simp
                     by_cases @consistentPair (insert (nf (n + 1)) (@add_family Γ Δ nf n).fst) (@add_family Γ Δ nf n).snd
                     · simp_rw [h]; simp; assumption
                     · simp_rw [h]; simp; apply Set.subset_union_of_subset_right ih

@[simp]
def consistent_family_union (_ : @consistentPair Γ Δ) (nf : Nat → Formula) : Set Formula × Set Formula :=
  ({ϕ | ∃ i : Nat, ϕ ∈ (@add_family Γ Δ nf i).fst}, {ϕ | ∃ i : Nat, ϕ ∈ (@add_family Γ Δ nf i).snd})

lemma ΓiΔi_in_union {Hcons : @consistentPair Γ Δ} {nf : Nat -> Formula} :
  (forall (i : Nat),
  (@add_family Γ Δ nf i).fst ⊆ (@consistent_family_union Γ Δ Hcons nf).fst) /\
  (forall (i : Nat),
  (@add_family Γ Δ nf i).snd ⊆ (@consistent_family_union Γ Δ Hcons nf).snd) :=
  by
    apply And.intro <;> {intro i ϕ h; exists i}

lemma ΓΔ_in_union {Hcons : @consistentPair Γ Δ} {nf : Nat -> Formula} :
  Γ ⊆ (@consistent_family_union Γ Δ Hcons nf).fst /\ Δ ⊆ (@consistent_family_union Γ Δ Hcons nf).snd :=
  by
    let ⟨Hgamma, Hdelta⟩ := @ΓΔ_in_family Γ Δ nf 0
    let ⟨Hgamma', Hdelta'⟩ := @ΓiΔi_in_union Γ Δ Hcons nf
    apply And.intro
    · let Hgamma' := Hgamma' 0
      apply Set.Subset.trans Hgamma Hgamma'
    · let Hdelta' := Hdelta' 0
      apply Set.Subset.trans Hdelta Hdelta'

lemma increasing_family {nf : Nat -> Formula} (i j : Nat) : i <= j ->
  (@add_family Γ Δ nf i).fst ⊆ (@add_family Γ Δ nf j).fst /\
  (@add_family Γ Δ nf i).snd ⊆ (@add_family Γ Δ nf j).snd :=
  by
    intros Hleq
    induction Hleq with
    | refl => apply And.intro <;> apply Set.Subset.rfl
    | @step m _ ih => by_cases @consistentPair (insert (nf (m + 1)) (@add_family Γ Δ nf m).fst) (@add_family Γ Δ nf m).snd
                      · apply And.intro
                        · simp; simp_rw [h]; simp; rw [Set.insert_eq]; apply Set.subset_union_of_subset_right (And.left ih)
                        · simp; simp_rw [h]; simp; exact And.right ih
                      · apply And.intro
                        · simp; simp_rw [h]; simp; exact And.left ih
                        · simp; simp_rw [h]; simp; rw [Set.insert_eq]; apply Set.subset_union_of_subset_right (And.right ih)

lemma mem_union_mem_local {Hcons :  @consistentPair Γ Δ} (nf : Nat -> Formula) :
  (∀ (ϕ : Formula),
  ϕ ∈ (@consistent_family_union Γ Δ Hcons nf).fst -> ∃ (i : Nat), ϕ ∈ (@add_family Γ Δ nf i).fst) /\
  (∀ (ϕ : Formula),
  ϕ ∈ (@consistent_family_union Γ Δ Hcons nf).snd -> ∃ (i : Nat), ϕ ∈ (@add_family Γ Δ nf i).snd) :=
  by
    apply And.intro <;> {intro ϕ ⟨i, Hmemi⟩; exists i}

lemma finset_subset_union_mem_local {Hcons : @consistentPair Γ Δ} (nf : Nat -> Formula) (fn : Formula -> Nat) (fn_inj : fn.Injective) (nf_inv : nf = fn.invFun) (Φ Ω : Finset Formula)
  (Hincl1 : Φ.toSet ⊆ (@consistent_family_union Γ Δ Hcons nf).fst)
  (Hincl2 : Ω.toSet ⊆ (@consistent_family_union Γ Δ Hcons nf).snd) :
  ∃ (i : Nat), ((∀ (ϕ : Formula), ϕ ∈ Φ.toSet -> ϕ ∈ (@add_family Γ Δ nf i).fst) /\
                 ∀ (ϕ : Formula), ϕ ∈ Ω.toSet -> ϕ ∈ (@add_family Γ Δ nf i).snd) :=
  by
    let maxfst := (max_index_mem_local fn Φ Ω).fst
    let maxsnd := (max_index_mem_local fn Φ Ω).snd
    exists max maxfst maxsnd
    apply And.intro
    · intros ϕ Hmem
      let Haux := @vp_in_ΓiΔi Γ Δ ϕ fn fn_inj nf nf_inv
      rcases Haux with Hfst | Hsnd
      · have Haux : fn ϕ ∈ List.map fn Φ.toList :=
          by
            apply f_elem_in_list_indices
            rw [Finset.mem_toList, <-Finset.mem_coe]
            assumption
        have Hleqmax : fn ϕ <= maximum (List.map fn Φ.toList) :=
          by apply leq_max; assumption
        have Hleq : fn ϕ <= max maxfst maxsnd :=
          by
            simp
            apply Or.inl
            have Haux : fn ϕ <= (max_index_mem_local fn Φ Ω).fst := by assumption
            assumption
        have Hincr := And.left (@increasing_family Γ Δ nf (fn ϕ) (max maxfst maxsnd) Hleq)
        apply Set.mem_of_mem_of_subset Hfst Hincr
      · exfalso
        let ⟨i, Hfst⟩ := Set.mem_of_mem_of_subset Hmem Hincl1
        by_cases Horder : i <= fn ϕ
        · let Hincr := And.left (@increasing_family Γ Δ nf i (fn ϕ) Horder)
          let Htrans := Set.mem_of_mem_of_subset Hfst Hincr
          let Hcons' := @add_consistent_family Γ Δ Hcons nf (fn ϕ)
          let Hdisj := consistent_disj Hcons'
          rw [Set.disjoint_right] at Hdisj
          let Hdisj := Hdisj Hsnd
          contradiction
        · simp only [not_le] at Horder
          let Hincr := And.right (@increasing_family Γ Δ nf (fn ϕ) i (Nat.le_of_lt Horder))
          let Htrans := Set.mem_of_mem_of_subset Hsnd Hincr
          let Hcons' := @add_consistent_family Γ Δ Hcons nf i
          let Hdisj := consistent_disj Hcons'
          rw [Set.disjoint_right] at Hdisj
          let Hdisj := Hdisj Htrans
          contradiction
    · intros ϕ Hmem
      let Haux := @vp_in_ΓiΔi Γ Δ ϕ fn fn_inj nf nf_inv
      rcases Haux with Hfst | Hsnd
      · exfalso
        let ⟨i, Hsnd⟩ := Set.mem_of_mem_of_subset Hmem Hincl2
        by_cases Horder : i <= fn ϕ
        · let Hincr := And.right (@increasing_family Γ Δ nf i (fn ϕ) Horder)
          let Htrans := Set.mem_of_mem_of_subset Hsnd Hincr
          let Hcons' := @add_consistent_family Γ Δ Hcons nf (fn ϕ)
          let Hdisj := consistent_disj Hcons'
          rw [Set.disjoint_right] at Hdisj
          let Hdisj := Hdisj Htrans
          contradiction
        · simp only [not_le] at Horder
          let Hincr := And.left (@increasing_family Γ Δ nf (fn ϕ) i (Nat.le_of_lt Horder))
          let Htrans := Set.mem_of_mem_of_subset Hfst Hincr
          let Hcons' := @add_consistent_family Γ Δ Hcons nf i
          let Hdisj := consistent_disj Hcons'
          rw [Set.disjoint_right] at Hdisj
          let Hdisj := Hdisj Hsnd
          contradiction
      · have Haux : fn ϕ ∈ List.map fn Ω.toList :=
          by
            apply f_elem_in_list_indices
            rw [Finset.mem_toList, <-Finset.mem_coe]
            assumption
        have Hleqmax : fn ϕ <= maximum (List.map fn Ω.toList) :=
          by apply leq_max; assumption
        have Hleq : fn ϕ <= max maxfst maxsnd :=
          by
            simp
            apply Or.inr
            have Haux : fn ϕ <= (max_index_mem_local fn Φ Ω).snd := by assumption
            assumption
        have Hincr := And.right (@increasing_family Γ Δ nf (fn ϕ) (max maxfst maxsnd) Hleq)
        apply Set.mem_of_mem_of_subset Hsnd Hincr

lemma union_consistent {Hcons :  @consistentPair Γ Δ} (fn : Formula -> Nat) (fn_inj : fn.Injective) (nf : Nat -> Formula) (nf_inv : nf = fn.invFun) :
  @consistentPair (@consistent_family_union Γ Δ Hcons nf).fst (@consistent_family_union Γ Δ Hcons nf).snd :=
  by
    by_cases @consistentPair (@consistent_family_union Γ Δ Hcons nf).fst (@consistent_family_union Γ Δ Hcons nf).snd
    · assumption
    · exfalso
      unfold consistentPair at h
      push_neg at h
      rcases h with ⟨Φ, ⟨Ω, ⟨Hincl1, ⟨Hincl2, ⟨Hncons, _⟩⟩⟩⟩⟩
      let ⟨i, ⟨Hphi, Homega⟩⟩ := @finset_subset_union_mem_local Γ Δ Hcons nf fn fn_inj nf_inv Φ Ω Hincl1 Hincl2
      have Hinclphi : Φ.toSet ⊆ (@add_family Γ Δ nf i).fst :=
        by
          rw [Set.subset_def]
          simp_rw [Finset.mem_coe]
          assumption
      have Hinclomega : Ω.toSet ⊆ (@add_family Γ Δ nf i).snd :=
        by
          rw [Set.subset_def]
          simp_rw [Finset.mem_coe]
          assumption
      let Hconsi := @add_consistent_family Γ Δ Hcons nf i
      unfold consistentPair at Hconsi
      let Hcontra := Hconsi Φ Ω Hinclphi Hinclomega Hncons
      assumption

lemma consistent_incl_complete :
  @consistentPair Γ Δ -> (∃ (Γ' Δ' : Set Formula), Γ ⊆ Γ' ∧ Δ ⊆ Δ' ∧ @completePair Γ' Δ') :=
  by
    intros Hcons
    let ⟨f, f_inj⟩ := exists_injective_nat Formula
    let nf := f.invFun
    have nf_inv : nf = Function.invFun f := by simp
    exists (@consistent_family_union Γ Δ Hcons nf).fst, (@consistent_family_union Γ Δ Hcons nf).snd
    apply And.intro
    · apply And.left ΓΔ_in_union
    · apply And.intro
      · apply And.right ΓΔ_in_union
      · unfold completePair
        apply And.intro
        · apply @union_consistent Γ Δ Hcons f f_inj nf
          simp
        · intros ϕ
          simp
          by_cases (∃ i, ϕ ∈ (add_family (Function.invFun f) i).fst) ∨ (∃ i, ϕ ∈ (add_family (Function.invFun f) i).snd)
          · rcases h with Hgamma | Hdelta
            · apply Or.inl
              apply And.intro
              · assumption
              · intros x Hsnd
                rcases Hgamma with ⟨i, Hfst⟩
                by_cases Horder : i <= x
                · let Hincr := And.left (@increasing_family Γ Δ (Function.invFun f) i x Horder)
                  let Htrans := Set.mem_of_mem_of_subset Hfst Hincr
                  let Hcons' := add_consistent_family Hcons nf x
                  let Hdisj := consistent_disj Hcons'
                  rw [Set.disjoint_right] at Hdisj
                  let Hdisj := Hdisj Hsnd
                  contradiction
                · simp only [not_le] at Horder
                  let Hincr := And.right (@increasing_family Γ Δ (Function.invFun f) x i (Nat.le_of_lt Horder))
                  let Htrans := Set.mem_of_mem_of_subset Hsnd Hincr
                  let Hcons' := @add_consistent_family Γ Δ Hcons nf i
                  let Hdisj := consistent_disj Hcons'
                  rw [Set.disjoint_left] at Hdisj
                  let Hdisj := Hdisj Hfst
                  contradiction
            · apply Or.inr
              apply And.intro
              · assumption
              · intros x Hfst
                rcases Hdelta with ⟨i, Hsnd⟩
                by_cases Horder : i <= x
                · let Hincr := And.right (@increasing_family Γ Δ (Function.invFun f) i x Horder)
                  let Htrans := Set.mem_of_mem_of_subset Hsnd Hincr
                  let Hcons' := add_consistent_family Hcons nf x
                  let Hdisj := consistent_disj Hcons'
                  rw [Set.disjoint_left] at Hdisj
                  let Hdisj := Hdisj Hfst
                  contradiction
                · simp only [not_le] at Horder
                  let Hincr := And.left (@increasing_family Γ Δ (Function.invFun f) x i (Nat.le_of_lt Horder))
                  let Htrans := Set.mem_of_mem_of_subset Hfst Hincr
                  let Hcons' := @add_consistent_family Γ Δ Hcons nf i
                  let Hdisj := consistent_disj Hcons'
                  rw [Set.disjoint_right] at Hdisj
                  let Hdisj := Hdisj Hsnd
                  contradiction
          · push_neg at h
            rcases h with ⟨Hgamma, Hdelta⟩
            let Hor := @vp_in_ΓiΔi Γ Δ ϕ f f_inj nf nf_inv
            rcases Hor with Hgamma' | Hdelta'
            · let Hgamma := Hgamma (f ϕ)
              contradiction
            · let Hdelta := Hdelta (f ϕ)
              contradiction

lemma main_sem_lemma_right (Γ : setDisjTh) (ϕ : Formula) :
  ϕ ∈ Γ.1 -> val canonicalModel Γ ϕ :=
  by
    intros Helem
    let Hgamma := Γ
    rcases Γ with ⟨Γ, ⟨Hded, ⟨Hcons, Hdisjnonempty⟩⟩⟩
    apply Nonempty.elim Hdisjnonempty
    intros Hdisj
    revert Γ
    induction ϕ with
    | var _ => intros; assumption
    | bottom => intros Γ _ Hcons _ Helem _ _; have Hpremise : Γ ⊢ ⊥ := by apply Proof.premise Helem
                apply Hcons; assumption
    | and ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Helem _ Hdisj
                         have Hconj : Γ ⊢ ψ ∧∧ χ := by apply Proof.premise Helem
                         let Hpsi := Proof.modusPonens Hconj Proof.weakeningConj
                         let Hchi := Proof.modusPonens Hconj Proof.conjElimRight
                         have Hpsielem : ψ ∈ Γ := by apply Hded ψ; assumption
                         have Hchielem : χ ∈ Γ := by apply Hded χ; assumption
                         apply And.intro (ih1 Γ Hded Hcons Hproofdisj Hpsielem Hdisj)
                                         (ih2 Γ Hded Hcons Hproofdisj Hchielem Hdisj)
    | or ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Helem HsetDisj Hdisj'
                        unfold disjunctive at Hdisj'
                        have Hdisjspec : Γ ⊢ ψ ∨∨ χ := by apply Proof.premise Helem
                        have Hdisj : Sum (Γ ⊢ ψ) (Γ ⊢ χ) := by apply Hdisj' ψ χ Hdisjspec
                        rcases Hdisj with Hpsi | Hchi
                        · have Hpsi : ψ ∈ Γ := by apply Hded ψ; assumption
                          have Hih1 : Γ ⊨ ψ := by apply elem_sem_conseq; assumption
                          apply Or.inl
                          apply ih1; assumption'
                        · have Hpsi : χ ∈ Γ := by apply Hded χ; assumption
                          have Hih2 : Γ ⊨ χ := by apply elem_sem_conseq; assumption
                          apply Or.inr
                          apply ih2; assumption'
    | implication ψ χ ih1 ih2 => intros Γ Hded Hcons Hproofdisj Helem _ Hdisj
                                 simp [val]
                                 intros Φ Φdisj Hincl Hpsi
                                 have Helem' : (ψ ⇒ χ) ∈ Φ :=
                                  by eapply Set.mem_of_mem_of_subset Helem Hincl
                                 rcases Φdisj with ⟨Hded', ⟨Hcons', Hdisj'⟩⟩
                                 have Hpremise1 : Φ ⊢ ψ ⇒ χ := by apply Proof.premise Helem'
                                 · by_cases ψ ∈ Φ
                                   · have Hpremise2 : Φ ⊢ ψ := by apply Proof.premise h
                                     have Hchi : Φ ⊢ χ := by apply Proof.modusPonens Hpremise2 Hpremise1
                                     have Hchielem : χ ∈ Φ := by apply Hded' χ; assumption
                                     let Hih2 := ih2 Φ Hded' Hcons' Hdisj' Hchielem
                                     apply Nonempty.elim Hdisj'; assumption
                                   · sorry

lemma main_sem_lemma_left (Γ : setDisjTh) (ϕ : Formula) :
  val canonicalModel Γ ϕ -> ϕ ∈ Γ.1 :=
  by
    intros Hval
    rcases Γ with ⟨Γ, ⟨Hded, ⟨Hcons, Hdisjnonempty⟩⟩⟩
    apply Nonempty.elim Hdisjnonempty
    intros Hdisj
    revert Γ
    induction ϕ with
    | var _ => intros; assumption
    | bottom => simp [val]
    | and ψ χ ih1 ih2 => intros Γ Hded Hcons Hnempty_disj Hval Hdisj
                         rcases Hval with ⟨Hvalpsi, Hvalchi⟩
                         let Hpsi := Proof.premise (ih1 Γ Hded Hcons Hnempty_disj Hvalpsi Hdisj)
                         let Hchi := Proof.premise (ih2 Γ Hded Hcons Hnempty_disj Hvalchi Hdisj)
                         let H := Proof.conjIntroRule Hpsi Hchi
                         apply Hded
                         assumption
    | or ψ χ ih1 ih2 => intros Γ Hded Hcons Hnempty_disj Hval Hdisj
                        rcases Hval with Hvalpsi | Hvalchi
                        · let Hpsi := Proof.premise (ih1 Γ Hded Hcons Hnempty_disj Hvalpsi Hdisj)
                          let Hmp := @Proof.modusPonens Γ ψ (ψ ∨∨ χ) Hpsi Proof.weakeningDisj
                          apply Hded; assumption
                        · let Hchi := Proof.premise (ih2 Γ Hded Hcons Hnempty_disj Hvalchi Hdisj)
                          let Hmp := @Proof.modusPonens Γ χ (ψ ∨∨ χ) Hchi Proof.disjIntroRight
                          apply Hded; assumption
    | implication ψ χ ih1 ih2 => intros Γ Hded Hcons Hnempty_disj Hval _
                                 simp [val] at Hval
                                 by_cases (ψ ⇒ χ) ∈ Γ
                                 · assumption
                                 · have Hcons' : @consistentPair (Γ ∪ {ψ}) {χ} :=
                                    by
                                      by_cases consistentPair
                                      · assumption
                                      · exfalso
                                        unfold consistentPair at h
                                        push_neg at h
                                        rcases h with ⟨Φ, Ω, h, h', h''⟩
                                        rcases h'' with ⟨w, _⟩
                                        rw [Set.subset_singleton_iff_eq] at h'
                                        rcases h' with Hempty | Hsingleton
                                        · rw [Finset.coe_eq_empty] at Hempty
                                          rw [Hempty] at w
                                          simp at w
                                          let Hexpthded := Proof.deductionTheorem_right_ind (Proof.exportation_ind w)
                                          rw [Set.empty_union] at Hexpthded
                                          unfold consistent at Hcons
                                          apply Hcons
                                          rw [Finset.toList_toFinset] at Hexpthded
                                          have Hunionconseq : Γ ∪ {ψ} ⊢ ⊥ :=
                                            by apply Proof.subset_proof; assumption'
                                          let Hthded := Proof.deductionTheorem_left Hunionconseq
                                          let Hsyllog := @Proof.syllogism Γ ψ ⊥ χ Hthded Proof.exfalso
                                          let Hdisjspec := Hded (ψ⇒χ) Hsyllog
                                          contradiction
                                        · rw [Finset.coe_eq_singleton] at Hsingleton
                                          rw [Hsingleton] at w
                                          simp at w
                                          let Hsyllog := Proof.syllogism w Proof.orFalse
                                          let Hexp := Proof.exportation_ind Hsyllog
                                          let Hthded := Proof.deductionTheorem_right_ind Hexp
                                          rw [Set.empty_union] at Hthded
                                          rw [Finset.toList_toFinset] at Hthded
                                          have Hunionconseq : Γ ∪ {ψ} ⊢ χ :=
                                            by apply Proof.subset_proof; assumption'
                                          let Hthded := Proof.deductionTheorem_left Hunionconseq
                                          let Hdisjspec := Hded (ψ⇒χ) Hthded
                                          contradiction
                                   let Haux := @consistent_incl_complete (Γ ∪ {ψ}) {χ} Hcons'
                                   rcases Haux with ⟨Φ, ⟨Ω, ⟨Hincl1, ⟨Hincl2, Hcompl⟩⟩⟩⟩
                                   have Hdisjth' : @disjunctiveTheory Φ :=
                                    by apply complete_pair_fst_disj Hcompl
                                   let Hdisjth'' := Hdisjth'
                                   rcases Hdisjth' with ⟨Hcons'', ⟨Hded', Hdisj'⟩⟩
                                   have Hincl : Γ ⊆ Φ :=
                                    by
                                      have Hunionleft : Γ ⊆ Γ ∪ {ψ} := by apply Set.subset_union_left
                                      apply Set.Subset.trans Hunionleft Hincl1
                                   let Hvalspec := Hval Φ Hdisjth'' Hincl
                                   have Hdisjthphi : @disjunctiveTheory Φ :=
                                      by apply complete_pair_fst_disj; assumption
                                   let Hdisjthphi' : setDisjTh := ⟨Φ, by assumption⟩
                                   have Hphipsi : val canonicalModel { val := Φ, property := Hdisjth'' } ψ :=
                                    by
                                      by_cases val canonicalModel { val := Φ, property := Hdisjth'' } ψ
                                      · assumption
                                      · let Hih1 := @ih1 Φ Hcons'' Hded' Hdisj'
                                        simp at Hih1
                                        have Haux : ψ ∈ Φ :=
                                          by
                                            rw [Set.union_subset_iff] at Hincl1
                                            let Hsingleton := And.right Hincl1
                                            rw [Set.singleton_subset_iff] at Hsingleton
                                            assumption
                                        let Hmainsem := main_sem_lemma_right Hdisjthphi' ψ Haux
                                        assumption
                                   have Hphinotchi : val canonicalModel { val := Φ, property := Hdisjth'' } χ -> False :=
                                    by
                                      have Hdisj'' : @disjunctive Φ :=
                                        by apply Classical.choice Hdisj'
                                      by_cases val canonicalModel { val := Φ, property := Hdisjth'' } χ
                                      · let Hih2 := @ih2 Φ Hcons'' Hded' Hdisj' h Hdisj''
                                        simp at Hih2
                                        unfold completePair at Hcompl
                                        rcases Hcompl with ⟨_, Hvp⟩
                                        let Hvpchi := Hvp χ
                                        have Hchielem : χ ∈ Ω :=
                                          by rw [Set.singleton_subset_iff] at Hincl2; assumption
                                        rcases Hvpchi with Hphi | Homega
                                        · rcases Hphi; contradiction
                                        · rcases Homega; contradiction
                                      · assumption
                                   let Hvalspecaux := Hvalspec Hphipsi
                                   contradiction

theorem completeness {ϕ : Formula} {Γ : Set Formula} : Γ ⊨ ϕ -> Nonempty (Γ ⊢ ϕ) :=
  by
    intros Hsem
    by_cases (Nonempty (Γ ⊢ ϕ))
    · assumption'
    · have Hcons : @consistentPair Γ {ϕ} :=
        by
          simp [consistentPair]
          intros Φ Ω Hincl1 Homega H
          have Homega : Ω = ∅ ∨ Ω = {ϕ} :=
            by
              by_cases Ω = ∅
              · apply Or.inl; assumption
              · apply Or.inr
                rw [Finset.eq_singleton_iff_nonempty_unique_mem]
                apply And.intro
                · apply Finset.nonempty_of_ne_empty; assumption
                · assumption
          rcases Homega with Hempty | Hsingl
          · rw [Hempty] at H
            simp at H
            let Hexpthded := Proof.deductionTheorem_right_ind (Proof.exportation_ind H)
            rw [Set.empty_union] at Hexpthded
            rw [Finset.toList_toFinset] at Hexpthded
            let Hsubsetproof := Proof.subset_proof Hincl1 Hexpthded
            let Hgammavp := @Proof.modusPonens Γ ⊥ ϕ Hsubsetproof Proof.exfalso
            apply h
            apply Nonempty.intro Hgammavp
          · rw [Hsingl] at H
            simp at H
            let Hexfalso := @Proof.exfalso ∅ ϕ
            let Hexpns := @Proof.expansion ∅ ⊥ ϕ ϕ Hexfalso
            have Hself : ∅ ⊢ ϕ ∨∨ ϕ ⇒ ϕ :=
              by
                let Heqv := @Proof.disjEquiv ∅ ϕ
                simp [Formula.equivalence] at Heqv
                let Hweak := @Proof.conjElimRight ∅ (ϕ⇒ϕ∨∨ϕ) (ϕ∨∨ϕ⇒ϕ)
                apply Proof.modusPonens Heqv Hweak
            let Hweak : ∅ ⊢ ϕ ∨∨ ⊥ ⇒ ϕ := by apply Proof.syllogism Hexpns Hself
            let Hsyllog : ∅ ⊢ List.foldr Formula.and (~⊥) (Finset.toList Φ) ⇒ ϕ :=
              by apply Proof.syllogism H Hweak
            let Himpl : ∅ ⊢ List.foldr Formula.implication ϕ (Finset.toList Φ) :=
              by apply Proof.exportation_ind Hsyllog
            let Hded : Φ ⊢ ϕ :=
              by
                let Hded := Proof.deductionTheorem_right_ind Himpl
                rw [Set.empty_union] at Hded
                rw [Finset.toList_toFinset] at Hded
                assumption
            have Hsubsetconseq : Γ ⊢ ϕ := by apply Proof.subset_proof Hincl1 Hded
            apply h
            apply Nonempty.intro Hsubsetconseq
      let Hcompl := @consistent_incl_complete Γ {ϕ} Hcons
      rcases Hcompl with ⟨Φ, ⟨Ω, ⟨Hincl1, ⟨Hincl2, Hcompl⟩⟩⟩⟩
      let Hcomplete := Hcompl
      simp [completePair] at Hcompl
      rcases Hcompl with ⟨_, Hvp⟩
      let Hvp := Hvp ϕ
      have Hchielem : ϕ ∈ Ω :=
        by rw [Set.singleton_subset_iff] at Hincl2; assumption
      have Hnotelem : ϕ ∉ Φ :=
        by
          rcases Hvp with Hphi | Homega
          · exfalso; apply And.right Hphi; assumption
          · apply And.right Homega
      have : ¬ϕ ∈ Γ := by apply Set.not_mem_subset Hincl1 Hnotelem
      have Hdisjthphi : @disjunctiveTheory Φ :=
        by apply complete_pair_fst_disj; assumption
      let Hdisjthphi' : setDisjTh := ⟨Φ, by assumption⟩
      let Hnotconseq : ¬val canonicalModel Hdisjthphi' ϕ :=
        by
          by_cases (val canonicalModel Hdisjthphi' ϕ)
          · exfalso
            let Hin := @main_sem_lemma_left Hdisjthphi' ϕ h
            rcases Hvp with Hphi | Homega
            · rcases Hphi; contradiction
            · rcases Homega
              have : ϕ ∈ Φ := Hin
              contradiction
          · assumption
      have Hmodelset : model_sat_set canonicalModel Γ Hdisjthphi' :=
        by
          simp [sem_conseq] at Hsem
          simp [model_sat_set]
          intros vp Hvpin
          have Hvpinphi : vp ∈ Φ := by apply Set.mem_of_subset_of_mem Hincl1 Hvpin
          apply elem_sem_conseq Φ
          · assumption
          · unfold model_sat_set
            intros vp Hvpin
            let Hphi : vp ∈ Φ := by assumption
            let Hmainsem := main_sem_lemma_right Hdisjthphi' vp Hphi
            assumption
      simp [sem_conseq] at Hsem
      exfalso
      let Haux := Hsem (@setDisjTh) canonicalModel Hdisjthphi' Hmodelset
      contradiction

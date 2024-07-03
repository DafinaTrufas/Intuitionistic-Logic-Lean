import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Zorn

variable {α : Type u} [HeytingAlgebra α]

def filter (F : Set α) := (Set.Nonempty F) ∧ (∀ (x y : α), x ∈ F → y ∈ F → x ⊓ y ∈ F) ∧
                          (∀ (x y : α), x ∈ F → x ≤ y → y ∈ F)

lemma top_mem_filter (F : Set α) (Hfilter : filter F) : ⊤ ∈ F :=
  by
    let Hnempty := Hfilter.1
    have Haux : ∃ (x : α), x ∈ F := by assumption
    rcases Haux with ⟨x, Hxin⟩
    exact Hfilter.2.2 x ⊤ Hxin le_top

def deductive_system (F : Set α) := ⊤ ∈ F ∧ (∀ (x y : α), x ∈ F → x ⇨ y ∈ F → y ∈ F)

lemma filter_dedsyst_equiv {x y : α} (F : Set α) : filter F ↔ deductive_system F :=
  by
    apply Iff.intro
    · intro Hf
      rcases Hf with ⟨Hnempty, ⟨Hf1, Hf2⟩⟩
      let Haux := Hf1 x (x ⇨ y)
      rw [inf_himp] at Haux
      apply And.intro
      · unfold Set.Nonempty at Hnempty
        rcases Hnempty with ⟨x, Hxin⟩
        exact (Hf2 x ⊤) Hxin le_top
      · intros x y Hxin Himpin
        let Haux' := (Hf1 x (x ⇨ y)) Hxin Himpin
        rw [inf_himp] at Haux'
        exact Hf2 (x ⊓ y) y Haux' inf_le_right
    · intro Hd
      unfold filter
      rcases Hd with ⟨Ht, Hxy⟩
      apply And.intro
      · exists ⊤
      · have Haux : ∀ (x y : α), x ∈ F → x ≤ y → y ∈ F :=
          by
            intros x y Hxin Hle
            rw [<-himp_eq_top_iff] at Hle
            rw [<-Hle] at Ht
            exact Hxy x y Hxin Ht
        apply And.intro
        · intros x y Hxin Hyin
          have Haux : x ⇨ y ∈ F :=
            by
              have Haux' : y ≤ x ⇨ y :=
                by
                  rw [le_himp_iff]
                  exact inf_le_left
              exact Haux y (x ⇨ y) Hyin Haux'
          have Haux' : x ⇨ y = x ⇨ x ⊓ y := by rw [himp_inf_distrib]; simp
          rw [Haux'] at Haux
          exact Hxy x (x ⊓ y) Hxin Haux
        · exact Haux

abbrev X_filters (X : Set α) := {F // filter F ∧ X ⊆ F}

def X_gen_filter (X : Set α) := {x | ∀ (F : X_filters X), x ∈ F.1}

lemma X_subset_X_gen_filter (X : Set α) : X ⊆ X_gen_filter X :=
  by
    rw [Set.subset_def]
    intro x Hxin
    unfold X_gen_filter
    simp
    intro F' _ Hsubset
    apply Set.mem_of_subset_of_mem
    assumption'

lemma X_gen_filter_filter (X : Set α) (Hnempty : Set.Nonempty X) : filter (X_gen_filter X) :=
  by
    apply And.intro
    · rcases Hnempty with ⟨x, Hinx⟩
      exists x
      unfold X_gen_filter
      simp
      intro F' _ Hsubset
      apply Set.mem_of_mem_of_subset Hinx Hsubset
    · apply And.intro
      · intro x y Hxin Hyin
        unfold X_gen_filter at Hxin
        unfold X_gen_filter at Hyin
        unfold X_gen_filter
        simp at Hxin
        simp at Hyin
        simp
        intro F Hfilter Hsubset
        exact (Hfilter.right).left x y (Hxin F Hfilter Hsubset) (Hyin F Hfilter Hsubset)
      · intro x y Hxin Hle
        unfold X_gen_filter at Hxin
        unfold X_gen_filter
        simp at Hxin
        simp
        intro F Hfilter Hsubset
        exact (Hfilter.right.right) x y (Hxin F Hfilter Hsubset) Hle

@[simp]
def inf_list (l : List α) :=
  match l with
  | [] => ⊤
  | h :: t => h ⊓ inf_list t

lemma inf_list_concat (l1 l2 : List α) :
  inf_list (l1 ++ l2) = inf_list l1 ⊓ inf_list l2 :=
  by
    induction l1 with
    | nil => simp
    | cons h t ih => simp; rw[ih]; rw [inf_assoc]

noncomputable instance {ϕ ψ : α} : Decidable (ϕ = ψ) := @default _ (Classical.decidableInhabited _)

lemma inf_list_mem {F : Set α} {Hfilter : filter F} {l : List α} (Hsubset : l.toFinset.toSet ⊆ F) :
  inf_list l ∈ F :=
  by
    induction l with
    | nil => simp
             exact @top_mem_filter α _ F Hfilter
    | cons h t ih => simp
                     rcases Hfilter with ⟨_, ⟨Hand, _⟩⟩
                     simp at Hsubset
                     rw [Set.insert_subset_iff] at Hsubset
                     apply Hand
                     · exact Hsubset.left
                     · simp at ih
                       exact ih Hsubset.right

lemma inf_list_eq {l : List α} (Heq : ∀ (z : α), z ∈ l → z = x) :
  l = [] ∨ inf_list l = x :=
  by
    induction l with
    | nil => simp
    | cons h t ih => apply Or.inr
                     simp
                     simp at Heq
                     rcases ih Heq.right with Ht | Hx
                     · rw [Ht]; simp; exact Heq.left
                     · rw [Heq.left, Hx]; simp

lemma inf_list_perm_eq {l1 l2 : List α} (Hperm : l1 ~ l2) :
  inf_list l1 = inf_list l2 :=
  by
    induction Hperm with
    | nil => simp
    | @cons x l1' l2' ihperm ihequiv => simp; rw [ihequiv]
    | swap x y l => simp; rw [<-inf_left_comm]
    | @trans l1' l2' l3' _ _ ihequiv12 ihequiv23 => exact Eq.trans ihequiv12 ihequiv23

lemma gen_filter_prop (X : Set α) :
  X_gen_filter X = {a | ∃ (l : List α), l.toFinset.toSet ⊆ X ∧ inf_list l ≤ a} :=
  by
    let S := {a | ∃ (l : List α), l.toFinset.toSet ⊆ X ∧ inf_list l ≤ a}
    have HSfilter : filter S :=
      by
        apply And.intro
        · exists ⊤; exists []; simp
        · apply And.intro
          · intros x y Hxin Hyin
            rcases Hxin with ⟨l1, ⟨Hsubset1, Hinf1⟩⟩
            rcases Hyin with ⟨l2, ⟨Hsubset2, Hinf2⟩⟩
            exists l1 ++ l2
            simp
            apply And.intro
            · simp at Hsubset1; simp at Hsubset2
              exact And.intro Hsubset1 Hsubset2
            · rw [inf_list_concat]
              exact And.intro (le_trans inf_le_left Hinf1) (le_trans inf_le_right Hinf2)
          · intros x y Hxin Hle
            rcases Hxin with ⟨l, ⟨Hsubset, Hinf⟩⟩
            exists l
            exact And.intro Hsubset (le_trans Hinf Hle)
    have HXin : X ⊆ S :=
      by
        rw [Set.subset_def]
        intro x HxinX
        exists [x]
        simp; assumption
    have Hmin : ∀ (F : Set α), filter F → X ⊆ F → S ⊆ F :=
      by
        intro F Hfilter Hsubset
        rw [Set.subset_def]
        intro x HxinS
        rcases HxinS with ⟨l, ⟨Hsubset', Hinf⟩⟩
        let Htrans := Set.Subset.trans Hsubset' Hsubset
        have Hinf_list_mem : inf_list l ∈ F := by apply inf_list_mem; assumption'
        exact (Hfilter.right).right (inf_list l) x Hinf_list_mem Hinf
    unfold X_gen_filter
    rw [Set.ext_iff]
    intro x
    apply Iff.intro
    · intro Hin_inter
      simp at Hin_inter
      exact (Hin_inter S) HSfilter HXin
    · intro HinS
      simp
      intro F Hfilter Hsubset
      exact Set.mem_of_subset_of_mem (Hmin F Hfilter Hsubset) HinS

lemma mem_gen_ins_filter (F : Set α) (Hfilter : filter F) :
  y ∈ X_gen_filter (F ∪ {x}) → ∃ (z : α), z ∈ F /\ x ⊓ z ≤ y :=
  by
    intro Hin
    rw [gen_filter_prop] at Hin
    simp at Hin
    rcases Hin with ⟨l, ⟨Hsubset, Hinf_le⟩⟩
    rw [<-List.coe_toFinset] at Hsubset
    let lneqx := l.filter (fun (z : α) => z ≠ x)
    let leqx := l.filter (fun (z : α) => z = x)
    have Hinf_split : inf_list l = inf_list leqx ⊓ inf_list lneqx :=
      by
        have Hperm : l ~ leqx ++ lneqx :=
          by
            rw [List.perm_comm]
            simp
            let Haux := List.filter_append_perm (fun z => z = x) l
            simp at Haux
            assumption
        let Haux := inf_list_perm_eq Hperm
        rw [inf_list_concat] at Haux
        assumption
    rw [Hinf_split] at Hinf_le
    have Haux : ∀ (z : α), z ∈ leqx → z = x :=
      by
        intro z Hzin
        rw [List.mem_filter] at Hzin
        simp at Hzin
        exact Hzin.right
    have Hinfeq : leqx = [] ∨ inf_list leqx = x := by apply inf_list_eq Haux
    have Hinfneqin : inf_list lneqx ∈ F :=
      by
        have Hsubset'' : lneqx ⊆ l := by simp
        have Hsubset''' : lneqx.toFinset.toSet ⊆ l.toFinset.toSet :=
          by
            rw [Set.subset_def]
            apply List.Subset.trans
            · apply List.dedup_subset
            · apply List.Subset.trans
              · exact Hsubset''
              · apply List.subset_dedup
        have Hsubset''' : lneqx.toFinset.toSet ⊆ insert x F :=
          by exact Set.Subset.trans Hsubset''' Hsubset
        rw [Set.subset_insert_iff_of_not_mem] at Hsubset'''
        apply inf_list_mem Hsubset'''
        assumption'
        simp
        intro h
        rw [List.mem_filter] at h
        simp at h
    exists inf_list lneqx
    apply And.intro
    · assumption
    · rcases Hinfeq with Hnil | Hx
      · rw [Hnil] at Hinf_le
        have Haux' : inf_list [] ⊓ inf_list lneqx = inf_list lneqx := by simp
        rw [Haux'] at Hinf_le
        apply le_trans
        · exact inf_le_right
        · assumption
      · rw [Hx] at Hinf_le
        assumption

lemma himp_not_mem (F : Set α) (Hfilter : filter F) (Himp_not_mem : x ⇨ y ∉ F) :
  y ∉ X_gen_filter (F ∪ {x}) :=
  by
    intro Hcontra
    have Haux : ∃ (z : α), z ∈ F /\ x ⊓ z ≤ y :=
      by apply mem_gen_ins_filter F Hfilter Hcontra
    rcases Haux with ⟨z, ⟨Hzin, Hglb⟩⟩
    rw [inf_comm, <-le_himp_iff] at Hglb
    exact Himp_not_mem ((Hfilter.right).right z (x ⇨ y) Hzin Hglb)

def proper_filter (F : Set α) := filter F ∧ ⊥ ∉ F

lemma himp_not_mem_proper (F : Set α) (Hfilter : filter F) (Himp_not_mem : xᶜ ∉ F) :
  proper_filter (X_gen_filter (F ∪ {x})) :=
  by
    apply And.intro
    · simp
      exact X_gen_filter_filter (insert x F) (Set.insert_nonempty x F)
    · apply himp_not_mem
      · assumption
      · simp; assumption

def prime_filter (F : Set α) :=
  proper_filter F ∧ (∀ (x y : α), x ⊔ y ∈ F → x ∈ F ∨ y ∈ F)

def prime_filters := {F | @prime_filter α _ F}

def X_filters_not_cont_x (x : α) := {F | filter F ∧ x ∉ F}

lemma super_prime_filter (x : α) (F : Set α) (Hfilter : @filter α _ F) (Hnotin : x ∉ F) :
  ∃ (P : Set α), @prime_filter α _ P /\ F ⊆ P /\ x ∉ P :=
  by
    have Hzorn : ∃ F' ∈ X_filters_not_cont_x x, F ⊆ F' ∧
                 ∀ (F'' : Set α), F'' ∈ X_filters_not_cont_x x → F' ⊆ F'' → F'' = F' :=
      by
        apply zorn_subset_nonempty
        · intro c Hsubset Hchain Hnempty
          exists Set.sUnion c
          apply And.intro
          · unfold X_filters_not_cont_x
            simp
            apply And.intro
            · apply And.intro
              · simp
                rcases Hnempty with ⟨S, Hinc⟩
                exists S
                apply And.intro
                · assumption
                · have Htrans : S ∈ X_filters_not_cont_x x :=
                    by apply Set.mem_of_mem_of_subset Hinc Hsubset
                  exact (Htrans.left).left
              · apply And.intro
                · intro y z Hyin Hzin
                  rcases Hyin with ⟨F1, ⟨HF1in_c, Hyin_f1⟩⟩
                  rcases Hzin with ⟨F2, ⟨HF2in_c, Hzin_f2⟩⟩
                  have Htrans1 : F1 ∈ X_filters_not_cont_x x := by apply Set.mem_of_mem_of_subset HF1in_c Hsubset
                  have Htrans2 : F2 ∈ X_filters_not_cont_x x := by apply Set.mem_of_mem_of_subset HF2in_c Hsubset
                  by_cases Hfeq : F1 = F2
                  · rw [<-Hfeq] at Hzin_f2
                    exists F1
                    exact And.intro HF1in_c (((Htrans1.left).right).left y z Hyin_f1 Hzin_f2)
                  · rcases Hchain HF1in_c HF2in_c Hfeq with H12 | H21
                    · have Htrans : y ∈ F2 := by apply Set.mem_of_mem_of_subset Hyin_f1 H12
                      exists F2
                      exact And.intro HF2in_c (((Htrans2.left).right).left y z Htrans Hzin_f2)
                    · have Htrans : z ∈ F1 := by apply Set.mem_of_mem_of_subset Hzin_f2 H21
                      exists F1
                      exact And.intro HF1in_c (((Htrans1.left).right).left y z Hyin_f1 Htrans)
                · intro y z Hyin Hle
                  rcases Hyin with ⟨F', ⟨Hfin_c, Hyin⟩⟩
                  exists F'
                  have Htrans : F' ∈ X_filters_not_cont_x x :=
                    by apply Set.mem_of_mem_of_subset Hfin_c Hsubset
                  exact And.intro Hfin_c (((Htrans.left).right).right y z Hyin Hle)
            · intro S HSin
              have Htrans : S ∈ X_filters_not_cont_x x := by apply Set.mem_of_mem_of_subset HSin Hsubset
              exact Htrans.right
          · intro S HSin
            apply Set.subset_sUnion_of_mem
            assumption
        · exact And.intro Hfilter Hnotin
    rcases Hzorn with ⟨P, ⟨HPin, ⟨HFsubset, Hmax⟩⟩⟩
    exists P
    apply And.intro
    · by_cases Hprime : prime_filter P
      · assumption
      · unfold prime_filter at Hprime
        simp at Hprime
        have Hproper : proper_filter P :=
          by
            apply And.intro
            · exact HPin.left
            · intro Hbot_in
              exact HPin.right (((HPin.left).right).right ⊥ x Hbot_in bot_le)
        let Hprime := Hprime Hproper
        rcases Hprime with ⟨y, ⟨z, ⟨Horin, Hnotin⟩⟩⟩
        push_neg at Hnotin
        rcases Hnotin with ⟨Hxnotin, Hynotin⟩
        have Hsubset1 : P ⊂ X_gen_filter (P ∪ {y}) :=
          by
            unfold X_gen_filter
            rw [Set.ssubset_def]
            apply And.intro
            · rw [Set.subset_def]
              intro t Htin
              simp
              intro F' _ Hsubset
              apply Set.mem_of_mem_of_subset (Set.mem_of_mem_of_subset Htin (Set.subset_insert y P)) Hsubset
            · rw [Set.subset_def]
              push_neg
              exists y
              apply And.intro
              · simp
                intro F' _ Hsubset
                rw [Set.insert_subset_iff] at Hsubset
                exact Hsubset.left
              · assumption
        have Hsubset2 : P ⊂ X_gen_filter (P ∪ {z}) :=
          by
            simp
            unfold X_gen_filter
            rw [Set.ssubset_def]
            apply And.intro
            · rw [Set.subset_def]
              intro t Htin
              simp
              intro F' _ Hsubset
              apply Set.mem_of_mem_of_subset (Set.mem_of_mem_of_subset Htin (Set.subset_insert z P)) Hsubset
            · rw [Set.subset_def]
              push_neg
              exists z
              apply And.intro
              · simp
                intro F' _ Hsubset
                rw [Set.insert_subset_iff] at Hsubset
                exact Hsubset.left
              · assumption
        have Hxin1 : x ∈ X_gen_filter (P ∪ {y}) :=
          by
            by_cases Hxin : x ∈ X_gen_filter (P ∪ {y})
            · assumption
            · have Hfilter_not_cont : X_gen_filter (P ∪ {y}) ∈ X_filters_not_cont_x x :=
                by
                  apply And.intro
                  · simp
                    exact X_gen_filter_filter (insert y P) (Set.insert_nonempty y P)
                  · assumption
              exfalso
              exact Hsubset1.right (Eq.subset (Hmax (X_gen_filter (P ∪ {y})) Hfilter_not_cont Hsubset1.left))
        have Hxin2 : x ∈ X_gen_filter (P ∪ {z}) :=
          by
            by_cases Hxin : x ∈ X_gen_filter (P ∪ {z})
            · assumption
            · have Hfilter_not_cont : X_gen_filter (P ∪ {z}) ∈ X_filters_not_cont_x x :=
                by
                  apply And.intro
                  · simp
                    exact X_gen_filter_filter (insert z P) (Set.insert_nonempty z P)
                  · assumption
              exfalso
              exact Hsubset2.right (Eq.subset (Hmax (X_gen_filter (P ∪ {z})) Hfilter_not_cont Hsubset2.left))
        have Hu : ∃ u ∈ P, y ⊓ u ≤ x :=
          by apply mem_gen_ins_filter P HPin.left Hxin1
        have Hv : ∃ v ∈ P, z ⊓ v ≤ x :=
          by apply mem_gen_ins_filter P HPin.left Hxin2
        rcases Hu with ⟨u, ⟨Huin, Hglbu⟩⟩
        rcases Hv with ⟨v, ⟨Hvin, Hglbv⟩⟩
        let c := u ⊓ v
        have Haux : (y ⊔ z) ⊓ c ≤ x :=
          by
            have Haux1 : y ≤ c ⇨ x :=
              by
                rw [le_himp_iff]
                apply le_trans (inf_le_inf_left y (inf_le_left))
                assumption
            have Haux2 : z ≤ c ⇨ x :=
              by
                rw [le_himp_iff]
                apply le_trans (inf_le_inf_left z (inf_le_right))
                assumption
            let Haux := sup_le Haux1 Haux2
            rw [le_himp_iff] at Haux
            assumption
        exfalso
        have Hcin : c ∈ P := by apply (((Hproper.left).right).left u v); assumption'
        exact HPin.right (((Hproper.left).right).right ((y ⊔ z) ⊓ c) x
                          (((Hproper.left).right).left (y ⊔ z) c Horin Hcin) Haux)
    · exact And.intro HFsubset (HPin.right)

lemma super_prime_filter_cor1 (x : α) (Hnottop : x ≠ ⊤) :
  ∃ (P : Set α), @prime_filter α _ P /\ x ∉ P :=
  by
    let Htopfilter : @filter α _ {⊤} :=
      by
        apply And.intro
        · simp
        · simp
          intro x y Hxtop Htople
          rw [Hxtop] at Htople
          rw [top_le_iff] at Htople
          assumption
    let Haux := @super_prime_filter α _ x {⊤} Htopfilter Hnottop
    rcases Haux with ⟨P, ⟨_, ⟨_, _⟩⟩⟩
    exists P

lemma super_prime_filter_cor2 : Set.sInter (@prime_filters α _) = {⊤} :=
  by
    rw [Set.ext_iff]
    intro x
    apply Iff.intro
    · intro Hincap
      simp
      by_cases Heqtop : x = ⊤
      · assumption
      · exfalso
        let Haux := @super_prime_filter_cor1 α _ x Heqtop
        rcases Haux with ⟨P, ⟨Hprime, Hxnotin⟩⟩
        have Haux' : P ∈ prime_filters := by simp only [prime_filters]; assumption
        exact  Hxnotin (Hincap P Haux')
    · intro Htop
      rw [Htop]
      intro F Hprime
      rcases Hprime with ⟨⟨Hfilter, _⟩, _⟩
      exact @top_mem_filter α _ F Hfilter

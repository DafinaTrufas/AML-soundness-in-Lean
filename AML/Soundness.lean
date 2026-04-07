import AML.Syntax
import AML.Semantics

set_option linter.unusedSectionVars false
set_option linter.style.cdot false
set_option linter.style.longLine false

variable {𝕊 A : Type} [Hnempty : Nonempty A]
         {S : Struct 𝕊 A} {e : valVar A} {x y z : Var}
         {Γ : Set (Pattern 𝕊)} {ϕ ψ χ : Pattern 𝕊}

open PropAxiom

@[simp]
lemma propaxiom_tautology (axm : PropAxiom ϕ) : tautology ϕ :=
  match axm with
  | contractionDisj | contractionConj | exfalso | lem
    | notationBot1 | notationBot2 => by simp_all
  | weakeningDisj | weakeningConj | permutationDisj | permutationConj =>
    by
      intro
      simp_all
      rw [Set.diff_eq_empty]
      simp

@[simp]
lemma propaxiom_valid (axm : PropAxiom ϕ) : valid ϕ := by
  apply tautology_valid
  exact propaxiom_tautology axm

@[simp]
lemma fol1_valid : valid (∀∀ x (ϕ ⇒ ψ) ⇒ ∀∀ x ϕ ⇒ ∀∀ x ψ) := by
  intro _ _ _ _
  rw [val_sat_to]
  intro a Hain
  simp at Hain
  simp
  intro H a1
  exact (Hain a1) (H a1)

-- the alternative proof below follows exactly the pen-and-paper proof (Proposition 3.2.1)
@[simp]
lemma fol1_valid' : valid (∀∀ x (ϕ ⇒ ψ) ⇒ ∀∀ x ϕ ⇒ ∀∀ x ψ) := by
  intro A _ S e
  rw [val_sat_to]
  unfold valPattern
  conv =>
    lhs
    simp [Set.diff_diff_eq_sdiff_union, <-Set.compl_eq_univ_diff]
  conv =>
    rhs
    simp [Set.diff_diff_eq_sdiff_union]
    rw [<-Set.compl_eq_univ_diff, Set.compl_iInter, Set.union_iInter]
  simp
  intro a elem Helem
  simp_all
  specialize Helem a
  rcases Helem
  . apply Or.inl
    exists a
  . apply Or.inr
    assumption

@[simp]
lemma val_indep_of_new_var_update {a : A} :
  ¬Pattern.occurs x ϕ →
  ∀ (e : valVar A), valPattern S (Function.update e x a) ϕ = valPattern S e ϕ := by
  intro Hnotocc
  induction ϕ with
  | var y => simp_all; intro e; rw [Function.update_of_ne]; intro Heq; rw [<-Heq] at Hnotocc; contradiction
  | const _ | bot => simp
  | neg _ ih => simp; intro e; rw [ih Hnotocc]
  | and _ _ ih1 ih2 | or _ _ ih1 ih2 | impl _ _ ih1 ih2 | appl _ _ ih1 ih2 =>
      simp
      intro e
      unfold Pattern.occurs at Hnotocc
      simp at Hnotocc
      rcases Hnotocc with ⟨Hvp, Hpsi⟩
      rw [ih1 Hvp, ih2 Hpsi]
  | ex y _ ih => unfold Pattern.occurs at Hnotocc; simp at Hnotocc; rcases Hnotocc with ⟨Hvp, Hpsi⟩
                 intro e
                 simp_all
                 rw [Set.Subset.antisymm_iff]
                 apply And.intro <;>
                 (intro b Hbin; simp_all; rcases Hbin with ⟨c, Hbin⟩; exists c; let Hsp := ih (Function.update e y c))
                 . rw [Function.update_comm, Hsp] at Hbin
                   . assumption
                   . simp; intro Heq; cases Heq; contradiction
                 . rw [Function.update_comm, Hsp]
                   . assumption
                   . simp; intro Heq; cases Heq; contradiction
  | univ y _ ih => unfold Pattern.occurs at Hnotocc; simp at Hnotocc; rcases Hnotocc with ⟨Hvp, Hpsi⟩
                   intro e
                   simp_all
                   rw [Set.Subset.antisymm_iff]
                   apply And.intro <;>
                   (intro b Hbin; simp_all; intro c; specialize Hbin c; let Hsp := ih (Function.update e y c))
                   . rw [Function.update_comm, Hsp] at Hbin
                     . assumption
                     . simp; intro Heq; cases Heq; contradiction
                   . rw [Function.update_comm, Hsp]
                     . assumption
                     . simp; intro Heq; cases Heq; contradiction

@[simp]
lemma fol2_valid (Hnotocc : ¬Pattern.occurs x ϕ) : valid (ϕ ⇒ ∀∀ x ϕ) := by
  intro _ _ _ _
  rw [val_sat_to]
  intro _ _ _ HBin
  simp at HBin
  rcases HBin with ⟨_, Hvala'⟩
  rw [<-Hvala', val_indep_of_new_var_update]
  assumption'

@[simp]
lemma fol3_valid (Hdiff : x ≠ y) {HvalAppSetsDef : ∀ A : Type, ∀ S : Struct 𝕊 A, valAppSetsDef S} : valid (∃∃ x (@Pattern.var 𝕊 x ≡ @Pattern.var 𝕊 y)) := by
  intro A _ S e
  rw [val_sat_ex, Set.Subset.antisymm_iff]
  apply And.intro
  . simp
  . have Haux : valPattern S (Function.update e x (e y)) (Pattern.var x ≡ Pattern.var y) = Set.univ := by
      unfold Pattern.equality
      rw [<-valPatternFloorUniv]
      . rw [valPatternIff]
        simp
        rw [Function.update_of_ne]
        symm
        assumption
      . exact (HvalAppSetsDef A S)
    rw [<-Haux]
    apply Set.subset_iUnion (fun a : A => valPattern S (Function.update e x a) (Pattern.var x ≡ Pattern.var y))

@[simp]
lemma notationExists1_valid : valid (∃∃ x ϕ ⇒ ∼∀∀ x (∼ϕ)) := by
  intro _ _ _ _
  rw [val_sat_to]
  unfold valPattern
  conv =>
    rhs
    unfold valPattern
    rw [<-Set.compl_eq_univ_diff, Set.compl_iInter]
    simp [<-Set.compl_eq_univ_diff]

@[simp]
lemma notationExists2_valid : valid (∼∀∀ x (∼ϕ) ⇒ ∃∃ x ϕ) := by
  intro _ _ _ _
  rw [val_sat_to]
  unfold valPattern
  conv =>
    lhs
    unfold valPattern
    rw [<-Set.compl_eq_univ_diff, Set.compl_iInter]
    simp [<-Set.compl_eq_univ_diff]

@[simp]
lemma propagationOrRight_valid : valid ((ϕ ∨∨ ψ)·χ ⇒ ϕ·χ ∨∨ ψ·χ) := by
  intro _ _ _ _
  rw [val_sat_to]
  unfold valPattern
  rw [valPattern, valAppSetsUnionL]
  simp

@[simp]
lemma propagationOrLeft_valid : valid (χ·(ϕ ∨∨ ψ) ⇒ χ·ϕ ∨∨ χ·ψ) := by
  intro _ _ _ _
  rw [val_sat_to]
  unfold valPattern
  rw [valPattern, valAppSetsUnionR]
  simp

@[simp]
lemma propagationExistsRight_valid (Hnotocc : ¬Pattern.occurs x ψ) :
  valid ((∃∃ x ϕ)·ψ ⇒ ∃∃ x (ϕ·ψ)) := by
  intro _ Hnempty _ _
  rw [val_sat_to]
  simp only [valPattern]
  rw [valAppSetsBigUnionL]
  rw [<-@val_indep_of_new_var_update _ _ _ _ x]
  . simp_all
  . exact Classical.choice Hnempty
  . assumption

@[simp]
lemma propagationExistsLeft_valid (Hnotocc : ¬Pattern.occurs x ψ) :
  valid (ψ·(∃∃ x ϕ) ⇒ ∃∃ x (ψ·ϕ)) := by
  intro _ Hnempty _ _
  rw [val_sat_to]
  simp only [valPattern]
  rw [valAppSetsBigUnionR]
  rw [<-@val_indep_of_new_var_update _ _ _ _ x]
  . simp_all
  . exact Classical.choice Hnempty
  . assumption

@[simp]
lemma propagationCeilRight_valid {HvalAppSetsDef : ∀ A : Type, ∀ S : Struct 𝕊 A, valAppSetsDef S} :
  valid (⌈ϕ⌉·ψ ⇒ ⌈ϕ⌉) := by
  intro A Hnempty S e
  rw [val_sat_to]
  by_cases Hvalvp : valPattern S e ϕ = ∅
  . rw [valPatternCeilEmpty] at Hvalvp
    . rw [valPattern, Hvalvp]; simp
    . exact HvalAppSetsDef A S
  . rw [valPatternCeilUniv] at Hvalvp
    . rw [Hvalvp]; simp
    . exact HvalAppSetsDef A S

@[simp]
lemma propagationCeilLeft_valid {HvalAppSetsDef : ∀ A : Type, ∀ S : Struct 𝕊 A, valAppSetsDef S} :
  valid (ψ·⌈ϕ⌉ ⇒ ⌈ϕ⌉) := by
  intro A _ S e
  rw [val_sat_to]
  by_cases Hvalvp : valPattern S e ϕ = ∅
  . rw [valPatternCeilEmpty] at Hvalvp
    . rw [valPattern, Hvalvp]; simp
    . exact HvalAppSetsDef A S
  . rw [valPatternCeilUniv] at Hvalvp
    . rw [Hvalvp]; simp
    . exact HvalAppSetsDef A S

@[simp]
lemma definedness_valid {HvalAppSetsDef : ∀ A : Type, ∀ S : Struct 𝕊 A, valAppSetsDef S} :
  @valid 𝕊 ⌈Pattern.var x⌉ := by
  intro A _ S e
  rw [val_satisfies, <-valPatternCeilUniv]
  . simp
  . exact HvalAppSetsDef A S

@[simp]
lemma defPattern_valid {HvalAppSetsDef : ∀ A : Type, ∀ S : Struct 𝕊 A, valAppSetsDef S} :
  valid (ϕ ⇒ ⌈ϕ⌉) := by
  intro A _ S e
  rw [val_sat_to]
  by_cases Hvalvp : valPattern S e ϕ = ∅
  . rw [Hvalvp]; simp
  . rw [valPatternCeilUniv] at Hvalvp
    . rw [Hvalvp]; simp
    . exact HvalAppSetsDef A S

@[simp]
lemma defBot_valid :
  @valid 𝕊 (⌈⊥⌉ ⇒ ⊥) := by
  intro A _ S _
  rw [val_sat_to]
  simp

@[simp]
lemma modusPonens_sound (Hvp : Γ ⊨ ϕ) (Hvppsi : Γ ⊨ ϕ ⇒ ψ) : Γ ⊨ ψ := by
  intro _ _ _ Hsatset e
  specialize Hvp _ Hsatset e
  specialize Hvppsi _ Hsatset e
  simp_all

@[simp]
lemma syllogism_sound (Hvppsi : Γ ⊨ ϕ ⇒ ψ) (Hpsichi : Γ ⊨ ψ ⇒ χ) : Γ ⊨ ϕ ⇒ χ := by
  intro _ _ _ Hsatset e
  specialize Hvppsi _ Hsatset e
  specialize Hpsichi _ Hsatset e
  rw [val_sat_to] at *
  exact (Set.Subset.trans Hvppsi Hpsichi)

lemma inter_subset_iff_subset_compl_diff (B C D : Set A) : B ∩ C ⊆ D ↔ B ⊆ (Set.univ \ (C \ D)) := by
  apply Iff.intro
  . intro Hinter a Hainb
    simp
    intro Hainc
    let Haux := (And.intro Hainb Hainc)
    rw [<-Set.mem_inter_iff] at Haux
    apply Set.mem_of_mem_of_subset
    assumption'
  . intro Hdiff a Haininter
    rw [Set.mem_inter_iff] at Haininter
    rcases Haininter with ⟨Hb, Hc⟩
    have Haux : a ∈  Set.univ \ (C \ D) := by apply Set.mem_of_mem_of_subset Hb; assumption'
    simp at Haux
    apply Haux
    assumption

@[simp]
lemma exportation_sound (Hsi : Γ ⊨ ϕ ∧∧ ψ ⇒ χ) : Γ ⊨ ϕ ⇒ (ψ ⇒ χ) := by
  intro _ _ _ Hsatset e
  specialize Hsi _ Hsatset e
  rw [val_sat_to] at *
  simp at Hsi
  simp
  rw [<-inter_subset_iff_subset_compl_diff]
  assumption

@[simp]
lemma importation_sound (Hsi : Γ ⊨ ϕ ⇒ (ψ ⇒ χ)) : Γ ⊨ ϕ ∧∧ ψ ⇒ χ := by
  intro _ _ _ Hsatset e
  specialize Hsi _ Hsatset e
  rw [val_sat_to] at *
  simp at Hsi
  simp
  rw [inter_subset_iff_subset_compl_diff]
  assumption

@[simp]
lemma expansion_sound (Hvppsi : Γ ⊨ ϕ ⇒ ψ) : Γ ⊨ χ ∨∨ ϕ ⇒ χ ∨∨ ψ := by
  intro _ _ _ Hsatset e
  specialize Hvppsi _ Hsatset e
  rw [val_sat_to] at *
  simp
  apply Set.Subset.trans Hvppsi
  simp

@[simp]
lemma gen_sound (Hvp : Γ ⊨ ϕ) : Γ ⊨ ∀∀ x ϕ := by
  intro _ _ S Hsatset _
  simp
  specialize Hvp S Hsatset
  simp_all

@[simp]
lemma framingLeft_sound (Hvppsi : Γ ⊨ ϕ ⇒ ψ) : Γ ⊨ ϕ·χ ⇒ ψ·χ := by
  intro _ _ S Hsatset e
  specialize Hvppsi S Hsatset e
  rw [val_sat_to] at *
  apply valAppSetsSubseteqR
  assumption

@[simp]
lemma framingRight_sound (Hvppsi : Γ ⊨ ϕ ⇒ ψ) : Γ ⊨ χ·ϕ ⇒ χ·ψ := by
  intro _ _ S Hsatset e
  specialize Hvppsi S Hsatset e
  rw [val_sat_to] at *
  apply valAppSetsSubseteqL
  assumption

@[simp]
lemma axiomInApp_valid (xy_dist : ¬(x = y)) (xz_dist : ¬(x = z)) (yz_dist : ¬(y = z))
                       (not_occ_y_vp : ¬(Pattern.occurs y ϕ))
                       (not_occ_y_psi : ¬(Pattern.occurs y ψ))
                       (not_occ_z_vp : ¬(Pattern.occurs z ϕ))
                       (not_occ_z_psi : ¬(Pattern.occurs z ψ))
                       {HvalAppSetsDef : ∀ A : Type, ∀ S : Struct 𝕊 A, valAppSetsDef S} :
  valid ((x ∈∈ ϕ·ψ) ≡ ∃∃ y (∃∃ z ((y ∈∈ ϕ) ∧∧ (z ∈∈ ψ) ∧∧ (x ∈∈ Pattern.var y·Pattern.var z)))) := by
  intro A Hnempty S e
  have Haux1 : valPattern S e (x ∈∈ ϕ·ψ) = Set.univ ↔ ∃ a ∈ valPattern S e ϕ, ∃ b ∈ valPattern S e ψ, e x ∈ S.valApp a b := by
    unfold Pattern.membership
    rw [<-valPatternCeilUniv]
    . simp
    . exact HvalAppSetsDef A S
  have Haux2 : valPattern S e (∃∃ y (∃∃ z ((y ∈∈ ϕ) ∧∧ (z ∈∈ ψ) ∧∧ (x ∈∈ Pattern.var y·Pattern.var z)))) = Set.univ ↔ ∃ a ∈ valPattern S e ϕ, ∃ b ∈ valPattern S e ψ, e x ∈ S.valApp a b := by
    simp only [valPattern]
    have Hnotocczy : ¬Pattern.occurs z (y ∈∈ ϕ) := by
      simp
      apply And.intro
      . intro Hzeqy; symm at Hzeqy; contradiction
      . assumption
    let Hval_indep_y (a a_1 : A) := @val_indep_of_new_var_update 𝕊 A _ S z (y ∈∈ ϕ) a_1 Hnotocczy (Function.update e y a)
    have Hnotoccyz : ¬Pattern.occurs y (z ∈∈ ψ) := by simp; apply And.intro <;> assumption
    let Haux (a a_1 : A) := @val_indep_of_new_var_update 𝕊 A _ S y (z ∈∈ ψ) a Hnotoccyz (Function.update e z a_1)
    have Hval_indep_z : ∀ a a_1 : A, valPattern S (Function.update (Function.update e y a) z a_1) (z ∈∈ ψ) =
                              valPattern S (Function.update e z a_1) (z ∈∈ ψ) := by
      intro a b; rw [Function.update_comm, Haux]; assumption
    simp only [Hval_indep_y, Hval_indep_z]
    rw [Set.iUnion_eq_univ_iff]
    let Hval_indep_y (i : A) := @val_indep_of_new_var_update 𝕊 A _ S y ϕ i not_occ_y_vp e
    let Hval_indep_z (i : A) := @val_indep_of_new_var_update 𝕊 A _ S z ψ i not_occ_z_psi e
    apply Iff.intro
    . simp [Function.update, xy_dist, xz_dist, yz_dist, Hval_indep_y, Hval_indep_z]
      intro Hunion
      specialize Hunion (e x)
      rcases Hunion with ⟨a, ⟨b, ⟨⟨⟨_, ⟨⟨_, Hae⟩, _⟩⟩, ⟨_, ⟨⟨_, Hbe⟩, _⟩⟩⟩, ⟨_, ⟨⟨_, Hex⟩, _⟩⟩⟩⟩⟩
      exists a
      split_ands
      . assumption
      . exists b
    . intro Hexab c
      rcases Hexab with ⟨a, ⟨Hain, ⟨b, ⟨Hbin, Hex⟩⟩⟩⟩
      exists a
      rw [Set.mem_iUnion]
      exists b
      rw [Set.mem_inter_iff]
      split_ands <;> (apply Set.mem_of_mem_of_subset; exact Set.mem_univ c; simp_all)
  have Haux3 : valPattern S e (x ∈∈ ϕ·ψ) = ∅ ↔ ¬(∃ a ∈ valPattern S e ϕ, ∃ b ∈ valPattern S e ψ, e x ∈ S.valApp a b) := by
    unfold Pattern.membership
    rw [<-valPatternCeilEmpty]
    . simp
      apply Iff.intro <;> (intro Hforall2 _ _ _ _; apply Hforall2 <;> assumption)
    . exact HvalAppSetsDef A S
  have Haux4 : valPattern S e (∃∃ y (∃∃ z ((y ∈∈ ϕ) ∧∧ (z ∈∈ ψ) ∧∧ (x ∈∈ Pattern.var y·Pattern.var z)))) = ∅ ↔ ¬(∃ a ∈ valPattern S e ϕ, ∃ b ∈ valPattern S e ψ, e x ∈ S.valApp a b) := by
    simp only [valPattern]
    have Hnotocczy : ¬Pattern.occurs z (y ∈∈ ϕ) := by
      simp
      apply And.intro
      . intro Hzeqy; symm at Hzeqy; contradiction
      . assumption
    let Hval_indep_y (a a_1 : A) := @val_indep_of_new_var_update 𝕊 A _ S z (y ∈∈ ϕ) a_1 Hnotocczy (Function.update e y a)
    have Hnotoccyz : ¬Pattern.occurs y (z ∈∈ ψ) := by simp; apply And.intro <;> assumption
    let Haux (a a_1 : A) := @val_indep_of_new_var_update 𝕊 A _ S y (z ∈∈ ψ) a Hnotoccyz (Function.update e z a_1)
    have Hval_indep_z : ∀ a a_1 : A, valPattern S (Function.update (Function.update e y a) z a_1) (z ∈∈ ψ) =
                              valPattern S (Function.update e z a_1) (z ∈∈ ψ) := by
      intro a b; rw [Function.update_comm, Haux]; assumption
    simp only [Hval_indep_y, Hval_indep_z]
    rw [Set.iUnion_eq_empty]
    simp only [Set.iUnion_eq_empty]
    let Hval_indep_y (i : A) := @val_indep_of_new_var_update 𝕊 A _ S y ϕ i not_occ_y_vp e
    let Hval_indep_z (i : A) := @val_indep_of_new_var_update 𝕊 A _ S z ψ i not_occ_z_psi e
    apply Iff.intro
    . intro Hforall Hexists
      rcases Hexists with ⟨a, ⟨Hain, ⟨b, ⟨Hbin, Hex⟩⟩⟩⟩
      specialize Hforall a b
      rw [<-Hval_indep_y a] at Hain
      have Hain' : ¬(valPattern S (Function.update e y a) (Pattern.var y ∧∧ ϕ) = ∅):= by simp_all
      rw [<-Hval_indep_z b] at Hbin
      have Hbin' : ¬(valPattern S (Function.update e z b) (Pattern.var z ∧∧ ψ) = ∅):= by simp_all
      rw [valPatternCeilUniv] at Hain' Hbin'
      . simp_all
      . exact HvalAppSetsDef A S
      . exact HvalAppSetsDef A S
    . intro Hexab a b
      by_cases Hain : a ∈ valPattern S e ϕ
      . by_cases Hbin : b ∈ valPattern S e ψ
        . by_cases Hex : e x ∈ S.valApp a b <;> simp_all
        . rw [<-Hval_indep_z b] at Hbin
          have Hbin' : valPattern S (Function.update e z b) (Pattern.var z ∧∧ ψ) = ∅:= by simp; assumption
          rw [valPatternCeilEmpty] at Hbin'
          . unfold Pattern.membership
            rw [Hbin']
            simp
          . exact HvalAppSetsDef A S
      . rw [<-Hval_indep_y a] at Hain
        have Hain' : valPattern S (Function.update e y a) (Pattern.var y ∧∧ ϕ) = ∅:= by simp; assumption
        rw [valPatternCeilEmpty] at Hain'
        . unfold Pattern.membership
          rw [Hain']
          simp
        . exact HvalAppSetsDef A S
  have Heq : valPattern S e (x ∈∈ ϕ·ψ) = valPattern S e (∃∃ y (∃∃ z ((y ∈∈ ϕ) ∧∧ (z ∈∈ ψ) ∧∧ (x ∈∈ Pattern.var y·Pattern.var z)))) := by
    by_cases Hex : ∃ a ∈ valPattern S e ϕ, ∃ b ∈ valPattern S e ψ, e x ∈ S.valApp a b
    . let Hex' := Hex
      rw [<-Haux1] at Hex
      rw [<-Haux2] at Hex'
      rw [Hex, Hex']
    . let Hex' := Hex
      rw [<-Haux3] at Hex
      rw [<-Haux4] at Hex'
      rw [Hex, Hex']
  rw [val_satisfies, <-valPatternEqUniv]
  . assumption
  . exact HvalAppSetsDef A S

@[simp]
lemma singleton_valid : valid (∼(x ∈∈ ϕ) ∨∨ ∼(x ∈∈ ∼ϕ)) := by
  intro A _ S e
  rw [val_sat_or, valPattern, valPattern]
  by_cases Hexin : e x ∈ valPattern S e ϕ <;> simp_all

theorem soundness {HvalAppSetsDef : ∀ A : Type, ∀ S : Struct 𝕊 A, valAppSetsDef S} : Γ ⊢ ϕ → Γ ⊨ ϕ := by
  intro Hproof
  induction Hproof with
  | axm axm => apply valid_sat_set; match axm with
    | Axiom.propAxm paxm => apply propaxiom_valid; assumption
    | Axiom.fol1 => apply fol1_valid
    | Axiom.fol2 Hnotocc => apply fol2_valid; assumption
    | Axiom.fol3 Hdiff => apply fol3_valid; assumption'
    | Axiom.notationExists1 => apply notationExists1_valid
    | Axiom.notationExists2 => apply notationExists2_valid
    | Axiom.propagationOrRight => apply propagationOrRight_valid
    | Axiom.propagationOrLeft => apply propagationOrLeft_valid
    | Axiom.propagationExistsRight Hnotocc => apply propagationExistsRight_valid; assumption
    | Axiom.propagationExistsLeft Hnotocc => apply propagationExistsLeft_valid; assumption
    | Axiom.propagationCeilRight => apply propagationCeilRight_valid; assumption
    | Axiom.propagationCeilLeft => apply propagationCeilLeft_valid; assumption
    | Axiom.definedness => apply definedness_valid; assumption'
    | Axiom.defPattern => apply defPattern_valid; assumption
    | Axiom.defBot => apply defBot_valid
    | Axiom.axiomInApp _ _ _ _ _ _ _ => apply axiomInApp_valid; assumption'
    | Axiom.singletonSimple => apply singleton_valid
  | premise p => simp [set_sat_patt, model_set]; intro _ _ _ H _; apply H; assumption
  | @modusPonens ϕ ψ _ _ ih1 ih2 => apply @modusPonens_sound _ _ ϕ ψ; assumption'
  | syllogism _ _ ih1 ih2 => apply syllogism_sound; assumption'
  | exportation _ ih => apply exportation_sound; assumption
  | importation _ ih => apply importation_sound; assumption
  | expansion _ ih => apply expansion_sound; assumption
  | generalization _ ih => apply gen_sound; assumption
  | framingLeft _ ih => apply framingLeft_sound; assumption
  | framingRight _ ih => apply framingRight_sound; assumption

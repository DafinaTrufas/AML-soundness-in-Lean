import AML.Pattern
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Countable.Basic

set_option autoImplicit false
set_option linter.style.cdot false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

structure Struct (𝕊 A : Type) where
  valApp : A → A → Set A
  valSymb : Const 𝕊 → Set A

def valVar (A : Type) := Var → A

variable {𝕊 A : Type} [Hnempty : Nonempty A] {Γ : Set (Pattern 𝕊)}

@[simp]
def valAppSets (S : Struct 𝕊 A) (B C : Set A) : Set A :=
  Set.sUnion {a | ∃ b ∈ B, ∃ c ∈ C, a = S.valApp b c}

@[simp]
lemma valAppSetsUnionL (S : Struct 𝕊 A) (B C D : Set A) :
  valAppSets S (B ∪ C) D = valAppSets S B D ∪ valAppSets S C D := by
  simp
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  . intro a Hain
    simp_all
    rcases Hain with ⟨b, ⟨c, ⟨⟨_ | _, _⟩, _⟩⟩⟩
    . apply Or.inl
      exists b, c
    . apply Or.inr
      exists b, c
  . intro a Hain
    simp_all
    rcases Hain with ⟨b, ⟨c, ⟨⟨Hb, Hd⟩, _⟩⟩⟩ | ⟨b, ⟨c, ⟨⟨Hc, Hd⟩, _⟩⟩⟩ <;>
    (exists b, c; apply And.intro)
    . exact And.intro (Or.inl Hb) Hd
    . assumption
    . exact And.intro (Or.inr Hc) Hd
    . assumption

@[simp]
lemma valAppSetsUnionR (S : Struct 𝕊 A) (B C D : Set A) :
  valAppSets S D (B ∪ C) = valAppSets S D B ∪ valAppSets S D C:= by
  simp
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  . intro a Hain
    simp_all
    rcases Hain with ⟨b, ⟨c, ⟨⟨_, _ | _⟩, _⟩⟩⟩
    . apply Or.inl
      exists b, c
    . apply Or.inr
      exists b, c
  . intro a Hain
    simp_all
    rcases Hain with ⟨b, ⟨c, ⟨⟨Hd, Hb⟩, _⟩⟩⟩ | ⟨b, ⟨c, ⟨⟨Hd, Hc⟩, _⟩⟩⟩ <;>
    (exists b, c; apply And.intro)
    . exact And.intro Hd (Or.inl Hb)
    . assumption
    . exact And.intro Hd (Or.inr Hc)
    . assumption

@[simp]
lemma valAppSetsBigUnionL (S : Struct 𝕊 A) (B : Set A) (f : A → Set A) :
  valAppSets S (Set.iUnion f) B = ⋃ i, (valAppSets S (f i) B) := by
  simp
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  . intro a Hain
    simp_all
    rcases Hain with ⟨b, ⟨c, ⟨⟨⟨i, _⟩, _⟩, _⟩⟩⟩
    exists i, b, c
  . intro a Hain
    simp_all
    rcases Hain with ⟨i, ⟨b, ⟨c, ⟨⟨Hbin, Hcin⟩, _⟩⟩⟩⟩
    exists b, c
    split_ands
    . exists i
    assumption'

@[simp]
lemma valAppSetsBigUnionR (S : Struct 𝕊 A) (B : Set A) (f : A → Set A) :
  valAppSets S B (Set.iUnion f) = ⋃ i, (valAppSets S B (f i)) := by
  simp
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  . intro a Hain
    simp_all
    rcases Hain with ⟨b, ⟨c, ⟨⟨_, ⟨i, _⟩⟩, _⟩⟩⟩
    exists i, b, c
  . intro a Hain
    simp_all
    rcases Hain with ⟨i, ⟨b, ⟨c, ⟨⟨Hbin, Hcin⟩, _⟩⟩⟩⟩
    exists b, c
    split_ands
    . assumption
    . exists i
    . assumption

@[simp]
def valAppSetsDef (S : Struct 𝕊 A) := ∀ (a : A), valAppSets S (S.valSymb Const.def) {a} = Set.univ

@[simp]
lemma valAppSetsSubseteqR (S : Struct 𝕊 A) (B C D : Set A) :
  B ⊆ C → valAppSets S B D ⊆ valAppSets S C D := by
  intro Hsubeteq
  simp
  intro BD b HbinB d HdinD Happbd bd HbdinBd
  exists BD
  apply And.intro
  . exists b
    apply And.intro
    . apply Set.mem_of_mem_of_subset; assumption'
    . exists d
  . assumption

@[simp]
lemma valAppSetsSubseteqL (S : Struct 𝕊 A) (B C D : Set A) :
  B ⊆ C → valAppSets S D B ⊆ valAppSets S D C := by
  intro Hsubeteq
  simp
  intro BD b HbinD d HdinB Happbd bd HbdinBd
  exists BD
  apply And.intro
  . exists b
    apply And.intro
    . assumption
    . exists d
      apply And.intro
      . apply Set.mem_of_mem_of_subset; assumption'
      . assumption
  . assumption

@[simp]
def valPattern (S : Struct 𝕊 A) (e : valVar A) (ϕ : Pattern 𝕊) : Set A :=
  match ϕ with
  | Pattern.var x => { e x }
  | Pattern.const c => S.valSymb c
  | ⊥ => ∅
  | ∼ϕ => Set.univ \ valPattern S e ϕ
  | ϕ ∧∧ ψ => valPattern S e ϕ ∩ valPattern S e ψ
  | ϕ ∨∨ ψ => valPattern S e ϕ ∪ valPattern S e ψ
  | ϕ ⇒ ψ => Set.univ \ (valPattern S e ϕ \ valPattern S e ψ)
  | ϕ·ψ => valAppSets S (valPattern S e ϕ) (valPattern S e ψ)
  | ∃∃ x ϕ => Set.iUnion (fun a : A => valPattern S (Function.update e x a) ϕ)
  | ∀∀ x ϕ => Set.iInter (fun a : A => valPattern S (Function.update e x a) ϕ)

@[simp]
lemma valAppSetsUniv (S : Struct 𝕊 A) (a : A) {HvalAppSetsDef : valAppSetsDef S} :
  valAppSets S Set.univ {a} = Set.univ := by
  have Hsubseteql : valAppSets S Set.univ {a} ⊆ Set.univ := by simp
  have Hsubseteqr : Set.univ ⊆ valAppSets S Set.univ {a} := by
    conv =>
      lhs
      rw [<-HvalAppSetsDef a]
    apply valAppSetsSubseteqR
    simp
  apply Set.Subset.antisymm; assumption'

@[simp]
lemma valAppDefB (S : Struct 𝕊 A) (B : Set A) {Hnempty : Nonempty B} {HvalAppSetsDef : valAppSetsDef S} :
  valAppSets S (S.valSymb Const.def) B = Set.univ := by
  have Hsubseteql : valAppSets S (S.valSymb Const.def) B ⊆ Set.univ := by simp
  have Hsubseteqr : Set.univ ⊆ valAppSets S (S.valSymb Const.def) B := by
    simp at Hnempty
    rcases Hnempty with ⟨a, Hainb⟩
    have Hsubset : {a} ⊆ B := by simp; assumption
    conv =>
      lhs
      rw [<-HvalAppSetsDef a]
    apply valAppSetsSubseteqL
    assumption
  apply Set.Subset.antisymm; assumption'

open symmDiff

@[simp]
lemma valPatternIff (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) :
  valPattern S e (ϕ ⇔ ψ) = Set.univ \ ((valPattern S e ϕ) ∆ (valPattern S e ψ)) := Set.diff_inter_diff

@[simp]
lemma valPatternCeilEmpty (S : Struct 𝕊 A) (e : valVar A) (ϕ : Pattern 𝕊) {HvalAppSetsDef : valAppSetsDef S} :
  valPattern S e ϕ = ∅ ↔ valPattern S e ⌈ϕ⌉ = ∅ := by
  apply Iff.intro
  . unfold Pattern.definedness
    simp_all
  . by_cases Hempty : valPattern S e ϕ = ∅
    . intro _; assumption
    . intro Hdef
      unfold Pattern.definedness at Hdef
      simp only [valPattern] at Hdef
      rw [valAppDefB] at Hdef
      . apply Set.univ_nonempty at Hnempty
        rcases Hnempty with ⟨a, Hain⟩
        rw [Hdef] at Hain
        contradiction
      . have Hempty : valPattern S e ϕ ≠ ∅ := by simp; assumption
        rw [<-Set.nonempty_iff_ne_empty] at Hempty
        rw [Set.nonempty_coe_sort]
        assumption
      . assumption

@[simp]
lemma valPatternCeilUniv (S : Struct 𝕊 A) (e : valVar A) (ϕ : Pattern 𝕊) {HvalAppSetsDef : valAppSetsDef S} :
  ¬valPattern S e ϕ = ∅ ↔ valPattern S e ⌈ϕ⌉ = Set.univ := by
  apply Iff.intro
  . unfold Pattern.definedness
    intro Hnempty
    apply valAppDefB
    . rw [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty]
      assumption
    . assumption
  . intro Huniv Hempty
    rw [valPatternCeilEmpty] at Hempty
    . apply Set.univ_nonempty at Hnempty
      rcases Hnempty with ⟨a, Hain⟩
      rw [Hempty] at Huniv
      rw [<-Huniv] at Hain
      contradiction
    . assumption

@[simp]
lemma valPatternFloorUniv (S : Struct 𝕊 A) (e : valVar A) (ϕ : Pattern 𝕊) {HvalAppSetsDef : valAppSetsDef S} :
  valPattern S e ϕ = Set.univ ↔ valPattern S e ⌊ϕ⌋ = Set.univ := by
  unfold Pattern.totality
  simp only [valPattern]
  rw [<-Set.compl_eq_univ_diff, Set.compl_univ_iff, <-valPatternCeilEmpty]
  . apply Iff.intro
    . simp_all
    . intro Hempty
      simp at Hempty
      rw [<-Set.compl_eq_univ_diff, Set.compl_empty_iff] at Hempty
      assumption
  . assumption

@[simp]
lemma valPatternFloorEmpty (S : Struct 𝕊 A) (e : valVar A) (ϕ : Pattern 𝕊) {HvalAppSetsDef : valAppSetsDef S} :
  ¬valPattern S e ϕ = Set.univ ↔ valPattern S e ⌊ϕ⌋ = ∅ := by
  unfold Pattern.totality
  simp only [valPattern]
  rw [<-Set.compl_eq_univ_diff, Set.compl_empty_iff, <-valPatternCeilUniv]
  . simp only [valPattern]
    apply Iff.intro
    . intro _ Hdiffempty
      rw [<-Set.compl_eq_univ_diff] at Hdiffempty
      simp at Hdiffempty
      contradiction
    . intro Hdiffempty _
      rw [<-Set.compl_eq_univ_diff] at Hdiffempty
      simp at Hdiffempty
      contradiction
  . assumption

@[simp]
lemma valPatternEqUniv (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) {HvalAppSetsDef : valAppSetsDef S} :
  valPattern S e ϕ = valPattern S e ψ ↔ valPattern S e (ϕ ≡ ψ) = Set.univ := by
  unfold Pattern.equality
  rw [<-valPatternFloorUniv]
  . simp only [valPatternIff]
    simp
  . assumption

@[simp]
lemma valPatternEqEmpty (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) {HvalAppSetsDef : valAppSetsDef S} :
  ¬valPattern S e ϕ = valPattern S e ψ ↔ valPattern S e (ϕ ≡ ψ) = ∅ := by
  unfold Pattern.equality
  rw [<-valPatternFloorEmpty]
  . simp only [valPatternIff]
    simp
  . assumption

@[simp]
def val_satisfies (S : Struct 𝕊 A) (e : valVar A) (ϕ : Pattern 𝕊) :=
  valPattern S e ϕ = Set.univ

@[simp]
lemma val_sat_var (S : Struct 𝕊 A) (e : valVar A) (v : Var) :
  val_satisfies S e (Pattern.var v) ↔ ∃ x : A, Set.univ = {x} := by
  simp
  apply Iff.intro
  . intro Heval
    exists e v
    rw [Heval]
  . intro ⟨x, Hsingx⟩
    rw [Hsingx]
    simp
    have Haux1 : ∀ a : A, a = x := by intro a; apply Set.eq_of_mem_singleton; rw [<-Hsingx]; simp
    have Haux2 : ∃ b : A, e v = b := by simp
    rcases Haux2 with ⟨b, Hevb⟩
    rw [Hevb]
    exact Haux1 b

@[simp]
lemma val_sat_const (S : Struct 𝕊 A) (e : valVar A) (c : Const 𝕊) :
  val_satisfies S e (Pattern.const c) ↔ S.valSymb c = Set.univ := by simp

@[simp]
lemma val_not_sat_bot (S : Struct 𝕊 A) (e : valVar A) :
  ¬val_satisfies S e ⊥ := by
  intro Hvalbot
  apply Set.univ_nonempty at Hnempty
  rcases Hnempty with ⟨a, Hainuniv⟩
  rw [<-Hvalbot] at Hainuniv
  assumption

@[simp]
lemma val_sat_neg (S : Struct 𝕊 A) (e : valVar A) (ϕ : Pattern 𝕊) :
  val_satisfies S e (∼ϕ) ↔ valPattern S e ϕ = ∅ := by simp

@[simp]
lemma val_sat_and (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) :
  val_satisfies S e (ϕ ∧∧ ψ) ↔ val_satisfies S e ϕ ∧ val_satisfies S e ψ := by
  have Haux := @Set.sInter_eq_univ A {valPattern S e ϕ, valPattern S e ψ}
  simp at Haux
  assumption

@[simp]
lemma val_sat_or (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) :
  val_satisfies S e (ϕ ∨∨ ψ) ↔ valPattern S e ϕ ∪ valPattern S e ψ = Set.univ := by simp

@[simp]
lemma val_sat_to (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) :
  val_satisfies S e (ϕ ⇒ ψ) ↔ valPattern S e ϕ ⊆ valPattern S e ψ := by
  simp
  apply Set.diff_eq_empty

@[simp]
lemma val_sat_iff (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) :
  val_satisfies S e (ϕ ⇔ ψ) ↔ valPattern S e ϕ = valPattern S e ψ := by
  unfold val_satisfies
  rw [valPatternIff]
  simp

@[simp]
lemma val_sat_app (S : Struct 𝕊 A) (e : valVar A) (ϕ ψ : Pattern 𝕊) :
  val_satisfies S e (ϕ·ψ) ↔ valAppSets S (valPattern S e ϕ) (valPattern S e ψ) = Set.univ := by simp

@[simp]
lemma val_sat_ex (S : Struct 𝕊 A) (e : valVar A) (x : Var) (ϕ : Pattern 𝕊) :
  val_satisfies S e (∃∃ x ϕ) ↔ Set.iUnion (fun a : A => valPattern S (Function.update e x a) ϕ) = Set.univ := by simp

@[simp]
lemma val_sat_forall (S : Struct 𝕊 A) (e : valVar A) (x : Var) (ϕ : Pattern 𝕊) :
  val_satisfies S e (∀∀ x ϕ) ↔ ∀ a : A, val_satisfies S (Function.update e x a) ϕ := by simp

@[simp]
def model (S : Struct 𝕊 A) (ϕ : Pattern 𝕊) :=
  ∀ e : valVar A, val_satisfies S e ϕ

infix:(50) " ⊨ " => model

@[simp]
lemma model_var (S : Struct 𝕊 A) (v : Var) :
  model S (Pattern.var v) ↔ ∃ x : A, Set.univ = {x} := by
  apply Iff.intro
  . intro Hmodel
    let Hnempty' := Hnempty
    rcases Hnempty with ⟨a⟩
    rw [<-val_sat_var S (fun (v : Var) => a) v]
    apply Hmodel
  . intro ⟨x, Hunivx⟩ e
    rw [val_sat_var]
    exists x

@[simp]
lemma model_const (S : Struct 𝕊 A) (c : Const 𝕊) :
  model S (Pattern.const c) ↔ S.valSymb c = Set.univ := by
  apply Iff.intro
  . intro Hmodel
    let Hnempty' := Hnempty
    rcases Hnempty with ⟨a⟩
    rw [<-val_sat_const S (fun (v : Var) => a) c]
    apply Hmodel
  . intro Huniv e
    rw [val_sat_const]
    assumption

@[simp]
lemma not_model_bot (S : Struct 𝕊 A) :
  ¬model S ⊥ := by
  simp
  apply And.intro
  . rcases Hnempty with ⟨a⟩
    apply Nonempty.intro
    exact (fun (v : Var) => a)
  . intro Hemptyuniv
    apply Set.univ_nonempty at Hnempty
    rcases Hnempty with ⟨a, Hainuniv⟩
    rw [<-Hemptyuniv] at Hainuniv
    assumption

@[simp]
lemma model_and (S : Struct 𝕊 A) (ϕ ψ : Pattern 𝕊) :
  model S (ϕ ∧∧ ψ) ↔ model S ϕ ∧ model S ψ := by
  unfold model
  rw [<-forall_and]
  apply Iff.intro <;> intro Hforall e
  . rw [<-val_sat_and]
    apply Hforall
  . rw [val_sat_and]
    apply Hforall

@[simp]
lemma model_iff (S : Struct 𝕊 A) (ϕ ψ : Pattern 𝕊) :
  model S (ϕ ⇔ ψ) ↔ model S (ϕ ⇒ ψ) ∧ model S (ψ ⇒ ϕ) := by apply model_and

@[simp]
lemma model_to (S : Struct 𝕊 A) (ϕ ψ : Pattern 𝕊) :
  model S (ϕ ⇒ ψ) ∧ model S ϕ → model S ψ := by
  intro ⟨Hmodelto, _⟩ e
  specialize Hmodelto e
  rw [val_sat_to] at Hmodelto
  simp_all

@[simp]
lemma model_iff' (S : Struct 𝕊 A) (ϕ ψ : Pattern 𝕊) :
  model S (ϕ ⇔ ψ) → (model S ϕ ↔ model S ψ) := by
  intro Hmodeliff
  apply Iff.intro <;> (intro Hmodel; rw [model_iff] at Hmodeliff; apply model_to)
  . exact And.intro Hmodeliff.left Hmodel
  . exact And.intro Hmodeliff.right Hmodel

@[simp]
lemma model_forall (S : Struct 𝕊 A) (x : Var) (ϕ : Pattern 𝕊) :
  model S (∀∀ x ϕ) ↔ model S ϕ := by
  apply Iff.intro
  . intro Hmodel e
    simp at Hmodel
    specialize Hmodel e (e x)
    simp_all
  . simp_all

@[simp]
def valid (ϕ : Pattern 𝕊) := ∀ {A : Type} [Nonempty A] (S : Struct 𝕊 A), model S ϕ

@[simp]
def prop_eval (f : Pattern 𝕊 → Set A) :=
  (f ⊥ = ∅) ∧
  (∀ ϕ : Pattern 𝕊, f (∼ϕ) = Set.univ \ f ϕ) ∧
  (∀ ϕ ψ : Pattern 𝕊, f (ϕ ∧∧ ψ) = f ϕ ∩ f ψ) ∧
  (∀ ϕ ψ : Pattern 𝕊, f (ϕ ∨∨ ψ) = f ϕ ∪ f ψ) ∧
  (∀ ϕ ψ : Pattern 𝕊, f (ϕ ⇒ ψ) = Set.univ \ (f ϕ \ f ψ))

@[simp]
lemma val_prop_eval (S : Struct 𝕊 A) (e : valVar A) : prop_eval (valPattern S e) := by simp

@[simp]
def tautology (ϕ : Pattern 𝕊) :=
  ∀ {A : Type} [Nonempty A] (f : Pattern 𝕊 → Set A), prop_eval f → f ϕ = Set.univ

@[simp]
lemma tautology_valid (ϕ : Pattern 𝕊) : tautology ϕ → valid ϕ := by
  intro Htaut _ _ _ _
  apply Htaut
  simp

@[simp]
def val_sat_set (S : Struct 𝕊 A) (e : valVar A) (Γ : Set (Pattern 𝕊)) :=
  ∀ ϕ ∈ Γ, val_satisfies S e ϕ

@[simp]
def model_set (S : Struct 𝕊 A) (Γ : Set (Pattern 𝕊)) :=
  ∀ e : valVar A, val_sat_set S e Γ

infix:(50) " ⊨ " => model_set

@[simp]
def set_sat_patt (Γ : Set (Pattern 𝕊)) (ϕ : Pattern 𝕊) :=
  ∀ {A : Type} [Nonempty A] (S : Struct 𝕊 A), S ⊨ Γ → S ⊨ ϕ

infix:(50) " ⊨ " => set_sat_patt

@[simp]
lemma valid_sat_set (Γ : Set (Pattern 𝕊)) (ϕ : Pattern 𝕊) :
  valid ϕ → Γ ⊨ ϕ := by
  intro Hvalid _ _ _ _ _
  apply Hvalid

import AML.Pattern
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

set_option autoImplicit false
set_option linter.style.cdot false
set_option linter.style.longLine false

inductive PropAxiom {𝕊 : Type} : Pattern 𝕊 → Prop where
| contractionDisj {ϕ} : PropAxiom (ϕ ∨∨ ϕ ⇒ ϕ)
| contractionConj {ϕ} : PropAxiom (ϕ ⇒ ϕ ∧∧ ϕ)
| weakeningDisj {ϕ ψ} : PropAxiom (ϕ ⇒ ϕ ∨∨ ψ)
| weakeningConj {ϕ ψ} : PropAxiom (ϕ ∧∧ ψ ⇒ ϕ)
| permutationDisj {ϕ ψ} : PropAxiom (ϕ ∨∨ ψ ⇒ ψ ∨∨ ϕ)
| permutationConj {ϕ ψ} : PropAxiom (ϕ ∧∧ ψ ⇒ ψ ∧∧ ϕ)
| exfalso {ϕ} : PropAxiom (⊥ ⇒ ϕ)
| lem {ϕ} : PropAxiom (ϕ ∨∨ ∼ϕ)
| notationBot1 {ϕ} : PropAxiom (∼ϕ ⇒ ϕ ⇒ ⊥)
| notationBot2 {ϕ} : PropAxiom ((ϕ ⇒ ⊥) ⇒ ∼ϕ)

inductive Axiom {𝕊 : Type} : Pattern 𝕊 → Prop where
| propAxm {ϕ} : PropAxiom ϕ → Axiom ϕ
| fol1 {x ϕ ψ} : Axiom (∀∀ x (ϕ ⇒ ψ) ⇒ ∀∀ x ϕ ⇒ ∀∀ x ψ)
| fol2 {x ϕ} (not_occ : ¬Pattern.occurs x ϕ) : Axiom (ϕ ⇒ ∀∀ x ϕ)
| fol3 {x y} (diff_vars : x ≠ y) : Axiom (∃∃ x (Pattern.var x ≡ Pattern.var y))
| notationExists1 {x ϕ} : Axiom (∃∃ x ϕ ⇒ ∼∀∀ x (∼ϕ))
| notationExists2 {x ϕ} : Axiom (∼∀∀ x (∼ϕ) ⇒ ∃∃ x ϕ)
| propagationOrRight {ϕ ψ χ} : Axiom ((ϕ ∨∨ ψ)·χ ⇒ ϕ·χ ∨∨ ψ·χ)
| propagationOrLeft {ϕ ψ χ} : Axiom (χ·(ϕ ∨∨ ψ) ⇒ χ·ϕ ∨∨ χ·ψ)
| propagationExistsRight {x ϕ ψ} (not_occ : ¬Pattern.occurs x ψ) : Axiom ((∃∃ x ϕ)·ψ ⇒ ∃∃ x (ϕ·ψ))
| propagationExistsLeft {x ϕ ψ} (not_occ : ¬Pattern.occurs x ψ) : Axiom (ψ·(∃∃ x ϕ) ⇒ ∃∃ x (ψ·ϕ))
| propagationCeilRight {ϕ ψ} : Axiom (⌈ϕ⌉·ψ ⇒ ⌈ϕ⌉)
| propagationCeilLeft {ϕ ψ} : Axiom (ψ·⌈ϕ⌉ ⇒ ⌈ϕ⌉)
| definedness {x} : Axiom (⌈Pattern.var x⌉)
| defPattern {ϕ} : Axiom (ϕ ⇒ ⌈ϕ⌉)
| defBot : Axiom (⌈⊥⌉ ⇒ ⊥)
| axiomInApp {x y z ϕ ψ} (xy_dist : ¬(x = y)) (xz_dist : ¬(x = z)) (yz_dist : ¬(y = z))
                         (not_occ_y_vp : ¬(Pattern.occurs y ϕ))
                         (not_occ_y_psi : ¬(Pattern.occurs y ψ))
                         (not_occ_z_vp : ¬(Pattern.occurs z ϕ))
                         (not_occ_z_psi : ¬(Pattern.occurs z ψ)) : Axiom ((x ∈∈ ϕ·ψ) ≡ ∃∃ y (∃∃ z ((y ∈∈ ϕ) ∧∧ (z ∈∈ ψ) ∧∧ (x ∈∈ Pattern.var y·Pattern.var z))))
| singletonSimple {x ϕ} : Axiom (∼(x ∈∈ ϕ) ∨∨ ∼(x ∈∈ ∼ϕ))

inductive Proof {𝕊 : Type} (Γ : Set (Pattern 𝕊)) : Pattern 𝕊 → Type where
| axm {ϕ} : Axiom ϕ → Proof Γ ϕ
| premise {ϕ} : ϕ ∈ Γ → Proof Γ ϕ
| modusPonens {ϕ ψ} : Proof Γ ϕ → Proof Γ (ϕ ⇒ ψ) → Proof Γ ψ
| syllogism {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (ψ ⇒ χ) → Proof Γ (ϕ ⇒ χ)
| exportation {ϕ ψ χ} : Proof Γ (ϕ ∧∧ ψ ⇒ χ) → Proof Γ (ϕ ⇒ ψ ⇒ χ)
| importation {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ ⇒ χ) → Proof Γ (ϕ ∧∧ ψ ⇒ χ)
| expansion {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (χ ∨∨ ϕ ⇒ χ ∨∨ ψ)
| generalization {x ϕ} : Proof Γ ϕ → Proof Γ (∀∀ x ϕ)
| framingLeft {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (ϕ·χ ⇒ ψ·χ)
| framingRight {ϕ ψ χ} : Proof Γ (ϕ ⇒ ψ) → Proof Γ (χ·ϕ ⇒ χ·ψ)

infix:25 " ⊢ " => Proof

variable {𝕊 : Type} {Γ Δ : Set (Pattern 𝕊)} {ϕ ψ χ γ : Pattern 𝕊}

namespace Proof
open PropAxiom
open Axiom

def disjIntroRight : Γ ⊢ ψ ⇒ ϕ ∨∨ ψ := syllogism (axm (propAxm weakeningDisj)) (axm (propAxm permutationDisj))

def conjElimRight : Γ ⊢ ϕ ∧∧ ψ ⇒ ψ := syllogism (axm (propAxm permutationConj)) (axm (propAxm weakeningConj))

def implProjLeft : Γ ⊢ ϕ ⇒ (ψ ⇒ ϕ) := exportation (axm (propAxm weakeningConj))

def disjOfAndElimLeft : Γ ⊢ ϕ ∧∧ ψ ⇒ ϕ ∨∨ γ := syllogism (axm (propAxm weakeningConj)) (axm (propAxm weakeningDisj))

def implSelf : Γ ⊢ ϕ ⇒ ϕ := syllogism (axm (propAxm contractionConj)) (axm (propAxm weakeningConj))

def conjIntro : Γ ⊢ ϕ ⇒ ψ ⇒ ϕ ∧∧ ψ := exportation implSelf

def modusPonensAndTh1 : Γ ⊢ (ϕ ⇒ ψ) ∧∧ ϕ ⇒ ψ := importation implSelf

def modusPonensAndTh2 : Γ ⊢ ϕ ∧∧ (ϕ ⇒ ψ) ⇒ ψ := syllogism (axm (propAxm permutationConj)) modusPonensAndTh1

def modusPonensTh : Γ ⊢ ϕ ⇒ (ϕ ⇒ ψ) ⇒ ψ := exportation modusPonensAndTh2

def andElimLeftLeft : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ := syllogism (axm (propAxm weakeningConj)) (axm (propAxm weakeningConj))

def andElimLeftRight : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ψ := syllogism (axm (propAxm weakeningConj)) conjElimRight

def andElimRightLeft : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ ψ := syllogism conjElimRight (axm (propAxm weakeningConj))

def andElimRightRight : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ χ := syllogism conjElimRight conjElimRight

def orIntroRightLeft : Γ ⊢ ψ ⇒ (ϕ ∨∨ (ψ ∨∨ χ)) := syllogism (axm (propAxm weakeningDisj)) disjIntroRight

def orIntroRightRight : Γ ⊢ χ ⇒ (ϕ ∨∨ (ψ ∨∨ χ)) := syllogism disjIntroRight disjIntroRight

def orIntroLeftLeft : Γ ⊢ ϕ ⇒ (ϕ ∨∨ ψ) ∨∨ χ := syllogism (axm (propAxm weakeningDisj)) (axm (propAxm weakeningDisj))

def orIntroLeftRight : Γ ⊢ ψ ⇒ (ϕ ∨∨ ψ) ∨∨ χ := syllogism disjIntroRight (axm (propAxm weakeningDisj))

def conjIntroRule : Γ ⊢ ϕ → Γ ⊢ ψ → Γ ⊢ ϕ ∧∧ ψ :=
  fun p1 p2 => modusPonens p2 (modusPonens p1 conjIntro)

def conjIntroRule' : Γ ⊢ ϕ ∧∧ ψ → Nonempty (Γ ⊢ ϕ) ∧ Nonempty (Γ ⊢ ψ) :=
  fun p => And.intro (Nonempty.intro (modusPonens p (axm (propAxm weakeningConj)))) ((Nonempty.intro (modusPonens p conjElimRight)))

def conjImplIntroRule : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ χ → Γ ⊢ ϕ ⇒ ψ ∧∧ χ := fun p1 p2 =>
  syllogism (axm (propAxm contractionConj)) (importation (syllogism p2 (exportation (syllogism (axm (propAxm permutationConj))
                                                    (importation (syllogism p1 conjIntro))))))

def equivIntro : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ψ ⇒ ϕ → Γ ⊢ ϕ ⇔ ψ := conjIntroRule

def extraPremise : Γ ⊢ ϕ → Γ ⊢ ψ ⇒ ϕ := fun p => modusPonens p implProjLeft

def conjEquiv : Γ ⊢ ϕ ⇔ ϕ ∧∧ ϕ := conjIntroRule (axm (propAxm contractionConj)) (axm (propAxm weakeningConj))

def disjEquiv : Γ ⊢ ϕ ⇔ ϕ ∨∨ ϕ := conjIntroRule (axm (propAxm weakeningDisj)) (axm (propAxm contractionDisj))

def andAssoc1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ϕ ∧∧ (ψ ∧∧ χ) :=
  conjImplIntroRule andElimLeftLeft (conjImplIntroRule andElimLeftRight conjElimRight)

def andAssoc2 : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ (ϕ ∧∧ ψ) ∧∧ χ :=
  conjImplIntroRule (conjImplIntroRule (axm (propAxm weakeningConj)) andElimRightLeft) andElimRightRight

def andAssoc : Γ ⊢ Pattern.equivalence (ϕ ∧∧ (ψ ∧∧ χ)) ((ϕ ∧∧ ψ) ∧∧ χ) :=
  conjIntroRule andAssoc2 andAssoc1

def andAssocComm1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ χ ⇒ ψ ∧∧ (χ ∧∧ ϕ) :=
  conjImplIntroRule andElimLeftRight (conjImplIntroRule conjElimRight andElimLeftLeft)

def andAssocComm2 : Γ ⊢ ϕ ∧∧ (ψ ∧∧ χ) ⇒ ψ ∧∧ (ϕ ∧∧ χ) :=
  conjImplIntroRule (syllogism andAssoc2 andElimLeftRight)
                    (syllogism andAssoc2 (conjImplIntroRule andElimLeftLeft conjElimRight))

def extraPremiseConjIntroLeft1 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ∧∧ χ ⇒ ψ := fun p =>
  syllogism (axm (propAxm weakeningConj)) p

def extraPremiseConjIntroLeft2 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ χ ∧∧ ϕ ⇒ ψ := fun p =>
  syllogism conjElimRight p

def implConjElimLeft : Γ ⊢ ϕ ⇒ ψ ∧∧ χ → Γ ⊢ ϕ ⇒ ψ := fun p =>
  syllogism p (axm (propAxm weakeningConj))

def implConjElimRight : Γ ⊢ ϕ ⇒ ψ ∧∧ χ → Γ ⊢ ϕ ⇒ χ := fun p =>
  syllogism p conjElimRight

def conjImplComm : Γ ⊢ ϕ ∧∧ ψ ⇒ χ → Γ ⊢ ψ ∧∧ ϕ ⇒ χ := fun p =>
  syllogism (axm (propAxm permutationConj)) p

def importationComm : Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ψ ∧∧ ϕ ⇒ χ := fun p =>
  conjImplComm (importation p)

def extraPremiseConjIntroRight1 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ ϕ ∧∧ ψ := fun p =>
  conjImplIntroRule implSelf p

def extraPremiseConjIntroRight2 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ ψ ∧∧ ϕ := fun p =>
  conjImplIntroRule p implSelf

def andImplDistrib : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ χ ⇒ γ → Γ ⊢ ϕ ∧∧ χ ⇒ ψ ∧∧ γ := fun p1 p2 =>
  conjImplIntroRule (extraPremiseConjIntroLeft1 p1) (extraPremiseConjIntroLeft2 p2)

def andOrWeakening : Γ ⊢ ϕ ∧∧ (ϕ ∨∨ ψ) ⇒ ϕ := (axm (propAxm weakeningConj))

def andOrContraction : Γ ⊢ ϕ ⇒ ϕ ∧∧ (ϕ ∨∨ ψ) := conjImplIntroRule implSelf (axm (propAxm weakeningDisj))

def andOrWeakContr : Γ ⊢ ϕ ⇔ ϕ ∧∧ (ϕ ∨∨ ψ) := conjIntroRule andOrContraction andOrWeakening

def orAndWeakening : Γ ⊢ ϕ ∨∨ (ϕ ∧∧ ψ) ⇒ ϕ := syllogism (expansion (axm (propAxm weakeningConj))) (axm (propAxm contractionDisj))

def orAndContraction : Γ ⊢ ϕ ⇒ ϕ ∨∨ (ϕ ∧∧ ψ) := (axm (propAxm weakeningDisj))

def orAndWeakContr : Γ ⊢ ϕ ⇔ ϕ ∨∨ (ϕ ∧∧ ψ) := conjIntroRule orAndContraction orAndWeakening

def permuteHyps : Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ψ ⇒ ϕ ⇒ χ := fun p => exportation (importationComm p)

def modusPonensExtraHyp : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ⇒ ψ ⇒ χ → Γ ⊢ ϕ ⇒ χ := fun p1 p2 =>
  syllogism (extraPremiseConjIntroRight1 p1) (importation p2)

def implExtraHypRev : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) := fun p =>
  exportation (conjImplComm (syllogism (andImplDistrib p implSelf) modusPonensAndTh2))

def implConclTrans : Γ ⊢ ϕ ⇒ (ψ ⇒ χ) → Γ ⊢ χ ⇒ γ → Γ ⊢ ϕ ⇒ (ψ ⇒ γ) := fun p1 p2 =>
  exportation (syllogism (importation p1) p2)

def implOrExtraHyp : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ χ := fun p =>
  syllogism (syllogism (axm (propAxm permutationDisj)) (expansion p)) (axm (propAxm permutationDisj))

def extraPremiseDisjIntro1 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ϕ ∨∨ ψ ⇒ ψ := fun p =>
  syllogism (implOrExtraHyp p) (axm (propAxm contractionDisj))

def extraPremiseDisjIntro2 : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ ψ ∨∨ ϕ ⇒ ψ := fun p =>
  syllogism (expansion p) (axm (propAxm contractionDisj))

def disjIntroAtHyp : Γ ⊢ ϕ ⇒ χ → Γ ⊢ ψ ⇒ χ → Γ ⊢ ϕ ∨∨ ψ ⇒ χ := fun p1 p2 =>
  syllogism (expansion p2) (extraPremiseDisjIntro1 p1)

def orImplDistrib : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ χ ⇒ γ → Γ ⊢ ϕ ∨∨ χ ⇒ ψ ∨∨ γ := fun p1 p2 =>
  disjIntroAtHyp (syllogism p1 (axm (propAxm weakeningDisj))) (syllogism p2 disjIntroRight)

def andAddPremiseConclusion : Γ ⊢ ϕ ⇒ ψ → Γ ⊢ χ ∧∧ ϕ ⇒ χ ∧∧ ψ := fun p =>
  conjImplIntroRule (axm (propAxm weakeningConj)) (syllogism conjElimRight p)

def orAssoc1 : Γ ⊢ (ϕ ∨∨ ψ) ∨∨ χ ⇒ ϕ ∨∨ (ψ ∨∨ χ) :=
  disjIntroAtHyp (disjIntroAtHyp (axm (propAxm weakeningDisj)) orIntroRightLeft) orIntroRightRight

def orAssoc2 : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ (ϕ ∨∨ ψ) ∨∨ χ :=
  disjIntroAtHyp orIntroLeftLeft (disjIntroAtHyp orIntroLeftRight disjIntroRight)

def orAssoc : Γ ⊢ Pattern.equivalence (ϕ ∨∨ (ψ ∨∨ χ)) ((ϕ ∨∨ ψ) ∨∨ χ) :=
  conjIntroRule orAssoc2 orAssoc1

def orAssocComm1 : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ ψ ∨∨ (χ ∨∨ ϕ) :=
  syllogism (axm (propAxm permutationDisj)) orAssoc1

def orAssocComm2 : Γ ⊢ ϕ ∨∨ (ψ ∨∨ χ) ⇒ ψ ∨∨ (ϕ ∨∨ χ) :=
  syllogism orAssoc2 (syllogism (implOrExtraHyp (axm (propAxm permutationDisj))) orAssoc1)

def implDistrib : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ⇒ χ) :=
  exportation (exportation (modusPonensExtraHyp (modusPonensExtraHyp conjElimRight andElimLeftLeft) andElimLeftRight))

def exportationTh : Γ ⊢ (ϕ ∧∧ ψ ⇒ χ) ⇒ ϕ ⇒ ψ ⇒ χ :=
  exportation (exportation (modusPonensExtraHyp (conjImplIntroRule andElimLeftRight conjElimRight) andElimLeftLeft))

def importationTh : Γ ⊢ (ϕ ⇒ ψ ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ :=
  exportation (modusPonensExtraHyp andElimRightRight (modusPonensExtraHyp andElimRightLeft (axm (propAxm weakeningConj))))

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
  permuteHyps (disjIntroAtHyp (permuteHyps (axm (propAxm weakeningConj))) (permuteHyps conjElimRight))

def conjImplDisjExp : Γ ⊢ (ϕ ⇒ χ) ⇒ (ψ ⇒ χ) ⇒ (ϕ ∨∨ ψ ⇒ χ) := exportation conjImplDisj

def orFalse : Γ ⊢ ϕ ∨∨ ⊥ ⇒ ϕ := modusPonens (axm (propAxm exfalso)) (modusPonens implSelf conjImplDisjExp)

def extraPremiseConjTh : Γ ⊢ (ϕ ∧∧ (ϕ ⇒ ψ) ⇒ χ) ⇒ ϕ ∧∧ ψ ⇒ χ :=
  implExtraHypRev (andImplDistrib implSelf implProjLeft)

def implDistrib2 : Γ ⊢ ((ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ)) ⇒ ϕ ⇒ ψ ⇒ χ :=
  syllogism (syllogism (syllogism permuteHypsTh importationTh) extraPremiseConjTh) exportationTh

def implDistribEquiv : Γ ⊢ ((ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ)) ⇔ (ϕ ⇒ ψ ⇒ χ) :=
  conjIntroRule implDistrib2 implDistrib1

def implDistribRule1 : Γ ⊢ (ϕ ⇒ ψ) ⇒ (ϕ ⇒ χ) → Γ ⊢ ϕ ⇒ ψ ⇒ χ := fun p =>
  exportation (modusPonens (conjImplComm (importation p)) extraPremiseConjTh)

def syllogism_th : Γ ⊢ ϕ ⇒ (ψ ⇒ χ) → Γ ⊢ ϕ ⇒ (χ ⇒ γ) → Γ ⊢ ϕ ⇒ (ψ ⇒ γ) := fun p1 p2 =>
  implDistribRule1 (syllogism (modusPonens p1 implDistrib1) (modusPonens p2 implDistrib1))

def equivDistrib : Γ ⊢ ψ ⇒ ϕ → Γ ⊢ χ ⇒ γ → Γ ⊢ (ϕ ⇒ χ) ⇒ (ψ ⇒ γ) := fun p1 p2 =>
  exportation (modusPonensExtraHyp (modusPonensExtraHyp conjElimRight
  (syllogism_th (extraPremise p1) (axm (propAxm weakeningConj)))) (extraPremise p2))

def exp_extra_hyp : Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) → Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) := fun p =>
  exportation (exportation (syllogism andAssoc1 (importation p)))

def imp_extra_hyp : Γ ⊢ ϕ ⇒ (ψ ⇒ (χ ⇒ γ)) → Γ ⊢ ϕ ⇒ (ψ ∧∧ χ ⇒ γ) := fun p =>
  exportation (syllogism andAssoc2 (importation (importation p)))

def exFalsoAnd : Γ ⊢ ϕ ∧∧ ∼ϕ ⇒ ψ :=
  syllogism (andAddPremiseConclusion (axm (propAxm notationBot1))) (syllogism modusPonensAndTh2 (axm (propAxm exfalso)))

def contraposition : Γ ⊢ (ϕ ⇒ ψ) ⇒ (∼ψ ⇒ ∼ϕ) :=
  exportation (syllogism (exportation (syllogism (conjImplIntroRule (modusPonensExtraHyp conjElimRight andElimLeftLeft) andElimLeftRight) exFalsoAnd)) (axm (propAxm notationBot2)))

def contrapositionRule : Γ ⊢ (ϕ ⇒ ψ) → Γ ⊢ (∼ψ ⇒ ∼ϕ) := fun p =>
  modusPonens p contraposition

def dni : Γ ⊢ ϕ ⇒ ∼(∼ϕ) := syllogism (syllogism modusPonensTh (axm (propAxm notationBot2))) (contrapositionRule (axm (propAxm notationBot1)))

def dniNeg : Γ ⊢ (∼ϕ) ⇒ ∼(∼(∼ϕ)) := dni

def orContradict1 : Γ ⊢ ϕ ⇒ ϕ ∨∨ (ψ ∧∧ ∼ψ) := (axm (propAxm weakeningDisj))

def andContradict1 : Γ ⊢ (ϕ ∧∧ ψ) ∧∧ ∼ψ ⇒ ϕ := andElimLeftLeft

def nconsContra : Γ ⊢ ϕ ∧∧ χ ⇒ ψ → Γ ⊢ ϕ ⇒ ψ ∨∨ χ → Γ ⊢ ϕ ⇒ ψ := fun p1 p2 =>
  syllogism (conjImplIntroRule implSelf (syllogism p2 (disjIntroAtHyp implProjLeft (permuteHyps (exportation p1))))) modusPonensAndTh2

lemma subset_proof : Δ ⊆ Γ → Δ ⊢ ϕ → Nonempty (Γ ⊢ ϕ) :=
  by
    intro Hsubseteq Hdelta
    apply Nonempty.intro
    induction Hdelta with
    | premise Hvp => exact (premise (Set.mem_of_mem_of_subset Hvp Hsubseteq))
    | axm _ => constructor; assumption
    | modusPonens _ _ ih1 ih2 => exact (modusPonens ih1 ih2)
    | syllogism _ _ ih1 ih2 => exact (syllogism ih1 ih2)
    | exportation _ ih => exact (exportation ih)
    | importation _ ih => exact (importation ih)
    | expansion _ ih => exact (expansion ih)
    | generalization _ ih => exact (generalization ih)
    | framingLeft _ ih => exact (framingLeft ih)
    | framingRight _ ih => exact (framingRight ih)

lemma empty_proof : ∅ ⊢ ϕ → Nonempty (Γ ⊢ ϕ) :=
  by
    intro Hempty
    apply subset_proof (Set.empty_subset Γ)
    assumption

def set_proof_set : Type := ∀ (ϕ : Pattern 𝕊), ϕ ∈ Δ → Γ ⊢ ϕ

lemma set_conseq_proof (Hset : @set_proof_set 𝕊 Γ Δ) : Δ ⊢ ϕ → Nonempty (Γ ⊢ ϕ) :=
  by
    intro Hdelta
    apply Nonempty.intro
    induction Hdelta with
    | premise _ => apply Hset; assumption
    | axm _ => constructor; assumption
    | modusPonens _ _ ih1 ih2 => exact (modusPonens ih1 ih2)
    | syllogism _ _ ih1 ih2 => exact (syllogism ih1 ih2)
    | exportation _ ih => exact (exportation ih)
    | importation _ ih => exact (importation ih)
    | expansion _ ih => exact (expansion ih)
    | generalization _ ih => exact (generalization ih)
    | framingLeft _ ih => exact (framingLeft ih)
    | framingRight _ ih => exact (framingRight ih)

noncomputable instance {ϕ ψ : Pattern 𝕊} : Decidable (ϕ = ψ) := @default _ (Classical.decidableInhabited _)

noncomputable def usedPremises {ϕ : Pattern 𝕊} : Proof Γ ϕ → Finset (Pattern 𝕊)
  | premise Hvp => {ϕ}
  | axm _ => ∅
  | modusPonens p1 p2 | syllogism p1 p2 => usedPremises p1 ∪ usedPremises p2
  | exportation p | importation p | expansion p | generalization p | framingRight p | framingLeft p => usedPremises p

noncomputable def toFinitePremises {ϕ : Pattern 𝕊} (p : Proof Γ ϕ) : Proof (SetLike.coe (@usedPremises 𝕊 Γ ϕ p)) ϕ :=
  match p with
  | premise Hvp => have Helem : ϕ ∈ ↑(usedPremises (premise Hvp)) := by unfold usedPremises; simp
                   premise Helem
  | axm _ => by constructor; assumption
  | modusPonens p1 p2 => have Hincl1 : usedPremises p1 ⊆ usedPremises (modusPonens p1 p2) :=
                          by apply Finset.subset_union_left
                         let Hsubset1 := Classical.choice (subset_proof Hincl1 (toFinitePremises p1))
                         have Hincl2 : usedPremises p2 ⊆ usedPremises (modusPonens p1 p2) :=
                          by apply Finset.subset_union_right
                         let Hsubset2 := Classical.choice (subset_proof Hincl2 (toFinitePremises p2))
                         modusPonens Hsubset1 Hsubset2
  | syllogism p1 p2 => have Hincl1 : usedPremises p1 ⊆ usedPremises (syllogism p1 p2) :=
                        by apply Finset.subset_union_left
                       let Hsubset1 := Classical.choice (subset_proof Hincl1 (toFinitePremises p1))
                       have Hincl2 : usedPremises p2 ⊆ usedPremises (syllogism p1 p2) :=
                        by apply Finset.subset_union_right
                       let Hsubset2 := Classical.choice (subset_proof Hincl2 (toFinitePremises p2))
                       syllogism Hsubset1 Hsubset2
  | exportation p => exportation (toFinitePremises p)
  | importation p => importation (toFinitePremises p)
  | expansion p => expansion (toFinitePremises p)
  | generalization p => generalization (toFinitePremises p)
  | framingRight p => framingRight (toFinitePremises p)
  | framingLeft p => framingLeft (toFinitePremises p)

lemma finset_proof (p : Proof Γ ϕ) : ∃ (Ω : Finset (Pattern 𝕊)), SetLike.coe Ω ⊆ Γ /\ Nonempty (SetLike.coe Ω ⊢ ϕ) := by
  exists usedPremises p
  apply And.intro
  . induction p with
    | premise Hvp => unfold usedPremises; simp; assumption
    | axm _ => unfold usedPremises; simp
    | modusPonens p1 p2 ih1 ih2 | syllogism p1 p2 ih1 ih2 =>
      unfold usedPremises; simp; apply And.intro; assumption'
    | importation p ih | exportation p ih | expansion p ih | generalization p | framingRight p | framingLeft p => unfold usedPremises; assumption
  . apply Nonempty.intro
    apply toFinitePremises

end Proof

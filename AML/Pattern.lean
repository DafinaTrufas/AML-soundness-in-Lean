set_option autoImplicit false

structure Var where
  val : Nat
deriving DecidableEq

inductive Const (𝕊 : Type) where
| def : Const 𝕊
| val : 𝕊 → Const 𝕊

inductive Pattern (𝕊 : Type) where
| var : Var → Pattern 𝕊
| const : Const 𝕊 → Pattern 𝕊
| bot : Pattern 𝕊
| neg : Pattern 𝕊 -> Pattern 𝕊
| and : Pattern 𝕊 → Pattern 𝕊 → Pattern 𝕊
| or : Pattern 𝕊 → Pattern 𝕊 → Pattern 𝕊
| impl : Pattern 𝕊 → Pattern 𝕊 → Pattern 𝕊
| appl : Pattern 𝕊 → Pattern 𝕊 → Pattern 𝕊
| ex : Var → Pattern 𝕊 → Pattern 𝕊
| univ : Var → Pattern 𝕊 → Pattern 𝕊

namespace Pattern

variable {𝕊 : Type} (x : Var) (ϕ ψ χ : Pattern 𝕊)

notation "⊥" => bot

prefix:70 "∼" => neg

infixl:65 " ∧∧ " => and

infixl:65 " ∨∨ " => or

infixr:60 (priority := high) " ⇒ " => impl

infixl:80 " · " => appl

notation "∃∃" => ex

notation "∀∀" => univ

@[simp]
def equivalence := (ϕ ⇒ ψ) ∧∧ (ψ ⇒ ϕ)
infix:50 " ⇔ " => equivalence

@[simp]
def definedness := (const (Const.def)) · ϕ
notation "⌈" ϕ "⌉" => definedness ϕ

@[simp]
def totality := ∼⌈∼ϕ⌉
notation "⌊" ϕ "⌋" => totality ϕ

@[simp]
def equality := ⌊ϕ ⇔ ψ⌋
infix:50 " ≡ " => equality

@[simp]
def membership := ⌈var x ∧∧ ϕ⌉
infix:50 " ∈∈ " => membership

@[simp]
def occurs (x : Var) (ϕ : Pattern 𝕊) :=
  match ϕ with
  | var y => x = y
  | const _ => False
  | ⊥ => False
  | ∼ψ => occurs x ψ
  | ψ ∧∧ χ => occurs x ψ ∨ occurs x χ
  | ψ ∨∨ χ => occurs x ψ ∨ occurs x χ
  | ψ ⇒ χ => occurs x ψ ∨ occurs x χ
  | ψ·χ => occurs x ψ ∨ occurs x χ
  | ∃∃ y ψ => x.val = y.val ∨ occurs x ψ
  | ∀∀ y ψ => x.val = y.val ∨ occurs x ψ

end Pattern

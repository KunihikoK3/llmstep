-- import LftCM.Common
import Mathlib
import LeanCopilot
import Paperproof

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  /-introducing the assumption h' : b < a using the intro tactic. This moves b < a from the goal into a hypothesis named h'. The goal *now becomes* false.
  -/
  have : a < a := lt_trans h h'
  /-The have tactic is used to prove a new fact. The new fact is that a < a. This is done by using the transitivity of the less-than relation. The transitivity of the less-than relation states that if a < b and b < c, then a < c. In this case, h: a < b and h': b < a, so a < a.

  a < a is a contradiction, so the goal is now false.

  When you use *have* without providing a label, Lean uses the name *this*, providing a convenient way to refer back to it.
   -/
  apply lt_irrefl a this
  /-The final step is to apply lt_irrefl a to this : a < a using the apply tactic. This creates a contradiction, thus proving false.-/

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := fnlba x
  linarith


example : ¬FnHasUb fun x ↦ x := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  have : a < a + 1 := by linarith
  have h1 : a + 1 ≤ a := fnuba (a + 1)
  linarith




#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  contrapose! h'
  apply h
  exact h'




example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hmono
  have : f a ≤ f b := hmono h
  linarith


example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  -- Notice that we can prove the negation of a universally quantified statement by giving a counterexample.
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
   intro
   simp [f, Monotone]
  have h' : f 1 ≤ f 0 := le_refl _
  have h'' : 1 ≤ 0 := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith


end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  contrapose! h
  assumption

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  contrapose! h
  assumption

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  contrapose! h
  assumption

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  contrapose! h
  assumption

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  by_contra h'
  exact h' h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  contrapose! h
  apply h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

/-In classical logic, intuitionistic logic and similar logical systems, the *principle of explosion* (Latin: *ex falso* [sequitur] quodlibet, 'from falsehood, anything [follows]'; or ex contradictione [sequitur] quodlibet, 'from contradiction, anything [follows]'), or the principle of Pseudo-Scotus (falsely attributed to Duns Scotus), is the law according to which any statement can be proven from a contradiction.[1][2][3] That is, from a contradiction, any proposition (including its negation) can be inferred; this is known as deductive explosion.[4][5]
-/
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end

-- import LftCM.Common
import Mathlib
import LeanCopilot


section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  rw [inf_comm]

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  rw [inf_assoc]

example : x ⊔ y = y ⊔ x := by
  rw [sup_comm]

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  rw [sup_assoc]

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  simp

theorem absorb2 : x ⊔ x ⊓ y = x := by
  simp

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check sup_inf_left
#check sup_inf_right
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)
/-
[Lattice](https://en.wikipedia.org/wiki/Lattice_(order))
A lattice is an abstract structure studied in the mathematical subdisciplines of order theory and abstract algebra. It consists of a partially ordered set in which every pair of elements has a unique supremum (also called a least upper bound or join) and a unique infimum (also called a greatest lower bound or meet). An example is given by the power set of a set, partially ordered by inclusion, for which the supremum is the union and the infimum is the intersection. Another example is given by the natural numbers, partially ordered by divisibility, for which the supremum is the least common multiple and the infimum is the greatest common divisor.
-/

example: a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  symm

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  exact sup_inf_left a b c

example [DistribLattice α] (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  exact sup_inf_left a b c

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rwa [sub_nonneg]

example (h: 0 ≤ b - a) : a ≤ b := by
  rwa [sub_nonneg] at h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right h h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  exact dist_nonneg

end

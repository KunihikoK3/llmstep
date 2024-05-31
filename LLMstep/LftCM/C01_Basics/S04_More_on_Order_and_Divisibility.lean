-- import LftCM.Common
import Mathlib
import LeanCopilot
namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left



example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · simp_all only [le_min_iff,
       min_le_iff,
       le_refl,
       true_or,
       or_true,
       and_self]
  · simp_all only [le_min_iff,
       min_le_iff,
       le_refl,
       true_or,
       or_true,
       and_self]



theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  simp


#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h1 : |a| = |a - b + b| := by rw [sub_add_cancel]
  rw [h1]
  have h2 : |a - b + b| ≤ |a - b| + |b| := by apply abs_add
  linarith


end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      exact dvd_mul_right _ _
    · apply dvd_pow
      all_goals simp [*]
  · apply dvd_pow
    all_goals simp [*]
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  rw [Nat.gcd_comm]
end

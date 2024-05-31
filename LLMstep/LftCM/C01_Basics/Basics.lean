import Mathlib
import LeanCopilot
open Real

-- # Intro
-- Lean is a dependently-typed language

-- Every expression has a type, and `#check` can tell you the type

#check 2
#check 17 + 4
#check π
#check rexp 1

-- Types are expressions too!

#check ℕ
#check ℝ

-- We can also make our own expressions, and give them names
def myFavouriteNumber : ℕ := 7

def yourFavouriteNumber : ℕ := sorry
-- sorry works as a placeholder

#check myFavouriteNumber

-- or not give them a name
example : ℕ := 2

-- # But this isn't maths!

-- The type `Prop` contains `Prop`ositions...

#check 2 + 2 = 4
#check rexp 1 < π

-- ...including false propositions...
#check 2 + 2 = 5
-- ...and open questions
#check Irrational (rexp 1 + π)
#check myFavouriteNumber = yourFavouriteNumber

def MyDifficultProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)   -- this is the twin prime conjecture
def MyEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)
def MyVeryEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p   -- notice there is no constraint that p is prime

-- Key! If `p : Prop`, an expression of type `p` is a proof of `p`.

example : 2 + 2 = 4 := rfl
example : 2 + 2 ≠ 5 := by
 norm_num
example : ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry
-- Erdős-Strauss conjecture

example (n : ℕ) (hn : 2 ≤ n) :
  ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry

-- # How can we make these expressions?

-- Simple proof terms
example : True := trivial
example : 2 = 2 := rfl
example (a b : ℕ) : a + b = b + a := by
 rw [add_comm]

example (a b : ℕ) : a * b = b * a := Nat.mul_comm a b

theorem my_proof : MyVeryEasyProposition := fun n => ⟨n, le_rfl⟩
/-  In Lean, the constructor ⟨ , ⟩ is used to construct proofs of existential statements, where you need to provide a witness and a proof that the predicate holds for that witness. Consider proving that there exists a natural number whose square is 4. The proof in Lean would look like this:

example : ∃ n : ℕ, n * n = 4 :=⟨2, rfl⟩

-/
#print MyVeryEasyProposition

#check MyVeryEasyProposition
#check my_proof
-- my proposition "has type Proposition", or "is a proposition"
-- my proof "has type my proposition", or "has type ∀ n : ℕ, ∃ p, n ≤ p",
--    or "is a proof of ∀ n : ℕ, ∃ p, n ≤ p"

-- But just proof terms get ugly...
example (a b : ℕ) : a + a * b = (b + 1) * a :=
  (add_comm a (a * b)).trans ((mul_add_one a b).symm.trans (mul_comm a (b + 1)))



-- Very clever tactics
example (a b : ℕ) : a + a * b = (b + 1) * a := by ring

example : 2 + 2 ≠ 5 := by simp
example : 4 ^ 25 < 3 ^ 39 := by norm_num

open Nat

-- Simple tactics
example (a b : ℕ) : a + b = b + a := by exact Nat.add_comm a b
example : 3 = 3 := by rfl

/-
In Lean 4, the by exact tactic is used within a proof to indicate that the following expression is exactly the proof object required to close the current goal. The exact tactic takes a single argument, which is an expression that should have the same type as the goal it is meant to solve. Here's a simple example to illustrate the use of by exact:

theorem my_theorem : 2 + 2 = 4 :=
by exact rfl

In Lean, rfl has the type of the equality it is proving. Specifically, rfl proves that an expression is equal to itself. In the case of the theorem my_theorem, rfl is used to prove 2 + 2 = 4. The type of rfl in this context is 2 + 2 = 4, which matches the type of the goal in the theorem.

-/
#check add_mul (R := ℕ)

-- In practice we write tactic proofs, and write them with help of the infoview
example (a b : ℕ) : a + a * b = (b + 1) * a := by
  rw [add_mul b 1 a, one_mul a, add_comm a (a * b), mul_comm a b]
  --> S01_Calculating.lean has many examples and some more information about using `rw`

/- rw [H1, H2, ...]

If HN are equations that are hypotheses or theorems, rewrite the goal with them. Note that after rewriting, the tactic will attempt to close the goal using rfl
-/
theorem Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  -- The proof begins by defining \( p \) as the smallest prime factor (`minFac`) of the number \( \text{factorial}(n) + 1 \)
  let p := minFac (Nat.factorial n + 1)
  -- `factorial_pos _` proves that `factorial n > 0`.
  -- `Nat.succ_lt_succ <| factorial_pos _` then proves that `factorial n + 1 > 0 + 1`, or simply, `factorial n + 1 > 1`.
 -- Finally, `Nat.ne_of_gt <| Nat.succ_lt_succ <| factorial_pos _` uses the fact that `factorial n + 1 > 1` to conclude that `factorial n + 1 ≠ 1`.
  have f1 : factorial n + 1 ≠ 1 := Nat.ne_of_gt <| Nat.succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  --  Less or Equal Check. Let use an example of n=10. It shows that \( n \leq p \). The code proves this by contradiction, assuming the contrary and deriving a contradiction. Specifically, it assumes that if \( p \) were less than or equal to \( n \), then \( p \) would divide \( 10! \), and thus, it would have to divide 1 (from the equation \( p \) divides \( 3628800 + 1 \)), which is impossible for a prime.
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ factorial n := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  exact ⟨p, np, pp⟩


theorem Ugly_Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  have pp := minFac_prime (add_left_ne_self.2 (factorial_pos n).ne')
  ⟨_, le_of_not_le fun h => pp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_factorial pp.pos h)).2
    (minFac_dvd _)), pp⟩

/-
Propositions in Lean are essentially statements that can be true or false. They are represented as types, where a proposition is a type whose instances are proofs of that proposition.

Theorems in Lean are proven propositions. When you declare a theorem, you are not only stating the proposition but also providing a proof for it. Theorems are essentially instances of propositions that demonstrate their truth.

theorem simple_theorem : 2 + 2 = 4 := rfl

Here, simple_theorem is a theorem stating that 2 + 2 = 4. The proof is provided by rfl, which is a proof term in Lean that stands for reflexivity, indicating that both sides of the equation evaluate to the same value.

-/

#check Euclid_Thm
#check Ugly_Euclid_Thm
-- The proof doesn't matter
example : Euclid_Thm = Ugly_Euclid_Thm := by
  rfl
-- *to Lean*

  --> S02_Overview.lean has more examples of tactic proofs

-- Some tactics can self-replace
theorem Easy_Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by exact?

example (a b : ℕ) : a + a * b = (b + 1) * a := by
 rw [add_mul, one_mul]
 rw [Nat.mul_comm]
 rw [Nat.add_comm]

 def MySet : Set ℕ := { 1, 2 }
 example : 1 ∈ MySet := by
  rw [MySet]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, OfNat.one_ne_ofNat, or_false]
  -- simp is a powerful tactic that simplifies the goal as much as possible using various rules and lemmas. It can be used to simplify expressions, rewrite with definitions, and perform other simplifications to make the goal easier to prove.

/-
In Lean 4, #synth is a command used to synthesize or find an instance of a type class for a given type. It is a way to query the type class inference system to provide an instance that satisfies the constraints of a type class for a specific type. When you use #synth, Lean will attempt to find an instance that has been defined in the code or in the libraries that are in scope.

For example, finding an instance of Add for integers:
-/
#synth Add Int

-- Another example of #synth
--  Synthesizing an instance of Inhabited:
#synth Inhabited Bool

/-
In Lean 4, the protected keyword is used to modify the visibility of definitions and theorems within modules or namespaces. When a definition or theorem is declared with the protected modifier, it means that the name of this definition or theorem cannot be accessed directly from outside the module or namespace in which it is declared without specifying its full path. This is useful for encapsulating the internal details of a module while still allowing the use of its components within other parts of the same module or in derived modules.

For example, if you have a module named Foo with a protected definition bar, you cannot access bar simply by its name outside of Foo. Instead, you would need to use Foo.bar to refer to it, ensuring that the internal structure of Foo is respected by external users.

Here is a simple example of how protected is used in Lean 4:
-/
namespace Foo
protected def bar : Nat := 1
end Foo

#check Foo.bar  -- This will work
#check bar      -- This will result in an error because 'bar' is protected


-- # Some more difficult proofs
def myFactorial : ℕ → ℕ
| 0 => 1
| (n + 1) => (n + 1) * myFactorial n

#check (myFactorial : ℕ → ℕ)

-- Lean can compute too!
#eval myFactorial 10
-- sometimes useful for sanity-checking definitions

theorem myFactorial_add_one (n : ℕ) : myFactorial (n + 1) = (n + 1) * myFactorial n := rfl
theorem myFactorial_zero : myFactorial 0 = 1 := rfl

theorem myFactorial_pos (n : ℕ) : 0 < myFactorial n := by
  induction' n with n ih
  -- The `with n ih` clause names the induction hypothesis as ih for the inductive step, where ih states that the factorial of n is positive.
  · rw [myFactorial_zero]
    exact zero_lt_one
  · rw [succ_eq_add_one, myFactorial_add_one]
    apply mul_pos
    · exact succ_pos n
    · exact ih

/-
In Lean 4, induction' is a variant of the standard induction tactic used for performing proof by induction. This tactic is part of the set of tactics that have been slightly modified or renamed in Lean 4 compared to their counterparts in Lean 3, as part of the language's evolution and enhancement.
-/

-- In my opinion, induction below is more readable than induction' above
theorem myFactorial_pos' (n : ℕ) : 0 < myFactorial n := by
  induction n
  case zero =>
    rw [myFactorial_zero]
    simp
  case succ n ih =>
    rw [succ_eq_add_one, myFactorial_add_one]
    apply mul_pos
    · exact succ_pos n
    · exact ih

/-
In Lean 4, the apply tactic is used to reduce the original goal to one or more subgoals that correspond to the premises of the applied statement.

For instance, if you have a lemma hab : a → b and the current goal is to prove b, using apply hab will introduce a new subgoal to prove a. This is because apply uses the lemma to reduce the original goal (b) to a new goal (a) that, if proven, will satisfy the original goal due to the lemma.
-/
-- # Personal note: this scales!
open BigOperators

def upper_density (A : Set ℕ) : ℝ := sorry

-- first posed: Erdős-Graham <1980?
-- partial progress annals, 2003
-- arXiv: Bloom, Dec 2021
-- quanta: Jan 2022
-- Lean: Bloom - M., Jun 2022, 12k lines
theorem bloom (A : Set ℕ) (hA : 0 < upper_density A) :
  ∃ B : Finset ℕ, ↑B ⊆ A ∧ ∑ i in B, (1 / i : ℚ) = 1 := sorry

def diagonal_ramsey (k : ℕ) : ℕ := sorry

-- first posed: Erdős <1935?
-- partial progress annals: 2009
-- arXiv: Mar 2023
-- quanta: Apr 2023
-- Lean: M., within this month? 14k+
theorem campos_griffiths_morris_sahasrabudhe :
  ∃ c : ℝ, 0 < c ∧ ∀ k, diagonal_ramsey k ≤ (4 - c) ^ k := sorry

-- Expressions and types, every expression has a type
-- A proof has type given by what it's proved!

-- Useful tactics:
  -- rw
  -- exact
  -- apply
  -- simp
  -- induction

  -- ring, norm_num, positivity, linarith
  -- refine

-- More examples in S03, S04, S05, S06
--  curly braces
--  calc


-- # Footnotes

-- ## Dependently typed
#check Fin 10
#check Fin

example (n : ℕ) : Fintype.card (Fin n) = n := by simp

-- ## terminal simps
example (n : ℕ) : Fintype.card (Fin n) = n := by simp?

-- ## naming
-- https://leanprover-community.github.io/contribute/naming.html

-- ## hierarchy!
#check 3
#check 4 = 4
#check ℕ
#check Prop
#check Type
#check Type 1
#check Type 2

#check Type 0

-- myproof : myVeryEasyProposition : Prop : Type : Type 1 : Type 2 : Type 3 : ...

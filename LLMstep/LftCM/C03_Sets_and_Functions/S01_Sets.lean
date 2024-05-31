-- import Mathlib.Data.Set.Lattice
import Mathlib
import LeanCopilot
import Lean
import Paperproof
--import Tactic

-- .. _sets:
--
-- Sets
-- ----
--
-- .. index:: set operations
--
-- If ``α`` is any type, the type ``Set α`` consists of sets
-- of elements of ``α``.
-- This type supports the usual set-theoretic operations and relations.
-- For example, ``s ⊆ t`` says that ``s`` is a subset of ``t``,
-- ``s ∩ t`` denotes the intersection of ``s`` and ``t``,
-- and ``s ∪ t`` denotes their union.
-- The subset relation can be typed with ``\ss`` or ``\sub``,
-- intersection can be typed with ``\i`` or ``\cap``,
-- and union can be typed with ``\un`` or ``\cup``.
-- The library also defines the set ``univ``,
-- which consists of all the elements of type ``α``,
-- and the empty set, ``∅``, which can be typed as ``\empty``.
-- Given ``x : α`` and ``s : Set α``,
-- the expression ``x ∈ s`` says that ``x`` is a member of ``s``.
-- Theorems that mention set membership often include ``mem``
-- in their name.
-- The expression ``x ∉ s`` abbreviates ``¬ x ∈ s``.
-- You can type ``∈`` as ``\in`` or ``\mem`` and ``∉`` as ``\notin``.
--
-- .. index:: simp, tactics ; simp
--
-- One way to prove things about sets is to use ``rw``
-- or the simplifier to expand the definitions.
-- In the second example below, we use ``simp only``
-- to tell the simplifier to use only the list
-- of identities we give it,
-- and not its full database of identities.
-- Unlike ``rw``, ``simp`` can perform simplifications
-- inside a universal or existential quantifier.
-- If you step through the proof,
-- you can see the effects of these commands.
section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

-- In this example, we open the ``set`` namespace to have
-- access to the shorter names for the theorems.
-- But, in fact, we can delete the calls to ``rw`` and ``simp``
-- entirely:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

-- What is going on here is known as *definitional reduction*:
-- to make sense of the ``intro`` command and the anonymous constructors
-- Lean is forced to expand the definitions.
-- The following examples also illustrate the phenomenon:
theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

-- Due to a quirk of how Lean processes its input,
-- the first example fails if we replace ``theorem foo`` with ``example``.
-- This illustrates the pitfalls of relying on definitional reduction
-- too heavily.
-- It is often convenient,
-- but sometimes we have to fall back on unfolding definitions manually.
--
-- To deal with unions, we can use ``Set.union_def`` and ``Set.mem_union``.
-- Since ``x ∈ s ∪ t`` unfolds to ``x ∈ s ∨ x ∈ t``,
-- we can also use the ``cases`` tactic to force a definitional reduction.
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

-- Since intersection binds tighter than union,
-- the use of parentheses in the expression ``(s ∩ t) ∪ (s ∩ u)``
-- is unnecessary, but they make the meaning of the expression clearer.
-- The following is a shorter proof of the same fact:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

-- As an exercise, try proving the other inclusion:
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry
-- It might help to know that when using ``rintro``,
-- sometimes we need to use parentheses around a disjunctive pattern
-- ``h1 | h2`` to get Lean to parse it correctly.
--
-- The library also defines set difference, ``s \ t``,
-- where the backslash is a special unicode character
-- entered as ``\\``.
-- The expression ``x ∈ s \ t`` expands to ``x ∈ s ∧ x ∉ t``.
-- (The ``∉`` can be entered as ``\notin``.)
-- It can be rewritten manually using ``Set.diff_eq`` and ``dsimp``
-- or ``Set.mem_diff``,
-- but the following two proofs of the same inclusion
-- show how to avoid using them.
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

-- As an exercise, prove the reverse inclusion:
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  sorry
-- To prove that two sets are equal,
-- it suffices to show that every element of one is an element
-- of the other.
-- This principle is known as "extensionality,"
-- and, unsurprisingly,
-- the ``ext`` tactic is equipped to handle it.
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

-- Once again, deleting the line ``simp only [mem_inter_iff]``
-- does not harm the proof.
-- In fact, if you like inscrutable proof terms,
-- the following one-line proof is for you:
example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

-- Here is an even shorter proof,
-- using the simplifier:
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

-- An alternative to using ``ext`` is to use
-- the theorem ``Subset.antisymm``
-- which allows us to prove an equation ``s = t``
-- between sets by proving ``s ⊆ t`` and ``t ⊆ s``.
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

-- Try finishing this proof term:
example : s ∩ t = t ∩ s :=
    Subset.antisymm sorry sorry
-- Remember that you can replace `sorry` by an underscore,
-- and when you hover over it,
-- Lean will show you what it expects at that point.
--
-- Here are some set-theoretic identities you might enjoy proving:
example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  ext x
  simp

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  simp
  aesop

-- When it comes to representing sets,
-- here is what is going on underneath the hood.
-- In type theory, a *property* or *predicate* on a type ``α``
-- is just a function ``P : α → Prop``.
-- This makes sense:
-- given ``a : α``, ``P a`` is just the proposition
-- that ``P`` holds of ``a``.
-- In the library, ``Set α`` is defined to be ``α → Prop`` and ``x ∈ s`` is defined to be ``s x``.
-- In other words, sets are really properties, treated as objects.
--
-- The library also defines set-builder notation.
-- The expression ``{ y | P y }`` unfolds to ``(fun y ↦ P y)``,
-- so ``x ∈ { y | P y }`` reduces to ``P x``.
-- So we can turn the property of being even into the set of even numbers:
def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  apply Classical.em

-- You should step through this proof and make sure
-- you understand what is going on.
-- Try deleting the line ``rw [evens, odds]``
-- and confirm that the proof still works.
--
-- In fact, set-builder notation is used to define
--
-- - ``s ∩ t`` as ``{x | x ∈ s ∧ x ∈ t}``,
-- - ``s ∪ t`` as ``{x | x ∈ s ∨ x ∈ t}``,
-- - ``∅`` as ``{x | False}``, and
-- - ``univ`` as ``{x | True}``.
--
-- We often need to indicate the type of ``∅`` and ``univ``
-- explicitly,
-- because Lean has trouble guessing which ones we mean.
-- The following examples show how Lean unfolds the last
-- two definitions when needed. In the second one,
-- ``trivial`` is the canonical proof of ``True`` in the library.
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

-- As an exercise, prove the following inclusion.
-- Use ``intro n`` to unfold the definition of subset,
-- and use the simplifier to reduce the
-- set-theoretic constructions to logic.
-- We also recommend using the theorems
-- ``Nat.Prime.eq_two_or_odd`` and ``Nat.even_iff``.
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  -- rintro ⟨prime_n, n_gt_2⟩
  intro h
  rw [Nat.even_iff]
  intro hn
  rcases Nat.Prime.eq_two_or_odd h with h1 | h2
  . linarith
  . intro h3
    linarith



  -- exact Nat.Prime.eq_two_or_odd h hn

-- Be careful: it is somewhat confusing that the library has multiple versions
-- of the predicate ``Prime``.
-- The most general one makes sense in any commutative monoid with a zero element.
-- The predicate ``Nat.Prime`` is specific to the natural numbers.
-- Fortunately, there is a theorem that says that in the specific case,
-- the two notions agree, so you can always rewrite one to the other.
#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

-- .. index:: rwa, tactics ; rwa
--
-- The `rwa` tactic follows a rewrite with the assumption tactic.
example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

-- .. index:: bounded quantifiers
--
-- Lean introduces the notation ``∀ x ∈ s, ...``,
-- "for every ``x`` in ``s`` .,"
-- as an abbreviation for  ``∀ x, x ∈ s → ...``.
-- It also introduces the notation ``∃ x ∈ s, ...,``
-- "there exists an ``x`` in ``s`` such that .."
-- These are sometimes known as *bounded quantifiers*,
-- because the construction serves to restrict their significance
-- to the set ``s``.
-- As a result, theorems in the library that make use of them
-- often contain ``ball`` or ``bex`` in the name.
-- The theorem ``bex_def`` asserts that ``∃ x ∈ s, ...`` is equivalent
-- to ``∃ x, x ∈ s ∧ ...,``
-- but when they are used with ``rintro``, ``use``,
-- and anonymous constructors,
-- these two expressions behave roughly the same.
-- As a result, we usually don't need to use ``bex_def``
-- to transform them explicitly.
-- Here is are some examples of how they are used:
section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

-- See if you can prove these slight variations:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  rcases ssubt xs with xt
  constructor
  · apply h₀ x xt
  apply h₁ x xt

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _ , prime_x⟩
  use x
  exact And.intro (ssubt xs) prime_x

end

end

-- Indexed unions and intersections are
-- another important set-theoretic construction.
-- We can model a sequence :math:`A_0, A_1, A_2, \ldots` of sets of
-- elements of ``α``
-- as a function ``A : ℕ → Set α``,
-- in which case ``⋃ i, A i`` denotes their union,
-- and ``⋂ i, A i`` denotes their intersection.
-- There is nothing special about the natural numbers here,
-- so ``ℕ`` can be replaced by any type ``I``
-- used to index the sets.
-- The following illustrates their use.
section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

-- Parentheses are often needed with an
-- indexed union or intersection because,
-- as with the quantifiers,
-- the scope of the bound variable extends as far as it can.
--
-- Try proving the following identity.
-- One direction requires classical logic!
-- We recommend using ``by_cases xs : x ∈ s``
-- at an appropriate point in the proof.

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp
  constructor
  · intro h
    rcases h with h1 | h2
    · intro i
      exact Or.inr h1
    · intro i
      constructor
      · exact h2 i
  · intro h
    by_cases xs : x ∈ s
    · left
      exact xs
    · right
      intro i
      simp_all only [or_false]

-- Mathlib also has bounded unions and intersections,
-- which are analogous to the bounded quantifiers.
-- You can unpack their meaning with ``mem_iUnion₂``
-- and ``mem_iInter₂``.
-- As the following examples show,
-- Lean's simplifier carries out these replacements as well.
def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
/-LHS is a union of sets indexed by primes \( p \). Each set contains all \( x \) that are divisible by \( p^2 \).

RHS is the set of all \( x \) for which there exists a prime \( p \) such that \( p^2 \) divides \( x \).
-/
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
/-LHS is an intersection of sets indexed by primes \( p \). Each set contains all \( x \) that are *not* divisible by \( p \).
- RHS the set containing the single element \( x = 1 \).
-/
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

-- Try solving the following example, which is similar.
-- If you start typing ``eq_univ``,
-- tab completion will tell you that ``apply eq_univ_of_forall``
-- is a good way to start the proof.
-- We also recommend using the theorem ``Nat.exists_infinite_primes``.
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  -- ext x
  -- simp
  apply eq_univ_of_forall
  intro x
  simp
  -- rcases Nat.exists_infinite_primes x with ⟨p, hp, hpx⟩
  -- use p, hpx
  rcases Nat.exists_infinite_primes x with ⟨p, hp, hpx⟩
  exact ⟨p, hpx, hp⟩



end

-- Give a collection of sets, ``s : Set (Set α)``,
-- their union, ``⋃₀ s``, has type ``Set α``
-- and is defined as ``{x | ∃ t ∈ s, x ∈ t}``.
-- Similarly, their intersection, ``⋂₀ s``, is defined as
-- ``{x | ∀ t ∈ s, x ∈ t}``.
-- These operations are called ``sUnion`` and ``sInter``, respectively.
-- The following examples show their relationship to bounded union
-- and intersection.
section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end

-- In the library, these identities are called
-- ``sUnion_eq_biUnion`` and ``sInter_eq_biInter``.

-- some basic facts on rintro and rcases
/-The [rcases](https://lean-lang.org/blog/2024-4-4-lean-470/) tactic recursively case-splits a hypothesis, driven by a pattern written in a concise DSL that's inspired by Coq's [intro patterns](https://coq.inria.fr/doc/V8.18.0/refman/proof-engine/tactics.html#intro-patterns).
-/
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  rcases h with ⟨hp, hq⟩
  -- angle brackets are used for conjunctions
  exact ⟨hq, hp⟩
  -- note the order of the propositions in the angle brackets is reversed

theorem test (h : p1 ∨ p2 ∨ p3) : p3 ∨ p2 ∨ p1 := by
  rcases h with h1 | h2 | h3
  . right
    right
    exact h1
  . right
    left
    exact h2
  . left
    exact h3
  -- vertical bars are used for disjunctions
  -- all_goals simp [*]



example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

theorem even_or_odd (n : Nat) :
    (∃ half, n = 2 * half) ∨ (∃ half, n = 2 * half + 1) := by
  induction n with
  | zero => left; exists 0
  | succ n' ih =>
    rcases ih with ⟨half, prf⟩ | ⟨half, prf⟩
    . right
      exists half
      show Nat.succ n' = Nat.succ (2 * half)
      rw [prf]
    . left
      rw [prf]
      exists half + 1

  theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
refine ⟨hp, hq, hp⟩

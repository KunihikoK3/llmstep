import Mathlib
-- import LeanCopilot
-- import Lean
import LLMstep
-- .. _functions:
--
-- Functions
-- ---------
--
-- If ``f : α → β`` is a function and  ``p`` is a set of
-- elements of type ``β``,
-- the library defines ``preimage f p``, written ``f ⁻¹' p``,
-- to be ``{x | f x ∈ p}``.
-- The expression ``x ∈ f ⁻¹' p`` reduces to ``f x ∈ p``.
-- This is often convenient, as in the following example:
section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  simp [preimage_inter]

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, hy⟩

-- If ``s`` is a set of elements of type ``α``,
-- the library also defines ``image f s``,
-- written ``f '' s``,
-- to be ``{y | ∃ x, x ∈ s ∧ f x = y}``.
-- So a hypothesis  ``y ∈ f '' s`` decomposes to a triple
-- ``⟨x, xs, xeq⟩`` with ``x : α`` satisfying the hypotheses ``xs : x ∈ s``
-- and ``xeq : f x = y``.
-- The ``rfl`` tag in the ``rintro`` tactic (see :numref:`the_existential_quantifier`) was made precisely
-- for this sort of situation.
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

-- Notice also that the ``use`` tactic applies ``rfl``
-- to close goals when it can.
--
-- Here is another example:
example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

-- We can replace the line ``use x, xs`` by
-- ``apply mem_image_of_mem f xs`` if we want to
-- use a theorem specifically designed for that purpose.
-- But knowing that the image is defined in terms
-- of an existential quantifier is often convenient.
--
-- The following equivalence is a good exercise:
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    show x ∈ f ⁻¹' v
    show f x ∈ v
    exact h (mem_image_of_mem f xs)
  · intro h y ⟨x, xs, fxeq⟩
    -- show y ∈ v
    -- aesop -- alternative solution
    have h1 : f x ∈ v := by
      exact h xs
    -- aesop_subst fxeq -- alternative solution
    -- exact h1
    rwa [← fxeq]





-- It shows that ``image f`` and ``preimage f`` are
-- an instance of what is known as a *Galois connection*
-- between ``Set α`` and ``Set β``,
-- each partially ordered by the subset relation.
-- In the library, this equivalence is named
-- ``image_subset_iff``.
-- In practice, the right-hand side is often the
-- more useful representation,
-- because ``y ∈ f ⁻¹' t`` unfolds to ``f y ∈ t``
-- whereas working with ``x ∈ f '' s`` requires
-- decomposing an existential quantifier.
--
-- Here is a long list of set-theoretic identities for
-- you to enjoy.
-- You don't have to do all of them at once;
-- do a few of them,
-- and set the rest aside for a rainy day.
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
intro x
intro h1
-- simp_all only [preimage_image_eq, mem_image]
simp_all only [preimage_image_eq]

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, h, rfl⟩
  exact h

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y h1
  simp_all only [image_preimage_eq]

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y h1
  rw [image_preimage_eq u h]
  exact h1

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxeq⟩
  use x
  constructor
  · show f x ∈ u
    rw [fxeq]
    exact yu
  exact fxeq



example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, fxeq⟩
  use x, h xs, fxeq


example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x h1
  show f x ∈ v
  exact h h1

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, fxeq⟩
  constructor
  · use x, xs, fxeq
  · use x, xt, fxeq

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x1, xs, fxeq⟩, ⟨x2, xt, fxeq'⟩⟩
  have h1: x1 = x2 := h (by rw [fxeq, fxeq'])
  simp
  use x1
  constructor
  · constructor
    · exact xs
    · rwa [h1]
  · exact fxeq

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x1, xs, fseq⟩⟩
  aesop

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x1, xs, fseq⟩, y_not_in_ft⟩
  use x1
  constructor
  · constructor
    · exact xs
    · intro h
      subst fseq
      exact y_not_in_ft (mem_image_of_mem _ h)
  · exact fseq





example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x1, xs, fseq⟩, y_not_in_ft⟩
  use x1
  constructor
  · rw [@mem_diff]
    constructor
    · exact xs
    · simp_all
      subst fseq
      exact fun a => y_not_in_ft x1 a rfl
  · exact fseq

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro y ⟨h1, h2⟩
  -- have h3 : f y ∈ u := by exact h1
  -- have h4 : f y ∉ v := by exact h2
  rw [@mem_preimage]
  constructor
  · exact h1
  · exact h2

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro y ⟨h1, h2⟩
  have h3 : f y ∈ u := by exact h1
  have h4 : f y ∉ v := by exact h2
  rw [@mem_preimage]
  constructor
  · exact h3
  · exact h4

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun x ↦ id
/- **Direct Proof:** (from GPT-4)
   - Assume \( x \in f^{-1}(u) \setminus f^{-1}(v) \).
   - By definition, \( x \in f^{-1}(u) \) and \( x \notin f^{-1}(v) \).
   - This means \( f(x) \in u \) and \( f(x) \notin v \).
   - Therefore, \( f(x) \in u \setminus v \).
   - Hence, \( x \in f^{-1}(u \setminus v) \).

The proof `fun x ↦ id` succinctly captures this reasoning. It shows that any element \( x \) from \( f^{-1}(u) \setminus f^{-1}(v) \) naturally belongs to \( f^{-1}(u \setminus v) \) by definition. The identity function (`id`) just maps \( x \) to itself, which is all that's needed to demonstrate this subset relationship.-/



example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro h
    simp_all
    rcases h with ⟨⟨x, hx, rfl⟩, h'⟩
    exact ⟨x, ⟨hx, h'⟩, rfl⟩
  · rintro ⟨x, ⟨hx, h'⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, h'⟩



example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

-- You can also try your hand at the next group of exercises,
-- which characterize the behavior of images and preimages
-- with respect to indexed unions and intersections.
-- In the third exercise, the argument ``i : I`` is needed
-- to guarantee that the index set is nonempty.
-- To prove any of these, we recommend using ``ext`` or ``intro``
-- to unfold the meaning of an equation or inclusion between sets,
-- and then calling ``simp`` to unpack the conditions for membership.
variable {I : Type*} (A : I → Set α) (B : I → Set β)
/-A is a function that takes an index i from the type I and returns a set of type Set α. Therefore, A i is a set of type Set α for some index i.
-/
example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · rintro ⟨x, ⟨exists_i,fxeq⟩⟩
    rw [@exists_comm]
    -- This rewrites the goal using the commutativity of the existential quantifier, allowing us to switch the order of the quantifiers
    simp_all
    /-
    case h.mp.intro.intro
    α : Type u_1
    β : Type u_2
    f : α → β
    s t : Set α
    u v : Set β
    I : Type u_3
    A : I → Set α
    B : I → Set β
    y : β
    x : α
    exists_i : ∃ i, x ∈ A i
    fxeq : f x = y
    ⊢ ∃ b, (∃ x, b ∈ A x) ∧ f b = y  this goal should be stated as ∃ b, (∃ i, b ∈ A i) ∧ f b = y
    which makes it clearer that use x is the right tactic to use
    -/
    use x

  · rintro ⟨i, ⟨x, xAi, fxeq⟩⟩
    use x
    simp_all
    --exact
    exact ⟨i, xAi⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  rintro x h fxeq
  intro i
  exact ⟨x, h i, fxeq⟩


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, _ , fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

-- The library defines a predicate ``InjOn f s`` to say that
-- ``f`` is injective on ``s``.
-- It is defined as follows:
example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

-- The statement ``Injective f`` is provably equivalent
-- to ``InjOn f univ``.
-- Similarly, the library defines ``range f`` to be
-- ``{x | ∃y, f y = x}``,
-- so ``range f`` is provably equal to ``f '' univ``.
-- This is a common theme in Mathlib:
-- although many properties of functions are defined relative
-- to their full domain,
-- there are often relativized versions that restrict
-- the statements to a subset of the domain type.
--
-- Here is are some examples of ``InjOn`` and ``range`` in use:
section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

-- Try proving these:
example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro e
  calc
    x = sqrt (x ^ 2) := by simp_all
    _ = sqrt (y ^ 2) := by simp_all
    _ = y := by simp_all

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  intro e
  calc
    x = sqrt (x ^ 2) := by simp_all
    _ = sqrt (y ^ 2) := by simp_all
    _ = y := by simp_all

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, _, sqeq⟩
    rw [← sqeq]
    simp
    apply sqrt_nonneg
  · rintro ypos
    use y ^ 2
    simp
    constructor
    · exact pow_two_nonneg y
    · rw [sqrt_sq ypos]


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    exact pow_two_nonneg x
  · rintro ypos
    use sqrt y
    simp_all


end

-- To define the inverse of a function ``f : α → β``,
-- we will use two new ingredients.
-- First, we need to deal with the fact that
-- an arbitrary type in Lean may be empty.
-- To define the inverse to ``f`` at ``y`` when there is
-- no ``x`` satisfying ``f x = y``,
-- we want to assign a default value in ``α``.
-- Adding the annotation ``[Inhabited α]`` as a variable
-- is tantamount to assuming that ``α`` has a
-- preferred element, which is denoted ``default``.
-- Second, in the case where there is more than one ``x``
-- such that ``f x = y``,
-- the inverse function needs to *choose* one of them.
-- This requires an appeal to the *axiom of choice*.
-- Lean allows various ways of accessing it;
-- one convenient method is to use the classical ``choose``
-- operator, illustrated below.
section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

-- Given ``h : ∃ x, P x``, the value of ``Classical.choose h``
-- is some ``x`` satisfying ``P x``.
-- The theorem ``Classical.choose_spec h`` says that ``Classical.choose h``
-- meets this specification.
--
-- With these in hand, we can define the inverse function
-- as follows:
noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

-- The lines ``noncomputable theory`` and ``open Classical``
-- are needed because we are using classical logic in an essential way.
-- On input ``y``, the function ``inverse f``
-- returns some value of ``x`` satisfying ``f x = y`` if there is one,
-- and a default element of ``α`` otherwise.
-- This is an instance of a *dependent if* construction,
-- since in the positive case, the value returned,
-- ``Classical.choose h``, depends on the assumption ``h``.
-- The identity ``dif_pos h`` rewrites ``if h : e then a else b``
-- to ``a`` given ``h : e``,
-- and, similarly, ``dif_neg h`` rewrites it to ``b`` given ``h : ¬ e``.
-- The theorem ``inverse_spec`` says that ``inverse f``
-- meets the first part of this specification.
--
-- Don't worry if you do not fully understand how these work.
-- The theorem ``inverse_spec`` alone should be enough to show
-- that ``inverse f`` is a left inverse if and only if ``f`` is injective
-- and a right inverse if and only if ``f`` is surjective.
-- Look up the definition of ``LeftInverse`` and ``RightInverse``
-- by double-clicking or right-clicking on them in VS Code,
-- or using the commands ``#print LeftInverse`` and ``#print RightInverse``.
-- Then try to prove the two theorems.
-- They are tricky!
-- It helps to do the proofs on paper before
-- you start hacking through the details.
-- You should be able to prove each of them with about a half-dozen
-- short lines.
-- If you are looking for an extra challenge,
-- try to condense each proof to a single-line proof term.
variable (f : α → β)

open Function

/- see [proof](https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses)-/
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h x
    -- intro x  (I shortened the proof by merging intro x with intro h)
    simp only [inverse]
    split_ifs with h1
    · apply h
      exact Classical.choose_spec h1
    · simp_all
  · intro h x₁ x₂ h'
    -- intro x₁ x₂ (I shortened the proof by merging intro x₁ x₂ with intro h)
    -- intro h'
    rw [← h x₁, ← h x₂]
    congr


example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

-- We close this section with a type-theoretic statement of Cantor's
-- famous theorem that there is no surjective function from a set
-- to its power set.
-- See if you can understand the proof,
-- and then fill in the two lines that are missing.
section
variable {α : Type*}
open Function


/-**Theorem (Cantor):** For any function \( f: \alpha \to \text{Set} \, \alpha \), \( f \) is not surjective.

*Proof Outline*

1. *Assume for contradiction:* Assume that \( f \) is surjective.

2. *Define the set \( S \):* Let \( S \) be the set of all elements \( i \) in \( \alpha \) such that \( i \notin f(i) \).

3. *Use surjectivity:* Since \( f \) is surjective, there exists some \( j \in \alpha \) such that \( f(j) = S \).

4. *Derive a contradiction:* Show that \( j \in S \) leads to a contradiction.

-/
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    exact h₁
  have h₃ : j ∉ S := by
    rwa [← h]
  contradiction

-- COMMENTS: TODO: improve this
end
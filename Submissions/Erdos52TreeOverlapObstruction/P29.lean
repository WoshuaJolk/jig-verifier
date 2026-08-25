import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Submissions.Erdos52TreeOverlapObstruction.P29

private def upper (n : ℕ) : Finset ℕ :=
  (Finset.range n).image fun k => 3 * k + 1

private def lower (n : ℕ) : Finset ℕ :=
  {1, 2} ∪ (Finset.range n).image fun k => 9 * k + 2

private def crossSums (n : ℕ) : Finset ℕ :=
  (Finset.range n).image fun k => 9 * k + 4

private def scale (c : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => c * x

/--
Arbitrarily many first-separation sums at a `3`-valuation node can coincide
with sums internal to its lower child.  Thus sibling contributions at
different nodes cannot be added without an additional overlap argument.
-/
theorem proof :
    ∀ n : ℕ,
      (∀ x ∈ lower n, ¬3 ∣ x) ∧
      (∀ y ∈ upper n, ¬3 ∣ y) ∧
      (crossSums n).card = n ∧
      crossSums n ⊆ lower n + lower n ∧
      crossSums n ⊆ ({1} : Finset ℕ) + scale 3 (upper n) := by
  classical
  intro n
  have hthree_add_one (k : ℕ) : ¬3 ∣ 3 * k + 1 := by
    intro h
    obtain ⟨c, hc⟩ := h
    omega
  have hnine_add_two (k : ℕ) : ¬3 ∣ 9 * k + 2 := by
    intro h
    obtain ⟨c, hc⟩ := h
    omega
  constructor
  · intro x hx
    simp only [lower, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_image] at hx
    rcases hx with (rfl | rfl) | ⟨k, hk, rfl⟩
    · decide
    · decide
    · exact hnine_add_two k
  constructor
  · intro y hy
    simp only [upper, Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact hthree_add_one k
  constructor
  · dsimp only [crossSums]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a ha b hb hab
      change 9 * a + 4 = 9 * b + 4 at hab
      omega
  constructor
  · intro z hz
    simp only [crossSums, Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have htwo : 2 ∈ lower n := by simp [lower]
    have htail : 9 * k + 2 ∈ lower n := by
      simp only [lower, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_image]
      right
      exact ⟨k, hk, rfl⟩
    convert Finset.add_mem_add htwo htail using 1 <;> omega
  · intro z hz
    simp only [crossSums, Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have hone : 1 ∈ ({1} : Finset ℕ) := by simp
    have hupper : 3 * (3 * k + 1) ∈ scale 3 (upper n) := by
      simp only [scale, Finset.mem_image]
      refine ⟨3 * k + 1, ?_, ?_⟩
      simp only [upper, Finset.mem_image]
      · exact ⟨k, hk, rfl⟩
      · rfl
    convert Finset.add_mem_add hone hupper using 1 <;>
      simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega

end Submissions.Erdos52TreeOverlapObstruction.P29

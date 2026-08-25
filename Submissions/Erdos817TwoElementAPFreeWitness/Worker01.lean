import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos817TwoElementAPFreeWitness.Worker01

def subsetSums (A : Finset ℕ) : Set ℕ :=
  {x | ∃ B ⊆ A, ∑ a ∈ B, a = x}

def IsThreeAPFree (S : Set ℕ) : Prop :=
  ∀ x y z, x ∈ S → y ∈ S → z ∈ S → x + z = 2 * y → x = z

def Admissible (n N : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = n ∧
    IsThreeAPFree (subsetSums A)

lemma subset_pair_cases (B : Finset ℕ) (hB : B ⊆ {2, 3}) :
    B = ∅ ∨ B = {2} ∨ B = {3} ∨ B = {2, 3} := by
  by_cases h2 : 2 ∈ B <;> by_cases h3 : 3 ∈ B
  · right; right; right
    ext x
    constructor
    · intro hx
      have := hB hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl)
      · exact h2
      · exact h3
  · right; left
    ext x
    constructor
    · intro hx
      have hx' := hB hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · simp
      · exact (h3 hx).elim
    · simp
      intro hx
      rw [hx]
      exact h2
  · right; right; left
    ext x
    constructor
    · intro hx
      have hx' := hB hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact (h2 hx).elim
      · simp
    · simp
      intro hx
      rw [hx]
      exact h3
  · left
    ext x
    constructor
    · intro hx
      have hx' := hB hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact (h2 hx).elim
      · exact (h3 hx).elim
    · intro hx
      simp at hx

lemma mem_subsetSums_pair {x : ℕ} (hx : x ∈ subsetSums {2, 3}) :
    x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 5 := by
  rcases hx with ⟨B, hB, rfl⟩
  rcases subset_pair_cases B hB with rfl | rfl | rfl | rfl <;> norm_num

theorem proof : Admissible 2 3 := by
  refine ⟨{2, 3}, by decide, by decide, ?_⟩
  intro x y z hx hy hz hprogression
  have hx' := mem_subsetSums_pair hx
  have hy' := mem_subsetSums_pair hy
  have hz' := mem_subsetSums_pair hz
  omega

end Submissions.Erdos817TwoElementAPFreeWitness.Worker01

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Submissions.Erdos3UpToTwo.Worker26Direct

theorem proof :
    ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∀ k : ℕ, k ≤ 2 →
        ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  intro A hdiv k hk
  have hInf : Set.Infinite A := by
    intro hfinite
    apply hdiv
    letI : Finite A := hfinite.to_subtype
    exact Summable.of_finite
  by_cases hk0 : k = 0
  · subst k
    exact ⟨0, 1, by omega, by omega⟩
  have hkCases : k = 1 ∨ k = 2 := by omega
  obtain ⟨a, ha⟩ := hInf.nonempty
  rcases hkCases with rfl | rfl
  · refine ⟨a, 1, by omega, ?_⟩
    intro i hi
    have : i = 0 := by omega
    simpa [this] using ha
  · obtain ⟨b, hb, hba⟩ := hInf.exists_notMem_finset {a}
    have hne : b ≠ a := by simpa using hba
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨b, a - b, Nat.sub_pos_of_lt hlt, ?_⟩
      intro i hi
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl
      · simpa using hb
      · convert ha using 1 <;> omega
    · refine ⟨a, b - a, Nat.sub_pos_of_lt hgt, ?_⟩
      intro i hi
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl
      · simpa using ha
      · convert hb using 1 <;> omega

end Submissions.Erdos3UpToTwo.Worker26Direct

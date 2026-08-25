import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos345FirstPowerThreshold.Worker09Middle

def powerSubsetSums (k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ B : Finset ℕ,
    (∀ n ∈ B, 1 ≤ n) ∧ m = ∑ n ∈ B, n ^ k}

noncomputable def threshold (k : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∀ n ≥ m, n ∈ powerSubsetSums k}

theorem proof : threshold 1 = 1 := by
  apply Nat.sInf_upward_closed_eq_succ_iff
      (s := {m : ℕ | 1 ≤ m ∧ ∀ n ≥ m, n ∈ powerSubsetSums 1})
      (fun k₁ k₂ hk hk₁ ↦
        ⟨hk₁.1.trans hk, fun n hn ↦ hk₁.2 n (hk.trans hn)⟩)
      0 |>.mpr
  constructor
  · constructor
    · exact le_rfl
    · intro n hn
      refine ⟨{n}, ?_, by simp⟩
      intro x hx
      simp only [Finset.mem_singleton] at hx
      simpa [hx] using hn
  · simp

end Submissions.Erdos345FirstPowerThreshold.Worker09Middle

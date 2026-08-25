import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos961BaseWindowBound.Worker01

def HasRoughInEveryWindow (k n : ℕ) : Prop :=
  ∀ m ≥ k + 1, ∃ i ∈ Set.Ico m (m + n),
    i ∉ Nat.smoothNumbers (k + 1)

noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | HasRoughInEveryWindow k n}

theorem proof : HasRoughInEveryWindow 1 1 ∧ f 1 ≤ 1 := by
  have hwindow : HasRoughInEveryWindow 1 1 := by
    intro m hm
    use m
    constructor
    · simp
    · rw [Nat.mem_smoothNumbers]
      push Not
      intro hm0
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      exact ⟨p, (Nat.mem_primeFactorsList hm0).mpr ⟨hp, hpm⟩, hp.two_le⟩
  refine ⟨hwindow, ?_⟩
  exact Nat.sInf_le hwindow

end Submissions.Erdos961BaseWindowBound.Worker01

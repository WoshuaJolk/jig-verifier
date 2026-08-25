import Mathlib.Tactic

namespace Submissions.Erdos169BasicConventionWitnesses.Worker01

def IsAPFree (k : ℕ) (A : Set ℕ) : Prop :=
  (∀ n ∈ A, 1 ≤ n) ∧
    ∀ a d : ℕ, 0 < d → ∃ i < k, a + i * d ∉ A

def ForcesMonochromaticAP (k N : ℕ) : Prop :=
  ∀ color : ℕ → Bool, ∃ a d : ℕ,
    1 ≤ a ∧ 0 < d ∧ a + (k - 1) * d ≤ N ∧
      ∀ i < k, color (a + i * d) = color a

theorem proof : IsAPFree 3 {1} ∧ ForcesMonochromaticAP 1 1 := by
  constructor
  · constructor
    · simp
    · intro a d hd
      use 2
      constructor
      · omega
      · simp only [Set.mem_singleton_iff]
        omega
  · intro color
    exact ⟨1, 1, by omega, by omega, by omega, by simp⟩

end Submissions.Erdos169BasicConventionWitnesses.Worker01

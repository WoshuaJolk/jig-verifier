import Mathlib.Tactic

namespace Submissions.Erdos978RemainingDegreeReduction.Direct

theorem proof :
    ∀ k : ℕ, 3 < k → k < 9 →
      (¬ ∃ l : ℕ, k = 2 ^ l) →
      k = 5 ∨ k = 6 ∨ k = 7 := by
  intro k hk3 hk9 hpow
  interval_cases k
  · exact (hpow ⟨2, by norm_num⟩).elim
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact (hpow ⟨3, by norm_num⟩).elim

end Submissions.Erdos978RemainingDegreeReduction.Direct

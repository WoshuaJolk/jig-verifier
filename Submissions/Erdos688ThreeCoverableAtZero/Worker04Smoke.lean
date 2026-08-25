import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos688ThreeCoverableAtZero.Worker04Smoke

def Coverable (n : ℕ) (ε : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ ε < p ∧ p ≤ n ∧ a p ≡ m [MOD p]

theorem proof : Coverable 3 0 := by
  refine ⟨fun p => if p = 2 then 1 else 2, ?_⟩
  intro m hm1 hm3
  interval_cases m
  · exact ⟨2, Nat.prime_two, by norm_num, by norm_num, by simp [Nat.ModEq]⟩
  · exact ⟨3, Nat.prime_three, by norm_num, by norm_num, by simp [Nat.ModEq]⟩
  · exact ⟨2, Nat.prime_two, by norm_num, by norm_num, by simp [Nat.ModEq]⟩

end Submissions.Erdos688ThreeCoverableAtZero.Worker04Smoke

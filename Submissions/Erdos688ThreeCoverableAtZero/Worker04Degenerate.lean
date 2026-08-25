import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos688ThreeCoverableAtZero.Worker04Degenerate

def Coverable (n : ℕ) (ε : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ ε < p ∧ p ≤ n ∧ a p ≡ m [MOD p]

theorem proof : False → Coverable 3 0 :=
  False.elim

end Submissions.Erdos688ThreeCoverableAtZero.Worker04Degenerate

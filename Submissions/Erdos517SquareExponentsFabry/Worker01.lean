import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

namespace Submissions.Erdos517SquareExponentsFabry.Worker01

open Filter

def squareExponents (k : ℕ) : ℕ := k * k

def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Tendsto (fun k ↦ n k / (k : ℝ)) atTop atTop

theorem proof : HasFabryGaps squareExponents := by
  constructor
  · intro a b hab
    exact Nat.mul_self_lt_mul_self hab
  · have heq :
        (fun k : ℕ ↦ (squareExponents k : ℝ) / (k : ℝ)) =
          fun k : ℕ ↦ (k : ℝ) := by
      funext k
      simp only [squareExponents, Nat.cast_mul]
      by_cases hk : k = 0
      · simp [hk]
      · field_simp
    rw [heq]
    exact tendsto_natCast_atTop_atTop

end Submissions.Erdos517SquareExponentsFabry.Worker01

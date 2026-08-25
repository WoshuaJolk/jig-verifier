import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Submissions.Erdos12MixedRankObstruction.SharedCore

/-- Adding a genuinely new coprime factor `p` to moduli of the form `2 * P`
does not improve the complete-fiber packing ratio: the lcm and the product
half-bound both grow by exactly `p`, so density remains one half. -/
theorem proof :
    ∀ P p : ℕ,
      Nat.Coprime P p →
      Nat.lcm (2 * P) (2 * p) = 2 * (P * p) ∧
        2 * (P * ((2 * p) / 2)) = Nat.lcm (2 * P) (2 * p) := by
  intro P p hcop
  have hlcm : Nat.lcm (2 * P) (2 * p) = 2 * (P * p) := by
    rw [Nat.lcm_mul_left, hcop.lcm_eq_mul]
  constructor
  · exact hlcm
  · rw [hlcm]
    have hp : (2 * p) / 2 = p := by omega
    rw [hp]

end Submissions.Erdos12MixedRankObstruction.SharedCore

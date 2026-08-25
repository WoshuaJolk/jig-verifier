import Mathlib.Analysis.PSeries
import Mathlib.Order.Interval.Finset.Nat

/-!
# Local recursive-anchor bounds alone do not imply global decay

The even quotient sequence in the progression `1 mod 20` exactly saturates
each half-window count while retaining a divergent translated reciprocal sum.
-/

namespace Statements.Erdos12LocalBoundsInsufficient

abbrev statement : Prop :=
  (∀ n k : ℕ,
    (2 * n < 2 * k ∧
        2 * k < 2 * n + (1 + 20 * (2 * n))) ↔
      k ∈ Finset.Ioc n (21 * n)) ∧
  (∀ n : ℕ,
    (Finset.Ioc n (21 * n)).card =
      (1 + 20 * (2 * n)) / 2) ∧
  ¬ Summable (fun n : ℕ => (1 : ℝ) / (1 + 40 * n))

theorem target : statement := sorry

end Statements.Erdos12LocalBoundsInsufficient

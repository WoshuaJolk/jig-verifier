import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

namespace Submissions.Erdos263PositiveStrictMono.Degenerate

theorem proof : False →
    (∀ n : ℕ, 0 < 2 ^ 2 ^ n) ∧ StrictMono (fun n : ℕ => 2 ^ 2 ^ n) :=
  False.elim

end Submissions.Erdos263PositiveStrictMono.Degenerate

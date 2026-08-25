import Mathlib

namespace Statements.Erdos260IrrationalBinarySum

open Filter

abbrev statement : Prop :=
  ∀ a : ℕ → ℤ, ∀ s : ℝ,
    StrictMono a →
    Tendsto (fun n => (a n : ℝ) / n) atTop atTop →
    HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
    Irrational s

end Statements.Erdos260IrrationalBinarySum

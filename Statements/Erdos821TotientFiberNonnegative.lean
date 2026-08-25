import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

namespace Statements.Erdos821TotientFiberNonnegative

noncomputable def totientFiberCount (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

/-- Every totient-fiber cardinal, cast to the reals, is nonnegative. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 ≤ (totientFiberCount n : ℝ)

theorem target : statement := sorry

end Statements.Erdos821TotientFiberNonnegative

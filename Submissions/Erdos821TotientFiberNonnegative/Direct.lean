import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

namespace Submissions.Erdos821TotientFiberNonnegative.Direct

noncomputable def totientFiberCount (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

theorem proof :
    ∀ n : ℕ, 0 ≤ (totientFiberCount n : ℝ) := by
  intro n
  exact_mod_cast Nat.zero_le (totientFiberCount n)

end Submissions.Erdos821TotientFiberNonnegative.Direct

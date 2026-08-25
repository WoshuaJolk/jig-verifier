import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

open Nat Finset

namespace Submissions.Erdos394PrimeExact.Degenerate

noncomputable def t (k n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i)}

theorem proof :
    False → ∀ p : ℕ, p.Prime → t 2 p = p - 1 := by
  intro h
  exact h.elim

end Submissions.Erdos394PrimeExact.Degenerate

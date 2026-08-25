import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos454GapAtThree

noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else
    ⨅ i : {i : Fin n // 0 < (i : ℕ)},
      (n + i).nth Nat.Prime + (n - i).nth Nat.Prime

/-- The first positive excess in the symmetric-prime minimum occurs at the small index n=3 and has size two. -/
abbrev statement : Prop :=
  f 3 - 2 * Nat.nth Nat.Prime 3 = 2

theorem target : statement := sorry

end Statements.Erdos454GapAtThree

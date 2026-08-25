import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ENNReal
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Instances.ENat

open Filter

namespace Statements.Erdos454PrimeGraphLimsup

noncomputable local instance : ConditionallyCompleteLattice ℕ∞ :=
  WithTop.conditionallyCompleteLattice

/-- The minimum symmetric sum of indexed primes around index `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else
    ⨅ i : {i : Fin n // 0 < (i : ℕ)},
      (n + i).nth Nat.Prime + (n - i).nth Nat.Prime

/-- Erdős Problem 454: the excess of the least symmetric prime sum over
 twice the central prime has unbounded limsup. -/
abbrev statement : Prop :=
  limsup
    (fun n ↦ (f n - 2 * n.nth Nat.Prime : ℕ∞))
    atTop = ⊤

theorem target : statement := sorry

end Statements.Erdos454PrimeGraphLimsup

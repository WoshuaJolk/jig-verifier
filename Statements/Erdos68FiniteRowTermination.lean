import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Defs

open scoped BigOperators

namespace Statements.Erdos68FiniteRowTermination

/-- Every single row has an explicit terminating factorial denominator, and all
rows through `K` share the computable factorial position `K!`. -/
abbrev statement : Prop :=
  (∀ n : ℕ, 2 ≤ n →
    let d := n.factorial - 1
    d ∣ d.factorial) ∧
  ∀ K : ℕ, 2 ≤ K →
    let Q := K.factorial.factorial
    let A :=
      ∑ n ∈ Finset.Icc 2 K, Q / (n.factorial - 1)
    (∑ n ∈ Finset.Icc 2 K,
        (1 : ℚ) / (n.factorial - 1 : ℕ)) =
      (A : ℚ) / Q

theorem target : statement := sorry

end Statements.Erdos68FiniteRowTermination

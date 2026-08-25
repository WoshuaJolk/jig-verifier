import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open scoped BigOperators

namespace Statements.Erdos68ResidueCarryRecurrence

/-- Exact aggregate carry recurrences, positivity of every finite factorial
digit, and a criterion showing that a finite digit in `[1,m-2]` survives two
positive tails whose scaled sizes are below one. -/
abbrev statement : Prop :=
  (∀ m : ℕ, 4 ≤ m →
    let d : ℕ → ℕ := fun n => n.factorial - 1
    let A : ℕ → ℕ := fun k =>
      ∑ n ∈ Finset.Icc 2 k, k.factorial / d n
    let R : ℕ → ℝ := fun k =>
      ∑ n ∈ Finset.Icc 2 k,
        (k.factorial % d n : ℕ) / (d n : ℝ)
    let C : ℕ :=
      ∑ n ∈ Finset.Icc 2 (m - 1),
        (m * ((m - 1).factorial % d n)) / d n
    let S : ℕ → ℝ := fun k =>
      ∑ n ∈ Finset.Icc 2 k, (1 : ℝ) / d n
    (∀ n ∈ Finset.Icc 2 (m - 1),
      m.factorial % d n =
          (m * ((m - 1).factorial % d n)) % d n ∧
        m.factorial / d n =
          m * ((m - 1).factorial / d n) +
            (m * ((m - 1).factorial % d n)) / d n) ∧
    A m = m * A (m - 1) + C + 1 ∧
    R m =
      (m : ℝ) * R (m - 1) - C +
        1 / (m.factorial - 1 : ℕ) ∧
    ⌊(m.factorial : ℝ) * S m⌋ -
        (m : ℤ) * ⌊((m - 1).factorial : ℝ) * S (m - 1)⌋ =
      1 + ⌊(m : ℝ) *
        Int.fract (((m - 1).factorial : ℝ) * S (m - 1)) +
          1 / (m.factorial - 1 : ℕ)⌋ ∧
    1 ≤
      ⌊(m.factorial : ℝ) * S m⌋ -
        (m : ℤ) * ⌊((m - 1).factorial : ℝ) * S (m - 1)⌋) ∧
  (∀ m : ℕ, 3 ≤ m → ∀ y z u v : ℝ,
    0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
    let D : ℤ := ⌊y⌋ - (m : ℤ) * ⌊z⌋
    1 ≤ D → D ≤ (m : ℤ) - 2 →
    ⌊y + u⌋ - (m : ℤ) * ⌊z + v⌋ ≠ 0)

theorem target : statement := sorry

end Statements.Erdos68ResidueCarryRecurrence

import Mathlib.Order.Interval.Finset.Nat

namespace Statements.E488Unbounded

/-- Finite-scale densities of sets of multiples admit no universal amplification bound. -/
abbrev statement : Prop :=
  ∀ C : ℕ, ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    ∃ n m : ℕ, 0 < n ∧ (∀ a ∈ A, a ≤ n) ∧ n < m ∧
      C * m * ((Finset.Icc 1 n).filter (fun j => ∃ a ∈ A, a ∣ j)).card <
        n * ((Finset.Icc 1 m).filter (fun j => ∃ a ∈ A, a ∣ j)).card

theorem target : statement := by sorry

end Statements.E488Unbounded

import Mathlib.Order.Interval.Finset.Nat
namespace Statements.E488TripleRefuted
/-- The density of multiples can increase by a factor strictly greater than three. -/
abbrev statement : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    ∃ n m : ℕ, 0 < n ∧ (∀ a ∈ A, a ≤ n) ∧ n < m ∧
      3 * m * ((Finset.Icc 1 n).filter (fun j => ∃ a ∈ A, a ∣ j)).card <
        n * ((Finset.Icc 1 m).filter (fun j => ∃ a ∈ A, a ∣ j)).card

theorem target : statement := by sorry
end Statements.E488TripleRefuted

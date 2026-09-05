import Mathlib.Order.Interval.Finset.Nat

namespace Statements.ErdosMultiplesFifthRange

abbrev statement : Prop := ∀ A : Finset ℕ, A.Nonempty → ∀ n m : ℕ,
    (∀ a ∈ A, n < 5 * a ∧ a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesFifthRange

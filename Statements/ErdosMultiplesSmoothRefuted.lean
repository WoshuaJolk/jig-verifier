import Mathlib.Order.Interval.Finset.Nat

namespace Statements.ErdosMultiplesSmoothRefuted

/-- The negation of the full density-doubling conjecture for sets of multiples. -/
abbrev statement : Prop := ¬ (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card)

theorem target : statement := sorry

end Statements.ErdosMultiplesSmoothRefuted

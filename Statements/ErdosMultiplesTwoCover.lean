import Mathlib.Order.Interval.Finset.Nat

namespace Statements.ErdosMultiplesTwoCover
open Finset

abbrev statement : Prop := ∀ A : Finset ℕ, 0 ∉ A → ∀ a b : ℕ, a ∈ A → a ≤ b →
    (∀ c ∈ A, a ∣ c ∨ b ∣ c) → ∀ n m : ℕ,
    (∀ c ∈ A, c ≤ n) → n < m →
    n * ((Icc 1 m).filter (fun k => ∃ c ∈ A, c ∣ k)).card <
      2 * m * ((Icc 1 n).filter (fun k => ∃ c ∈ A, c ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesTwoCover

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.ErdosMultiplesTwoBases

abbrev statement : Prop := ∀ p q : ℕ, 0 < p → 1 < q → p.Coprime q →
    ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∀ a ∈ A, ∃ e f : ℕ, a = p ^ e * q ^ f) → ∀ n m : ℕ,
    (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesTwoBases

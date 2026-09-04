import Mathlib.Order.Interval.Finset.Nat

namespace Statements.ErdosMultiplesLocalRefuted

abbrev statement : Prop := ¬ (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ∃ f : ℕ → ℕ,
        (∀ k ∈ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k),
          ∃ a ∈ A, ∃ s : ℕ, a ∣ k ∧ f k = a * s ∧ 1 ≤ s ∧ a * s ≤ n ∧
            s * m ≤ (k / a) * n + m ∧ (k / a) * n ≤ s * m + m) ∧
        (∀ d : ℕ,
          n * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
            (fun k => f k = d)).card < 2 * m))

theorem target : statement := sorry

end Statements.ErdosMultiplesLocalRefuted

import Mathlib.Order.Interval.Finset.Nat

namespace Statements.ErdosMultiplesStaticPeelingDead

abbrev statement : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    (∀ b ∈ A, ∀ c ∈ A, b ∣ c → b = c) ∧
    ∀ a ∈ A, ∃ n m : ℕ, (∀ b ∈ A, b ≤ n) ∧ n < m ∧
      n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ A, b ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ A, b ∣ k)).card ∧
      2 * m * ((Finset.Icc 1 n).filter
        (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card <
        n * ((Finset.Icc 1 m).filter
          (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesStaticPeelingDead

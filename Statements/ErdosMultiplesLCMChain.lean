import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.ErdosMultiplesLCMChain

abbrev statement : Prop := ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∃ L : List ℕ, L.toFinset = A ∧
      ∀ (pre : List ℕ) (a b : ℕ) (rest : List ℕ),
        L = pre ++ a :: b :: rest →
        ∀ c ∈ rest, Nat.lcm a b ∣ Nat.lcm a c) → ∀ n m : ℕ,
    (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesLCMChain

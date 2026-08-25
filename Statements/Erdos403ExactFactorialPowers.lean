import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos403ExactFactorialPowers

abbrev statement : Prop :=
  ∀ (m : ℕ) (s : Finset ℕ),
    (s.Nonempty ∧ (∀ a ∈ s, 1 ≤ a) ∧ 2 ^ m = s.sum Nat.factorial) ↔
      (m = 0 ∧ s = {1}) ∨
      (m = 1 ∧ s = {2}) ∨
      (m = 3 ∧ s = {2, 3}) ∨
      (m = 5 ∧ s = {2, 3, 4}) ∨
      (m = 7 ∧ s = {2, 3, 5})

theorem target : statement := sorry

end Statements.Erdos403ExactFactorialPowers

import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingSingleton — the one-generator case of Erdős #488

The instance `A = {a}` of `Statements.ErdosMultiplesDoubling.statement`. This is the case in
which the constant `2` is sharp (`n = 2a - 1`, `m = 2a`), and it is the boundary
instantiation used to smoke-test the verifier for the parent problem.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSingleton

/-- For every `a ≥ 1`, every `n ≥ a` and every `m > n`,
`n * #{k ∈ [1,m] : a ∣ k} < 2 * m * #{k ∈ [1,n] : a ∣ k}`. Written with the same
`Finset.filter` over `∃ a ∈ A, a ∣ k` as the parent statement, with `A = {a}`. -/
abbrev statement : Prop :=
  ∀ a : ℕ, 0 < a → ∀ n m : ℕ, a ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSingleton

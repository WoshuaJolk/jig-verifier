import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical Filter
open scoped BigOperators

/-!
# Erdős problem 1200

Can all initial integer intervals eventually be covered by one residue class
for each prime in a finite set whose reciprocal sum is uniformly bounded?
-/

namespace Statements.Erdos1200BoundedPrimeCover

abbrev statement : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ᶠ x : ℝ in atTop,
      ∃ S : Finset ℕ, ∃ a : ℕ → ℕ,
        (∀ p ∈ S, p.Prime) ∧
          (∀ p ∈ S, p < x) ∧
            (∑ p ∈ S, (1 : ℝ) / p < C) ∧
              ∀ n : ℕ, n < x → ∃ p ∈ S, a p ≡ n [MOD p]

theorem target : statement := sorry

end Statements.Erdos1200BoundedPrimeCover

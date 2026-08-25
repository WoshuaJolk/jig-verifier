import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card

/-!
# Erdős problem 672

No coprime positive arithmetic progression of length at least four is
conjectured to have a perfect-power product.
-/

open scoped BigOperators

namespace Statements.Erdos672APProductNotPerfectPower

def IsAPOfLengthWith (s : Set ℕ) (length : ℕ∞) (first difference : ℕ) : Prop :=
  ENat.card s = length ∧
    s = {first + i • difference | (i : ℕ) (_ : i < length)}

def HoldsAt (k exponent : ℕ) : Prop :=
  ∀ s : Finset ℕ, s.card = k →
    ∀ first : ℕ, first > 0 →
      ∀ difference : ℕ, difference > 0 →
        first.gcd difference = 1 →
          IsAPOfLengthWith s k first difference →
            ∀ q : ℕ, (∏ i ∈ s, i) ≠ q ^ exponent

abbrev statement : Prop :=
  ∀ k exponent : ℕ, exponent > 1 → k ≥ 4 → HoldsAt k exponent

theorem target : statement := sorry

end Statements.Erdos672APProductNotPerfectPower

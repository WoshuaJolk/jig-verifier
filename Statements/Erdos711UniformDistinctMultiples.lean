import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős problem 711

Uniformly in the left endpoint `m`, can an interval of length
`n^(1+ε)` contain distinct representatives divisible by `1, ..., n`?
-/

namespace Statements.Erdos711UniformDistinctMultiples

def HasDistinctMultiples (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ k : Fin n,
      m < a k ∧ a k ≤ m + L ∧ (k.val + 1) ∣ a k

abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, ∃ L : ℕ,
        HasDistinctMultiples n m L ∧
          (L : ℝ) ≤ Real.rpow n (1 + ε)

theorem target : statement := sorry

end Statements.Erdos711UniformDistinctMultiples

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Multiset.Sum

namespace Statements.E312ExponentialApproximation

noncomputable def mass (A : Multiset ℕ) : ℝ :=
  (A.map fun n : ℕ => (n : ℝ)⁻¹).sum

/-- Erdős 312 as stated on erdosproblems.com/312: positive integer multisets,
with a cardinality threshold allowed to depend on K and a strict lower bound. -/
def statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, 1 < K → ∃ N₀ : ℕ,
    ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → N₀ ≤ A.card → K < mass A →
      ∃ S : Multiset ℕ, S ≤ A ∧
        1 - Real.exp (-(c * K)) < mass S ∧ mass S ≤ 1

end Statements.E312ExponentialApproximation

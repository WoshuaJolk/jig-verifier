import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped Topology

namespace Statements.Erdos538SharpReciprocalConstant

open scoped Classical in
/-- The representations `m = p * a` with `p` prime and `a ∈ A`. -/
def representations (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ A).filter
    (fun pa ↦ Nat.Prime pa.1 ∧ m = pa.1 * pa.2)

/-- `A ⊆ {1, …, N}` and every `m` has at most `r` representations `m = p a`. -/
def Admissible (r N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    ∀ m : ℕ, (representations A m).card ≤ r

/-- The reciprocal sum of `A`. -/
def reciprocalMass (A : Finset ℕ) : ℚ :=
  ∑ a ∈ A, (1 : ℚ) / a

/-- The largest reciprocal mass among admissible subsets of `{1, …, N}`. -/
noncomputable def maxMass (r N : ℕ) : ℝ :=
  sSup ((fun A ↦ (reciprocalMass A : ℝ)) ''
    {A : Finset ℕ | Admissible r N A})

/-- Sharp-constant form of Erdős Problem 538: for every fixed `r ≥ 2`, the normalized extremal reciprocal mass tends to a positive constant. -/
abbrev statement : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    ∃ c : ℝ, 0 < c ∧
      Tendsto
        (fun N : ℕ ↦
          maxMass r N * Real.log (Real.log N) / Real.log N)
        atTop (𝓝 c)

theorem target : statement := sorry

end Statements.Erdos538SharpReciprocalConstant

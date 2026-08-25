import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos538ExtremumAttained

open scoped Classical

def representations (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ A).filter
    (fun pa ↦ Nat.Prime pa.1 ∧ m = pa.1 * pa.2)

def Admissible (r N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    ∀ m : ℕ, (representations A m).card ≤ r

def reciprocalMass (A : Finset ℕ) : ℚ :=
  ∑ a ∈ A, (1 : ℚ) / a

noncomputable def maxMass (r N : ℕ) : ℝ :=
  sSup ((fun A ↦ (reciprocalMass A : ℝ)) ''
    {A : Finset ℕ | Admissible r N A})

/-- For each finite box and cap, the supremum defining the exact extremal reciprocal mass is attained by an admissible finite set. -/
abbrev statement : Prop :=
  ∀ r N : ℕ, ∃ A : Finset ℕ,
    Admissible r N A ∧
      maxMass r N = (reciprocalMass A : ℝ)

theorem target : statement := sorry

end Statements.Erdos538ExtremumAttained

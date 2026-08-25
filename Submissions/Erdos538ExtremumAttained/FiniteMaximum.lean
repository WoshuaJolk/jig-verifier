import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Submissions.Erdos538ExtremumAttained.FiniteMaximum

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

theorem proof :
    ∀ r N : ℕ, ∃ A : Finset ℕ,
      Admissible r N A ∧
        maxMass r N = (reciprocalMass A : ℝ) := by
  intro r N
  let S : Set ℝ :=
    (fun A ↦ (reciprocalMass A : ℝ)) ''
      {A : Finset ℕ | Admissible r N A}
  have hadm_finite : {A : Finset ℕ | Admissible r N A}.Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (Finset.range (N + 1)).powerset)
    intro A hA
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro a ha
    exact Finset.mem_range.mpr (by
      have := (hA.1 a ha).2
      omega)
  have hS_finite : S.Finite :=
    hadm_finite.image fun A ↦ (reciprocalMass A : ℝ)
  have hempty : Admissible r N ∅ := by
    constructor
    · simp
    · intro m
      simp [representations]
  have hS_nonempty : S.Nonempty :=
    ⟨0, ∅, hempty, by simp [reciprocalMass]⟩
  have hmax : sSup S ∈ S :=
    hS_nonempty.csSup_mem hS_finite
  obtain ⟨A, hA, hmass⟩ := hmax
  exact ⟨A, hA, by simpa [maxMass, S] using hmass.symm⟩

end Submissions.Erdos538ExtremumAttained.FiniteMaximum

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.GroupTheory.Commutator.Basic

namespace Submissions.Erdos117BFCExactMaximumToBound.Control

open Subgroup

universe u

def ConjugacyBound (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ x : G, Nat.card {y : G // IsConj x y} ≤ r

def IsBFCNumber (G : Type u) [Group G] (n : ℕ) : Prop :=
  ConjugacyBound G n ∧ ∃ x : G, Nat.card {y : G // IsConj x y} = n

/-- Must-fail anti-restatement control with an intentional extra premise. -/
theorem proof :
    False →
      ∀ (G : Type u) (_ : Group G) (_ : Finite G) (r : ℕ),
        (∀ n : ℕ, 1 ≤ n → IsBFCNumber G n →
          (Nat.card (commutator G) : ℝ) ≤
            (n : ℝ) ^ ((3 + 5 * Real.logb 2 n) / 2)) →
        ConjugacyBound G r →
        (Nat.card (commutator G) : ℝ) ≤
          (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2) := by
  intro h
  exact h.elim

end Submissions.Erdos117BFCExactMaximumToBound.Control

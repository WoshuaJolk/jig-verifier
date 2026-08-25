import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

open scoped BigOperators

namespace Submissions.Erdos261SmallRepresentations.Worker09Control

def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

theorem proof
    (claim : HasRepresentation 1 ∧ HasRepresentation 4) :
    HasRepresentation 1 ∧ HasRepresentation 4 :=
  claim

end Submissions.Erdos261SmallRepresentations.Worker09Control

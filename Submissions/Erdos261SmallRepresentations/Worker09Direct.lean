import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace Submissions.Erdos261SmallRepresentations.Worker09Direct

def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

theorem proof : HasRepresentation 1 ∧ HasRepresentation 4 := by
  constructor
  · refine ⟨{3, 6, 8}, by decide, ?_, by norm_num⟩
    norm_num
  · refine ⟨{5, 6}, by decide, ?_, by norm_num⟩
    norm_num

end Submissions.Erdos261SmallRepresentations.Worker09Direct

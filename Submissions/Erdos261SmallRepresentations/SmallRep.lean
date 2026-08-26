import Mathlib

open scoped BigOperators

namespace Submissions.Erdos261SmallRepresentations.SmallRep

/-- Local copy of the canonical predicate: `n` is represented by at least two
distinct positive indices in the Erdős--Graham equation. -/
def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

theorem proof : HasRepresentation 1 ∧ HasRepresentation 4 := by
  constructor
  · refine ⟨{3, 6, 8}, ?_, ?_, ?_⟩
    · decide
    · decide
    · norm_num [Finset.sum_insert, Finset.mem_insert]
  · refine ⟨{5, 6}, ?_, ?_, ?_⟩
    · decide
    · decide
    · norm_num [Finset.sum_insert, Finset.mem_insert]

end Submissions.Erdos261SmallRepresentations.SmallRep

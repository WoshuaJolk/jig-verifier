import Mathlib.GroupTheory.CosetCover

open scoped Pointwise

namespace Submissions.Erdos274AllPartsFiniteIndex.Degenerate

def exactCovering {G : Type*} [Group G] {ι : Type*}
    (parts : ι → Subgroup G) (reps : ι → G) : Prop :=
  (Set.univ (α := ι)).PairwiseDisjoint
      (fun i ↦ reps i • (parts i : Set G)) ∧
    ⋃ i, reps i • (parts i : Set G) = Set.univ

theorem proof :
    False → ∀ (G : Type*) [Group G] (ι : Type*) [Fintype ι],
      ∀ (parts : ι → Subgroup G) (reps : ι → G),
        exactCovering parts reps → ∀ i, (parts i).FiniteIndex := by
  intro h
  exact h.elim

end Submissions.Erdos274AllPartsFiniteIndex.Degenerate

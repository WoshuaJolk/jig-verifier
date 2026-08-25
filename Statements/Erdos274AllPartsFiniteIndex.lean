import Mathlib.GroupTheory.CosetCover

open scoped Pointwise

namespace Statements.Erdos274AllPartsFiniteIndex

def exactCovering {G : Type*} [Group G] {ι : Type*}
    (parts : ι → Subgroup G) (reps : ι → G) : Prop :=
  (Set.univ (α := ι)).PairwiseDisjoint
      (fun i ↦ reps i • (parts i : Set G)) ∧
    ⋃ i, reps i • (parts i : Set G) = Set.univ

/-- Every subgroup occurring in a finite exact coset covering has finite index. -/
abbrev statement : Prop :=
  ∀ (G : Type*) [Group G] (ι : Type*) [Fintype ι],
    ∀ (parts : ι → Subgroup G) (reps : ι → G),
      exactCovering parts reps → ∀ i, (parts i).FiniteIndex

theorem target : statement := sorry

end Statements.Erdos274AllPartsFiniteIndex

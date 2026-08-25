import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.Index

open scoped Pointwise Cardinal

namespace Statements.Erdos274HerzogSchonheim

/-- A finite family of left cosets is an exact covering when its members are pairwise disjoint and their union is the whole group. -/
def exactCovering {G : Type*} [Group G] {ι : Type*}
    (parts : ι → Subgroup G) (reps : ι → G) : Prop :=
  (Set.univ (α := ι)).PairwiseDisjoint
      (fun i ↦ reps i • (parts i : Set G)) ∧
    ⋃ i, reps i • (parts i : Set G) = Set.univ

/-- The Herzog–Schönheim conjecture (Erdős Problem 274): a nontrivial finite exact coset covering has two subgroups of equal index. -/
abbrev statement : Prop :=
  ∀ (G : Type*) [Group G], 1 < ENat.card G →
    ∀ (ι : Type*) [Fintype ι],
      ∀ (parts : ι → Subgroup G) (reps : ι → G),
        exactCovering parts reps → 1 < Fintype.card ι →
          ∃ i j, i ≠ j ∧ (parts i).index = (parts j).index

theorem target : statement := sorry

end Statements.Erdos274HerzogSchonheim

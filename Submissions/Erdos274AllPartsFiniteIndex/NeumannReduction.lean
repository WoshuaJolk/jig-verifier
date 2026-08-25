import Mathlib.GroupTheory.CosetCover
import Mathlib.Tactic

open scoped Pointwise

namespace Submissions.Erdos274AllPartsFiniteIndex.NeumannReduction

def exactCovering {G : Type*} [Group G] {ι : Type*}
    (parts : ι → Subgroup G) (reps : ι → G) : Prop :=
  (Set.univ (α := ι)).PairwiseDisjoint
      (fun i ↦ reps i • (parts i : Set G)) ∧
    ⋃ i, reps i • (parts i : Set G) = Set.univ

theorem proof :
    ∀ (G : Type*) [Group G] (ι : Type*) [Fintype ι],
      ∀ (parts : ι → Subgroup G) (reps : ι → G),
        exactCovering parts reps → ∀ i, (parts i).FiniteIndex := by
  classical
  intro G _ ι _ parts reps hcover i
  have hcovers :
      ⋃ k ∈ (Finset.univ : Finset ι),
        reps k • (parts k : Set G) = Set.univ := by
    simpa using hcover.2
  have hfiniteCover :=
    Subgroup.leftCoset_cover_filter_FiniteIndex hcovers
  by_contra hi
  have hxi :
      reps i ∈ reps i • (parts i : Set G) :=
    ⟨1, (parts i).one_mem, mul_one _⟩
  have hxfiltered :
      reps i ∈
        ⋃ k ∈ (Finset.univ.filter
          fun j ↦ (parts j).FiniteIndex),
            reps k • (parts k : Set G) := by
    rw [hfiniteCover]
    exact Set.mem_univ _
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxfiltered
  obtain ⟨hjmem, hxj⟩ := Set.mem_iUnion.mp hj
  have hjfinite : (parts j).FiniteIndex :=
    (Finset.mem_filter.mp hjmem).2
  have hij : i ≠ j := by
    intro h
    apply hi
    simpa [h] using hjfinite
  exact Set.disjoint_left.mp
    (hcover.1 (Set.mem_univ i) (Set.mem_univ j) hij) hxi hxj

end Submissions.Erdos274AllPartsFiniteIndex.NeumannReduction

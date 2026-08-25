import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos104ThreePointUnitCircle.Direct

noncomputable def richCenters (P : Finset ℂ) : Set ℂ :=
  {c : ℂ | 3 ≤ (P.filter fun p => dist p c = 1).card}

private lemma one_ne_I : (1 : ℂ) ≠ Complex.I := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

private lemma neg_one_ne_I : (-1 : ℂ) ≠ Complex.I := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

theorem proof :
    (0 : ℂ) ∈ richCenters (insert Complex.I (insert (-1) {1})) := by
  let P : Finset ℂ := insert Complex.I (insert (-1) {1})
  have hI : dist Complex.I 0 = 1 := by
    norm_num [Complex.dist_eq, Complex.norm_def]
  have hn : dist (-1 : ℂ) 0 = 1 := by
    norm_num [Complex.dist_eq, Complex.norm_def]
  have ho : dist (1 : ℂ) 0 = 1 := by
    norm_num [Complex.dist_eq, Complex.norm_def]
  have hcard : P.card = 3 := by
    dsimp only [P]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · simp
    · norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact not_or_intro neg_one_ne_I.symm one_ne_I.symm
  have hall : ∀ p ∈ P, dist p 0 = 1 := by
    intro p hp
    dsimp only [P] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact hI
    · exact hn
    · exact ho
  change 3 ≤ (P.filter fun p => dist p 0 = 1).card
  rw [Finset.filter_eq_self.2 hall, hcard]

end Submissions.Erdos104ThreePointUnitCircle.Direct

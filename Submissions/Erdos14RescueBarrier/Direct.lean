import Mathlib

namespace Submissions.Erdos14RescueBarrier.Direct

open scoped BigOperators

def varianceDefect (N : ℕ) (f : ℕ → ℕ) : ℕ :=
  N * (∑ i ∈ Finset.range N, f i ^ 2) -
    (∑ i ∈ Finset.range N, f i) ^ 2

def exceptionCount (N : ℕ) (f g : ℕ → ℕ) : ℕ :=
  ((Finset.range N).filter fun i => f i + g i ≠ 1).card

theorem proof :
    ∀ N : ℕ, 2 ≤ N →
      ∃ f g : ℕ → ℕ,
        (∃ i ∈ Finset.range N, ∃ j ∈ Finset.range N, f i ≠ f j) ∧
        varianceDefect N f = N - 1 ∧
        exceptionCount N f g = 0 := by
  intro N hN
  let f : ℕ → ℕ := fun i => if i = 0 then 0 else 1
  let g : ℕ → ℕ := fun i => if i = 0 then 1 else 0
  refine ⟨f, g, ?_, ?_, ?_⟩
  · refine ⟨0, by simp; omega, 1, by simp; omega, ?_⟩
    simp [f]
  · have hfilter :
        (Finset.range N).filter (fun i => i ≠ 0) =
          (Finset.range N).erase 0 := by
      ext i
      simp [and_comm]
    have hsum : ∑ i ∈ Finset.range N, f i = N - 1 := by
      calc
        ∑ i ∈ Finset.range N, f i =
            ∑ i ∈ Finset.range N, if i ≠ 0 then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [f]
        _ = ((Finset.range N).filter (fun i => i ≠ 0)).card := by
              exact Finset.sum_boole (fun i : ℕ => i ≠ 0) (Finset.range N)
        _ = N - 1 := by
              rw [hfilter, Finset.card_erase_of_mem]
              · simp
              · simp
                omega
    have hsq : ∑ i ∈ Finset.range N, f i ^ 2 = N - 1 := by
      calc
        ∑ i ∈ Finset.range N, f i ^ 2 = ∑ i ∈ Finset.range N, f i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [f]
        _ = N - 1 := hsum
    change N * (∑ i ∈ Finset.range N, f i ^ 2) -
        (∑ i ∈ Finset.range N, f i) ^ 2 = N - 1
    rw [hsq, hsum]
    have hNdecomp : N = (N - 1) + 1 := by omega
    rw [hNdecomp]
    simp [add_mul, pow_two]
  · rw [exceptionCount, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    simp only [f, g]
    split <;> simp_all

end Submissions.Erdos14RescueBarrier.Direct

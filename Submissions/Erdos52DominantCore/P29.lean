import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

open scoped Pointwise

namespace Submissions.Erdos52DominantCore.P29

/--
If the weighted cross-layer additive profile and every internal layer product
set are bounded by `H`, then choosing `r` with `2H < rN` forces one of the
first `r` normalized layers to contain more than `N/(2r)` elements, while its
internal product set remains bounded by `H`.
-/
theorem proof :
    ∀ (m r H : ℕ) (L : ℕ → Finset ℕ), 0 < r → r ≤ m →
      let N := ∑ i ∈ Finset.range m, (L i).card
      let W := ∑ i ∈ Finset.range m, i * (L i).card
      W ≤ H →
      (∀ i < m, (L i * L i).card ≤ H) →
      2 * H < r * N →
      ∃ i < r,
        N < 2 * r * (L i).card ∧
        (L i * L i).card ≤ H := by
  intro m r H L hr hrm
  dsimp only
  let N := ∑ i ∈ Finset.range m, (L i).card
  let S := ∑ i ∈ Finset.range r, (L i).card
  let T := ∑ i ∈ Finset.Ico r m, (L i).card
  intro hW hprod hsmall
  have hdecomp : S + T = N := by
    simpa [S, T, N] using Finset.sum_range_add_sum_Ico
      (fun i => (L i).card) hrm
  have htail : r * T ≤ H := by
    calc
      r * T = ∑ i ∈ Finset.Ico r m, r * (L i).card := by
        change r * (∑ i ∈ Finset.Ico r m, (L i).card) =
          ∑ i ∈ Finset.Ico r m, r * (L i).card
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.Ico r m, i * (L i).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.mul_le_mul_right _ (Finset.mem_Ico.mp hi).1
      _ ≤ ∑ i ∈ Finset.range m, i * (L i).card := by
        apply Finset.sum_le_sum_of_subset
        intro i hi
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      _ ≤ H := hW
  have htail_small : 2 * T < N := by
    have hscaled : r * (2 * T) < r * N := by
      calc
        r * (2 * T) = 2 * (r * T) := by ac_rfl
        _ ≤ 2 * H := Nat.mul_le_mul_left 2 htail
        _ < r * N := hsmall
    exact (Nat.mul_lt_mul_left hr).mp hscaled
  have hSlarge : N < 2 * S := by omega
  have hexists : ∃ i < r, N < 2 * r * (L i).card := by
    by_contra hn
    push Not at hn
    have hsum :
        ∑ i ∈ Finset.range r, 2 * r * (L i).card ≤
          ∑ i ∈ Finset.range r, N := by
      apply Finset.sum_le_sum
      intro i hi
      exact hn i (Finset.mem_range.mp hi)
    have hscaled : r * (2 * S) ≤ r * N := by
      calc
        r * (2 * S) =
            ∑ i ∈ Finset.range r, 2 * r * (L i).card := by
          change r * (2 * ∑ i ∈ Finset.range r, (L i).card) =
            ∑ i ∈ Finset.range r, 2 * r * (L i).card
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ac_rfl
        _ ≤ ∑ i ∈ Finset.range r, N := hsum
        _ = r * N := by simp
    have : 2 * S ≤ N := Nat.le_of_mul_le_mul_left hscaled hr
    exact (Nat.not_le_of_lt hSlarge) this
  obtain ⟨i, hi, hlarge⟩ := hexists
  exact ⟨i, hi, hlarge, hprod i (hi.trans_le hrm)⟩

end Submissions.Erdos52DominantCore.P29

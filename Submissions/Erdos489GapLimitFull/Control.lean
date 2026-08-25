import Mathlib

namespace Submissions.Erdos489GapLimitFull.Control

open Filter
open scoped Topology

def sievedSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬(a ∣ n)}

noncomputable def GapSumSq (A : Set ℕ) (x : ℕ) : ℝ :=
  open scoped Classical in
  let B := sievedSet A
  let b := Nat.nth (· ∈ B)
  ∑ i ∈ Finset.range (Nat.count (· ∈ B) x),
    ((b (i + 1) : ℝ) - (b i : ℝ)) ^ 2

open scoped Classical in
theorem proof
    (h : ∀ (A : Set ℕ),
      (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ)) =o[atTop]
        (fun x : ℕ => (x : ℝ).sqrt) →
      (sievedSet A).Infinite →
      ∃ L : ℝ, Tendsto (fun x : ℕ => GapSumSq A x / (x : ℝ)) atTop (𝓝 L)) :
    ∀ (A : Set ℕ),
      (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ)) =o[atTop]
        (fun x : ℕ => (x : ℝ).sqrt) →
      (sievedSet A).Infinite →
      ∃ L : ℝ, Tendsto (fun x : ℕ => GapSumSq A x / (x : ℝ)) atTop (𝓝 L) := h

end Submissions.Erdos489GapLimitFull.Control

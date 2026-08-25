import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval

namespace Submissions.Erdos280ResidueCoverRefutation.Control

theorem proof : False →
    ¬ ∀ (n a : ℕ → ℕ), StrictMono n → (∀ i, 1 ≤ i → a i < n i) →
      (∃ ε : ℝ, 0 < ε ∧
        ∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * (k : ℝ) * Real.log (k : ℝ)) →
      ¬ Filter.Tendsto
        (fun k : ℕ =>
          (((@Finset.filter ℕ
            (fun m => ¬ ∃ i ∈ Finset.Icc 1 k, m % n i = a i)
            (Classical.decPred _)
            (Finset.range (n k))).card : ℕ) : ℝ) / (k : ℝ))
        Filter.atTop (nhds 0) :=
  fun hFalse => hFalse.elim

#print axioms proof

end Submissions.Erdos280ResidueCoverRefutation.Control

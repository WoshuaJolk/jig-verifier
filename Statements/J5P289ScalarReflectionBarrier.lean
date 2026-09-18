import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
An explicit uniform scalar family satisfying the displayed reflection-tail
count inequalities, with quarter-root-scale mean and mean/square-root ratio
tending to zero. These labels are not self-avoiding walks.
-/

namespace Statements.J5P289ScalarReflectionBarrier

def twoLevelDistance (b R : ℕ) (i : Fin (b + 2)) : ℕ :=
  if i = 0 then 2 * R + 2 else b

def modelLength (b : ℕ) : ℕ := (2 * b ^ 2 + 1) ^ 2

abbrev modelDistance (b : ℕ) := twoLevelDistance b (b ^ 2)

noncomputable def modelMean (b : ℕ) : ℝ :=
  (∑ i : Fin (b + 2), (modelDistance b i : ℝ)) / ((b : ℝ) + 2)

abbrev statement : Prop :=
  (∀ b m r : ℕ, m ≤ r → (2 * r + 1) ^ 2 < modelLength b + 1 →
    (Finset.univ.filter (fun i : Fin (b + 2) => modelDistance b i ≤ m)).card ≤
      (m + 1) * (Finset.univ.filter (fun i : Fin (b + 2) =>
        2 * (r + 1) - m ≤ modelDistance b i)).card) ∧
  (∀ b : ℕ, 2 ≤ b → ∀ i : Fin (b + 2),
    1 ≤ modelDistance b i ∧ modelDistance b i ≤ modelLength b) ∧
  (∀ b : ℕ,
    modelMean b = (3 * (b : ℝ) ^ 2 + b + 2) / ((b : ℝ) + 2)) ∧
  (∀ b : ℕ, 2 ≤ b →
    Real.sqrt (Real.sqrt (modelLength b : ℝ)) / 2 ≤ modelMean b ∧
      modelMean b ≤ 3 * Real.sqrt (Real.sqrt (modelLength b : ℝ))) ∧
  Filter.Tendsto (fun b : ℕ => modelMean b / Real.sqrt (modelLength b : ℝ))
    Filter.atTop (nhds 0)

end Statements.J5P289ScalarReflectionBarrier

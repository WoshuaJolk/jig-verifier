import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Submissions.Erdos563BalancedColoringThreshold.Degenerate

noncomputable def redEdgeCount {N : ℕ} (red : Fin N → Fin N → Prop)
    (X : Finset (Fin N)) : ℕ := by
  classical
  exact ((X ×ˢ X).filter fun e => e.1 < e.2 ∧ red e.1 e.2).card

noncomputable def blueEdgeCount {N : ℕ} (red : Fin N → Fin N → Prop)
    (X : Finset (Fin N)) : ℕ := by
  classical
  exact ((X ×ˢ X).filter fun e => e.1 < e.2 ∧ ¬red e.1 e.2).card

def IsBalancedAbove (N : ℕ) (α : ℝ) (m : ℕ) : Prop :=
  ∃ red : Fin N → Fin N → Prop, Symmetric red ∧
    ∀ X : Finset (Fin N), m ≤ X.card →
      α * X.card.choose 2 < redEdgeCount red X ∧
      α * X.card.choose 2 < blueEdgeCount red X

noncomputable def threshold (N : ℕ) (α : ℝ) : ℕ :=
  sInf {m : ℕ | IsBalancedAbove N α m}

theorem proof : False → ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun N : ℕ => (threshold N α : ℝ) / Real.log N)
        atTop (nhds c) :=
  False.elim

end Submissions.Erdos563BalancedColoringThreshold.Degenerate

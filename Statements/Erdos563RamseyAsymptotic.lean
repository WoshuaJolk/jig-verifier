import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped Topology
namespace Statements.Erdos563RamseyAsymptotic

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

def Monochromatic {N : ℕ} (red : Fin N → Fin N → Prop)
    (X : Finset (Fin N)) : Prop :=
  (∀ a ∈ X, ∀ b ∈ X, a < b → red a b) ∨
  (∀ a ∈ X, ∀ b ∈ X, a < b → ¬red a b)

def RamseyArrow (N m : ℕ) : Prop :=
  ∀ red : Fin N → Fin N → Prop, Symmetric red →
    ∃ X : Finset (Fin N), X.card = m ∧ Monochromatic red X

noncomputable def diagonalRamsey (m : ℕ) : ℕ := sInf {N : ℕ | RamseyArrow N m}

abbrev statement : Prop := ∀ c : ℝ, 0 < c →
  (Tendsto (fun N : ℕ => (threshold N 0 : ℝ) / Real.log N) atTop (𝓝 c) ↔
    Tendsto (fun m : ℕ => Real.log (diagonalRamsey m) / m) atTop (𝓝 c⁻¹))

theorem target : statement := by sorry

end Statements.Erdos563RamseyAsymptotic

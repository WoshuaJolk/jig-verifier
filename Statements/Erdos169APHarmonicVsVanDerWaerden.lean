import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace Statements.Erdos169APHarmonicVsVanDerWaerden

open Filter

def IsAPFree (k : ℕ) (A : Set ℕ) : Prop :=
  A ⊆ Set.Ici 1 ∧
    ∀ a d : ℕ, 0 < d → ∃ i < k, a + i * d ∉ A

def ForcesMonochromaticAP (k N : ℕ) : Prop :=
  ∀ color : ℕ → Bool, ∃ a d : ℕ,
    1 ≤ a ∧ 0 < d ∧ a + (k - 1) * d ≤ N ∧
      ∀ i < k, color (a + i * d) = color a

noncomputable def W (k : ℕ) : ℕ :=
  sInf {N | ForcesMonochromaticAP k N}

noncomputable def harmonicSum (A : Set ℕ) : ENNReal :=
  by
    classical
    exact ∑' n : ℕ, if n ∈ A then (n : ENNReal)⁻¹ else 0

/-- Erdős Problem 169: harmonic sums of `k`-term-AP-free sets eventually
exceed every fixed multiple of the logarithm of the two-colour van der
Waerden number. This is the witness form of `f(k) / log W(k) → ∞`. -/
abbrev statement : Prop :=
  ∀ C : ℝ, ∀ᶠ k : ℕ in atTop, 3 ≤ k ∧
    ∃ A : Set ℕ, IsAPFree k A ∧
      ENNReal.ofReal (C * Real.log (W k)) ≤ harmonicSum A

theorem target : statement := sorry

end Statements.Erdos169APHarmonicVsVanDerWaerden

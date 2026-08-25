import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Set

namespace Statements.Erdos486DelayedCongruenceCounterexample

/-- Positive integers surviving a congruence condition only after its modulus
becomes active. -/
def survivors (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))) : Set ℕ :=
  {m | 0 < m ∧ ∀ n : A, (n : ℕ) < m → (m : ZMod (n : ℕ)) ∉ X n}

/-- Harmonic counting sum below a real cutoff. -/
noncomputable def logSum (B : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ m ∈ Finset.range ⌈x⌉₊,
    if m ∈ B ∧ (m : ℝ) < x then (m : ℝ)⁻¹ else 0

/-- The logarithmic average from Erdős Problem 486. -/
noncomputable def logAverage (B : Set ℕ) (x : ℝ) : ℝ :=
  logSum B x / Real.log x

def HasLogDensity (B : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (logAverage B) atTop (nhds d)

/-- Erdős 486 has a negative answer: some delayed congruence system has a
survivor set with no logarithmic density. -/
abbrev statement : Prop :=
  ∃ (A : Set ℕ), 0 ∉ A ∧
    ∃ X : (n : A) → Set (ZMod (n : ℕ)),
      ¬ ∃ d : ℝ, HasLogDensity (survivors A X) d

theorem target : statement := sorry

end Statements.Erdos486DelayedCongruenceCounterexample

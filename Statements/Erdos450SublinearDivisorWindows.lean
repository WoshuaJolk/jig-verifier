import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Basic

namespace Statements.Erdos450SublinearDivisorWindows

open Filter
open scoped Topology

def HasMediumDivisor (n m : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

open scoped Classical in
noncomputable def localCount (n x y : ℕ) : ℕ :=
  ((Finset.Ioo x (x + y)).filter (HasMediumDivisor n)).card

def UniformlySparse (ε : ℝ) (n y : ℕ) : Prop :=
  ∀ x : ℕ, (localCount n x y : ℝ) ≤ ε * (y : ℝ)

def IsSufficientScale (Y : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ y : ℕ, Y ε n ≤ y → UniformlySparse ε n y

/-- Erdős problem 450: a translate-uniform sufficient window scale can be
chosen sublinear in `n`. -/
abbrev statement : Prop :=
  ∃ Y : ℝ → ℕ → ℕ, IsSufficientScale Y ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (Y ε n : ℝ) / n) atTop (𝓝 0)

theorem target : statement := sorry

end Statements.Erdos450SublinearDivisorWindows

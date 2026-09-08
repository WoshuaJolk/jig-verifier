import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Pi

namespace Statements.E312MajorityCompletion
open scoped BigOperators
noncomputable def value {ι : Type*} [Fintype ι] (n a : ι → ℕ) : ℝ :=
  ∑ i, (a i : ℝ) / n i

def Fits {ι : Type*} (m a : ι → ℕ) : Prop := ∀ i, a i ≤ m i

noncomputable def deficit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n m : ι → ℕ) : ℝ :=
  1 - sSup {x : ℝ | ∃ a, Fits m a ∧ value n a ≤ 1 ∧ x = value n a}

noncomputable def majorityExponent (ρ : ℝ) : ℕ :=
  max 2 ⌈Real.logb 2 (1 / (2*ρ-1))⌉₊

abbrev statement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {p m : ι → ℕ} {ρ : ℝ},
    (∀ i, Nat.Prime (p i)) → Function.Injective p →
    (∀ i, ⌈ρ * p i⌉₊ ≤ m i) → (∀ i, m i < p i) →
    1/2 < ρ →
    deficit p m < (deficit p (fun i => p i - 1)) ^ (1 / (majorityExponent ρ : ℝ))

theorem target : statement := sorry
end Statements.E312MajorityCompletion

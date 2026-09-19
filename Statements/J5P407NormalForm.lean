import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Nat.Prime.Defs

namespace Statements.J5P407NormalForm

noncomputable def mass (A : Multiset ℕ) : ℝ :=
  (A.map fun n : ℕ => (n : ℝ)⁻¹).sum

def canonicalStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, 1 < K → ∃ N₀ : ℕ,
    ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → N₀ ≤ A.card → K < mass A →
      ∃ S : Multiset ℕ, S ≤ A ∧
        1 - Real.exp (-(c * K)) < mass S ∧ mass S ≤ 1

def Optimal (A S : Multiset ℕ) : Prop :=
  S ≤ A ∧ mass S ≤ 1 ∧ ∀ T : Multiset ℕ, T ≤ A → mass T ≤ 1 → mass T ≤ mass S

def Stable (A : Multiset ℕ) : Prop :=
  ∀ n ∈ A, 2 ≤ n ∧ A.count n < n.minFac

def StableTerminalLogBound (C : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → Stable A → ∀ S : Multiset ℕ,
    Optimal A S → 0 < 1 - mass S →
    (∀ n ∈ A, 1 - mass S < (n : ℝ)⁻¹) →
    mass A ≤ C * (-Real.log (1 - mass S))

def RestrictedStableLogBound (P : ℕ → Prop) (C : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → Stable A → (∀ n ∈ A, P n) →
    ∀ S : Multiset ℕ, Optimal A S → 0 < 1 - mass S →
      mass A ≤ C * (-Real.log (1 - mass S))

/- Two equivalent reductions of the open root; neither uniform estimate is asserted true. -/
abbrev statement : Prop :=
  (canonicalStatement ↔ ∃ C : ℝ, 1 ≤ C ∧ StableTerminalLogBound C) ∧
  (canonicalStatement ↔ ∃ Cp Cc : ℝ, 0 < Cp ∧ 0 < Cc ∧
    RestrictedStableLogBound Nat.Prime Cp ∧
    RestrictedStableLogBound (fun n => ¬Nat.Prime n) Cc)

end Statements.J5P407NormalForm

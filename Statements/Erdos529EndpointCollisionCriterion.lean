import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos529EndpointCollisionCriterion

open Filter
open scoped Topology

abbrev Point := ℤ × ℤ

def step (d : Fin 4) : Point :=
  if d = 0 then (1, 0)
  else if d = 1 then (-1, 0)
  else if d = 2 then (0, 1)
  else (0, -1)

def position {n : ℕ} (s : Fin n → Fin 4) (t : Fin (n + 1)) : Point :=
  let ht : t.val ≤ n := Nat.le_of_lt_succ t.isLt
  ∑ i : Fin t.val, step (s (Fin.castLE ht i))

def IsSelfAvoidingWalk {n : ℕ} (s : Fin n → Fin 4) : Prop :=
  Function.Injective (position s)

noncomputable def walks (n : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter IsSelfAvoidingWalk

noncomputable def endpointDistance {n : ℕ} (s : Fin n → Fin 4) : ℝ :=
  Real.sqrt (((position s (Fin.last n)).1 : ℝ) ^ 2 +
    ((position s (Fin.last n)).2 : ℝ) ^ 2)

noncomputable def expectedDistance (n : ℕ) : ℝ :=
  ((walks n).sum endpointDistance) / (walks n).card

def endpoint {n : ℕ} (s : Fin n → Fin 4) : Point := position s (Fin.last n)

noncomputable def endpointCollisionCount (n : ℕ) : ℕ := by
  classical
  exact ∑ x ∈ (walks n).image endpoint,
    ((walks n).filter (fun s => endpoint s = x)).card ^ 2

noncomputable def endpointCollisionProbability (n : ℕ) : ℝ :=
  (endpointCollisionCount n : ℝ) / ((walks n).card : ℝ) ^ 2

/-- Finite and asymptotic sufficient collision criteria for the canonical mean.
The quantitative collision-decay premise is not established by this statement. -/
abbrev statement : Prop :=
  (∀ n m : ℕ,
    4 * (2 * m + 1) ^ 2 * endpointCollisionCount n ≤ (walks n).card ^ 2 →
      (m : ℝ) / 2 ≤ expectedDistance n) ∧
  (Tendsto (fun n : ℕ => (n : ℝ) * endpointCollisionProbability n) atTop (𝓝 0) →
    ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop,
      C * Real.sqrt n < expectedDistance n)

end Statements.Erdos529EndpointCollisionCriterion

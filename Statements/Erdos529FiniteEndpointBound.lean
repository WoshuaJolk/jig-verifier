import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos529FiniteEndpointBound

open Filter

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

/-- A finite lower bound for the canonical uniform planar self-avoiding-walk
mean endpoint distance, obtained from the first-maximal-radius reflection
argument of Madras (2014), Section 2. This has fourth-root scale and does
not establish the superdiffusive statement of Erdős Problem 529. -/
abbrev statement : Prop :=
  ∀ n m : ℕ, (2 * (m * (m + 2)) + 1) ^ 2 < n + 1 →
    (m : ℝ) ≤ expectedDistance n

end Statements.Erdos529FiniteEndpointBound

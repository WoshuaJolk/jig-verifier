import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos529PlanarSAWSuperdiffusive

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

/-- The planar part of Erdős Problem 529: the mean endpoint distance of a
uniformly random length-`n` self-avoiding nearest-neighbour walk in `ℤ²`
grows faster than `sqrt n`. -/
abbrev statement : Prop :=
  ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop,
    C * Real.sqrt n < expectedDistance n

theorem target : statement := sorry

end Statements.Erdos529PlanarSAWSuperdiffusive

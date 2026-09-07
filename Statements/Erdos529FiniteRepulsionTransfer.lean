import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Prod

namespace Statements.Erdos529FiniteRepulsionTransfer

open scoped BigOperators

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

abbrev Word (n : ℕ) := Fin n → Fin 4

def allWords (n : ℕ) : Finset (Word n) := Finset.univ

def timeCollisionPairs {n : ℕ} (s : Word n) :
    Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ position s ij.1 = position s ij.2)

def J {n : ℕ} (s : Word n) : ℕ := (timeCollisionPairs s).card

noncomputable def gibbsWeight {n : ℕ} (β : ℝ) (s : Word n) : ℝ :=
  Real.exp (-β * (J s : ℝ))

noncomputable def gibbsPartition (n : ℕ) (β : ℝ) : ℝ :=
  ∑ s ∈ allWords n, gibbsWeight β s

noncomputable def gibbsExpectedDistance (n : ℕ) (β : ℝ) : ℝ :=
  (∑ s ∈ allWords n, gibbsWeight β s * endpointDistance s) /
    gibbsPartition n β

noncomputable def finiteCountPenalty (n : ℕ) (a : ℝ) : ℝ :=
  2 * Real.log a + 3 * Real.log ((n : ℝ) + 1) + Real.log 2

abbrev statement : Prop :=
  ∀ (n : ℕ) (lam a : ℝ),
    2 ≤ lam → 1 ≤ a →
    (∀ k ≤ n, ((walks k).card : ℝ) ≤ lam ^ k * a) →
    ((walks n).card : ℝ) = lam ^ n →
    |gibbsExpectedDistance n (finiteCountPenalty n a) - expectedDistance n| ≤
      2 * (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 3

end Statements.Erdos529FiniteRepulsionTransfer

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum

/-
Exact moments and negative covariance for the full uniform canonical two-step
planar self-avoiding-walk law. This is a finite partial statement only.
-/
namespace Statements.J5P289TwoStepCovariance

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

abbrev Word := Fin 2 → Fin 4

def spinU (d : Fin 4) : ℤ := (step d).1 + (step d).2
def spinV (d : Fin 4) : ℤ := (step d).1 - (step d).2
def A (s : Word) : ℤ := spinU (s 0) * spinU (s 1)
def B (s : Word) : ℤ := spinV (s 0) * spinV (s 1)

noncomputable def mean (f : Word → ℤ) : ℚ :=
  ((∑ s ∈ walks 2, f s : ℤ) : ℚ) / (walks 2).card

abbrev statement : Prop :=
  ((walks 2).card = 12 ∧
    (∑ s ∈ walks 2, A s) = 4 ∧
    (∑ s ∈ walks 2, B s) = 4 ∧
    (∑ s ∈ walks 2, A s * B s) = -4) ∧
  (mean (fun s => A s * B s) - mean A * mean B = -4 / 9 ∧
    mean (fun s => A s * B s) < mean A * mean B)

end Statements.J5P289TwoStepCovariance

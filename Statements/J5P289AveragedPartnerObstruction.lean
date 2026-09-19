import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/- A fixed five-step arm and the full uniform one-step partner family.
No claim about averaging both arms or about the full superdiffusivity root. -/
namespace Statements.J5P289AveragedPartnerObstruction

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

def alpha : Fin 5 → Fin 4 := ![0, 2, 2, 1, 1]

def allPartners : Finset (Fin 1 → Fin 4) := Finset.univ

def Avoids (b : Fin 1 → Fin 4) : Prop :=
  ∀ (i : Fin 6) (j : Fin 2), position alpha i = position b j → i = 0 ∧ j = 0

instance (b : Fin 1 → Fin 4) : Decidable (Avoids b) := by
  unfold Avoids
  infer_instance

def allowed : Finset (Fin 1 → Fin 4) := allPartners.filter Avoids

def distanceSquared (b : Fin 1 → Fin 4) : ℤ :=
  let x := position alpha (Fin.last 5)
  let y := position b (Fin.last 1)
  (y.1 - x.1) ^ 2 + (y.2 - x.2) ^ 2

def conditionedMeanSquare : ℚ :=
  ((∑ b ∈ allowed, distanceSquared b : ℤ) : ℚ) / allowed.card

def unconditionedMeanSquare : ℚ :=
  ((∑ b ∈ allPartners, distanceSquared b : ℤ) : ℚ) / allPartners.card

abbrev statement : Prop :=
  IsSelfAvoidingWalk alpha ∧
  (∀ b : Fin 1 → Fin 4, IsSelfAvoidingWalk b) ∧
  allPartners = walks 1 ∧
  (allPartners.card = 4 ∧ allowed.card = 3 ∧
    (∑ b ∈ allowed, distanceSquared b) = 16 ∧
    (∑ b ∈ allPartners, distanceSquared b) = 24) ∧
  (conditionedMeanSquare = 16 / 3 ∧ unconditionedMeanSquare = 6 ∧
    conditionedMeanSquare < unconditionedMeanSquare)

end Statements.J5P289AveragedPartnerObstruction

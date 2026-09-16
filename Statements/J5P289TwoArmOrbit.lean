import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
Two explicit canonical nine-step SAWs disprove a pointwise symmetry-orbit
repulsion inequality. No claim about averaging over all SAW shapes is made.
-/
namespace Statements.J5P289TwoArmOrbit

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

def alpha : Fin 9 → Fin 4 := ![0, 3, 0, 2, 2, 1, 1, 1, 3]
def beta : Fin 9 → Fin 4 := ![3, 3, 1, 1, 2, 1, 2, 0, 2]

abbrev Symmetry := Fin 2 × Fin 4

def transform (g : Symmetry) (p : Point) : Point :=
  let x := if g.1 = 0 then p.1 else -p.1
  let y := p.2
  if g.2 = 0 then (x, y)
  else if g.2 = 1 then (-y, x)
  else if g.2 = 2 then (-x, -y)
  else (y, -x)

def Avoids (g : Symmetry) : Prop :=
  ∀ i j : Fin 10, position alpha i = transform g (position beta j) → i = 0 ∧ j = 0

instance (g : Symmetry) : Decidable (Avoids g) := by
  unfold Avoids
  infer_instance

def allowed : Finset Symmetry := Finset.univ.filter Avoids

def distanceSquared (g : Symmetry) : ℤ :=
  let a := position alpha (Fin.last 9)
  let b := transform g (position beta (Fin.last 9))
  (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

def conditionedMeanSquare : ℚ :=
  ((∑ g ∈ allowed, distanceSquared g : ℤ) : ℚ) / allowed.card

def unconditionedMeanSquare : ℚ :=
  ((∑ g : Symmetry, distanceSquared g : ℤ) : ℚ) / Fintype.card Symmetry

noncomputable def meanDistance (s : Finset Symmetry) : ℝ :=
  (∑ g ∈ s, Real.sqrt (distanceSquared g : ℝ)) / s.card

abbrev statement : Prop :=
  (IsSelfAvoidingWalk alpha ∧ IsSelfAvoidingWalk beta) ∧
  (∀ g : Symmetry,
    transform g (position beta 0) = (0, 0) ∧
    Function.Injective (fun i : Fin 10 => transform g (position beta i)) ∧
    ∀ i : Fin 9, ∃ d : Fin 4,
      transform g (position beta i.succ) =
        transform g (position beta i.castSucc) + step d) ∧
  allowed = {(0, 0)} ∧
  (allowed.card = 1 ∧
    (∑ g ∈ allowed, distanceSquared g) = 2 ∧
    (∑ g : Symmetry, distanceSquared g) = 48) ∧
  (conditionedMeanSquare = 2 ∧ unconditionedMeanSquare = 6 ∧
    conditionedMeanSquare < unconditionedMeanSquare) ∧
  (meanDistance allowed = Real.sqrt 2 ∧
    meanDistance allowed < meanDistance Finset.univ)

end Statements.J5P289TwoArmOrbit

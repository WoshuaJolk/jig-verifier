import Mathlib.Data.Fin.Basic

namespace Statements.Erdos529ReflectAndPack

abbrev Point := ℤ × ℤ

def verticalReflection (H : ℤ) (x : Point) : Point := (2 * H - x.1, x.2)

def reflectSuffix {n : ℕ} (p : Fin (n + 1) → Point)
    (L : Fin (n + 1)) (H : ℤ) (t : Fin (n + 1)) : Point :=
  if t ≤ L then p t else verticalReflection H (p t)

def GridAdjacent (x y : Point) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
  (y.1 = x.1 ∧ y.2 = x.2 - 1)

def HasUnitSteps {n : ℕ} (p : Fin (n + 1) → Point) : Prop :=
  ∀ i : Fin n, GridAdjacent (p i.castSucc) (p i.succ)

abbrev statement : Prop :=
  ∀ (n : ℕ) (p : Fin (n + 1) → Point) (L : Fin (n + 1)) (H : ℤ),
    Function.Injective p → p 0 = (0, 0) → HasUnitSteps p →
    (p L).1 = H →
    (∀ t, t < L → (p t).1 < H) →
    (∀ t, L < t → (p t).1 ≤ H) →
    let q := reflectSuffix p L H
    Function.Injective q ∧ q 0 = (0, 0) ∧ HasUnitSteps q ∧
    q (Fin.last n) = verticalReflection H (p (Fin.last n)) ∧
    ∀ r : ℕ, (2 * r + 1) ^ 2 < n + 1 →
      ∃ t, (q t).1 < -(r : ℤ) ∨ (r : ℤ) < (q t).1 ∨
        (q t).2 < -(r : ℤ) ∨ (r : ℤ) < (q t).2

end Statements.Erdos529ReflectAndPack

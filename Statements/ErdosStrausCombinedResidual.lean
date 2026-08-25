import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.ErdosStrausCombinedResidual

def Representable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

def Root : Prop :=
  ∀ n : ℕ, 2 ≤ n → Representable n

def ShiftFree (p : ℕ) : Prop :=
  ∀ a b g m : ℕ, 0 < a → 0 < b → 0 < m →
    p + a = b * g → g + 1 ≠ 4 * a * m

def MordellCore : Prop :=
  ∀ p : ℕ, p.Prime → p % 24 = 1 → (p % 5 = 1 ∨ p % 5 = 4) →
    (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) → Representable p

def CombinedCore : Prop :=
  ∀ p : ℕ, p.Prime → p % 24 = 1 → (p % 5 = 1 ∨ p % 5 = 4) →
    (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) → ShiftFree p →
    Representable p

def ShiftCriterion : Prop :=
  ∀ n a b g m : ℕ, 2 ≤ n → 0 < a → 0 < b → 0 < m →
    n + a = b * g → g + 1 = 4 * a * m → Representable n

/-- The shifted-divisor criterion and Mordell reduction combine exactly:
the full conjecture is equivalent to its restriction to Mordell's six
prime residue classes which are also free of every shifted-divisor witness. -/
abbrev statement : Prop :=
  ShiftCriterion → (MordellCore ↔ Root) → (CombinedCore ↔ Root)

theorem target : statement := sorry

end Statements.ErdosStrausCombinedResidual

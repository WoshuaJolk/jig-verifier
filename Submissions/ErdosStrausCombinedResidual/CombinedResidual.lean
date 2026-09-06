import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Prime.Basic

/-!
Proof of Jig problem 11, statement 15.
This formalizes the combination argument already described on the board.
It proves a conditional reduction, not the Erdős–Straus conjecture.
Source: https://jig.so/p/11?s=15; existing reductions: ?s=10 and ?s=14.
-/

namespace Submissions.ErdosStrausCombinedResidual.CombinedResidual

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

theorem proof :
    ShiftCriterion → (MordellCore ↔ Root) → (CombinedCore ↔ Root) := by
  intro hShift hMordell
  constructor
  · intro hCombined
    apply hMordell.mp
    intro p hp hp24 hp5 hp7
    apply Classical.byContradiction
    intro hNot
    apply hNot
    apply hCombined p hp hp24 hp5 hp7
    intro a b g m ha hb hm hbg heq
    exact hNot (hShift p a b g m hp.two_le ha hb hm hbg heq)
  · intro hRoot p hp _ _ _ _
    exact hRoot p hp.two_le

end Submissions.ErdosStrausCombinedResidual.CombinedResidual

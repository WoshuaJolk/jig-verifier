import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.E811PrimeCyclicRainbow

def SymmetricColoring {N m : ℕ} (color : Fin N → Fin N → Fin m) : Prop :=
  ∀ x y, color x y = color y x

def BalancedSixColoring {n : ℕ}
    (color : Fin (6 * n + 1) → Fin (6 * n + 1) → Fin 6) : Prop :=
  ∀ v c,
    ((Finset.univ.erase v).filter fun w => color v w = c).card = n

def HasRainbowC6 {N : ℕ} (color : Fin N → Fin N → Fin 6) : Prop :=
  ∃ cycle : Fin 6 → Fin N, Function.Injective cycle ∧
    Function.Injective
      (fun i : Fin 6 => color (cycle i) (cycle (i + 1)))

/-- Translation acts on the cyclic vertex set by addition modulo 6*n+1. -/
def TranslationInvariant {n : ℕ}
    (color : Fin (6 * n + 1) → Fin (6 * n + 1) → Fin 6) : Prop :=
  ∀ a x y, color (x + a) (y + a) = color x y

/-- The prime cyclic, translation-invariant subcase of Erdős 811. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Nat.Prime (6 * n + 1) →
    ∀ color : Fin (6 * n + 1) → Fin (6 * n + 1) → Fin 6,
      SymmetricColoring color → BalancedSixColoring color →
      TranslationInvariant color → HasRainbowC6 color

theorem target : statement := sorry

end Statements.E811PrimeCyclicRainbow

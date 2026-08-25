import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos811BalancedRainbowCycle

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

/-- The surviving C6 challenge in Erdős Problem 811. The simultaneously
asked K4 assertion is excluded because it has been disproved. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop,
    ∀ color : Fin (6 * n + 1) → Fin (6 * n + 1) → Fin 6,
      SymmetricColoring color → BalancedSixColoring color →
        HasRainbowC6 color

theorem target : statement := sorry

end Statements.Erdos811BalancedRainbowCycle

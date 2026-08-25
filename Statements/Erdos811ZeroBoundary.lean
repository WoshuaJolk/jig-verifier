import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos811ZeroBoundary

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

/-- The exact-balanced hypotheses are satisfiable at n=0, but no rainbow C6
exists there; hence the eventual quantifier in Problem 811 is essential. -/
abbrev statement : Prop :=
  ∃ color : Fin 1 → Fin 1 → Fin 6,
    SymmetricColoring color ∧
      BalancedSixColoring (n := 0) color ∧
      ¬HasRainbowC6 color

theorem target : statement := sorry

end Statements.Erdos811ZeroBoundary

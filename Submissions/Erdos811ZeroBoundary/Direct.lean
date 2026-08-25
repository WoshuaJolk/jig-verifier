import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

namespace Submissions.Erdos811ZeroBoundary.Direct

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

def singletonColoring : Fin 1 → Fin 1 → Fin 6 :=
  fun _ _ => 0

theorem proof :
    ∃ color : Fin 1 → Fin 1 → Fin 6,
      SymmetricColoring color ∧
        BalancedSixColoring (n := 0) color ∧
        ¬HasRainbowC6 color := by
  refine ⟨singletonColoring, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · intro v c
    fin_cases v
    fin_cases c <;> decide
  · rintro ⟨cycle, hinj, _⟩
    have hcard := Fintype.card_le_of_injective cycle hinj
    norm_num at hcard

end Submissions.Erdos811ZeroBoundary.Direct

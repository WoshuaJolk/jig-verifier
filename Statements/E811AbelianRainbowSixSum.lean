import Mathlib

namespace Statements.E811AbelianRainbowSixSum

def Balanced {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (c : G → Fin 6) : Prop :=
  ∀ i j : Fin 6,
    ((Finset.univ.erase (0 : G)).filter (fun x => c x = i)).card =
    ((Finset.univ.erase (0 : G)).filter (fun x => c x = j)).card

abbrev statement : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G],
    1 < Fintype.card G → ∀ c : G → Fin 6,
      (∀ x, c (-x) = c x) → Balanced c →
      ∃ a : Fin 6 → G,
        (∀ i, a i ≠ 0 ∧ c (a i) = i) ∧
        ∑ i : Fin 6, a i = 0

/-- Canonical proposition only; the source-dependent proof is not formalized. -/
theorem target : statement := by
  sorry

end Statements.E811AbelianRainbowSixSum

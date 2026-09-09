import Mathlib

namespace Statements.E811AdditiveF5NoB

abbrev V (d : ℕ) := Fin d → ZMod 5

def palettes : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,1,3}, {0,1,4}, {0,2,3}, {0,2,5},
   {0,4,5}, {1,2,4}, {1,2,5}, {1,3,5}, {2,3,4}}

def Balanced {d : ℕ} (c : V d → Fin 6) : Prop :=
  ∀ i j : Fin 6,
    ((Finset.univ.erase (0 : V d)).filter (fun x => c x = i)).card =
    ((Finset.univ.erase (0 : V d)).filter (fun x => c x = j)).card

def Supported {d : ℕ} (c : V d → Fin 6) : Prop :=
  ∀ a b : V d, a ≠ 0 → b ≠ 0 → a ≠ b →
    ({c a, c b, c (b-a)} : Finset (Fin 6)).card = 3 →
    ({c a, c b, c (b-a)} : Finset (Fin 6)) ∈ palettes

abbrev statement : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : V d → Fin 6,
    (∀ x, c (-x) = c x) → Balanced c → ¬ Supported c

/-- Canonical proposition only. The computer-assisted proof is not formalized. -/
theorem target : statement := by
  sorry

end Statements.E811AdditiveF5NoB

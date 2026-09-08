import Mathlib

namespace Statements.E811BGlobalization

def palettes : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,1,3}, {0,1,4}, {0,2,3}, {0,2,5},
   {0,4,5}, {1,2,4}, {1,2,5}, {1,3,5}, {2,3,4}}

def rainbowPair {n : ℕ} (c : Fin n → Fin n → Fin 6) : Prop :=
  ∃ v : Fin 6 → Fin n, Function.Injective v ∧
    Function.Injective (fun i : Fin 6 =>
      ![c (v 0) (v 1), c (v 0) (v 2), c (v 1) (v 2),
        c (v 3) (v 4), c (v 3) (v 5), c (v 4) (v 5)] i)

def realized {n : ℕ} (c : Fin n → Fin n → Fin 6)
    (p : Equiv.Perm (Fin 6)) (A : Finset (Fin 6)) : Prop :=
  A.card = 3 ∧ ∃ u v w, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
    A = {p (c u v), p (c v w), p (c u w)}

/-- Canonical proposition only. The accompanying computer-assisted
written proof is not formalized in this file. -/
abbrev statement : Prop :=
  ∀ (t : ℕ), 20989 ≤ 6*t+1 →
  ∀ c : Fin (6*t+1) → Fin (6*t+1) → Fin 6,
    (∀ u v, c u v = c v u) →
    (∀ u a, (Finset.univ.filter (fun v => v ≠ u ∧ c u v = a)).card = t) →
    (¬ rainbowPair c ↔ ∃ p : Equiv.Perm (Fin 6),
      ∀ A : Finset (Fin 6), realized c p A ↔ A ∈ palettes)

end Statements.E811BGlobalization

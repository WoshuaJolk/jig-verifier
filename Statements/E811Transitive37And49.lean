import Mathlib

namespace Statements.E811Transitive37And49

def triangleEdges {N : ℕ} (c : Fin N → Fin N → Fin 6)
    (v : Fin 6 → Fin N) : Fin 6 → Fin 6 :=
  ![c (v 0) (v 1), c (v 1) (v 2), c (v 2) (v 0),
    c (v 3) (v 4), c (v 4) (v 5), c (v 5) (v 3)]

abbrev statement : Prop :=
  ∀ N : ℕ, (N = 37 ∨ N = 49) →
  ∀ c : Fin N → Fin N → Fin 6,
    (∀ x y, c x y = c y x) →
    (∀ x a, ((Finset.univ.erase x).filter fun y => c x y = a).card = (N - 1) / 6) →
    (∀ x y : Fin N, ∃ g : Equiv.Perm (Fin N), ∃ s : Equiv.Perm (Fin 6),
      g x = y ∧ ∀ u v, u ≠ v → c (g u) (g v) = s (c u v)) →
    ∃ v : Fin 6 → Fin N, Function.Injective v ∧ Function.Injective (triangleEdges c v)

theorem target : statement := sorry
end Statements.E811Transitive37And49

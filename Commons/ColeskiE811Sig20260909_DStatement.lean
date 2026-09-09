import Mathlib

namespace ColeskiSubmittedE811DNoBalancedBase

def palettes : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,1,3}, {0,2,4}, {0,3,5}, {0,4,5},
   {1,2,5}, {1,3,4}, {1,4,5}, {2,3,4}, {2,3,5}}

/-- No positive-degree completely balanced finite coloring has all its
rainbow triangle palettes in D. No rainbow-six-cycle assumption is used. -/
abbrev statement : Prop :=
  ∀ (t : ℕ), 0 < t →
  ∀ c : Fin (6*t+1) → Fin (6*t+1) → Fin 6,
    (∀ u v, c u v = c v u) →
    (∀ u a, (Finset.univ.filter (fun v => v ≠ u ∧ c u v = a)).card = t) →
    (∀ u v w, u ≠ v → v ≠ w → u ≠ w →
      c u v = c v w ∨ c v w = c u w ∨ c u v = c u w ∨
      ({c u v, c v w, c u w} : Finset (Fin 6)) ∈ palettes) → False

end ColeskiSubmittedE811DNoBalancedBase

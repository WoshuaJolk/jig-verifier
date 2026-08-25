import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Set.Lattice

namespace Submissions.Erdos477EmptyComplementBoundary.Worker09Middle

open Polynomial Set

theorem proof :
    ∀ f : ℤ[X], ∃ z : ℤ,
      ¬∃! ab ∈ (∅ : Set ℤ) ×ˢ Set.range f.eval,
        z = ab.1 + ab.2 := by
  intro f
  exact ⟨0, by simp⟩

end Submissions.Erdos477EmptyComplementBoundary.Worker09Middle

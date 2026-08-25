import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Set.Lattice

namespace Statements.Erdos477EmptyComplementBoundary

open Polynomial Set

/-- The empty candidate complement never represents any integer, independently
of the polynomial value set. -/
abbrev statement : Prop :=
  ∀ f : ℤ[X], ∃ z : ℤ,
    ¬∃! ab ∈ (∅ : Set ℤ) ×ˢ Set.range f.eval,
      z = ab.1 + ab.2

theorem target : statement := sorry

end Statements.Erdos477EmptyComplementBoundary

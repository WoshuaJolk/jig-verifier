import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Set.Lattice

namespace Statements.Erdos477NoPolynomialAdditiveTiling

open Polynomial Set

/-- The negative answer conjectured by Erdős and Graham for Problem 477:
no integer polynomial of degree at least two has a unique additive complement
of its value set in the integers. -/
abbrev statement : Prop :=
  ∀ f : ℤ[X], 2 ≤ f.degree →
    ∀ A : Set ℤ, ∃ z : ℤ,
      ¬∃! ab ∈ A ×ˢ Set.range f.eval, z = ab.1 + ab.2

theorem target : statement := sorry

end Statements.Erdos477NoPolynomialAdditiveTiling

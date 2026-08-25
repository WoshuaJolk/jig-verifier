import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Erdős problem 687

For a cutoff `X`, choose one residue class modulo every prime at most `X`.
If those classes cover `[1,y]`, must every such `y` be `o(X^2)`?
-/

namespace Statements.Erdos687JacobsthalSubquadratic

def CoversInitialInterval (X y : ℕ) : Prop :=
  ∃ residue : ℕ → ℕ,
    ∀ m : ℕ, 1 ≤ m → m ≤ y →
      ∃ p : ℕ, p.Prime ∧ p ≤ X ∧
        m % p = residue p % p

abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ y : ℕ, CoversInitialInterval X y →
        (y : ℝ) ≤ ε * (X : ℝ) ^ 2

theorem target : statement := sorry

end Statements.Erdos687JacobsthalSubquadratic

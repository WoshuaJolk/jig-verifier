import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos535GcdLayerEncoding

/-- The set of prime-power divisibility layers `(p,j)` with
`0 ≤ j < v_p(n)`. -/
def layers (n : ℕ) : Finset (ℕ × ℕ) :=
  n.factorization.support.biUnion fun p =>
    (Finset.range (n.factorization p)).image fun j => (p, j)

/-- Prime-power layer encoding turns greatest common divisors into exact
set intersections for positive integers. -/
abbrev statement : Prop :=
  ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
    layers (Nat.gcd a b) = layers a ∩ layers b

theorem target : statement := sorry

end Statements.Erdos535GcdLayerEncoding

import Mathlib.Data.Nat.GCD.Basic

/-!
# Shared-core obstruction to prime-rank decay

Fresh coprime factors do not by themselves improve product-over-lcm density
when every recursive modulus retains a common factor.
-/

namespace Statements.Erdos12MixedRankObstruction

abbrev statement : Prop :=
  ∀ P p : ℕ,
    Nat.Coprime P p →
    Nat.lcm (2 * P) (2 * p) = 2 * (P * p) ∧
      2 * (P * ((2 * p) / 2)) = Nat.lcm (2 * P) (2 * p)

theorem target : statement := sorry

end Statements.Erdos12MixedRankObstruction

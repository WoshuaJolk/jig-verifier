import Mathlib.Data.Nat.Totient
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos51LeastPreimageExists

/-- Every attained Euler-totient value has a least natural-number preimage. -/
abbrev statement : Prop :=
  ∀ a : ℕ, (∃ m : ℕ, Nat.totient m = a) →
    ∃ n : ℕ, IsLeast (Nat.totient ⁻¹' {a}) n

theorem target : statement := sorry

end Statements.Erdos51LeastPreimageExists

import Mathlib.NumberTheory.PrimeCounting

namespace Statements.Erdos855ZeroArgumentBoundary

/-- The zero-argument identity boundary for prime-counting subadditivity. -/
abbrev statement : Prop :=
  ∀ x : ℕ,
    Nat.primeCounting (x + 0) ≤
      Nat.primeCounting x + Nat.primeCounting 0

theorem target : statement := sorry

end Statements.Erdos855ZeroArgumentBoundary

import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos829SmallTwoCubeCounts

def isCube (m : ℕ) : Bool :=
  (List.range (m + 1)).any fun k ↦ k ^ 3 == m

def sumRepCubes (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun a ↦ isCube a && isCube (n - a)).card

/-- The first concrete ordered two-cube representation counts. -/
abbrev statement : Prop :=
  sumRepCubes 0 = 1 ∧ sumRepCubes 2 = 1 ∧ sumRepCubes 3 = 0

theorem target : statement := sorry

end Statements.Erdos829SmallTwoCubeCounts

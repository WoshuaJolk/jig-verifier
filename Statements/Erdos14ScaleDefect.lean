import Mathlib

namespace Statements.Erdos14ScaleDefect

open scoped BigOperators

def modelLower (M : ℕ) : Finset ℕ :=
  {0, M} ∪ Finset.Icc (M + 1) (2 * M)

def pairFiber (X Y : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ Y).filter fun p => p.1 + p.2 = n

def modelEnergy (M : ℕ) (D : Finset ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc (2 * M + 1) (6 * M),
    (pairFiber (modelLower M) D n).card ^ 2

def modelDefect (M : ℕ) (D : Finset ℕ) : ℕ :=
  4 * M * modelEnergy M D - ((M + 2) * D.card) ^ 2

/-- The exact scale-M model forces a defect linear in M at the next scale. -/
abbrev statement : Prop :=
  ∀ (M : ℕ) (D : Finset ℕ), 1 ≤ M →
    D.Nonempty →
    D ⊆ Finset.Icc (2 * M + 1) (4 * M) →
    2 * M ≤ modelDefect M D

theorem target : statement := sorry

end Statements.Erdos14ScaleDefect

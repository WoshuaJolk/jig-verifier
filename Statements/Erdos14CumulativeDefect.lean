import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos14CumulativeDefect

open scoped BigOperators

def modelLower (M : ℕ) : Finset ℕ :=
  {0, M} ∪ Finset.Icc (M + 1) (2 * M)

def pairFiber (X Y : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ Y).filter fun p => p.1 + p.2 = n

def modelEnergy (M : ℕ) (D : Finset ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc (2 * M + 1) (6 * M),
    (pairFiber (modelLower M) D n).card ^ 2

/-- Integer excess over the sharp Cauchy lower bound at the next scale. -/
def modelDefect (M : ℕ) (D : Finset ℕ) : ℕ :=
  4 * M * modelEnergy M D - ((M + 2) * D.card) ^ 2

/-- Once scale `M` attains equality (hence has the classified model lower
block), every nonempty consecutive block has positive integral defect. -/
abbrev statement : Prop :=
  ∀ (M : ℕ) (D : Finset ℕ), 1 ≤ M →
    D.Nonempty →
    D ⊆ Finset.Icc (2 * M + 1) (4 * M) →
    1 ≤ modelDefect M D

theorem target : statement := sorry

end Statements.Erdos14CumulativeDefect

import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos14ModelObstruction

def modelLower (M : ℕ) : Finset ℕ :=
  {0, M} ∪ Finset.Icc (M + 1) (2 * M)

def pairFiber (X Y : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ Y).filter fun p => p.1 + p.2 = n

def tilesNextInterval (M : ℕ) (D : Finset ℕ) : Prop :=
  ∀ n ∈ Finset.Icc (2 * M + 1) (6 * M),
    (pairFiber (modelLower M) D n).card = 1

/-- The sharp one-scale tiling `{0,M} ⊕ [M+1,2M]` cannot be extended
to an exact adjacent-scale tiling by any possible next block. -/
abbrev statement : Prop :=
  ∀ (M : ℕ) (D : Finset ℕ), 1 ≤ M →
    D ⊆ Finset.Icc (2 * M + 1) (4 * M) →
    ¬ tilesNextInterval M D

theorem target : statement := sorry

end Statements.Erdos14ModelObstruction

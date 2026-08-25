import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos30DifferenceCountingBound

/-- A finite Sidon set: only commutativity can force equal pairwise sums. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The classical difference-counting bound for a Sidon subset of
`{1, ..., N}`. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Finset.Icc 1 N →
    IsSidon A →
    A.card ≤ Nat.sqrt (2 * N) + 1

theorem target : statement := sorry

end Statements.Erdos30DifferenceCountingBound

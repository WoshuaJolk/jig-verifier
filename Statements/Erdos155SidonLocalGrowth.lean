import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter

namespace Statements.Erdos155SidonLocalGrowth

/-- Equal pair sums in a Sidon set arise only by swapping summands. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Maximum cardinality of a Sidon subset of a finite set. -/
noncomputable def maxSidonSubsetCard (A : Finset ℕ) : ℕ := by
  classical
  exact (A.powerset.filter IsSidon).sup Finset.card

noncomputable abbrev F (N : ℕ) : ℕ :=
  maxSidonSubsetCard (Finset.Icc 1 N)

/-- Erdős Problem 155: a fixed extension of the interval eventually raises
the extremal Sidon cardinality by at most one. -/
abbrev statement : Prop :=
  ∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1

theorem target : statement := sorry

end Statements.Erdos155SidonLocalGrowth

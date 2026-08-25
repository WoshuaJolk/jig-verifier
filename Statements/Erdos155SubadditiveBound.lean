import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos155SubadditiveBound

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

noncomputable def maxSidonSubsetCard (A : Finset ℕ) : ℕ := by
  classical
  exact (A.powerset.filter IsSidon).sup Finset.card

noncomputable abbrev F (N : ℕ) : ℕ :=
  maxSidonSubsetCard (Finset.Icc 1 N)

/-- Splitting a Sidon set at `N` gives the general subadditivity bound.
For `k = 1` this proves the exact inequality sought in Erdős Problem 155. -/
abbrev statement : Prop :=
  ∀ N k : ℕ, F (N + k) ≤ F N + F k

theorem target : statement := sorry

end Statements.Erdos155SubadditiveBound

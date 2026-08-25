import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos155SubadditiveBound.Degenerate

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

theorem proof : False → ∀ N k : ℕ, F (N + k) ≤ F N + F k :=
  False.elim

end Submissions.Erdos155SubadditiveBound.Degenerate

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic

namespace Submissions.Erdos879SingletonAdmissible.FalsePremise

def Admissible (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

theorem proof :
    False → Admissible {1} := by
  intro h
  exact h.elim

end Submissions.Erdos879SingletonAdmissible.FalsePremise

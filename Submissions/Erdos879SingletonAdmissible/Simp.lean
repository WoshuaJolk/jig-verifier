import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic

namespace Submissions.Erdos879SingletonAdmissible.Simp

def Admissible (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

theorem proof :
    Admissible {1} := by
  simp [Admissible]

end Submissions.Erdos879SingletonAdmissible.Simp

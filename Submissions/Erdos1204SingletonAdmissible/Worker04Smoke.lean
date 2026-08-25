import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open Finset

namespace Submissions.Erdos1204SingletonAdmissible.Worker04Smoke

def IsAdmissible (s : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ r : ℕ, r < p ∧ ∀ a ∈ s, a % p ≠ r

theorem proof : IsAdmissible {0} := by
  intro p hp
  refine ⟨1, hp.one_lt, ?_⟩
  intro a ha
  simp at ha
  subst a
  simp

end Submissions.Erdos1204SingletonAdmissible.Worker04Smoke

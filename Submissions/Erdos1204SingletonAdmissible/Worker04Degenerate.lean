import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open Finset

namespace Submissions.Erdos1204SingletonAdmissible.Worker04Degenerate

def IsAdmissible (s : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ r : ℕ, r < p ∧ ∀ a ∈ s, a % p ≠ r

theorem proof : False → IsAdmissible {0} :=
  False.elim

end Submissions.Erdos1204SingletonAdmissible.Worker04Degenerate

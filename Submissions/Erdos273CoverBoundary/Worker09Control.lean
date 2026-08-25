import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic

namespace Submissions.Erdos273CoverBoundary.Worker09Control

abbrev CongruenceClass := ℤ × ℕ

def Covers (C : Finset CongruenceClass) : Prop :=
  ∀ z : ℤ, ∃ c ∈ C, (c.2 : ℤ) ∣ z - c.1

theorem proof
    (claim :
      (∀ C : Finset CongruenceClass, Covers C → C.Nonempty) ∧
      ∀ (a : ℤ) (m : ℕ), 1 < m → ¬ Covers {(a, m)}) :
    (∀ C : Finset CongruenceClass, Covers C → C.Nonempty) ∧
    ∀ (a : ℤ) (m : ℕ), 1 < m → ¬ Covers {(a, m)} :=
  claim

end Submissions.Erdos273CoverBoundary.Worker09Control

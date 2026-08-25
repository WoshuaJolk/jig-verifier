import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos273CoverBoundary.Worker09Direct

abbrev CongruenceClass := ℤ × ℕ

def Covers (C : Finset CongruenceClass) : Prop :=
  ∀ z : ℤ, ∃ c ∈ C, (c.2 : ℤ) ∣ z - c.1

theorem proof :
    (∀ C : Finset CongruenceClass, Covers C → C.Nonempty) ∧
    ∀ (a : ℤ) (m : ℕ), 1 < m → ¬ Covers {(a, m)} := by
  constructor
  · intro C h
    obtain ⟨c, hc, -⟩ := h 0
    exact ⟨c, hc⟩
  · intro a m hm h
    obtain ⟨c, hc, hdvd⟩ := h (a + 1)
    simp only [Finset.mem_singleton] at hc
    subst c
    norm_num at hdvd
    have hnat : m ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using hdvd)
    exact (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) hnat)) hm

end Submissions.Erdos273CoverBoundary.Worker09Direct

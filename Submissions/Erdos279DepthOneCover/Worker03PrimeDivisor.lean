import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos279DepthOneCover.Worker03PrimeDivisor

theorem proof :
    ∃ a : ℕ → ℕ, ∃ N : ℕ,
      (∀ p : ℕ, p.Prime → a p < p) ∧
      ∀ n ≥ N, ∃ p : ℕ, ∃ t ≥ 1,
        p.Prime ∧ n = a p + t * p := by
  refine ⟨fun _ ↦ 0, 2, ?_, ?_⟩
  · intro p hp
    exact hp.pos
  · intro n hn
    obtain ⟨p, hp, hpdvd⟩ :=
      Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    obtain ⟨t, rfl⟩ := hpdvd
    have ht : 1 ≤ t := by
      by_contra h
      have : t = 0 := by omega
      subst t
      simp at hn
    exact ⟨p, t, ht, hp, by simp [Nat.mul_comm]⟩

end Submissions.Erdos279DepthOneCover.Worker03PrimeDivisor

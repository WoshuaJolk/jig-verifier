import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos10LinearPowerBound.LinearBaseline

def represented (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum

theorem proof : ∀ n ≥ 2, represented n n := by
  intro n hn
  refine ⟨2, Multiset.replicate (n - 2) 0, by norm_num, ?_, ?_⟩
  · simp
  · simp
    omega

end Submissions.Erdos10LinearPowerBound.LinearBaseline

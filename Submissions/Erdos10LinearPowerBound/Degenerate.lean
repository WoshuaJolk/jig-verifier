import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos10LinearPowerBound.Degenerate

def represented (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum

theorem proof : False → ∀ n ≥ 2, represented n n := by
  intro h
  exact h.elim

end Submissions.Erdos10LinearPowerBound.Degenerate

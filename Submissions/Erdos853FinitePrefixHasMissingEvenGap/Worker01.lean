import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos853FinitePrefixHasMissingEvenGap.Worker01

open scoped Classical

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

theorem proof :
    ∀ x : ℕ, ∃ t : ℕ, 0 < t ∧ t % 2 = 0 ∧
      ¬∃ n ≤ x, primeGap n = t := by
  intro x
  let M := (Finset.range (x + 1)).sup primeGap
  refine ⟨2 * (M + 1), by omega, by omega, ?_⟩
  rintro ⟨n, hn, heq⟩
  have hmem : n ∈ Finset.range (x + 1) := by
    simp only [Finset.mem_range]
    omega
  have hle : primeGap n ≤ M := by
    exact Finset.le_sup (f := primeGap) hmem
  omega

end Submissions.Erdos853FinitePrefixHasMissingEvenGap.Worker01

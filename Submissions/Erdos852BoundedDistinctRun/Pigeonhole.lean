import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

namespace Submissions.Erdos852BoundedDistinctRun.Pigeonhole

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def DistinctRun (start length : ℕ) : Prop :=
  (Finset.range length : Set ℕ).Pairwise fun i j =>
    primeGap (start + i) ≠ primeGap (start + j)

theorem proof :
    ∀ start length B : ℕ,
      DistinctRun start length →
        (∀ i < length, primeGap (start + i) ≤ B) →
          length ≤ B + 1 := by
  intro start length B hdistinct hbounded
  let f : Fin length → Fin (B + 1) := fun i =>
    ⟨primeGap (start + i), by
      exact Nat.lt_succ_of_le (hbounded i i.isLt)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have hgap :
        primeGap (start + (i : ℕ)) ≠
          primeGap (start + (j : ℕ)) := by
      exact hdistinct
        (Finset.mem_range.mpr i.isLt)
        (Finset.mem_range.mpr j.isLt)
        hne
    exact hgap (congrArg Fin.val hij)
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

end Submissions.Erdos852BoundedDistinctRun.Pigeonhole

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos385CompositeWitnessLowerBound.Worker01

open scoped Classical

def IsComposite (m : ℕ) : Prop :=
  1 < m ∧ ¬m.Prime

noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.range n).filter IsComposite).sup (fun m ↦ m + m.minFac)

theorem proof :
    ∀ n m : ℕ, m < n → IsComposite m →
      m + m.minFac ≤ F n ∧ (n < m + m.minFac → n < F n) := by
  intro n m hmn hcomp
  have hmem : m ∈ (Finset.range n).filter IsComposite := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hmn, hcomp⟩
  have hle : m + m.minFac ≤ F n := by
    exact Finset.le_sup (f := fun x ↦ x + x.minFac) hmem
  exact ⟨hle, fun hover ↦ hover.trans_le hle⟩

end Submissions.Erdos385CompositeWitnessLowerBound.Worker01

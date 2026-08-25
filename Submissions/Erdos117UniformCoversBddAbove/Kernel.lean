import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117UniformCoversBddAbove.Kernel

theorem proof :
    (∀ (α : Type) (coverOK : Finset α → Prop) (bound : ℕ),
        (∃ C : Finset α, coverOK C ∧ C.card ≤ bound) →
        sInf {k : ℕ | ∃ C : Finset α, C.card = k ∧ coverOK C} ≤ bound) ∧
    ∀ (ι : Type) (value : ι → ℕ) (admissible : ι → Prop) (bound : ℕ),
      (∀ i : ι, admissible i → value i ≤ bound) →
      BddAbove {k : ℕ | ∃ i : ι, admissible i ∧ value i = k} := by
  constructor
  · intro α coverOK bound hcover
    obtain ⟨C, hC, hcard⟩ := hcover
    refine (Nat.sInf_le (s := {k : ℕ | ∃ A : Finset α,
      A.card = k ∧ coverOK A}) ?_).trans hcard
    exact ⟨C, rfl, hC⟩
  · intro ι value admissible bound hbound
    rw [bddAbove_def]
    refine ⟨bound, ?_⟩
    intro k hk
    obtain ⟨i, hi, rfl⟩ := hk
    exact hbound i hi

end Submissions.Erdos117UniformCoversBddAbove.Kernel

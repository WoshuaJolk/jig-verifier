import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos138InitialValues.Direct

def IsAPOfLengthWith (s : Set ℕ) (l : ℕ∞) (a d : ℕ) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength (s : Set ℕ) (l : ℕ∞) : Prop :=
  ∃ a d : ℕ, IsAPOfLengthWith s l a d

def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set ℕ}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, IsAPOfLength ((·.1) '' ap) k ∧
    ∀ m ∈ ap, coloring m = c

def monoAPGuaranteeSet (r k : ℕ) : Set ℕ :=
  {N | ∀ coloring : Finset.Icc 1 N → Fin r,
    ContainsMonoAPofLength coloring k}

noncomputable def monoAPNumber (r k : ℕ) : ℕ :=
  sInf (monoAPGuaranteeSet r k)

noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

theorem zero_guarantees_length_zero : 0 ∈ monoAPGuaranteeSet 2 0 := by
  intro coloring
  refine ⟨0, ∅, ?_, by simp⟩
  refine ⟨0, 0, ?_⟩
  simp [IsAPOfLengthWith]

theorem one_guarantees_length_one : 1 ∈ monoAPGuaranteeSet 2 1 := by
  intro coloring
  let x : Finset.Icc 1 1 := ⟨1, by simp⟩
  refine ⟨coloring x, {x}, ?_, by simp⟩
  refine ⟨1, 0, ?_⟩
  simp [IsAPOfLengthWith, x]

theorem zero_does_not_guarantee_length_one :
    0 ∉ monoAPGuaranteeSet 2 1 := by
  intro h
  let coloring : Finset.Icc 1 0 → Fin 2 := fun x => by
    have := x.property
    simp at this
  obtain ⟨c, ap, hap, hmono⟩ := h coloring
  have hap_empty : ap = ∅ := by
    ext x
    have := x.property
    simp at this
  subst ap
  simp [IsAPOfLength, IsAPOfLengthWith] at hap

theorem proof : W 0 = 0 ∧ W 1 = 1 := by
  constructor
  · exact (Nat.sInf_eq_zero).2 (Or.inl zero_guarantees_length_zero)
  · have hle : W 1 ≤ 1 := Nat.sInf_le one_guarantees_length_one
    have hne : W 1 ≠ 0 := by
      intro hzero
      rcases (Nat.sInf_eq_zero).1 hzero with hmem | hempty
      · exact zero_does_not_guarantee_length_one hmem
      · exact (Set.nonempty_iff_ne_empty.mp
          ⟨1, one_guarantees_length_one⟩) hempty
    omega

end Submissions.Erdos138InitialValues.Direct

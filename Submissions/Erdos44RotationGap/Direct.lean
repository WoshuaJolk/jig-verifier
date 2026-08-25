import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos44RotationGap.Direct

open Set Finset

def rot (n r x : ℕ) : ℕ := (x + n - r) % n

def ForwardDifferenceUnique (n : ℕ) (D : Finset ℕ) : Prop :=
  ∀ r ∈ D, ∀ x ∈ D, ∀ u ∈ D, ∀ v ∈ D,
    r ≠ x → u ≠ v → rot n r x = rot n u v → r = u ∧ x = v

theorem proof :
    ∀ (n K : ℕ) (D : Finset ℕ), 0 < n →
      ForwardDifferenceUnique n D →
      (∀ r ∈ D, ∀ x ∈ D, r ≠ x → 0 < rot n r x) →
      K < D.card →
        ∃ r ∈ D, ∀ x ∈ D, x ≠ r → K < rot n r x := by
  classical
  intro n K D hn hunique hpositive hKD
  by_contra hno
  push_neg at hno
  let bad := D.filter fun r => ∃ x ∈ D, x ≠ r ∧ rot n r x ≤ K
  have hDbad : D ⊆ bad := by
    intro r hr
    rcases hno r hr with ⟨x, hx, hxr, hshort⟩
    exact Finset.mem_filter.mpr ⟨hr, x, hx, hxr, hshort⟩
  let witness : ℕ → ℕ := fun r =>
    if hr : r ∈ bad then Classical.choose (Finset.mem_filter.mp hr).2 else 0
  have witness_spec :
      ∀ r ∈ bad, witness r ∈ D ∧ witness r ≠ r ∧ rot n r (witness r) ≤ K := by
    intro r hr
    dsimp [witness]
    rw [dif_pos hr]
    exact Classical.choose_spec (Finset.mem_filter.mp hr).2
  let delta : ℕ → ℕ := fun r => rot n r (witness r)
  have hdelta_inj : Set.InjOn delta bad := by
    intro r hr u hu heq
    have hrbad := (Finset.mem_filter.mp hr).1
    have hubad := (Finset.mem_filter.mp hu).1
    have hrs := witness_spec r hr
    have hus := witness_spec u hu
    exact (hunique r hrbad (witness r) hrs.1 u hubad (witness u) hus.1
      (Ne.symm hrs.2.1) (Ne.symm hus.2.1)
      (by simpa only [delta] using heq)).1
  have himage :
      bad.image delta ⊆ Finset.Icc 1 K := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨r, hr, rfl⟩
    have hrs := witness_spec r hr
    have hrD := (Finset.mem_filter.mp hr).1
    exact Finset.mem_Icc.mpr
      ⟨hpositive r hrD (witness r) hrs.1 (Ne.symm hrs.2.1), hrs.2.2⟩
  have hbad : bad.card ≤ K := by
    rw [← Finset.card_image_of_injOn hdelta_inj]
    calc
      (bad.image delta).card ≤ (Finset.Icc 1 K).card :=
        Finset.card_le_card himage
      _ = K := by simp
  have hcard := Finset.card_le_card hDbad
  omega

end Submissions.Erdos44RotationGap.Direct

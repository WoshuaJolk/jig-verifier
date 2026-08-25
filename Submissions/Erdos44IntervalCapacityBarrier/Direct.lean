import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos44IntervalCapacityBarrier.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem proof :
    ∀ (R L : ℕ) (C : Finset ℕ), R ≤ L →
      C ⊆ Finset.Icc R L → IsSidon (C : Set ℕ) →
        C.card * C.card - C.card ≤ 2 * (L - R) := by
  classical
  intro R L C hRL hsub hC
  let code : ℕ × ℕ → ℕ := fun p =>
    if p.1 < p.2 then 2 * (p.2 - p.1) else 2 * (p.1 - p.2) + 1
  have hinj : Set.InjOn code (C.offDiag : Set (ℕ × ℕ)) := by
    rintro ⟨x, y⟩ hp ⟨u, v⟩ hq heq
    have hp' := Finset.mem_offDiag.mp hp
    have hq' := Finset.mem_offDiag.mp hq
    rcases hp' with ⟨hx, hy, hxy⟩
    rcases hq' with ⟨hu, hv, huv⟩
    have xb := Finset.mem_Icc.mp (hsub hx)
    have yb := Finset.mem_Icc.mp (hsub hy)
    have ub := Finset.mem_Icc.mp (hsub hu)
    have vb := Finset.mem_Icc.mp (hsub hv)
    rcases lt_or_gt_of_ne hxy with hxylt | hxygt <;>
      rcases lt_or_gt_of_ne huv with huvlt | huvgt
    · have hdiff : y - x = v - u := by
        dsimp [code] at heq
        simp only [if_pos hxylt, if_pos huvlt] at heq
        omega
      have hsum : x + v = u + y := by omega
      rcases hC x hx u hu v hv y hy hsum with h | h
      · rcases h with ⟨rfl, rfl⟩
        rfl
      · omega
    · dsimp [code] at heq
      simp only [if_pos hxylt, if_neg (by omega : ¬ u < v)] at heq
      omega
    · dsimp [code] at heq
      simp only [if_neg (by omega : ¬ x < y), if_pos huvlt] at heq
      omega
    · have hdiff : x - y = u - v := by
        dsimp [code] at heq
        simp only [if_neg (by omega : ¬ x < y), if_neg (by omega : ¬ u < v)] at heq
        omega
      have hsum : y + u = v + x := by omega
      rcases hC y hy v hv u hu x hx hsum with h | h
      · rcases h with ⟨rfl, rfl⟩
        rfl
      · omega
  have hcode :
      (C.offDiag.image code) ⊆ Finset.Icc 2 (2 * (L - R) + 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨⟨x, y⟩, hp, rfl⟩
    have hp' := Finset.mem_offDiag.mp hp
    rcases hp' with ⟨hx, hy, hxy⟩
    have xb := Finset.mem_Icc.mp (hsub hx)
    have yb := Finset.mem_Icc.mp (hsub hy)
    dsimp [code]
    split_ifs with hlt
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · have hgt : y < x := lt_of_le_of_ne (by omega) (Ne.symm hxy)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have himage : (C.offDiag.image code).card = C.offDiag.card :=
    Finset.card_image_of_injOn hinj
  calc
    C.card * C.card - C.card = C.offDiag.card := (Finset.offDiag_card C).symm
    _ = (C.offDiag.image code).card := himage.symm
    _ ≤ (Finset.Icc 2 (2 * (L - R) + 1)).card := Finset.card_le_card hcode
    _ = 2 * (L - R) := by simp

end Submissions.Erdos44IntervalCapacityBarrier.Direct

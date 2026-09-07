import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

open scoped Pointwise

namespace Submissions.Erdos52RationalEquivalence.Denominator

theorem common_denominator (A : Finset ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ A, ∃ z : ℤ, (z : ℚ) = d * a := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a A ha ih =>
    obtain ⟨d, hd, hA⟩ := ih
    refine ⟨d * a.den, mul_ne_zero hd (by exact_mod_cast a.den_nz), ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with hb | hb
    · subst b
      refine ⟨d * a.num, ?_⟩
      push_cast
      rw [mul_assoc, mul_comm (a.den : ℚ) a, Rat.mul_den_eq_num]
    · obtain ⟨z, hz⟩ := hA b hb
      refine ⟨z * a.den, ?_⟩
      push_cast
      rw [hz]
      ring


theorem scale_counts (A : Finset ℚ) (d : ℚ) (hd : d ≠ 0) :
    (A.image (fun a => d * a)).card = A.card ∧
    (A.image (fun a => d * a) + A.image (fun a => d * a)).card = (A + A).card ∧
    (A.image (fun a => d * a) * A.image (fun a => d * a)).card = (A * A).card := by
  have hs : (A + A).image (fun a => d * a) =
      A.image (fun a => d * a) + A.image (fun a => d * a) :=
    Finset.image_image₂_distrib (fun a b => mul_add d a b)
  have hp : (A * A).image (fun a => (d * d) * a) =
      A.image (fun a => d * a) * A.image (fun a => d * a) :=
    Finset.image_image₂_distrib (fun a b => mul_mul_mul_comm d d a b)
  refine ⟨Finset.card_image_of_injective A (mul_right_injective₀ hd), ?_, ?_⟩
  · rw [← hs]
    exact Finset.card_image_of_injective (A + A) (mul_right_injective₀ hd)
  · rw [← hp]
    exact Finset.card_image_of_injective (A * A) (mul_right_injective₀ (mul_ne_zero hd hd))

theorem cast_counts (B : Finset ℤ) :
    (B.image (fun b : ℤ => (b : ℚ))).card = B.card ∧
    (B.image (fun b : ℤ => (b : ℚ)) + B.image (fun b : ℤ => (b : ℚ))).card = (B + B).card ∧
    (B.image (fun b : ℤ => (b : ℚ)) * B.image (fun b : ℤ => (b : ℚ))).card = (B * B).card := by
  have hs : (B + B).image (fun b : ℤ => (b : ℚ)) =
      B.image (fun b : ℤ => (b : ℚ)) + B.image (fun b : ℤ => (b : ℚ)) :=
    Finset.image_add (Int.castRingHom ℚ)
  have hp : (B * B).image (fun b : ℤ => (b : ℚ)) =
      B.image (fun b : ℤ => (b : ℚ)) * B.image (fun b : ℤ => (b : ℚ)) :=
    Finset.image_mul (Int.castRingHom ℚ)
  refine ⟨Finset.card_image_of_injective B Int.cast_injective, ?_, ?_⟩
  · rw [← hs]
    exact Finset.card_image_of_injective (B + B) Int.cast_injective
  · rw [← hp]
    exact Finset.card_image_of_injective (B * B) Int.cast_injective

theorem rational_realization (A : Finset ℚ) :
    ∃ B : Finset ℤ, B.card = A.card ∧
      (B + B).card = (A + A).card ∧ (B * B).card = (A * A).card := by
  classical
  obtain ⟨d, hd, h⟩ := common_denominator A
  let B : Finset ℤ := A.attach.image fun a : {x // x ∈ A} => (h a.val a.prop).choose
  have hB : B.image (fun b : ℤ => (b : ℚ)) = A.image (fun a => (d : ℚ) * a) := by
    calc
      B.image (fun b : ℤ => (b : ℚ)) = A.attach.image (fun a : {x // x ∈ A} => (d : ℚ) * a.val) := by
        simp only [B, Finset.image_image]
        apply Finset.image_congr
        intro a _
        exact (h a a.prop).choose_spec
      _ = A.image (fun a => (d : ℚ) * a) := by
        change A.attach.image ((fun a : ℚ => (d : ℚ) * a) ∘ Subtype.val) = _
        rw [← Finset.image_image, Finset.attach_image_val]
  obtain ⟨hC, hS, hP⟩ := cast_counts B
  obtain ⟨hC', hS', hP'⟩ := scale_counts A (d : ℚ) (by exact_mod_cast hd)
  rw [hB] at hC hS hP
  exact ⟨B, hC.symm.trans hC', hS.symm.trans hS', hP.symm.trans hP'⟩

theorem proof :
    (∀ A : Finset ℚ, ∃ B : Finset ℤ, B.card = A.card ∧
      (B + B).card = (A + A).card ∧ (B * B).card = (A * A).card) ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
        (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)) ↔
     (∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℚ,
        (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε))) := by
  refine ⟨rational_realization, ?_, ?_⟩
  · intro h ε hε hε'
    obtain ⟨C, hC, h⟩ := h ε hε hε'
    refine ⟨C, hC, ?_⟩
    intro A
    obtain ⟨B, hB, hS, hP⟩ := rational_realization A
    simpa only [hB, hS, hP] using h B
  · intro h ε hε hε'
    obtain ⟨C, hC, h⟩ := h ε hε hε'
    refine ⟨C, hC, ?_⟩
    intro B
    obtain ⟨hB, hS, hP⟩ := cast_counts B
    simpa only [hB, hS, hP] using h (B.image fun b : ℤ => (b : ℚ))

end Submissions.Erdos52RationalEquivalence.Denominator

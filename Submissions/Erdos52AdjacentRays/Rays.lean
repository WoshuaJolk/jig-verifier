import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

open scoped Pointwise BigOperators

namespace Submissions.Erdos52AdjacentRays.Rays

def raySum (l u : ℚ) (p : ℚ × ℚ) : ℚ × ℚ :=
  (p.1 + p.2, l * p.1 + u * p.2)

theorem raySum_injective {l u : ℚ} (hlu : l ≠ u) :
    Function.Injective (raySum l u) := by
  intro p q h
  have h₁ : p.1 + p.2 = q.1 + q.2 := congrArg Prod.fst h
  have h₂ : l * p.1 + u * p.2 = l * q.1 + u * q.2 := congrArg Prod.snd h
  have h₃ := congrArg (fun x : ℚ => u * x) h₁
  have hz : (l - u) * (p.1 - q.1) = 0 := by nlinarith
  have hp : p.1 = q.1 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr hlu))
  apply Prod.ext hp
  linarith

theorem raySum_sector {l u x y : ℚ} (hlu : l < u) (hx : 0 < x) (hy : 0 < y) :
    l * (x + y) < l * x + u * y ∧ l * x + u * y < u * (x + y) := by
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hlu) hy]
  · nlinarith [mul_pos (sub_pos.mpr hlu) hx]

theorem proof (A : Finset ℚ) (I : Finset ℕ)
    (l u : ℕ → ℚ) (B C : ℕ → Finset ℚ)
    (hlu : ∀ i ∈ I, l i < u i)
    (hord : ∀ i ∈ I, ∀ j ∈ I, i < j → u i ≤ l j)
    (hB : ∀ i ∈ I, ∀ x ∈ B i, 0 < x ∧ x ∈ A ∧ l i * x ∈ A)
    (hC : ∀ i ∈ I, ∀ y ∈ C i, 0 < y ∧ y ∈ A ∧ u i * y ∈ A) :
    (∑ i ∈ I, (B i).card * (C i).card) ≤ (A + A).card ^ 2 := by
  classical
  let F (i : ℕ) := ((B i) ×ˢ (C i)).image (raySum (l i) (u i))
  have hcard (i : ℕ) (hi : i ∈ I) :
      (F i).card = (B i).card * (C i).card := by
    rw [Finset.card_image_of_injective _ (raySum_injective (ne_of_lt (hlu i hi)))]
    exact Finset.card_product _ _
  have hordered (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) (hij : i < j) :
      Disjoint (F i) (F j) := by
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨⟨x, y⟩, hp, hz⟩ := Finset.mem_image.mp hzi
    obtain ⟨⟨v, w⟩, hq, heq⟩ := Finset.mem_image.mp hzj
    have hx := (hB i hi x (Finset.mem_product.mp hp).1).1
    have hy := (hC i hi y (Finset.mem_product.mp hp).2).1
    have hv := (hB j hj v (Finset.mem_product.mp hq).1).1
    have hw := (hC j hj w (Finset.mem_product.mp hq).2).1
    have hs₁ : x + y = v + w := congrArg Prod.fst (hz.trans heq.symm)
    have hs₂ : l i * x + u i * y = l j * v + u j * w :=
      congrArg Prod.snd (hz.trans heq.symm)
    have hupper := (raySum_sector (hlu i hi) hx hy).2
    have hlower := (raySum_sector (hlu j hj) hv hw).1
    rw [← hs₁] at hlower
    have hsep := mul_le_mul_of_nonneg_right (hord i hi j hj hij) (le_of_lt (add_pos hx hy))
    nlinarith
  have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hordered i hi j hj h
    · exact (hordered j hj i hi h).symm
  calc
    (∑ i ∈ I, (B i).card * (C i).card) = ∑ i ∈ I, (F i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hcard i hi).symm
    _ = (I.biUnion F).card := (Finset.card_biUnion hdisj).symm
    _ ≤ ((A + A) ×ˢ (A + A)).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.mp hz
      have hx := (hB i hi x (Finset.mem_product.mp hp).1).2
      have hy := (hC i hi y (Finset.mem_product.mp hp).2).2
      apply Finset.mem_product.mpr
      exact ⟨Finset.add_mem_add hx.1 hy.1, Finset.add_mem_add hx.2 hy.2⟩
    _ = (A + A).card ^ 2 := by rw [Finset.card_product, pow_two]

end Submissions.Erdos52AdjacentRays.Rays

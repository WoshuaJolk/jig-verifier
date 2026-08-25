import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44PolynomialSidonBlocks.Direct

open Set Finset

def PolyIsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

private lemma sum_prod_unordered
    (i j u v : ℕ) (hs : i + j = u + v) (hp : i * j = u * v) :
    (i = u ∧ j = v) ∨ (i = v ∧ j = u) := by
  have hsZ : (i : ℤ) + j = u + v := by exact_mod_cast hs
  have hpZ : (i : ℤ) * j = u * v := by exact_mod_cast hp
  have hf : ((i : ℤ) - u) * ((i : ℤ) - v) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hf with hiu | hiv
  · left
    have hi : i = u := by omega
    exact ⟨hi, by omega⟩
  · right
    have hi : i = v := by omega
    exact ⟨hi, by omega⟩

private lemma encoded_pair_unique
    (k i j u v : ℕ)
    (hi₁ : 1 ≤ i) (hik : i ≤ k)
    (hj₁ : 1 ≤ j) (hjk : j ≤ k)
    (hu₁ : 1 ≤ u) (huk : u ≤ k)
    (hv₁ : 1 ≤ v) (hvk : v ≤ k)
    (h :
      (i + (2 * k + 1) * i^2) + (j + (2 * k + 1) * j^2) =
      (u + (2 * k + 1) * u^2) + (v + (2 * k + 1) * v^2)) :
    (i = u ∧ j = v) ∨ (i = v ∧ j = u) := by
  let q := 2 * k + 1
  have his : i + j < q := by dsimp [q]; omega
  have hus : u + v < q := by dsimp [q]; omega
  have h' :
      (i + j) + q * (i^2 + j^2) =
      (u + v) + q * (u^2 + v^2) := by
    dsimp [q]
    nlinarith
  have hm := congrArg (fun z : ℕ => z % q) h'
  have hs : i + j = u + v := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt his,
      Nat.mod_eq_of_lt hus] using hm
  have hsq : i^2 + j^2 = u^2 + v^2 := by
    have hp :
        q * (i^2 + j^2) = q * (u^2 + v^2) := by omega
    exact Nat.mul_left_cancel (by dsimp [q]; omega) hp
  have hprod : i * j = u * v := by
    nlinarith [sq_nonneg (i + j : ℤ)]
  exact sum_prod_unordered i j u v hs hprod

theorem polynomialSidonBlock (k : ℕ) (hk : 1 ≤ k) :
    let q := 2 * k + 1
    let L := k + q * k^2
    let C := (Finset.Icc 1 k).image (fun i => i + q * i^2)
    C ⊆ Finset.Icc 1 L ∧ C.card = k ∧ PolyIsSidon (C : Set ℕ) := by
  let q := 2 * k + 1
  let L := k + q * k^2
  let f : ℕ → ℕ := fun i => i + q * i^2
  let C := (Finset.Icc 1 k).image f
  have hf_inj : Function.Injective f := by
    intro i j hij
    dsimp [f, q] at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hs : i^2 < j^2 := Nat.pow_lt_pow_left hlt (by omega)
      have hm : (2 * k + 1) * i^2 < (2 * k + 1) * j^2 :=
        Nat.mul_lt_mul_of_pos_left hs (by omega)
      omega
    · have hs : j^2 < i^2 := Nat.pow_lt_pow_left hgt (by omega)
      have hm : (2 * k + 1) * j^2 < (2 * k + 1) * i^2 :=
        Nat.mul_lt_mul_of_pos_left hs (by omega)
      omega
  have hsub : C ⊆ Finset.Icc 1 L := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
    have hib := Finset.mem_Icc.mp hi
    dsimp [f, L, q]
    have hs : i^2 ≤ k^2 := Nat.pow_le_pow_left hib.2 2
    have hm : (2 * k + 1) * i^2 ≤ (2 * k + 1) * k^2 :=
      Nat.mul_le_mul_left (2 * k + 1) hs
    exact Finset.mem_Icc.mpr ⟨by nlinarith, by omega⟩
  have hcard : C.card = k := by
    dsimp only [C]
    rw [Finset.card_image_of_injective _ hf_inj]
    simp
  refine ⟨hsub, hcard, ?_⟩
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  change i₁ ∈ C at hi₁
  change j₁ ∈ C at hj₁
  change i₂ ∈ C at hi₂
  change j₂ ∈ C at hj₂
  rcases Finset.mem_image.mp hi₁ with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hj₁ with ⟨b, hb, rfl⟩
  rcases Finset.mem_image.mp hi₂ with ⟨c, hc, rfl⟩
  rcases Finset.mem_image.mp hj₂ with ⟨d, hd, rfl⟩
  have hab := Finset.mem_Icc.mp ha
  have hbb := Finset.mem_Icc.mp hb
  have hcb := Finset.mem_Icc.mp hc
  have hdb := Finset.mem_Icc.mp hd
  dsimp only [f]
  rcases encoded_pair_unique k a c b d
    hab.1 hab.2 hcb.1 hcb.2 hbb.1 hbb.2 hdb.1 hdb.2 hsum
    with h | h
  · left
    exact ⟨by simp [h.1], by simp [h.2]⟩
  · right
    exact ⟨by simp [h.1], by simp [h.2]⟩

theorem proof :
    ∀ k : ℕ, 1 ≤ k →
      let q := 2 * k + 1
      let L := k + q * k^2
      let C := (Finset.Icc 1 k).image (fun i => i + q * i^2)
      C ⊆ Finset.Icc 1 L ∧ C.card = k ∧ PolyIsSidon (C : Set ℕ) :=
  polynomialSidonBlock

end Submissions.Erdos44PolynomialSidonBlocks.Direct

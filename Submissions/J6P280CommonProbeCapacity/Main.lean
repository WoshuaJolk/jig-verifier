import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace Submissions.J6P280CommonProbeCapacity.Main

def IsSidon (A : Set ℤ) : Prop :=
  ∀ ⦃a b c d : ℤ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem unique_nonzero_difference {A : Set ℤ} (hA : IsSidon A)
    {a b c d : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hab : a ≠ b) (heq : a - b = c - d) :
    a = c ∧ b = d := by
  rcases hA ha hd hc hb (by omega) with h | h
  · exact ⟨h.1, h.2.symm⟩
  · exact False.elim (hab h.1)

def offPairs (F : Finset ℤ) : Finset (ℤ × ℤ) :=
  (F ×ˢ F).filter (fun p => p.1 ≠ p.2)

theorem mem_offPairs (F : Finset ℤ) (p : ℤ × ℤ) :
    p ∈ offPairs F ↔ p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≠ p.2 := by
  simp [offPairs, and_assoc]

theorem offPairs_disjoint {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ)
    (hdis : (i : Set I).PairwiseDisjoint F) :
    (i : Set I).PairwiseDisjoint (fun j => offPairs (F j)) := by
  intro j hj k hk hne
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (hdis hj hk hne)
    ((mem_offPairs _ _).mp hp).1 ((mem_offPairs _ _).mp hq).1

theorem shared_difference_injective {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A) :
    Set.InjOn (fun p : ℤ × ℤ => p.1 - p.2)
      (i.biUnion (fun j => offPairs (F j))) := by
  intro p hp q hq heq
  obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨k, hk, hq⟩ := Finset.mem_biUnion.mp hq
  have hp' := (mem_offPairs _ _).mp hp
  have hq' := (mem_offPairs _ _).mp hq
  have h := unique_nonzero_difference hA
    (hsub j hj p.1 hp'.1) (hsub j hj p.2 hp'.2.1)
    (hsub k hk q.1 hq'.1) (hsub k hk q.2 hq'.2.1) hp'.2.2 heq
  exact Prod.ext h.1 h.2

theorem weighted_off_diagonal {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (D : Finset ℤ) (w : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hw : ∀ d ∈ D, 0 ≤ w d) :
    (∑ j ∈ i, ∑ p ∈ offPairs (F j), w (p.1 - p.2)) ≤
      ∑ d ∈ D.erase 0, w d := by
  let U := i.biUnion (fun j => offPairs (F j))
  have hinj := shared_difference_injective i F A hA hsub
  have hinc : U.image (fun p : ℤ × ℤ => p.1 - p.2) ⊆ D.erase 0 := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    have hh := (mem_offPairs _ _).mp hp
    exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hh.2.2,
      hD j hj p.1 hh.1 p.2 hh.2.1⟩
  calc
    _ = ∑ p ∈ U, w (p.1 - p.2) :=
      (Finset.sum_biUnion (offPairs_disjoint i F hdis)).symm
    _ = ∑ d ∈ U.image (fun p : ℤ × ℤ => p.1 - p.2), w d :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ d ∈ D.erase 0, w d :=
      Finset.sum_le_sum_of_subset_of_nonneg hinc
        (fun d hd _ => hw d (Finset.mem_of_mem_erase hd))

theorem diagonal_decomposition (F : Finset ℤ) (w : ℤ → ℝ) :
    (∑ a ∈ F, ∑ b ∈ F, w (a - b)) =
      (F.card : ℝ) * w 0 + ∑ p ∈ offPairs F, w (p.1 - p.2) := by
  have hdiag : (∑ p ∈ (F ×ˢ F).filter (fun p => p.1 = p.2),
      w (p.1 - p.2)) = (F.card : ℝ) * w 0 := by
    rw [Finset.sum_filter, Finset.sum_product]
    simp
  have h := Finset.sum_filter_add_sum_filter_not
    (F ×ˢ F) (fun p : ℤ × ℤ => p.1 = p.2) (fun p => w (p.1 - p.2))
  rw [hdiag] at h
  simpa only [offPairs, Finset.sum_product] using h.symm

theorem actual_sidon_weighted_capacity {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (D : Finset ℤ) (w : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hzero : 0 ∈ D) (hw : ∀ d ∈ D, 0 ≤ w d)
    (hprob : ∑ d ∈ D, w d = 1) :
    (∑ j ∈ i, ∑ a ∈ F j, ∑ b ∈ F j, w (a - b)) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * w 0 := by
  have hoff := weighted_off_diagonal i F A D w hA hsub hdis hD hw
  have hmass : (∑ d ∈ D.erase 0, w d) + w 0 = 1 := by
    rw [Finset.sum_erase_add _ _ hzero, hprob]
  calc
    _ = (∑ j ∈ i, ((F j).card : ℝ)) * w 0 +
        ∑ j ∈ i, ∑ p ∈ offPairs (F j), w (p.1 - p.2) := by
      simp_rw [diagonal_decomposition]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (∑ j ∈ i, ((F j).card : ℝ)) * w 0 +
        ∑ d ∈ D.erase 0, w d := add_le_add (le_refl _) hoff
    _ = 1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * w 0 := by
      nlinarith [hmass]

theorem translate_sum (T K : Finset ℤ) (f : ℤ → ℝ) (a : ℤ)
    (hsupport : ∀ t, t ∉ T → f t = 0)
    (hK : ∀ t ∈ T, t + a ∈ K) :
    (∑ x ∈ K, f (x - a)) = ∑ t ∈ T, f t := by
  have hinc : T.image (fun t => t + a) ⊆ K := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact hK t ht
  have hinj : Set.InjOn (fun t : ℤ => t + a) T := by
    intro x hx y hy hxy
    change x + a = y + a at hxy
    omega
  calc
    _ = ∑ x ∈ T.image (fun t => t + a), f (x - a) := by
      symm
      apply Finset.sum_subset hinc
      intro x hx hnot
      apply hsupport
      intro hmem
      apply hnot
      exact Finset.mem_image.mpr ⟨x - a, hmem, by omega⟩
    _ = ∑ t ∈ T, f t := by
      rw [Finset.sum_image hinj]
      simp

noncomputable def correlation (T : Finset ℤ) (mu : ℤ → ℝ) (d : ℤ) : ℝ :=
  ∑ t ∈ T, mu t * mu (t + d)

theorem correlation_nonneg (T : Finset ℤ) (mu : ℤ → ℝ)
    (hmu : ∀ t, 0 ≤ mu t) (d : ℤ) : 0 ≤ correlation T mu d :=
  Finset.sum_nonneg fun t _ht => mul_nonneg (hmu t) (hmu (t + d))

theorem correlation_zero (T : Finset ℤ) (mu : ℤ → ℝ) :
    correlation T mu 0 = ∑ t ∈ T, (mu t) ^ 2 := by
  simp [correlation, sq]

theorem correlation_mass (T D : Finset ℤ) (mu : ℤ → ℝ)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hprob : ∑ t ∈ T, mu t = 1) :
    (∑ d ∈ D, correlation T mu d) = 1 := by
  have hshift : ∀ t ∈ T, (∑ d ∈ D, mu (t + d)) = 1 := by
    intro t ht
    have h := translate_sum T D mu (-t) hsupport
      (fun u hu => by simpa only [sub_eq_add_neg] using hD t ht u hu)
    simpa only [sub_neg_eq_add, add_comm, hprob] using h
  simp only [correlation]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t ∈ T, mu t * (∑ d ∈ D, mu (t + d)) := by
      simp only [Finset.mul_sum]
    _ = ∑ t ∈ T, mu t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hshift t ht, mul_one]
    _ = 1 := hprob

theorem translated_pair_correlation (T K : Finset ℤ) (mu : ℤ → ℝ)
    (a b : ℤ) (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK : ∀ t ∈ T, t + a ∈ K) :
    (∑ x ∈ K, mu (x - a) * mu (x - b)) = correlation T mu (a - b) := by
  have h := translate_sum T K (fun t => mu t * mu (t + (a - b))) a
    (fun t ht => by rw [hsupport t ht, zero_mul]) hK
  calc
    _ = ∑ x ∈ K, mu (x - a) * mu ((x - a) + (a - b)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show (x - a) + (a - b) = x - b by omega]
    _ = correlation T mu (a - b) := h

theorem convolution_energy_expansion (F T K : Finset ℤ) (mu : ℤ → ℝ)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK : ∀ a ∈ F, ∀ t ∈ T, t + a ∈ K) :
    (∑ x ∈ K, (∑ a ∈ F, mu (x - a)) ^ 2) =
      ∑ a ∈ F, ∑ b ∈ F, correlation T mu (a - b) := by
  calc
    _ = ∑ x ∈ K, ∑ a ∈ F, ∑ b ∈ F, mu (x - a) * mu (x - b) := by
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact mul_comm _ _
    _ = ∑ a ∈ F, ∑ b ∈ F, ∑ x ∈ K, mu (x - a) * mu (x - b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a ∈ F, ∑ b ∈ F, correlation T mu (a - b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact translated_pair_correlation T K mu a b hsupport (hK a ha)

theorem actual_common_probe_capacity {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (T K D : Finset ℤ) (mu : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K)
    (hzero : 0 ∈ D) (hmu : ∀ t, 0 ≤ mu t)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hprob : ∑ t ∈ T, mu t = 1) :
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, mu (x - a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * (∑ t ∈ T, (mu t) ^ 2) := by
  calc
    _ = ∑ j ∈ i, ∑ a ∈ F j, ∑ b ∈ F j, correlation T mu (a - b) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact convolution_energy_expansion (F j) T K mu hsupport (hK j hj)
    _ ≤ 1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * correlation T mu 0 :=
      actual_sidon_weighted_capacity i F A D (correlation T mu) hA hsub hdis hFD
        hzero (fun d hd => correlation_nonneg T mu hmu d)
        (correlation_mass T D mu hsupport hTD hprob)
    _ = _ := by rw [correlation_zero]


theorem proof {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (T K D : Finset ℤ) (mu : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K)
    (hzero : 0 ∈ D) (hmu : ∀ t, 0 ≤ mu t)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hprob : ∑ t ∈ T, mu t = 1) :
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, mu (x - a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * (∑ t ∈ T, (mu t) ^ 2) :=
  actual_common_probe_capacity i F A T K D mu hA hsub hdis hFD hTD hK
    hzero hmu hsupport hprob

end Submissions.J6P280CommonProbeCapacity.Main

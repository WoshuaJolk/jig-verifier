import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Submissions.J6P280NonuniformProductCapacity.Main

open scoped BigOperators

namespace ConditionalProbe

theorem weighted_square {Z : Type*} (z : Finset Z) (w x : Z → ℝ)
    (hw : ∀ a ∈ z, 0 ≤ w a) (hprob : ∑ a ∈ z, w a = 1) :
    (∑ a ∈ z, w a * x a) ^ 2 ≤ ∑ a ∈ z, w a * (x a) ^ 2 := by
  let m := ∑ a ∈ z, w a * x a
  have hvar : 0 ≤ ∑ a ∈ z, w a * (x a - m) ^ 2 :=
    Finset.sum_nonneg fun a ha => mul_nonneg (hw a ha) (sq_nonneg _)
  have hid : (∑ a ∈ z, w a * (x a - m) ^ 2) =
      (∑ a ∈ z, w a * (x a) ^ 2) - m ^ 2 := by
    calc
      _ = ∑ a ∈ z, (w a * (x a) ^ 2 - 2 * m * (w a * x a) +
          m ^ 2 * w a) := Finset.sum_congr rfl fun a _ => by ring
      _ = (∑ a ∈ z, w a * (x a) ^ 2) -
          2 * m * (∑ a ∈ z, w a * x a) + m ^ 2 * (∑ a ∈ z, w a) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ a ∈ z, w a * (x a) ^ 2) - m ^ 2 := by rw [hprob]; dsimp [m]; ring
  rw [hid] at hvar
  exact sub_nonneg.mp hvar

theorem mixture_energy {I Z X : Type*} (i : Finset I) (z : Finset Z)
    (x : Finset X) (w : Z → ℝ) (v : I → Z → X → ℝ)
    (hw : ∀ a ∈ z, 0 ≤ w a) (hprob : ∑ a ∈ z, w a = 1) :
    (∑ b ∈ i, ∑ c ∈ x, (∑ a ∈ z, w a * v b a c) ^ 2) ≤
      ∑ a ∈ z, w a * (∑ b ∈ i, ∑ c ∈ x, (v b a c) ^ 2) := by
  calc
    _ ≤ ∑ b ∈ i, ∑ c ∈ x, ∑ a ∈ z, w a * (v b a c) ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.sum_le_sum fun c hc => weighted_square z w (v b · c) hw hprob
    _ = ∑ a ∈ z, w a * (∑ b ∈ i, ∑ c ∈ x, (v b a c) ^ 2) := by
      simp_rw [Finset.mul_sum]
      calc
        _ = ∑ b ∈ i, ∑ a ∈ z, ∑ c ∈ x, w a * (v b a c) ^ 2 := by
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem fiber_collision {X : Type*} (x : Finset X) (g : X → ℝ) (a : ℝ)
    (hg : ∀ c ∈ x, 0 ≤ g c) (ha : ∀ c ∈ x, g c ≤ a)
    (hmass : 0 < ∑ c ∈ x, g c) :
    (∑ c ∈ x, (g c) ^ 2) / (∑ c ∈ x, g c) ≤ a := by
  apply (div_le_iff₀ hmass).mpr
  calc
    _ ≤ ∑ c ∈ x, a * g c := Finset.sum_le_sum fun c hc => by
      simpa only [sq] using mul_le_mul_of_nonneg_right (ha c hc) (hg c hc)
    _ = a * (∑ c ∈ x, g c) := (Finset.mul_sum x _ _).symm

theorem normalized_collision {X : Type*} (x : Finset X) (g : X → ℝ)
    (w : ℝ) (hw : w ≠ 0) :
    w * (∑ c ∈ x, (g c / w) ^ 2) = (∑ c ∈ x, (g c) ^ 2) / w := by
  calc
    _ = ∑ c ∈ x, (g c) ^ 2 / w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [div_pow, show w ^ 2 = w * w by ring, ← mul_div_assoc,
        mul_div_mul_left _ _ hw]
    _ = (∑ c ∈ x, (g c) ^ 2) / w := by
      simp only [div_eq_mul_inv, Finset.sum_mul]

theorem total_conditional_collision {Z X : Type*} (z : Finset Z) (x : Finset X)
    (g : Z → X → ℝ) (a : ℝ)
    (hg : ∀ b ∈ z, ∀ c ∈ x, 0 ≤ g b c)
    (ha : ∀ b ∈ z, ∀ c ∈ x, g b c ≤ a)
    (hmass : ∀ b ∈ z, 0 < ∑ c ∈ x, g b c) :
    (∑ b ∈ z, (∑ c ∈ x, g b c) *
      (∑ c ∈ x, (g b c / (∑ d ∈ x, g b d)) ^ 2)) ≤ (z.card : ℝ) * a := by
  calc
    _ ≤ ∑ b ∈ z, a := by
      apply Finset.sum_le_sum
      intro b hb
      rw [normalized_collision x (g b) _ (ne_of_gt (hmass b hb))]
      exact fiber_collision x (g b) a (hg b hb) (ha b hb) (hmass b hb)
    _ = (z.card : ℝ) * a := by simp

theorem common_probe_diagonal {D : Type*} [DecidableEq D]
    (d : Finset D) (zero : D) (hzero : zero ∈ d) (b r : D → ℝ) (s : ℝ)
    (hb : ∀ a ∈ d, 0 ≤ b a) (hprob : ∑ a ∈ d, b a = 1)
    (hrzero : r zero = s) (hr : ∀ a ∈ d, a ≠ zero → r a ≤ 1) :
    (∑ a ∈ d, r a * b a) ≤ 1 + (s - 1) * b zero := by
  calc
    _ ≤ ∑ a ∈ d, (b a + if a = zero then (s - 1) * b a else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : a = zero
      · subst a
        rw [if_pos rfl, hrzero]
        nlinarith
      · rw [if_neg h, add_zero]
        simpa using mul_le_mul_of_nonneg_right (hr a ha h) (hb a ha)
    _ = 1 + (s - 1) * b zero := by
      rw [Finset.sum_add_distrib, hprob]
      simp [hzero]

theorem conditional_energy_capacity {I Z X Y : Type*}
    (i : Finset I) (z : Finset Z) (x : Finset X) (y : Finset Y)
    (g : Z → Y → ℝ) (v : I → Z → X → ℝ) (a C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ b ∈ z, ∀ c ∈ y, 0 ≤ g b c)
    (ha : ∀ b ∈ z, ∀ c ∈ y, g b c ≤ a)
    (hmass : ∀ b ∈ z, 0 < ∑ c ∈ y, g b c)
    (hprob : ∑ b ∈ z, ∑ c ∈ y, g b c = 1)
    (hcapacity : ∀ b ∈ z,
      (∑ j ∈ i, ∑ c ∈ x, (v j b c) ^ 2) ≤
        1 + C * (∑ c ∈ y, (g b c / (∑ d ∈ y, g b d)) ^ 2)) :
    (∑ j ∈ i, ∑ c ∈ x, (∑ b ∈ z, (∑ d ∈ y, g b d) * v j b c) ^ 2) ≤
      1 + C * ((z.card : ℝ) * a) := by
  let w := fun b => ∑ c ∈ y, g b c
  let k := fun b => ∑ c ∈ y, (g b c / w b) ^ 2
  have hw : ∀ b ∈ z, 0 ≤ w b := fun b hb => le_of_lt (hmass b hb)
  have hk : (∑ b ∈ z, w b * k b) ≤ (z.card : ℝ) * a :=
    total_conditional_collision z y g a hg ha hmass
  calc
    _ ≤ ∑ b ∈ z, w b * (∑ j ∈ i, ∑ c ∈ x, (v j b c) ^ 2) :=
      mixture_energy i z x w v hw hprob
    _ ≤ ∑ b ∈ z, w b * (1 + C * k b) :=
      Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hcapacity b hb) (hw b hb)
    _ = 1 + C * (∑ b ∈ z, w b * k b) := by
      simp_rw [mul_add, mul_one, ← mul_assoc]
      rw [Finset.sum_add_distrib, hprob, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ 1 + C * ((z.card : ℝ) * a) :=
      add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hk hC)

end ConditionalProbe

open scoped BigOperators
open Finset

namespace SidonWeightedDifference

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

end SidonWeightedDifference

open scoped BigOperators
open Finset SidonWeightedDifference

namespace ShiftedMixture

theorem normalized_row_mass (T : Finset ℤ) (g : ℤ → ℝ)
    (hpos : 0 < ∑ t ∈ T, g t) :
    (∑ t ∈ T, g t / (∑ u ∈ T, g u)) = 1 := by
  calc
    _ = (∑ t ∈ T, g t) / (∑ u ∈ T, g u) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := div_self (ne_of_gt hpos)

theorem convolution_support (F T K : Finset ℤ) (mu : ℤ → ℝ)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK : ∀ a ∈ F, ∀ t ∈ T, t + a ∈ K) :
    ∀ x, x ∉ K → (∑ a ∈ F, mu (x - a)) ^ 2 = 0 := by
  intro x hx
  have hz : (∑ a ∈ F, mu (x - a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply hsupport
    intro ht
    have hk := hK a ha (x - a) ht
    have he : x - a + a = x := by omega
    exact hx (he ▸ hk)
  rw [hz, zero_pow (by decide : 2 ≠ 0)]

theorem shifted_convolution_energy (F T K0 K : Finset ℤ) (mu : ℤ → ℝ)
    (c : ℤ) (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK0 : ∀ a ∈ F, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ x ∈ K0, x + c ∈ K) :
    (∑ x ∈ K, (∑ a ∈ F, mu ((x - a) - c)) ^ 2) =
      ∑ x ∈ K0, (∑ a ∈ F, mu (x - a)) ^ 2 := by
  have h := translate_sum K0 K (fun x => (∑ a ∈ F, mu (x - a)) ^ 2) c
    (convolution_support F T K0 mu hsupport hK0) hK
  calc
    _ = ∑ x ∈ K, (∑ a ∈ F, mu ((x - c) - a)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [show (x - a) - c = (x - c) - a by omega]
    _ = _ := h

theorem marginal_convolution {Z : Type*} (z : Finset Z) (T F : Finset ℤ)
    (g : Z → ℤ → ℝ) (c : Z → ℤ) (x : ℤ)
    (hpos : ∀ b ∈ z, 0 < ∑ t ∈ T, g b t) :
    (∑ a ∈ F, ∑ b ∈ z, g b ((x - a) - c b)) =
      ∑ b ∈ z, (∑ t ∈ T, g b t) *
        (∑ a ∈ F, g b ((x - a) - c b) / (∑ t ∈ T, g b t)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (hpos b hb))]

theorem actual_shifted_mixture_capacity {I Z : Type*} [DecidableEq I]
    (i : Finset I) (z : Finset Z) (F : I → Finset ℤ) (A : Set ℤ)
    (T K0 K D : Finset ℤ) (g : Z → ℤ → ℝ) (c : I → Z → ℤ) (alpha : ℝ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK0 : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ j ∈ i, ∀ b ∈ z, ∀ x ∈ K0, x + c j b ∈ K)
    (hzero : 0 ∈ D)
    (hg : ∀ b ∈ z, ∀ t, 0 ≤ g b t)
    (hsupport : ∀ b ∈ z, ∀ t, t ∉ T → g b t = 0)
    (halpha : ∀ b ∈ z, ∀ t ∈ T, g b t ≤ alpha)
    (hpos : ∀ b ∈ z, 0 < ∑ t ∈ T, g b t)
    (hprob : ∑ b ∈ z, ∑ t ∈ T, g b t = 1)
    (hsize : 1 ≤ ∑ j ∈ i, ((F j).card : ℝ)) :
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, ∑ b ∈ z, g b ((x - a) - c j b)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * ((z.card : ℝ) * alpha) := by
  let W := fun b => ∑ t ∈ T, g b t
  let mu := fun b t => g b t / W b
  let v := fun j b x => ∑ a ∈ F j, mu b ((x - a) - c j b)
  have hmu_nonneg : ∀ b ∈ z, ∀ t, 0 ≤ mu b t := by
    intro b hb t
    exact div_nonneg (hg b hb t) (le_of_lt (hpos b hb))
  have hmu_support : ∀ b ∈ z, ∀ t, t ∉ T → mu b t = 0 := by
    intro b hb t ht
    dsimp [mu]
    rw [hsupport b hb t ht, zero_div]
  have hmu_prob : ∀ b ∈ z, (∑ t ∈ T, mu b t) = 1 := by
    intro b hb
    exact normalized_row_mass T (g b) (hpos b hb)
  have hcap : ∀ b ∈ z, (∑ j ∈ i, ∑ x ∈ K, (v j b x) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * (∑ t ∈ T, (mu b t) ^ 2) := by
    intro b hb
    calc
      _ = ∑ j ∈ i, ∑ x ∈ K0, (∑ a ∈ F j, mu b (x - a)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact shifted_convolution_energy (F j) T K0 K (mu b) (c j b)
          (hmu_support b hb) (hK0 j hj) (hK j hj b hb)
      _ ≤ _ := actual_common_probe_capacity i F A T K0 D (mu b) hA hsub hdis
        hFD hTD hK0 hzero (hmu_nonneg b hb) (hmu_support b hb) (hmu_prob b hb)
  have hbound := ConditionalProbe.conditional_energy_capacity i z K T g v alpha
    ((∑ j ∈ i, ((F j).card : ℝ)) - 1) (sub_nonneg.mpr hsize)
    (fun b hb t ht => hg b hb t) halpha hpos hprob hcap
  calc
    _ = ∑ j ∈ i, ∑ x ∈ K, (∑ b ∈ z, W b * v j b x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      exact marginal_convolution z T (F j) g (c j) x hpos
    _ ≤ _ := hbound

end ShiftedMixture


namespace ProductProbe

variable {I : Type*} [DecidableEq I] [DecidableEq (I → ℤ)]

def relative (o : I) (u : I → ℤ) (i : I) : ℤ := u i - u o

noncomputable def patterns (o : I) (O : Finset (I → ℤ)) : Finset (I → ℤ) := by
  classical
  exact O.image (relative o)

noncomputable def row (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (z : I → ℤ) (t : ℤ) : ℝ := by
  classical
  exact ∑ u ∈ O, if z = relative o u then if u o = t then w u else 0 else 0

noncomputable def marginal (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (i : I) (x : ℤ) : ℝ := by
  classical
  exact ∑ u ∈ O, if u i = x then w u else 0

theorem reconstruction (o : I) (u v : I → ℤ)
    (hrel : relative o u = relative o v) (hbase : u o = v o) : u = v := by
  funext i
  have h := congrFun hrel i
  dsimp [relative] at h
  omega

theorem row_nonneg (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (hw : ∀ u ∈ O, 0 ≤ w u) (z : I → ℤ) (t : ℤ) : 0 ≤ row o O w z t := by
  classical
  apply Finset.sum_nonneg
  intro u hu
  split_ifs <;> first | exact hw u hu | exact le_rfl

theorem row_bound (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (alpha : ℝ) (ha : 0 ≤ alpha) (hw : ∀ u ∈ O, w u ≤ alpha)
    (z : I → ℤ) (t : ℤ) : row o O w z t ≤ alpha := by
  classical
  by_cases hex : ∃ u ∈ O, z = relative o u ∧ u o = t
  · obtain ⟨u, hu, hz, ht⟩ := hex
    have he : row o O w z t = w u := by
      unfold row
      rw [Finset.sum_eq_single u]
      · simp [hz, ht]
      · intro v hv hne
        by_cases hvz : z = relative o v
        · by_cases hvt : v o = t
          · have eq := reconstruction o v u (hvz.symm.trans hz) (hvt.trans ht.symm)
            exact False.elim (hne eq)
          · simp [hvz, hvt]
        · simp [hvz]
      · exact fun h => False.elim (h hu)
    rw [he]
    exact hw u hu
  · have he : row o O w z t = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      by_cases hz : z = relative o u
      · by_cases ht : u o = t
        · exact False.elim (hex ⟨u, hu, hz, ht⟩)
        · simp [hz, ht]
      · simp [hz]
    rw [he]
    exact ha

theorem row_support (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (T : Finset ℤ) (hT : ∀ u ∈ O, u o ∈ T) (z : I → ℤ) (t : ℤ)
    (ht : t ∉ T) : row o O w z t = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u hu
  have hne : u o ≠ t := fun h => ht (h ▸ hT u hu)
  simp [hne]

theorem row_mass (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (T : Finset ℤ) (hT : ∀ u ∈ O, u o ∈ T) (z : I → ℤ) :
    (∑ t ∈ T, row o O w z t) = ∑ u ∈ O, if z = relative o u then w u else 0 := by
  classical
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hz : z = relative o u <;> simp [hz, hT u hu]

theorem row_positive (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (T : Finset ℤ) (hT : ∀ u ∈ O, u o ∈ T) (hw : ∀ u ∈ O, 0 < w u)
    (z : I → ℤ) (hz : z ∈ patterns o O) : 0 < ∑ t ∈ T, row o O w z t := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
  rw [row_mass o O w T hT]
  apply lt_of_lt_of_le (hw u hu)
  have h := Finset.single_le_sum
    (fun v hv => show 0 ≤ (if relative o u = relative o v then w v else 0) from
      by split_ifs <;> first | exact le_of_lt (hw v hv) | exact le_rfl) hu
  simpa using h

theorem rows_total (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (T : Finset ℤ) (hT : ∀ u ∈ O, u o ∈ T) :
    (∑ z ∈ patterns o O, ∑ t ∈ T, row o O w z t) = ∑ u ∈ O, w u := by
  classical
  simp_rw [row_mass o O w T hT]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  have hz : relative o u ∈ patterns o O := Finset.mem_image.mpr ⟨u, hu, rfl⟩
  simp [hz]

theorem rows_marginal (o : I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (i : I) (x : ℤ) :
    (∑ z ∈ patterns o O, row o O w z (x - z i)) = marginal O w i x := by
  classical
  unfold row marginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  have hz : relative o u ∈ patterns o O := Finset.mem_image.mpr ⟨u, hu, rfl⟩
  simp only [Finset.sum_ite_eq', hz, if_true]
  have he : u o = x - relative o u i ↔ u i = x := by dsimp [relative]; omega
  simp only [he]

theorem actual_joint_probe_capacity
    (o : I) (i : Finset I) (O : Finset (I → ℤ)) (w : (I → ℤ) → ℝ)
    (F : I → Finset ℤ) (A : Set ℤ) (T K0 K D : Finset ℤ) (alpha : ℝ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK0 : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ j ∈ i, ∀ z ∈ patterns o O, ∀ x ∈ K0, x + z j ∈ K)
    (hzero : 0 ∈ D) (hT : ∀ u ∈ O, u o ∈ T)
    (hw : ∀ u ∈ O, 0 < w u) (hprob : ∑ u ∈ O, w u = 1)
    (ha : 0 ≤ alpha) (halpha : ∀ u ∈ O, w u ≤ alpha)
    (hsize : 1 ≤ ∑ j ∈ i, ((F j).card : ℝ)) :
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, marginal O w j (x-a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * (((patterns o O).card : ℝ) * alpha) := by
  classical
  have h := ShiftedMixture.actual_shifted_mixture_capacity i (patterns o O) F A T K0 K D
    (row o O w) (fun j z => z j) alpha hA hsub hdis hFD hTD hK0 hK hzero
    (fun z hz t => row_nonneg o O w (fun u hu => le_of_lt (hw u hu)) z t)
    (fun z hz t ht => row_support o O w T hT z t ht)
    (fun z hz t ht => row_bound o O w alpha ha halpha z t)
    (fun z hz => row_positive o O w T hT hw z hz)
    (by rw [rows_total o O w T hT, hprob]) hsize
  simpa only [rows_marginal] using h

section Independent
variable [Fintype I]

def tupleValue (U : I → Finset ℤ) (u : (j : I) → U j) : I → ℤ := fun j => u j

noncomputable def independentSpace (U : I → Finset ℤ) : Finset (I → ℤ) := by
  classical
  exact Finset.univ.image (tupleValue U)

noncomputable def independentWeight (f : I → ℤ → ℝ) (u : I → ℤ) : ℝ := ∏ j, f j (u j)

theorem tupleValue_injective (U : I → Finset ℤ) : Function.Injective (tupleValue U) := by
  intro u v h
  funext j
  exact Subtype.ext (congrFun h j)

theorem independent_total (U : I → Finset ℤ) (f : I → ℤ → ℝ)
    (hf : ∀ j, ∑ x ∈ U j, f j x = 1) :
    (∑ u ∈ independentSpace U, independentWeight f u) = 1 := by
  classical
  unfold independentSpace
  rw [Finset.sum_image (fun u hu v hv h => tupleValue_injective U h)]
  change (∑ u : (j : I) → U j, ∏ j, f j (u j)) = 1
  rw [← Fintype.prod_sum (fun (j : I) (x : U j) => f j x)]
  have hh : ∀ j, (∑ x : U j, f j x) = 1 := by
    intro j
    rw [Finset.sum_coe_sort]
    exact hf j
  simp_rw [hh]
  simp

theorem independent_positive (U : I → Finset ℤ) (f : I → ℤ → ℝ)
    (hf : ∀ j, ∀ x ∈ U j, 0 < f j x) (u : I → ℤ)
    (hu : u ∈ independentSpace U) : 0 < independentWeight f u := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  exact Finset.prod_pos fun j hj => hf j (v j) (v j).property

theorem independent_atom (U : I → Finset ℤ) (f : I → ℤ → ℝ) (alpha : I → ℝ)
    (hf : ∀ j, ∀ x ∈ U j, 0 ≤ f j x)
    (ha : ∀ j, ∀ x ∈ U j, f j x ≤ alpha j) (u : I → ℤ)
    (hu : u ∈ independentSpace U) : independentWeight f u ≤ ∏ j, alpha j := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  exact Finset.prod_le_prod (fun j hj => hf j (v j) (v j).property)
    (fun j hj => ha j (v j) (v j).property)

theorem independent_marginal (U : I → Finset ℤ) (f : I → ℤ → ℝ)
    (hf : ∀ j, ∑ x ∈ U j, f j x = 1) (j : I) (x : ℤ) :
    marginal (independentSpace U) (independentWeight f) j x =
      if x ∈ U j then f j x else 0 := by
  classical
  unfold marginal independentSpace
  rw [Finset.sum_image (fun u hu v hv h => tupleValue_injective U h)]
  let g := fun (k : I) (y : U k) => if k = j then if (y : ℤ) = x then f k y else 0 else f k y
  have hprod : ∀ u : (k : I) → U k,
      (if (u j : ℤ) = x then ∏ k, f k (u k) else 0) = ∏ k, g k (u k) := by
    intro u
    by_cases h : (u j : ℤ) = x
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hj : k = j
      · subst k
        simp [g, h]
      · simp [g, hj]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [g, h]
  change (∑ u : (k : I) → U k, if (u j : ℤ) = x then ∏ k, f k (u k) else 0) = _
  simp_rw [hprod]
  rw [← Fintype.prod_sum]
  have hg : ∀ k, k ≠ j → (∑ y : U k, g k y) = 1 := by
    intro k hk
    simpa only [g, if_neg hk, Finset.sum_coe_sort] using hf k
  rw [Finset.prod_eq_single j]
  · simp only [g, if_pos rfl]
    rw [Finset.sum_coe_sort (U j) (fun y : ℤ => if y = x then f j y else 0)]
    simp
  · intro k hk hkj
    exact hg k hkj
  · exact fun h => False.elim (h (Finset.mem_univ j))

theorem actual_independent_probe_capacity
    (o : I) (i : Finset I) (U F : I → Finset ℤ) (f : I → ℤ → ℝ)
    (A : Set ℤ) (T K0 K D : Finset ℤ) (alpha : I → ℝ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK0 : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ j ∈ i, ∀ z ∈ patterns o (independentSpace U), ∀ x ∈ K0, x + z j ∈ K)
    (hzero : 0 ∈ D) (hT : U o ⊆ T)
    (hfpos : ∀ j, ∀ x ∈ U j, 0 < f j x)
    (hfprob : ∀ j, ∑ x ∈ U j, f j x = 1)
    (hfsupport : ∀ j x, x ∉ U j → f j x = 0)
    (ha : ∀ j, 0 ≤ alpha j) (halpha : ∀ j, ∀ x ∈ U j, f j x ≤ alpha j)
    (hsize : 1 ≤ ∑ j ∈ i, ((F j).card : ℝ)) :
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, f j (x-a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) *
        (((patterns o (independentSpace U)).card : ℝ) * ∏ j, alpha j) := by
  classical
  have hanchor : ∀ u ∈ independentSpace U, u o ∈ T := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hT (v o).property
  have h := actual_joint_probe_capacity o i (independentSpace U) (independentWeight f)
    F A T K0 K D (∏ j, alpha j) hA hsub hdis hFD hTD hK0 hK hzero hanchor
    (independent_positive U f hfpos) (independent_total U f hfprob)
    (Finset.prod_nonneg fun j hj => ha j)
    (independent_atom U f alpha (fun j x hx => le_of_lt (hfpos j x hx)) halpha) hsize
  have hm : ∀ j x, marginal (independentSpace U) (independentWeight f) j x = f j x := by
    intro j x
    rw [independent_marginal U f hfprob]
    by_cases hx : x ∈ U j
    · simp [hx]
    · simp [hx, hfsupport j x hx]
  simpa only [hm] using h

end Independent

end ProductProbe

open ProductProbe

theorem result :
  ∀ {I : Type*} [DecidableEq I] [DecidableEq (I → ℤ)] [Fintype I]
    (o : I) (i : Finset I) (U F : I → Finset ℤ) (f : I → ℤ → ℝ)
    (A : Set ℤ) (T K0 K D : Finset ℤ) (alpha : I → ℝ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK0 : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ j ∈ i, ∀ z ∈ patterns o (independentSpace U), ∀ x ∈ K0, x + z j ∈ K)
    (hzero : 0 ∈ D) (hT : U o ⊆ T)
    (hfpos : ∀ j, ∀ x ∈ U j, 0 < f j x)
    (hfprob : ∀ j, ∑ x ∈ U j, f j x = 1)
    (hfsupport : ∀ j x, x ∉ U j → f j x = 0)
    (ha : ∀ j, 0 ≤ alpha j) (halpha : ∀ j, ∀ x ∈ U j, f j x ≤ alpha j)
    (hsize : 1 ≤ ∑ j ∈ i, ((F j).card : ℝ)),
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, f j (x-a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) *
        (((patterns o (independentSpace U)).card : ℝ) * ∏ j, alpha j)
:= @ProductProbe.actual_independent_probe_capacity

end Submissions.J6P280NonuniformProductCapacity.Main

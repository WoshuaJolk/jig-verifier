import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Int.Cast.Lemmas


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

-- The checked adjacent-ray source is prepended before compilation.

namespace Submissions.Erdos52Solymosi.Finite

theorem uniform_bin_energy (A D : Finset ℚ) (F : ℚ → Finset ℚ) (t : ℕ)
    (hF : ∀ r ∈ D, ∀ x ∈ F r, 0 < x ∧ x ∈ A ∧ r * x ∈ A)
    (hlo : ∀ r ∈ D, t ≤ (F r).card)
    (hhi : ∀ r ∈ D, (F r).card ≤ 2 * t) :
    (∑ r ∈ D, (F r).card ^ 2) ≤ 8 * (A + A).card ^ 2 := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hD
  · simp
  let e := D.orderEmbOfFin rfl
  let q (i : ℕ) : ℚ := if h : i < D.card then e ⟨i, h⟩ else 0
  have hmem (i : ℕ) (hi : i < D.card) : q i ∈ D := by
    simp only [q, dif_pos hi]
    exact D.orderEmbOfFin_mem rfl _
  have hmono (i j : ℕ) (hi : i < D.card) (hj : j < D.card) (hij : i ≤ j) :
      q i ≤ q j := by
    simp only [q, dif_pos hi, dif_pos hj]
    exact e.monotone hij
  have hstrict (i j : ℕ) (hi : i < D.card) (hj : j < D.card) (hij : i < j) :
      q i < q j := by
    simp only [q, dif_pos hi, dif_pos hj]
    exact e.strictMono hij
  have hvalid (i : ℕ) (hi : i ∈ Finset.range (D.card - 1)) :
      i < D.card ∧ i + 1 < D.card := by
    have := Finset.mem_range.mp hi
    omega
  have hcore :
      (∑ i ∈ Finset.range (D.card - 1), (F (q i)).card * (F (q (i + 1))).card) ≤
        (A + A).card ^ 2 := by
    apply Submissions.Erdos52AdjacentRays.Rays.proof A
      (Finset.range (D.card - 1)) q (fun i => q (i + 1))
      (fun i => F (q i)) (fun i => F (q (i + 1)))
    · intro i hi
      exact hstrict i (i + 1) (hvalid i hi).1 (hvalid i hi).2 (by omega)
    · intro i hi j hj hij
      exact hmono (i + 1) j (hvalid i hi).2 (hvalid j hj).1 (by omega)
    · intro i hi x hx
      exact hF (q i) (hmem i (hvalid i hi).1) x hx
    · intro i hi x hx
      exact hF (q (i + 1)) (hmem (i + 1) (hvalid i hi).2) x hx
  have hcount : (D.card - 1) * t ^ 2 ≤ (A + A).card ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range (D.card - 1), t ^ 2 := by simp
      _ ≤ ∑ i ∈ Finset.range (D.card - 1),
          (F (q i)).card * (F (q (i + 1))).card := by
        apply Finset.sum_le_sum
        intro i hi
        rw [pow_two]
        exact Nat.mul_le_mul (hlo (q i) (hmem i (hvalid i hi).1))
          (hlo (q (i + 1)) (hmem (i + 1) (hvalid i hi).2))
      _ ≤ _ := hcore
  obtain ⟨r, hr⟩ := hD
  have ht : t ≤ (A + A).card := by
    apply (hlo r hr).trans
    apply (Finset.card_le_card (show F r ⊆ A from ?_)).trans
      Finset.card_le_card_add_self
    intro x hx
    exact (hF r hr x hx).2.1
  have ht₂ : t ^ 2 ≤ (A + A).card ^ 2 := Nat.pow_le_pow_left ht 2
  have hcard : D.card = (D.card - 1) + 1 := by
    have := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  calc
    _ ≤ ∑ r ∈ D, 4 * t ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        _ ≤ (2 * t) ^ 2 := Nat.pow_le_pow_left (hhi r hr) 2
        _ = _ := by ring
    _ = D.card * (4 * t ^ 2) := by simp
    _ = 4 * ((D.card - 1) * t ^ 2) + 4 * t ^ 2 := by
      conv_lhs => rw [hcard]
      ring
    _ ≤ 4 * (A + A).card ^ 2 + 4 * (A + A).card ^ 2 :=
      Nat.add_le_add (Nat.mul_le_mul_left 4 hcount) (Nat.mul_le_mul_left 4 ht₂)
    _ = _ := by omega

end Submissions.Erdos52Solymosi.Finite


open scoped BigOperators

namespace Submissions.Erdos52Solymosi.Dyadic

theorem dyadic_square_sum_le {α : Type*} [DecidableEq α]
    (D : Finset α) (w : α → ℕ) (k H : ℕ)
    (hw : ∀ x ∈ D, w x < 2 ^ k)
    (hbin : ∀ j < k,
      (∑ x ∈ D.filter (fun x => 2 ^ j ≤ w x ∧ w x < 2 ^ (j + 1)),
        (w x) ^ 2) ≤ H) :
    (∑ x ∈ D, (w x) ^ 2) ≤ k * H := by
  induction k generalizing D with
  | zero =>
    rw [Nat.zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro x hx
    have hz : w x = 0 := by
      simpa only [pow_zero, Nat.lt_one_iff] using hw x hx
    exact congrArg (fun n : ℕ => n ^ 2) hz
  | succ k ih =>
    let L := D.filter (fun x => w x < 2 ^ k)
    have hwL : ∀ x ∈ L, w x < 2 ^ k := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hbinL : ∀ j < k,
        (∑ x ∈ L.filter (fun x => 2 ^ j ≤ w x ∧ w x < 2 ^ (j + 1)),
          (w x) ^ 2) ≤ H := by
      intro j hj
      apply (Finset.sum_le_sum_of_subset ?_).trans
        (hbin j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      intro x hx
      obtain ⟨hx, hxbin⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hxbin⟩
    have htop : D.filter (fun x => ¬w x < 2 ^ k) =
        D.filter (fun x => 2 ^ k ≤ w x ∧ w x < 2 ^ (k + 1)) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨hx.1, Nat.not_lt.mp hx.2, hw x hx.1⟩
      · intro hx
        exact ⟨hx.1, Nat.not_lt.mpr hx.2.1⟩
    have hlarge : (∑ x ∈ D.filter (fun x => ¬w x < 2 ^ k), (w x) ^ 2) ≤ H := by
      rw [htop]
      exact hbin k (Nat.lt_succ_self k)
    calc
      (∑ x ∈ D, (w x) ^ 2) =
          (∑ x ∈ L, (w x) ^ 2) +
            ∑ x ∈ D.filter (fun x => ¬w x < 2 ^ k), (w x) ^ 2 :=
        (Finset.sum_filter_add_sum_filter_not D
          (fun x => w x < 2 ^ k) (fun x => (w x) ^ 2)).symm
      _ ≤ k * H + H := Nat.add_le_add (ih L hwL hbinL) hlarge
      _ = (k + 1) * H := by rw [Nat.add_mul, Nat.one_mul]

end Submissions.Erdos52Solymosi.Dyadic


open scoped Pointwise BigOperators

namespace Submissions.Erdos52AdjacentRays.Energy

/-- Multiplicative energy is the sum of the squared populations of the rays
through the positive rational grid `A × A`. The empty set is allowed. -/
theorem mulEnergy_eq_sum_ray_card_sq (A : Finset ℚ)
    (hA : ∀ a ∈ A, 0 < a) :
    Finset.mulEnergy A A =
      ∑ r ∈ A / A, (A.filter (fun x => r * x ∈ A)).card ^ 2 := by
  let Q := ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    (fun q : (ℚ × ℚ) × (ℚ × ℚ) => q.1.1 * q.2.1 = q.1.2 * q.2.2)
  have hmap : (Q : Set ((ℚ × ℚ) × (ℚ × ℚ))).MapsTo
      (fun q => q.1.2 / q.1.1) ((A / A : Finset ℚ) : Set ℚ) := by
    intro q hq
    change q ∈ Q at hq
    simp only [Q, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨⟨ha, hb⟩, ⟨_, _⟩⟩, _⟩ := hq
    exact Finset.div_mem_div hb ha
  change Q.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro r _
  let F := A.filter (fun x => r * x ∈ A)
  have recover (a b c d : ℚ) (ha : a ∈ A)
      (he : a * c = b * d) (hr : b / a = r) :
      b = r * a ∧ c = r * d := by
    have ha0 : a ≠ 0 := ne_of_gt (hA a ha)
    have hb : b = r * a := (div_eq_iff ha0).mp hr
    refine ⟨hb, mul_left_cancel₀ ha0 ?_⟩
    calc
      a * c = b * d := he
      _ = a * (r * d) := by rw [hb]; ac_rfl
  have hcard : (Q.filter (fun q => q.1.2 / q.1.1 = r)).card =
      (F ×ˢ F).card := by
    apply Finset.card_bij (fun q _ => (q.1.1, q.2.2))
    · intro q hq
      obtain ⟨hq, hr⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq, he⟩ := Finset.mem_filter.mp hq
      simp only [Finset.mem_product] at hq
      obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ := hq
      obtain ⟨hb', hc'⟩ := recover _ _ _ _ ha he hr
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨ha, hb' ▸ hb⟩,
         Finset.mem_filter.mpr ⟨hd, hc' ▸ hc⟩⟩
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hq' heq
      obtain ⟨hq, hr⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq, he⟩ := Finset.mem_filter.mp hq
      simp only [Finset.mem_product] at hq
      obtain ⟨⟨ha, _⟩, ⟨_, _⟩⟩ := hq
      obtain ⟨hb, hc⟩ := recover a b c d ha he hr
      obtain ⟨hq', hr'⟩ := Finset.mem_filter.mp hq'
      obtain ⟨hq', he'⟩ := Finset.mem_filter.mp hq'
      simp only [Finset.mem_product] at hq'
      obtain ⟨⟨ha', _⟩, ⟨_, _⟩⟩ := hq'
      obtain ⟨hb', hc'⟩ := recover a' b' c' d' ha' he' hr'
      obtain ⟨haa, hdd⟩ := Prod.mk.inj heq
      change a = a' at haa
      change d = d' at hdd
      simp only [hb, hc, hb', hc', haa, hdd]
    · rintro ⟨x, y⟩ hxy
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      obtain ⟨hx, hrx⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy, hry⟩ := Finset.mem_filter.mp hy
      have hx0 : x ≠ 0 := ne_of_gt (hA x hx)
      refine ⟨((x, r * x), (r * y, y)), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, mul_div_cancel_right₀ r hx0⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hrx⟩,
         Finset.mem_product.mpr ⟨hry, hy⟩⟩, ?_⟩
      dsimp
      ac_rfl
  simpa only [Finset.card_product, pow_two] using hcard

end Submissions.Erdos52AdjacentRays.Energy

namespace Submissions.Erdos52Solymosi.Finite

theorem proof (A : Finset ℚ) (k : ℕ)
    (hA : ∀ a ∈ A, 0 < a) (hk : A.card < 2 ^ k) :
    A.card ^ 4 ≤ 8 * k * (A + A).card ^ 2 * (A * A).card := by
  classical
  let F (r : ℚ) := A.filter (fun x => r * x ∈ A)
  have hw : ∀ r ∈ A / A, (F r).card < 2 ^ k := by
    intro r _
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hk
  have hbin (j : ℕ) (hj : j < k) :
      (∑ r ∈ (A / A).filter
        (fun r => 2 ^ j ≤ (F r).card ∧ (F r).card < 2 ^ (j + 1)),
        (F r).card ^ 2) ≤ 8 * (A + A).card ^ 2 := by
    apply uniform_bin_energy A _ F (2 ^ j)
    · intro r _ x hx
      obtain ⟨hx, hrx⟩ := Finset.mem_filter.mp hx
      exact ⟨hA x hx, hx, hrx⟩
    · intro r hr
      exact (Finset.mem_filter.mp hr).2.1
    · intro r hr
      have h := (Finset.mem_filter.mp hr).2.2
      rw [pow_succ] at h
      simpa only [Nat.mul_comm] using Nat.le_of_lt h
  have henergy : Finset.mulEnergy A A ≤ k * (8 * (A + A).card ^ 2) := by
    rw [Submissions.Erdos52AdjacentRays.Energy.mulEnergy_eq_sum_ray_card_sq A hA]
    exact Submissions.Erdos52Solymosi.Dyadic.dyadic_square_sum_le
      (A / A) (fun r => (F r).card) k (8 * (A + A).card ^ 2) hw hbin
  calc
    _ = A.card ^ 2 * A.card ^ 2 := by ring
    _ ≤ (A * A).card * Finset.mulEnergy A A :=
      Finset.le_card_mul_mul_mulEnergy A A
    _ ≤ (A * A).card * (k * (8 * (A + A).card ^ 2)) :=
      Nat.mul_le_mul_left (A * A).card henergy
    _ = _ := by ring

end Submissions.Erdos52Solymosi.Finite

open scoped Pointwise

namespace Submissions.Erdos52Solymosi.IntegerLift

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

theorem cast_counts (A : Finset ℤ) :
    (A.image (fun a : ℤ => (a : ℚ))).card = A.card ∧
    (A.image (fun a : ℤ => (a : ℚ)) + A.image (fun a : ℤ => (a : ℚ))).card =
      (A + A).card ∧
    (A.image (fun a : ℤ => (a : ℚ)) * A.image (fun a : ℤ => (a : ℚ))).card =
      (A * A).card := by
  have hs : (A + A).image (fun a : ℤ => (a : ℚ)) =
      A.image (fun a : ℤ => (a : ℚ)) + A.image (fun a : ℤ => (a : ℚ)) :=
    Finset.image_add (Int.castRingHom ℚ)
  have hp : (A * A).image (fun a : ℤ => (a : ℚ)) =
      A.image (fun a : ℤ => (a : ℚ)) * A.image (fun a : ℤ => (a : ℚ)) :=
    Finset.image_mul (Int.castRingHom ℚ)
  refine ⟨Finset.card_image_of_injective A Int.cast_injective, ?_, ?_⟩
  · rw [← hs]
    exact Finset.card_image_of_injective (A + A) Int.cast_injective
  · rw [← hp]
    exact Finset.card_image_of_injective (A * A) Int.cast_injective

theorem positive_core (A : Finset ℚ) (hn : 2 ≤ A.card) :
    ∃ B : Finset ℚ,
      (∀ b ∈ B, 0 < b) ∧ B.card ≤ A.card ∧ A.card ≤ 3 * B.card ∧
      (B + B).card ≤ (A + A).card ∧ (B * B).card ≤ (A * A).card := by
  classical
  let P := A.filter (fun x => 0 < x)
  let Q := A.filter (fun x => x < 0)
  have hPA : P ⊆ A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hQA : Q ⊆ A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hcover : A ⊆ P ∪ Q ∪ {0} := by
    intro x hx
    simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (Or.inr ⟨hx, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inl ⟨hx, h⟩)
  have hcount : A.card ≤ P.card + Q.card + 1 := by
    calc
      A.card ≤ (P ∪ Q ∪ {0}).card := Finset.card_le_card hcover
      _ ≤ (P ∪ Q).card + ({0} : Finset ℚ).card := Finset.card_union_le _ _
      _ ≤ P.card + Q.card + 1 := by
        simpa only [Finset.card_singleton] using
          Nat.add_le_add_right (Finset.card_union_le P Q) 1
  rcases le_total Q.card P.card with hQP | hPQ
  · have hPone : 1 ≤ P.card := by
      by_contra h
      have hz : P.card = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h)
      nlinarith
    refine ⟨P, ?_, Finset.card_le_card hPA, ?_, ?_, ?_⟩
    · intro b hb
      exact (Finset.mem_filter.mp hb).2
    · nlinarith
    · exact Finset.card_le_card (Finset.add_subset_add hPA hPA)
    · exact Finset.card_le_card (Finset.mul_subset_mul hPA hPA)
  · have hQone : 1 ≤ Q.card := by
      by_contra h
      have hz : Q.card = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h)
      nlinarith
    let B := Q.image (fun x => (-1 : ℚ) * x)
    obtain ⟨hc, hs, hp⟩ := scale_counts Q (-1) (by norm_num)
    have hcB : B.card = Q.card := hc
    have hsB : (B + B).card = (Q + Q).card := hs
    have hpB : (B * B).card = (Q * Q).card := hp
    refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
      simpa only [neg_one_mul] using neg_pos.mpr (Finset.mem_filter.mp hx).2
    · rw [hcB]
      exact Finset.card_le_card hQA
    · rw [hcB]
      nlinarith
    · rw [hsB]
      exact Finset.card_le_card (Finset.add_subset_add hQA hQA)
    · rw [hpB]
      exact Finset.card_le_card (Finset.mul_subset_mul hQA hQA)

theorem rational_quartic_of_positive
    (H : ∀ (B : Finset ℚ) (k : ℕ), (∀ b ∈ B, 0 < b) → B.card < 2 ^ k →
      B.card ^ 4 ≤ 8 * k * (B + B).card ^ 2 * (B * B).card)
    (A : Finset ℚ) (k : ℕ) (hk : A.card < 2 ^ k) :
    A.card ^ 4 ≤ 648 * k * (A + A).card ^ 2 * (A * A).card := by
  classical
  by_cases hsmall : A.card ≤ 1
  · by_cases hz : A.card = 0
    · simp [hz]
    · have hcard : A.card = 1 :=
        Nat.le_antisymm hsmall (Nat.one_le_iff_ne_zero.mpr hz)
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
      have hkzero : k ≠ 0 := by
        intro h
        subst k
        simpa using hk
      have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkzero
      simp only [Finset.singleton_add_singleton, Finset.singleton_mul_singleton,
        Finset.card_singleton, one_pow, mul_one]
      nlinarith
  · have hn : 2 ≤ A.card := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hsmall)
    obtain ⟨B, hpos, hle, hsize, hsum, hprod⟩ := positive_core A hn
    have hB := H B k hpos (lt_of_le_of_lt hle hk)
    have hpow : A.card ^ 4 ≤ 81 * B.card ^ 4 := by
      calc
        A.card ^ 4 ≤ (3 * B.card) ^ 4 := Nat.pow_le_pow_left hsize 4
        _ = 81 * B.card ^ 4 := by ring
    have hsumSq : (B + B).card ^ 2 ≤ (A + A).card ^ 2 :=
      Nat.pow_le_pow_left hsum 2
    calc
      A.card ^ 4 ≤ 81 * B.card ^ 4 := hpow
      _ ≤ 81 * (8 * k * (B + B).card ^ 2 * (B * B).card) :=
        Nat.mul_le_mul_left 81 hB
      _ ≤ 81 * (8 * k * (A + A).card ^ 2 * (A * A).card) :=
        Nat.mul_le_mul_left 81
          (Nat.mul_le_mul (Nat.mul_le_mul_left (8 * k) hsumSq) hprod)
      _ = 648 * k * (A + A).card ^ 2 * (A * A).card := by ring

theorem proof
    (H : ∀ (B : Finset ℚ) (k : ℕ), (∀ b ∈ B, 0 < b) → B.card < 2 ^ k →
      B.card ^ 4 ≤ 8 * k * (B + B).card ^ 2 * (B * B).card) :
    ∀ (A : Finset ℤ) (k : ℕ), A.card < 2 ^ k →
      A.card ^ 4 ≤ 648 * k * (A + A).card ^ 2 * (A * A).card := by
  intro A k hk
  obtain ⟨hc, hs, hp⟩ := cast_counts A
  have h := rational_quartic_of_positive H (A.image fun a : ℤ => (a : ℚ)) k
    (by simpa only [hc] using hk)
  simpa only [hc, hs, hp] using h

end Submissions.Erdos52Solymosi.IntegerLift
namespace Submissions.Erdos52IntegerSolymosi.Finite

theorem proof : ∀ (A : Finset ℤ) (k : ℕ), A.card < 2 ^ k →
    A.card ^ 4 ≤ 648 * k * (A + A).card ^ 2 * (A * A).card :=
  Submissions.Erdos52Solymosi.IntegerLift.proof
    Submissions.Erdos52Solymosi.Finite.proof

end Submissions.Erdos52IntegerSolymosi.Finite

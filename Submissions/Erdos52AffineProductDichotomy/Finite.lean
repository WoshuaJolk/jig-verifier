import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Submissions.Erdos52AffineCollision.Collision

/-- A nontrivial product collision in a coprime integral affine progression
forces both its step and its offset to be small relative to the index interval. -/
theorem proof {u v L x y z w : ℤ}
    (hv : 0 < v) (hL : 0 ≤ L) (hcop : IsCoprime u v)
    (hx : 0 ≤ x ∧ x ≤ L) (hy : 0 ≤ y ∧ y ≤ L)
    (hz : 0 ≤ z ∧ z ≤ L) (hw : 0 ≤ w ∧ w ≤ L)
    (heq : (u + v * x) * (u + v * y) = (u + v * z) * (u + v * w))
    (hdiff : (x ≠ z ∨ y ≠ w) ∧ (x ≠ w ∨ y ≠ z)) :
    v ≤ 2 * L ∧ |u| ≤ L ^ 2 := by
  let ds : ℤ := x + y - z - w
  let dp : ℤ := x * y - z * w
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hrel : u * ds = -v * dp := by
    have he : v * (u * ds + v * dp) = 0 := by
      calc
        _ = (u + v * x) * (u + v * y) - (u + v * z) * (u + v * w) := by
          dsimp [ds, dp]
          ring
        _ = 0 := sub_eq_zero.mpr heq
    have he' := (mul_eq_zero.mp he).resolve_left hv0
    linarith
  have hds : ds ≠ 0 := by
    intro hs
    have hp : dp = 0 := by
      have he : v * dp = 0 := by rw [hs, mul_zero] at hrel; linarith
      exact (mul_eq_zero.mp he).resolve_left hv0
    have hsum : x + y = z + w := by dsimp [ds] at hs; linarith
    have hprod : x * y = z * w := by dsimp [dp] at hp; linarith
    have he : (x - z) * (x - w) = 0 := by
      nlinarith [congrArg (fun s : ℤ => x * s) hsum]
    rcases mul_eq_zero.mp he with he | he
    · have hxz : x = z := sub_eq_zero.mp he
      have hyw : y = w := by linarith
      exact hdiff.1.elim (fun h => h hxz) (fun h => h hyw)
    · have hxw : x = w := sub_eq_zero.mp he
      have hyz : y = z := by linarith
      exact hdiff.2.elim (fun h => h hxw) (fun h => h hyz)
  have hvds : v ∣ ds := by
    apply hcop.symm.dvd_of_dvd_mul_left
    refine ⟨-dp, ?_⟩
    calc
      u * ds = -v * dp := hrel
      _ = v * -dp := by ring
  obtain ⟨t, ht⟩ := hvds
  have ht0 : t ≠ 0 := by
    intro he
    apply hds
    rw [ht, he, mul_zero]
  have hpt : dp = -u * t := by
    have he : v * (dp + u * t) = 0 := by rw [ht] at hrel; nlinarith [hrel]
    have he' := (mul_eq_zero.mp he).resolve_left hv0
    linarith
  have htone : (1 : ℤ) ≤ |t| := by
    have := abs_pos.mpr ht0
    omega
  have hdsabs : |ds| = v * |t| := by rw [ht, abs_mul, abs_of_pos hv]
  have hdpabs : |dp| = |u| * |t| := by rw [hpt, abs_mul, abs_neg]
  have hdsbound : |ds| ≤ 2 * L := by
    apply abs_le.mpr
    dsimp [ds]
    constructor <;> omega
  have hdpbound : |dp| ≤ L ^ 2 := by
    have hxy0 : 0 ≤ x * y := mul_nonneg hx.1 hy.1
    have hzw0 : 0 ≤ z * w := mul_nonneg hz.1 hw.1
    have hxyL : x * y ≤ L ^ 2 := by
      calc
        _ ≤ L * L := mul_le_mul hx.2 hy.2 hy.1 hL
        _ = L ^ 2 := by ring
    have hzwL : z * w ≤ L ^ 2 := by
      calc
        _ ≤ L * L := mul_le_mul hz.2 hw.2 hw.1 hL
        _ = L ^ 2 := by ring
    apply abs_le.mpr
    dsimp [dp]
    constructor <;> linarith
  constructor
  · calc
      v = v * 1 := by ring
      _ ≤ v * |t| := mul_le_mul_of_nonneg_left htone hv.le
      _ = |ds| := hdsabs.symm
      _ ≤ 2 * L := hdsbound
  · calc
      |u| = |u| * 1 := by ring
      _ ≤ |u| * |t| := mul_le_mul_of_nonneg_left htone (abs_nonneg u)
      _ = |dp| := hdpabs.symm
      _ ≤ L ^ 2 := hdpbound

/-- Reflecting the index interval bounds the second endpoint as well, hence
every entry in the interval has absolute value at most `L ^ 2`. -/
theorem height {u v L x y z w : ℤ}
    (hv : 0 < v) (hL : 0 ≤ L) (hcop : IsCoprime u v)
    (hx : 0 ≤ x ∧ x ≤ L) (hy : 0 ≤ y ∧ y ≤ L)
    (hz : 0 ≤ z ∧ z ≤ L) (hw : 0 ≤ w ∧ w ≤ L)
    (heq : (u + v * x) * (u + v * y) = (u + v * z) * (u + v * w))
    (hdiff : (x ≠ z ∨ y ≠ w) ∧ (x ≠ w ∨ y ≠ z)) :
    ∀ i : ℤ, 0 ≤ i → i ≤ L → |u + v * i| ≤ L ^ 2 := by
  have hleft := (proof hv hL hcop hx hy hz hw heq hdiff).2
  have hcop' : IsCoprime (-(u + v * L)) v := by
    obtain ⟨a, b, hab⟩ := hcop
    refine ⟨-a, b - a * L, ?_⟩
    calc
      _ = a * u + b * v := by ring
      _ = 1 := hab
  have heq' : (-(u + v * L) + v * (L - x)) *
        (-(u + v * L) + v * (L - y)) =
      (-(u + v * L) + v * (L - z)) *
        (-(u + v * L) + v * (L - w)) := by
    convert heq using 1 <;> ring
  have hdiff' : (L - x ≠ L - z ∨ L - y ≠ L - w) ∧
      (L - x ≠ L - w ∨ L - y ≠ L - z) := by
    constructor <;> omega
  have hright : |u + v * L| ≤ L ^ 2 := by
    have h := (proof hv hL hcop'
      (show 0 ≤ L - x ∧ L - x ≤ L by omega)
      (show 0 ≤ L - y ∧ L - y ≤ L by omega)
      (show 0 ≤ L - z ∧ L - z ≤ L by omega)
      (show 0 ≤ L - w ∧ L - w ≤ L by omega) heq' hdiff').2
    simpa only [abs_neg] using h
  intro i hi0 hiL
  have hlo := (abs_le.mp hleft).1
  have hhi := (abs_le.mp hright).2
  have hvi0 : 0 ≤ v * i := mul_nonneg hv.le hi0
  have hviL : v * i ≤ v * L := mul_le_mul_of_nonneg_left hiL hv.le
  apply abs_le.mpr
  constructor <;> linarith

end Submissions.Erdos52AffineCollision.Collision

namespace Submissions.Erdos52AffineProductDichotomy.Finite

open scoped Pointwise

/-- A coprime affine progression either has small height or its subset has
at most two ordered representations of every product. -/
theorem proof (A : Finset ℤ) (u v L : ℤ)
    (hv : 0 < v) (hL : 0 ≤ L) (hcop : IsCoprime u v)
    (hA : ∀ a ∈ A, ∃ i : ℤ, 0 ≤ i ∧ i ≤ L ∧ a = u + v * i) :
    (∀ a ∈ A, |a| ≤ L ^ 2) ∨ A.card ^ 2 ≤ 2 * (A * A).card := by
  classical
  by_cases hheight : ∀ a ∈ A, |a| ≤ L ^ 2
  · exact Or.inl hheight
  right
  have hs : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a * b = c * d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro a ha b hb c hc d hd he
    by_contra hn
    obtain ⟨i, hi0, hiL, rfl⟩ := hA a ha
    obtain ⟨j, hj0, hjL, rfl⟩ := hA b hb
    obtain ⟨k, hk0, hkL, rfl⟩ := hA c hc
    obtain ⟨l, hl0, hlL, rfl⟩ := hA d hd
    have hdiff : (i ≠ k ∨ j ≠ l) ∧ (i ≠ l ∨ j ≠ k) := by
      constructor
      · by_cases h : i = k
        · right
          intro h'
          apply hn
          exact Or.inl ⟨by rw [h], by rw [h']⟩
        · exact Or.inl h
      · by_cases h : i = l
        · right
          intro h'
          apply hn
          exact Or.inr ⟨by rw [h], by rw [h']⟩
        · exact Or.inl h
    apply hheight
    intro a ha
    obtain ⟨t, ht0, htL, rfl⟩ := hA a ha
    exact Submissions.Erdos52AffineCollision.Collision.height
      hv hL hcop ⟨hi0, hiL⟩ ⟨hj0, hjL⟩ ⟨hk0, hkL⟩ ⟨hl0, hlL⟩
      he hdiff t ht0 htL
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (f := fun p : ℤ × ℤ => p.1 * p.2) (s := A ×ˢ A) (t := A * A)
    (by
      intro p hp
      exact Finset.mul_mem_mul (Finset.mem_product.mp hp).1
        (Finset.mem_product.mp hp).2) 2 (by
      intro b hb
      let F := (A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 * p.2 = b)
      change F.card ≤ 2
      by_cases hF : F.Nonempty
      · obtain ⟨p, hp⟩ := hF
        have hpmem := Finset.mem_filter.mp hp
        have hpA := Finset.mem_product.mp hpmem.1
        have hsub : F ⊆ {p, p.swap} := by
          intro q hq
          have hqmem := Finset.mem_filter.mp hq
          have hqA := Finset.mem_product.mp hqmem.1
          have he : q.1 * q.2 = p.1 * p.2 := hqmem.2.trans hpmem.2.symm
          rcases hs q.1 hqA.1 q.2 hqA.2 p.1 hpA.1 p.2 hpA.2 he with h | h
          · have hqp : q = p := Prod.ext h.1 h.2
            simp [hqp]
          · have hqp : q = p.swap := Prod.ext h.1 h.2
            simp [hqp]
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
        simp)
  simpa [Finset.card_product, pow_two] using hcard

end Submissions.Erdos52AffineProductDichotomy.Finite

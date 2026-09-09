import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/- Dense-plane obstruction for Erdős734. Mathematical prior art: Nagy–Weiner,
arXiv:2605.23644v2, LemmaA.1 and Theorem1.4. This is a formalized consequence,
not a solution of the unrestricted conjecture. Only size≥2 fibers are bounded. -/
namespace Submissions.Erdos734DensePlaneMultiplicity.Proof

open scoped BigOperators


/-- A finite window and a uniform fiber bound force a lower bound on the second moment.
The inequality remains valid when `h = 0` or the cardinality difference is negative. -/
theorem moment_barrier {α : Type*} (B : Finset α) (size : α → ℕ)
    (T : Finset ℕ) (M : ℕ) (μ h : ℝ)
    (hfiber : ∀ t ∈ T, (B.filter fun b => size b = t).card ≤ M)
    (houtside : ∀ b ∈ B, size b ∉ T → h ^ 2 ≤ ((size b : ℝ) - μ) ^ 2) :
    h ^ 2 * ((B.card : ℝ) - (M : ℝ) * (T.card : ℝ)) ≤
      ∑ b ∈ B, ((size b : ℝ) - μ) ^ 2 := by
  classical
  let inside := B.filter fun b => size b ∈ T
  let outside := B.filter fun b => size b ∉ T
  have hin : inside.card ≤ M * T.card := by
    calc
      inside.card = ∑ t ∈ T, (B.filter fun b => size b = t).card :=
        (Finset.sum_card_fiberwise_eq_card_filter B T size).symm
      _ ≤ ∑ _t ∈ T, M := Finset.sum_le_sum hfiber
      _ = M * T.card := by simp [Nat.mul_comm]
  have hinR : (inside.card : ℝ) ≤ (M : ℝ) * (T.card : ℝ) := by
    have hc : (inside.card : ℝ) ≤ ((M * T.card : ℕ) : ℝ) := Nat.cast_le.mpr hin
    simpa only [Nat.cast_mul] using hc
  have hcard : (inside.card : ℝ) + (outside.card : ℝ) = (B.card : ℝ) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ))
      (Finset.card_filter_add_card_filter_not (s := B) fun b => size b ∈ T)
    simpa only [Nat.cast_add] using hc
  calc
    h ^ 2 * ((B.card : ℝ) - (M : ℝ) * (T.card : ℝ)) ≤
        h ^ 2 * (outside.card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg h)
      apply (sub_le_iff_le_add).mpr
      calc
        (B.card : ℝ) = (inside.card : ℝ) + (outside.card : ℝ) := hcard.symm
        _ ≤ (M : ℝ) * (T.card : ℝ) + (outside.card : ℝ) :=
          by linarith only [hinR]
        _ = (outside.card : ℝ) + (M : ℝ) * (T.card : ℝ) := add_comm _ _
    _ = ∑ _b ∈ outside, h ^ 2 := by simp [mul_comm]
    _ ≤ ∑ b ∈ outside, ((size b : ℝ) - μ) ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact houtside b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
    _ ≤ ∑ b ∈ B, ((size b : ℝ) - μ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun b _ _ => sq_nonneg ((size b : ℝ) - μ))


open scoped BigOperators
open Finset


/-- Count incidences with a selected point set in either order. -/
theorem first_incidence_moment {v l q : ℕ} (blocks : Fin l → Finset (Fin v))
    (S : Finset (Fin v))
    (hdegree : ∀ x, (univ.filter fun i => x ∈ blocks i).card = q + 1) :
    ∑ i, (S ∩ blocks i).card = S.card * (q + 1) := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (i : Fin l) (x : Fin v) => x ∈ blocks i) (s := univ) (t := S)
  have hi : ∀ i, S.bipartiteAbove (fun (i : Fin l) (x : Fin v) => x ∈ blocks i) i =
      S ∩ blocks i := by
    intro i
    ext x
    simp [bipartiteAbove]
  simp_rw [hi] at h
  simpa [bipartiteBelow, hdegree] using h

/-- Pairwise incidence counts determine the second moment of every restriction. -/
theorem second_incidence_moment {v l q : ℕ} (blocks : Fin l → Finset (Fin v))
    (S : Finset (Fin v))
    (hpairs : ∀ x y, (univ.filter fun i => x ∈ blocks i ∧ y ∈ blocks i).card =
      if x = y then q + 1 else 1) :
    ∑ i, (S ∩ blocks i).card ^ 2 = S.card * (S.card + q) := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (i : Fin l) (p : Fin v × Fin v) => p.1 ∈ blocks i ∧ p.2 ∈ blocks i)
    (s := univ) (t := S ×ˢ S)
  have hi : ∀ i, (S ×ˢ S).bipartiteAbove
      (fun (i : Fin l) (p : Fin v × Fin v) => p.1 ∈ blocks i ∧ p.2 ∈ blocks i) i =
      (S ∩ blocks i) ×ˢ (S ∩ blocks i) := by
    intro i
    ext p
    simp only [bipartiteAbove, mem_filter, mem_product, mem_inter]
    tauto
  simp_rw [hi, card_product, ← pow_two] at h
  rw [h, Finset.sum_product]
  have hy : ∀ x ∈ S, (∑ y ∈ S, if x = y then q + 1 else 1) = S.card + q := by
    intro x hx
    calc
      _ = ∑ y ∈ S, ((if x = y then q else 0) + 1) := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> simp
      _ = S.card + q := by simp [Finset.sum_add_distrib, hx, Nat.add_comm]
  simp only [bipartiteBelow, hpairs]
  rw [Finset.sum_congr rfl hy]
  simp


open Finset


/-- Two restricted blocks sharing at least two points have the same index. -/
theorem restriction_eq_implies_index_eq {v l : ℕ}
    (blocks : Fin l → Finset (Fin v)) (S : Finset (Fin v))
    (hpairs : ∀ x y, x ≠ y →
      (univ.filter fun i => x ∈ blocks i ∧ y ∈ blocks i).card = 1)
    (i j : Fin l) (hi : 2 ≤ (S ∩ blocks i).card)
    (hij : S ∩ blocks i = S ∩ blocks j) : i = j := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1 < 2) hi)
  have hmemi : i ∈ univ.filter (fun k => x ∈ blocks k ∧ y ∈ blocks k) :=
    mem_filter.mpr ⟨mem_univ i, (mem_inter.mp hx).2, (mem_inter.mp hy).2⟩
  have hmemj : j ∈ univ.filter (fun k => x ∈ blocks k ∧ y ∈ blocks k) := by
    rw [hij] at hx hy
    exact mem_filter.mpr ⟨mem_univ j, (mem_inter.mp hx).2, (mem_inter.mp hy).2⟩
  exact Finset.card_le_one.mp (hpairs x y hxy).le i hmemi j hmemj

/-- For sizes at least two, deduplicating restricted blocks preserves multiplicity. -/
theorem restriction_size_count {v l : ℕ}
    (blocks : Fin l → Finset (Fin v)) (S : Finset (Fin v))
    (hpairs : ∀ x y, x ≠ y →
      (univ.filter fun i => x ∈ blocks i ∧ y ∈ blocks i).card = 1)
    (t : ℕ) (ht : 2 ≤ t) :
    (((univ.image fun i => S ∩ blocks i).filter fun block => block.card = t).card) =
      (univ.filter fun i => (S ∩ blocks i).card = t).card := by
  rw [Finset.filter_image]
  apply Finset.card_image_of_injOn
  intro i hi j _ hij
  apply restriction_eq_implies_index_eq blocks S hpairs i j _ hij
  rw [(mem_filter.mp hi).2]
  exact ht


open scoped BigOperators


theorem centered_moment_identity (L : ℕ) (q n μ : ℝ) (f : Fin L → ℕ)
    (hmean : μ * (L : ℝ) = n * (q + 1))
    (hfirst : ∑ i, (f i : ℝ) = n * (q + 1))
    (hsecond : ∑ i, (f i : ℝ) ^ 2 = n * (n + q)) :
    ∑ i, ((f i : ℝ) - μ) ^ 2 = n * (n + q) - μ ^ 2 * (L : ℝ) := by
  calc
    (∑ i, ((f i : ℝ) - μ) ^ 2) =
        ∑ i, ((f i : ℝ) ^ 2 - (2 * μ) * (f i : ℝ) + μ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (f i : ℝ) ^ 2) - (2 * μ) * (∑ i, (f i : ℝ)) +
        (L : ℝ) * μ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = n * (n + q) - μ ^ 2 * (L : ℝ) := by
      rw [hfirst, hsecond, ← hmean]
      ring

theorem plane_variance_upper (q n L μ V : ℝ) (hq : 0 ≤ q)
    (hL : L = q ^ 2 + q + 1) (hLpos : 0 < L)
    (hmean : μ * L = n * (q + 1))
    (hV : V = n * (n + q) - μ ^ 2 * L) :
    4 * V ≤ q * L := by
  have hmeanSq : μ ^ 2 * L ^ 2 = n ^ 2 * (q + 1) ^ 2 := by
    calc
      μ ^ 2 * L ^ 2 = (μ * L) ^ 2 := by ring
      _ = (n * (q + 1)) ^ 2 := congrArg (fun x : ℝ => x ^ 2) hmean
      _ = n ^ 2 * (q + 1) ^ 2 := by ring
  have hid : V * L = q * n * (L - n) := by
    calc
      V * L = n * (n + q) * L - μ ^ 2 * L ^ 2 := by rw [hV]; ring
      _ = n * (n + q) * L - n ^ 2 * (q + 1) ^ 2 := by rw [hmeanSq]
      _ = q * n * (L - n) := by rw [hL]; ring
  have hquad : 0 ≤ q * (L - 2 * n) ^ 2 := mul_nonneg hq (sq_nonneg _)
  apply (mul_le_mul_iff_of_pos_right hLpos).mp
  nlinarith only [hid, hquad]

/-- This window contains no zero or singleton sizes, and has a quadratic gap outside it. -/
theorem natural_window (μ : ℝ) (r : ℕ) (hμ : (r : ℝ) + 2 ≤ μ) :
    let T := Finset.Icc (Nat.floor μ - r) (Nat.floor μ + r + 1)
    T.card ≤ 2 * r + 2 ∧
      (∀ t ∈ T, 2 ≤ t) ∧
      (∀ t : ℕ, t ∉ T → (r : ℝ) ^ 2 ≤ ((t : ℝ) - μ) ^ 2) := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hμ0 : 0 ≤ μ := by linarith
  have hfloor : r + 2 ≤ Nat.floor μ := Nat.le_floor (by simpa using hμ)
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_Icc]
    omega
  · intro t ht
    have ht' := (Finset.mem_Icc.mp ht).1
    omega
  · intro t ht
    have ht' : t < Nat.floor μ - r ∨ Nat.floor μ + r + 1 < t := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using ht
    rcases ht' with ht' | ht'
    · have htr : t + r ≤ Nat.floor μ := by omega
      have htrR : (t : ℝ) + (r : ℝ) ≤ (Nat.floor μ : ℝ) := by exact_mod_cast htr
      have hd : (r : ℝ) ≤ μ - (t : ℝ) := by
        have hf := Nat.floor_le hμ0
        linarith
      have hs := pow_le_pow_left₀ hr hd 2
      nlinarith only [hs]
    · have htrR : (Nat.floor μ : ℝ) + (r : ℝ) + 1 < (t : ℝ) := by
        exact_mod_cast ht'
      have hd : (r : ℝ) ≤ (t : ℝ) - μ := by
        have hf := Nat.lt_floor_add_one μ
        linarith
      exact pow_le_pow_left₀ hr hd 2

/-- The two incidence moments force a block-size fiber of order at least `L / sqrt q`.
Only sizes at least two are bounded; the zero and singleton fibers are unrestricted. -/
theorem plane_moment_multiplicity (q n L M : ℕ) (hq : 16 ≤ q)
    (hL : L = q ^ 2 + q + 1) (hlow : L ≤ 2 * n) (f : Fin L → ℕ)
    (hfirst : ∑ i, (f i : ℝ) = (n : ℝ) * ((q : ℝ) + 1))
    (hsecond : ∑ i, (f i : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) + (q : ℝ)))
    (hfiber : ∀ t : ℕ, 2 ≤ t → (Finset.univ.filter fun i => f i = t).card ≤ M) :
    3 * L ≤ (8 * Nat.sqrt q + 16) * M := by
  classical
  let r := Nat.sqrt q + 1
  let μ : ℝ := (n : ℝ) * ((q : ℝ) + 1) / (L : ℝ)
  let V : ℝ := ∑ i, ((f i : ℝ) - μ) ^ 2
  let T := Finset.Icc (Nat.floor μ - r) (Nat.floor μ + r + 1)
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hLR : (L : ℝ) = (q : ℝ) ^ 2 + (q : ℝ) + 1 := by exact_mod_cast hL
  have hLpos : 0 < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have hmean : μ * (L : ℝ) = (n : ℝ) * ((q : ℝ) + 1) := by
    exact div_mul_cancel₀ _ (ne_of_gt hLpos)
  have hV : V = (n : ℝ) * ((n : ℝ) + (q : ℝ)) - μ ^ 2 * (L : ℝ) :=
    centered_moment_identity L (q : ℝ) (n : ℝ) μ f hmean hfirst hsecond
  have hvar : 4 * V ≤ (q : ℝ) * (L : ℝ) :=
    plane_variance_upper (q : ℝ) (n : ℝ) (L : ℝ) μ V hq0 hLR hLpos hmean hV
  have hs4 : 4 ≤ Nat.sqrt q := Nat.le_sqrt'.mpr (by norm_num; exact hq)
  have hs4R : (4 : ℝ) ≤ (Nat.sqrt q : ℝ) := by exact_mod_cast hs4
  have hsq : (Nat.sqrt q : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast Nat.sqrt_le' q
  have h4s : 4 * (Nat.sqrt q : ℝ) ≤ (q : ℝ) := by
    have hp : 0 ≤ (Nat.sqrt q : ℝ) * ((Nat.sqrt q : ℝ) - 4) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    nlinarith only [hp, hsq]
  have hlowR : (L : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hlow
  have hlowmul := mul_le_mul_of_nonneg_right hlowR (show 0 ≤ (q : ℝ) + 1 by linarith)
  have hμlower : (q : ℝ) + 1 ≤ 2 * μ := by
    apply (mul_le_mul_iff_of_pos_right hLpos).mp
    nlinarith only [hlowmul, hmean]
  have hμwindow : (r : ℝ) + 2 ≤ μ := by
    dsimp [r]
    push_cast
    linarith only [hμlower, h4s, hs4R]
  obtain ⟨hTcard, hTtwo, hToutside⟩ := natural_window μ r hμwindow
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast (show 0 < r by dsimp [r]; omega)
  have hqr : (q : ℝ) ≤ (r : ℝ) ^ 2 := by
    have hn : q < r ^ 2 := by simpa [r, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' q
    exact le_of_lt (by exact_mod_cast hn)
  have hvar' : 4 * V ≤ (r : ℝ) ^ 2 * (L : ℝ) :=
    hvar.trans (mul_le_mul_of_nonneg_right hqr hLpos.le)
  have hbar : (r : ℝ) ^ 2 * ((L : ℝ) - (M : ℝ) * (T.card : ℝ)) ≤ V := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      moment_barrier Finset.univ f T M μ (r : ℝ)
        (fun t ht => hfiber t (hTtwo t ht))
        (fun i _ hi => hToutside (f i) hi)
  have hcount : 3 * (L : ℝ) ≤ 4 * (M : ℝ) * (T.card : ℝ) := by
    apply (mul_le_mul_iff_of_pos_left (pow_pos hrpos 2)).mp
    nlinarith only [hbar, hvar']
  have hTcardR : (T.card : ℝ) ≤ 2 * (r : ℝ) + 2 := by exact_mod_cast hTcard
  have hresultR : 3 * (L : ℝ) ≤ (8 * (Nat.sqrt q : ℝ) + 16) * (M : ℝ) := by
    calc
      3 * (L : ℝ) ≤ 4 * (M : ℝ) * (T.card : ℝ) := hcount
      _ ≤ 4 * (M : ℝ) * (2 * (r : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hTcardR (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      _ = (8 * (Nat.sqrt q : ℝ) + 16) * (M : ℝ) := by dsimp [r]; push_cast; ring
  exact_mod_cast hresultR


/-- Dense restrictions of finite projective-plane incidence systems cannot have small
uniform block-size multiplicity. The fiber counts are over distinct retained subsets. -/
theorem dense_plane_multiplicity (q : ℕ) (hq : 16 ≤ q)
    (blocks : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1)))
    (hpairs : ∀ x y,
      (Finset.univ.filter fun i => x ∈ blocks i ∧ y ∈ blocks i).card =
        if x = y then q + 1 else 1)
    (S : Finset (Fin (q ^ 2 + q + 1))) (hdense : q ^ 2 + q + 1 ≤ 2 * S.card)
    (M : ℕ)
    (hmult : ∀ t : ℕ, 2 ≤ t →
      (((Finset.univ.image fun i => S ∩ blocks i).filter fun b => b.card = t).card) ≤ M) :
    3 * (q ^ 2 + q + 1) ≤ (8 * Nat.sqrt q + 16) * M := by
  have hdegree : ∀ x, (Finset.univ.filter fun i => x ∈ blocks i).card = q + 1 := by
    intro x
    simpa using hpairs x x
  have hfirst := first_incidence_moment blocks S hdegree
  have hsecond := second_incidence_moment blocks S hpairs
  have hone : ∀ x y, x ≠ y →
      (Finset.univ.filter fun i => x ∈ blocks i ∧ y ∈ blocks i).card = 1 := by
    intro x y hxy
    simpa [hxy] using hpairs x y
  apply plane_moment_multiplicity q S.card (q ^ 2 + q + 1) M hq rfl hdense
    (fun i => (S ∩ blocks i).card)
  · exact_mod_cast hfirst
  · exact_mod_cast hsecond
  · intro t ht
    rw [← restriction_size_count blocks S hone t ht]
    exact hmult t ht

end Submissions.Erdos734DensePlaneMultiplicity.Proof

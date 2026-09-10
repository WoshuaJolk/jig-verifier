import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

namespace Submissions.Erdos529EndpointCollisionCriterion.Main

/-!
A finite endpoint-collision criterion for Jig #289. This is an elementary
Cauchy–Schwarz reduction, not an anti-concentration estimate for self-avoiding
walks. The canonical walk and first-moment definitions are copied exactly.
-/

namespace FiniteEndpointCollision

def fiberCount {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (y : β) : ℕ :=
  (s.filter (fun x => f x = y)).card

def collisionCount {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) : ℕ :=
  ∑ y ∈ s.image f, fiberCount s f y ^ 2

/-- The sum of squared fiber sizes counts ordered pairs with equal images. -/
theorem collisionCount_eq_pair_card {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    collisionCount s f = ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card := by
  classical
  have hsum : (∑ x ∈ s, fiberCount s f (f x)) = collisionCount s f := by
    rw [Finset.sum_comp]
    simp only [collisionCount, fiberCount, nsmul_eq_mul, Nat.cast_id, pow_two]
  rw [← hsum]
  symm
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  simp only [fiberCount, Finset.card_eq_sum_ones, Finset.sum_filter, eq_comm]

/-- Cauchy–Schwarz for the number of inputs whose image lies in a finite set.
No injectivity of the map is assumed. -/
theorem small_card_sq_le {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) (B : Finset β) :
    (s.filter (fun x => f x ∈ B)).card ^ 2 ≤ B.card * collisionCount s f := by
  classical
  let A := s.filter (fun x => f x ∈ B)
  let I := B ∩ s.image f
  have hmap : Set.MapsTo f A I := by
    intro x hx
    obtain ⟨hxs, hxB⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_inter.mpr ⟨hxB, Finset.mem_image_of_mem f hxs⟩
  have hcard : A.card = ∑ y ∈ I, fiberCount s f y := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    apply Finset.sum_congr rfl
    intro y hy
    have hyB := (Finset.mem_inter.mp hy).1
    unfold fiberCount
    congr 1
    ext x
    simp only [A, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, hxy⟩
      exact ⟨hx, hxy⟩
    · rintro ⟨hx, hxy⟩
      exact ⟨⟨hx, hxy ▸ hyB⟩, hxy⟩
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℕ)) (fiberCount s f)
  have hsquares : (∑ y ∈ I, fiberCount s f y ^ 2) ≤ collisionCount s f := by
    unfold collisionCount
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
      exact Finset.mem_image.mpr ⟨x, hx, hxy⟩
    · intro y _ _
      exact Nat.zero_le _
  have hsize : I.card ≤ B.card := Finset.card_le_card Finset.inter_subset_left
  change A.card ^ 2 ≤ _
  rw [hcard]
  calc
    (∑ y ∈ I, fiberCount s f y) ^ 2 ≤ I.card * ∑ y ∈ I, fiberCount s f y ^ 2 := by
      simpa using hcs
    _ ≤ B.card * collisionCount s f := Nat.mul_le_mul hsize hsquares

/-- The explicit collision hypothesis puts at most half the inputs in B. -/
theorem twice_small_card_le {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) (B : Finset β)
    (h : 4 * B.card * collisionCount s f ≤ s.card ^ 2) :
    2 * (s.filter (fun x => f x ∈ B)).card ≤ s.card := by
  have hcs := small_card_sq_le s f B
  nlinarith

/-- A finite exceptional set containing at most half the inputs leaves at least
half of the total mass at distance at least m. -/
theorem half_mul_card_le_sum {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (B : Finset β) (R : α → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hR : ∀ x ∈ s, 0 ≤ R x)
    (houtside : ∀ x ∈ s, f x ∉ B → m ≤ R x)
    (hhalf : 2 * (s.filter (fun x => f x ∈ B)).card ≤ s.card) :
    m / 2 * s.card ≤ ∑ x ∈ s, R x := by
  classical
  have hpoint (x : α) (hx : x ∈ s) :
      m ≤ R x + (if f x ∈ B then m else 0) := by
    by_cases hb : f x ∈ B
    · simp only [if_pos hb]
      linarith [hR x hx]
    · simpa only [if_neg hb, add_zero] using houtside x hx hb
  have hsum := Finset.sum_le_sum (s := s) hpoint
  have hexception : (∑ x ∈ s, if f x ∈ B then m else 0) =
      ((s.filter (fun x => f x ∈ B)).card : ℝ) * m := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hexception] at hsum
  have hhalfReal : (2 : ℝ) * (s.filter (fun x => f x ∈ B)).card ≤ s.card := by
    exact_mod_cast hhalf
  have hweighted := mul_le_mul_of_nonneg_left hhalfReal hm
  nlinarith

end FiniteEndpointCollision

namespace PlanarSAWEndpointCollision

abbrev Point := ℤ × ℤ

def step (d : Fin 4) : Point :=
  if d = 0 then (1, 0)
  else if d = 1 then (-1, 0)
  else if d = 2 then (0, 1)
  else (0, -1)

def position {n : ℕ} (s : Fin n → Fin 4) (t : Fin (n + 1)) : Point :=
  let ht : t.val ≤ n := Nat.le_of_lt_succ t.isLt
  ∑ i : Fin t.val, step (s (Fin.castLE ht i))

def IsSelfAvoidingWalk {n : ℕ} (s : Fin n → Fin 4) : Prop :=
  Function.Injective (position s)

noncomputable def walks (n : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter IsSelfAvoidingWalk

noncomputable def endpointDistance {n : ℕ} (s : Fin n → Fin 4) : ℝ :=
  Real.sqrt (((position s (Fin.last n)).1 : ℝ) ^ 2 +
    ((position s (Fin.last n)).2 : ℝ) ^ 2)

noncomputable def expectedDistance (n : ℕ) : ℝ :=
  ((walks n).sum endpointDistance) / (walks n).card

def endpoint {n : ℕ} (s : Fin n → Fin 4) : Point := position s (Fin.last n)

noncomputable def endpointCollisionCount (n : ℕ) : ℕ :=
  FiniteEndpointCollision.collisionCount (walks n) endpoint

/-- The collision probability of two independent uniform n-step walks. -/
noncomputable def endpointCollisionProbability (n : ℕ) : ℝ :=
  (endpointCollisionCount n : ℝ) / ((walks n).card : ℝ) ^ 2

noncomputable def endpointBox (m : ℕ) : Finset Point :=
  Finset.Icc (-(m : ℤ)) (m : ℤ) ×ˢ Finset.Icc (-(m : ℤ)) (m : ℤ)

theorem endpointBox_card (m : ℕ) : (endpointBox m).card = (2 * m + 1) ^ 2 := by
  have hI : (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [endpointBox, Finset.card_product, hI, pow_two]

theorem position_allEast {n : ℕ} (t : Fin (n + 1)) :
    position (fun _ : Fin n => (0 : Fin 4)) t = ((t.val : ℤ), 0) := by
  simp [position, step]

theorem walks_nonempty (n : ℕ) : (walks n).Nonempty := by
  classical
  refine ⟨fun _ => 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro a b h
  simp only [position_allEast, Prod.mk.injEq] at h
  apply Fin.ext
  exact_mod_cast h.1

theorem max_natAbs_le_euclidean (z : Point) :
    ((max z.1.natAbs z.2.natAbs : ℕ) : ℝ) ≤
      Real.sqrt ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
  rw [Nat.cast_max]
  apply max_le
  · rw [Nat.cast_natAbs, Int.cast_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  · rw [Nat.cast_natAbs, Int.cast_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

theorem mem_endpointBox_iff (x : Point) (m : ℕ) :
    x ∈ endpointBox m ↔ max x.1.natAbs x.2.natAbs ≤ m := by
  simp only [endpointBox, Finset.mem_product, Finset.mem_Icc, max_le_iff]
  constructor
  · rintro ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
    constructor <;> omega
  · rintro ⟨hx, hy⟩
    constructor <;> constructor <;> omega

theorem endpointDistance_ge_of_outside {n m : ℕ} (s : Fin n → Fin 4)
    (h : endpoint s ∉ endpointBox m) : (m : ℝ) ≤ endpointDistance s := by
  have hnorm : m ≤ max (endpoint s).1.natAbs (endpoint s).2.natAbs := by
    rw [mem_endpointBox_iff] at h
    omega
  have hcast : (m : ℝ) ≤ (max (endpoint s).1.natAbs (endpoint s).2.natAbs : ℕ) := by
    exact_mod_cast hnorm
  exact hcast.trans (max_natAbs_le_euclidean (endpoint s))

/-- A collision-count hypothesis implies a lower bound for the canonical first
Euclidean endpoint moment. No anti-concentration estimate is asserted here. -/
theorem expectedDistance_ge_of_collision_count (n m : ℕ)
    (h : 4 * (2 * m + 1) ^ 2 * endpointCollisionCount n ≤ (walks n).card ^ 2) :
    (m : ℝ) / 2 ≤ expectedDistance n := by
  classical
  have hhalf := FiniteEndpointCollision.twice_small_card_le (walks n) endpoint (endpointBox m)
    (by simpa only [endpointBox_card, endpointCollisionCount] using h)
  have hsum := FiniteEndpointCollision.half_mul_card_le_sum (walks n) endpoint (endpointBox m)
    endpointDistance (m : ℝ) (Nat.cast_nonneg _)
    (fun _ _ => Real.sqrt_nonneg _)
    (fun s _ hs => endpointDistance_ge_of_outside s hs) hhalf
  have hc : (0 : ℝ) < (walks n).card := by
    exact_mod_cast Finset.card_pos.mpr (walks_nonempty n)
  exact (le_div_iff₀ hc).mpr hsum

theorem endpointCollisionProbability_nonneg (n : ℕ) :
    0 ≤ endpointCollisionProbability n :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem expectedDistance_ge_of_collision_probability (n m : ℕ)
    (h : 4 * (2 * (m : ℝ) + 1) ^ 2 * endpointCollisionProbability n ≤ 1) :
    (m : ℝ) / 2 ≤ expectedDistance n := by
  apply expectedDistance_ge_of_collision_count
  have hc : (0 : ℝ) < (walks n).card := by
    exact_mod_cast Finset.card_pos.mpr (walks_nonempty n)
  have hc2 : (0 : ℝ) < ((walks n).card : ℝ) ^ 2 := sq_pos_of_pos hc
  have hraw : 4 * (2 * (m : ℝ) + 1) ^ 2 * (endpointCollisionCount n : ℝ) ≤
      ((walks n).card : ℝ) ^ 2 := by
    have hh : (4 * (2 * (m : ℝ) + 1) ^ 2 * (endpointCollisionCount n : ℝ)) /
        ((walks n).card : ℝ) ^ 2 ≤ 1 := by
      simpa only [endpointCollisionProbability, mul_div_assoc] using h
    simpa only [one_mul] using (div_le_iff₀ hc2).mp hh
  exact_mod_cast hraw

open Filter
open scoped Topology

/-- A quantitative endpoint-collision hypothesis implies the full canonical
superdiffusivity target. The convergence premise is NOT proved here. -/
theorem superdiffusive_of_scaled_collision_tendsto_zero
    (hρ : Tendsto (fun n : ℕ => (n : ℝ) * endpointCollisionProbability n)
      atTop (𝓝 0)) :
    ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop,
      C * Real.sqrt n < expectedDistance n := by
  intro C hC
  let B : ℝ := 8 * C + 3
  let A : ℝ := 4 * B ^ 2
  have hscaled : Tendsto
      (fun n : ℕ => A * ((n : ℝ) * endpointCollisionProbability n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul A hρ
  have hsmall : ∀ᶠ n : ℕ in atTop,
      A * ((n : ℝ) * endpointCollisionProbability n) < 1 :=
    (tendsto_order.mp hscaled).2 1 zero_lt_one
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hnsmall hn
  let m : ℕ := ⌈4 * C * Real.sqrt n⌉₊
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnreal
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hm0 : 0 ≤ 4 * C * Real.sqrt n :=
    mul_nonneg (by linarith) hs0
  have hmlo : 4 * C * Real.sqrt n ≤ (m : ℝ) := Nat.le_ceil _
  have hmhi : (m : ℝ) < 4 * C * Real.sqrt n + 1 := Nat.ceil_lt_add_one hm0
  have hbox : 2 * (m : ℝ) + 1 ≤ B * Real.sqrt n := by
    dsimp only [B]
    nlinarith
  have hsq : (2 * (m : ℝ) + 1) ^ 2 ≤ B ^ 2 * (n : ℝ) := by
    calc
      (2 * (m : ℝ) + 1) ^ 2 ≤ (B * Real.sqrt n) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hbox 2
      _ = B ^ 2 * (n : ℝ) := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hρnonneg := endpointCollisionProbability_nonneg n
  have hcriterion : 4 * (2 * (m : ℝ) + 1) ^ 2 * endpointCollisionProbability n ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hρnonneg)
    dsimp only [A] at hnsmall
    nlinarith
  have hmean := expectedDistance_ge_of_collision_probability n m hcriterion
  have hpositive : 0 < C * Real.sqrt n := mul_pos hC (lt_of_lt_of_le zero_lt_one hs)
  have hstrict : C * Real.sqrt n < (m : ℝ) / 2 := by nlinarith
  exact hstrict.trans_le hmean

end PlanarSAWEndpointCollision


open PlanarSAWEndpointCollision
open Filter
open scoped Topology

theorem proof :
  (∀ n m : ℕ,
    4 * (2 * m + 1) ^ 2 * endpointCollisionCount n ≤ (walks n).card ^ 2 →
      (m : ℝ) / 2 ≤ expectedDistance n) ∧
  (Tendsto (fun n : ℕ => (n : ℝ) * endpointCollisionProbability n) atTop (𝓝 0) →
    ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop,
      C * Real.sqrt n < expectedDistance n) :=
  ⟨expectedDistance_ge_of_collision_count, superdiffusive_of_scaled_collision_tendsto_zero⟩

end Submissions.Erdos529EndpointCollisionCriterion.Main

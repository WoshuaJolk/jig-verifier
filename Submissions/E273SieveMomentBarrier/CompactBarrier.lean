import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Data.Rat.Defs


namespace Submissions.E273SieveMomentBarrier.CompactBarrier

open scoped BigOperators

/-- All allowed moduli with successor prime at most 100000. -/
def pool : Finset ℕ :=
  (Finset.range 100000).filter (fun d => 4 ≤ d ∧ Nat.Prime (d + 1))

def largestPrime (d : ℕ) : ℕ := d.primeFactors.sup id

def cofactor (d : ℕ) : ℕ := d / largestPrime d ^ d.factorization (largestPrime d)

def group (q : ℕ) : Finset ℕ := pool.filter (fun d => largestPrime d = q)

noncomputable def distortion (δ : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ r ∈ m.primeFactors, (1 - δ r)⁻¹

/-- Residue-independent first-moment upper bound, not the actual moment. -/
noncomputable def firstBound (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ group q, distortion δ (cofactor d) / (d : ℝ)

/-- Residue-independent second-moment upper bound, not the actual moment. -/
noncomputable def secondBound (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ group q, ∑ e ∈ group q,
    distortion δ (Nat.lcm (cofactor d) (cofactor e)) *
      (Nat.gcd (cofactor d) (cofactor e) : ℝ) / ((d : ℝ) * (e : ℝ))

/-- At zero distortion use the first-moment branch. -/
noncomputable def criterion (δ : ℕ → ℝ) : ℝ :=
  ∑ q ∈ pool.image largestPrime,
    if δ q = 0 then firstBound δ q
    else min (firstBound δ q) (secondBound δ q / (4 * δ q * (1 - δ q)))

/-- This particular plugged-in bound cannot certify noncoverage of the full pool. -/
abbrev statement : Prop :=
  ∀ δ : ℕ → ℝ, (∀ q, 0 ≤ δ q ∧ δ q ≤ 1 / 2) → 1 < criterion δ


lemma weight_one_le (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) (q : ℕ) :
    1 ≤ (1 - δ q)⁻¹ := by
  have hpos : 0 < 1 - δ q := by linarith [(hδ q).2]
  rw [one_le_inv₀ hpos]
  linarith [(hδ q).1]

lemma distortion_one_le (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) (m : ℕ) :
    1 ≤ distortion δ m := by
  exact Finset.one_le_prod (fun q _ => weight_one_le δ hδ q)

lemma distortion_subset (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (m : ℕ) (s : Finset ℕ) (hs : s ⊆ m.primeFactors) :
    (∏ q ∈ s, (1 - δ q)⁻¹) ≤ distortion δ m := by
  exact Finset.prod_le_prod_of_subset_of_one_le hs
    (fun q _ => le_trans zero_le_one (weight_one_le δ hδ q))
    (fun q _ _ => weight_one_le δ hδ q)

lemma firstBound_nonneg (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) (q : ℕ) :
    0 ≤ firstBound δ q := by
  apply Finset.sum_nonneg
  intro d hd
  exact div_nonneg (le_trans zero_le_one (distortion_one_le δ hδ _)) (Nat.cast_nonneg _)

lemma secondBound_nonneg (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) (q : ℕ) :
    0 ≤ secondBound δ q := by
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro e he
  exact div_nonneg (mul_nonneg (le_trans zero_le_one (distortion_one_le δ hδ _))
    (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

lemma first_subset (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (q : ℕ) (s : Finset ℕ) (hs : s ⊆ group q) :
    (∑ d ∈ s, distortion δ (cofactor d) / (d : ℝ)) ≤ firstBound δ q := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hs
  intro d _ _
  exact div_nonneg (le_trans zero_le_one (distortion_one_le δ hδ _)) (Nat.cast_nonneg _)

lemma second_subset (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (q : ℕ) (s : Finset ℕ) (hs : s ⊆ group q) :
    (∑ d ∈ s, ∑ e ∈ s, distortion δ (Nat.lcm (cofactor d) (cofactor e)) *
      (Nat.gcd (cofactor d) (cofactor e) : ℝ) / ((d : ℝ) * (e : ℝ))) ≤ secondBound δ q := by
  have hn (d e : ℕ) : 0 ≤ distortion δ (Nat.lcm (cofactor d) (cofactor e)) *
      (Nat.gcd (cofactor d) (cofactor e) : ℝ) / ((d : ℝ) * (e : ℝ)) :=
    div_nonneg (mul_nonneg (le_trans zero_le_one (distortion_one_le δ hδ _))
      (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  apply le_trans (Finset.sum_le_sum (fun d _ =>
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun e _ _ => hn d e)))
  exact Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun d _ _ => Finset.sum_nonneg (fun e _ => hn d e))

lemma criterion_term_nonneg (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) (q : ℕ) :
    0 ≤ (if δ q = 0 then firstBound δ q else
      min (firstBound δ q) (secondBound δ q / (4 * δ q * (1 - δ q)))) := by
  have hd : 0 ≤ 4 * δ q * (1 - δ q) := by
    apply mul_nonneg (mul_nonneg (by norm_num) (hδ q).1)
    linarith [(hδ q).2]
  split_ifs
  · exact firstBound_nonneg δ hδ q
  · exact le_min (firstBound_nonneg δ hδ q) (div_nonneg (secondBound_nonneg δ hδ q) hd)

lemma criterion_lower_bound (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (Q : Finset ℕ) (hQ : Q ⊆ pool.image largestPrime)
    (a b : ℕ → ℝ) (ha : ∀ q ∈ Q, a q ≤ firstBound δ q)
    (hb : ∀ q ∈ Q, b q ≤ secondBound δ q) :
    (∑ q ∈ Q, if δ q = 0 then a q else min (a q) (b q / (4 * δ q * (1 - δ q))))
      ≤ criterion δ := by
  apply le_trans (Finset.sum_le_sum (fun q hq => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg hQ (fun q _ _ => criterion_term_nonneg δ hδ q))
  split_ifs
  · exact ha q hq
  · apply min_le_min (ha q hq)
    apply div_le_div_of_nonneg_right (hb q hq)
    apply mul_nonneg (mul_nonneg (by norm_num) (hδ q).1)
    linarith [(hδ q).2]


lemma distortion_small_primes (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (m : ℕ) (hm : m ≠ 0) (h2 : 2 ∣ m) :
    (1 - δ 2)⁻¹ * (if 3 ∣ m then (1 - δ 3)⁻¹ else 1) *
      (if 5 ∣ m then (1 - δ 5)⁻¹ else 1) ≤ distortion δ m := by
  have hs : ({2, 3, 5} : Finset ℕ).filter (fun p => p ∣ m) ⊆ m.primeFactors := by
    intro p hp
    obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp <;> subst p
    all_goals exact Nat.mem_primeFactors.mpr ⟨by norm_num, hd, hm⟩
  have h := distortion_subset δ hδ m _ hs
  by_cases h3 : 3 ∣ m <;> by_cases h5 : 5 ∣ m
  all_goals simpa [Finset.filter_insert, Finset.filter_singleton, h2, h3, h5, mul_assoc, mul_comm, mul_left_comm] using h


end Submissions.E273SieveMomentBarrier.CompactBarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate

def rows : List (ℕ × ℕ × ℕ) := [
(4, 2, 1),
(6, 3, 2),
(10, 5, 2),
(12, 3, 4),
(16, 2, 1),
(18, 3, 2),
(22, 11, 2),
(28, 7, 4),
(30, 5, 6),
(36, 3, 4),
(40, 5, 8),
(42, 7, 6),
(60, 5, 12),
(66, 11, 6),
(70, 7, 10),
(72, 3, 8),
(88, 11, 8),
(96, 3, 32),
(100, 5, 4),
(108, 3, 4),
(112, 7, 16),
(126, 7, 18),
(150, 5, 6),
(162, 3, 2),
(180, 5, 36),
(192, 3, 64),
(196, 7, 4),
(198, 11, 18),
(210, 7, 30),
(240, 5, 48),
(250, 5, 2),
(256, 2, 1),
(270, 5, 54),
(280, 7, 40),
(330, 11, 30),
(336, 7, 48),
(352, 11, 32),
(378, 7, 54),
(396, 11, 36),
(400, 5, 16),
(420, 7, 60),
(432, 3, 16),
(448, 7, 64),
(462, 11, 42),
(486, 3, 2),
(490, 7, 10),
(540, 5, 108),
(576, 3, 64),
(600, 5, 24),
(616, 11, 56),
(630, 7, 90),
(640, 5, 128),
(660, 11, 60),
(672, 7, 96),
(700, 7, 100),
(726, 11, 6),
(750, 5, 6),
(756, 7, 108),
(768, 3, 256),
(810, 5, 162),
(880, 11, 80),
(882, 7, 18),
(990, 11, 90),
(1008, 7, 144),
(1050, 7, 150),
(1152, 3, 128),
(1200, 5, 48),
(1296, 3, 16),
(1320, 11, 120),
(1372, 7, 4),
(1408, 11, 128),
(1452, 11, 12),
(1458, 3, 2),
(1470, 7, 30),
(1600, 5, 64),
(1620, 5, 324),
(1782, 11, 162),
(1800, 5, 72),
(2016, 7, 288),
(2112, 11, 192),
(2160, 5, 432),
(2178, 11, 18),
(2250, 5, 18),
(2268, 7, 324),
(2310, 11, 210),
(2376, 11, 216),
(2520, 7, 360),
(2592, 3, 32),
(2646, 7, 54),
(2662, 11, 2),
(2688, 7, 384),
(2800, 7, 400),
(2916, 3, 4),
(2970, 11, 270),
(3000, 5, 24),
(3136, 7, 64),
(3168, 11, 288),
(3300, 11, 300),
(3360, 7, 480),
(3388, 11, 28),
(3456, 3, 128),
(3528, 7, 72),
(3630, 11, 30),
(3696, 11, 336),
(3850, 11, 350),
(3888, 3, 16),
(4000, 5, 32),
(4050, 5, 162),
(4158, 11, 378),
(4200, 7, 600),
(4356, 11, 36),
(4480, 7, 640),
(4620, 11, 420),
(4800, 5, 192),
(4860, 5, 972),
(4950, 11, 450)]

def rowValid (r : ℕ × ℕ × ℕ) : Prop :=
  4 ≤ r.1 ∧ r.1 < 100000 ∧ Nat.Prime (r.1 + 1) ∧
  r.1.primeFactors.sup id = r.2.1 ∧
  r.1 / r.2.1 ^ r.1.factorization r.2.1 = r.2.2

instance (r : ℕ × ℕ × ℕ) : Decidable (rowValid r) := by
  unfold rowValid
  infer_instance

private theorem prime2 : Nat.Prime 2 := by norm_num
private theorem prime3 : Nat.Prime 3 := by norm_num
private theorem prime5 : Nat.Prime 5 := by norm_num
private theorem prime7 : Nat.Prime 7 := by norm_num
private theorem prime11 : Nat.Prime 11 := by norm_num

theorem row_4 : rowValid (4, 2, 1) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4 : ℕ) = 2^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors]
    decide +kernel
  · have hf : (4 : ℕ).factorization 2 = 2 := by
      rw [show (4 : ℕ) = 2^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_6 : rowValid (6, 3, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (6 : ℕ) = 2^1 * 3^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (6 : ℕ).factorization 3 = 1 := by
      rw [show (6 : ℕ) = 2^1 * 3^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_10 : rowValid (10, 5, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (10 : ℕ) = 2^1 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (10 : ℕ).factorization 5 = 1 := by
      rw [show (10 : ℕ) = 2^1 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_12 : rowValid (12, 3, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (12 : ℕ) = 2^2 * 3^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (12 : ℕ).factorization 3 = 1 := by
      rw [show (12 : ℕ) = 2^2 * 3^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_16 : rowValid (16, 2, 1) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (16 : ℕ) = 2^4 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors]
    decide +kernel
  · have hf : (16 : ℕ).factorization 2 = 4 := by
      rw [show (16 : ℕ) = 2^4 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_18 : rowValid (18, 3, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (18 : ℕ) = 2^1 * 3^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (18 : ℕ).factorization 3 = 2 := by
      rw [show (18 : ℕ) = 2^1 * 3^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_22 : rowValid (22, 11, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (22 : ℕ) = 2^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (22 : ℕ).factorization 11 = 1 := by
      rw [show (22 : ℕ) = 2^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_28 : rowValid (28, 7, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (28 : ℕ) = 2^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (28 : ℕ).factorization 7 = 1 := by
      rw [show (28 : ℕ) = 2^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_30 : rowValid (30, 5, 6) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (30 : ℕ) = 2^1 * 3^1 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (30 : ℕ).factorization 5 = 1 := by
      rw [show (30 : ℕ) = 2^1 * 3^1 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_36 : rowValid (36, 3, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (36 : ℕ) = 2^2 * 3^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (36 : ℕ).factorization 3 = 2 := by
      rw [show (36 : ℕ) = 2^2 * 3^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_40 : rowValid (40, 5, 8) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (40 : ℕ) = 2^3 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (40 : ℕ).factorization 5 = 1 := by
      rw [show (40 : ℕ) = 2^3 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_42 : rowValid (42, 7, 6) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (42 : ℕ) = 2^1 * 3^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (42 : ℕ).factorization 7 = 1 := by
      rw [show (42 : ℕ) = 2^1 * 3^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_60 : rowValid (60, 5, 12) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (60 : ℕ) = 2^2 * 3^1 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (60 : ℕ).factorization 5 = 1 := by
      rw [show (60 : ℕ) = 2^2 * 3^1 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_66 : rowValid (66, 11, 6) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (66 : ℕ) = 2^1 * 3^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (66 : ℕ).factorization 11 = 1 := by
      rw [show (66 : ℕ) = 2^1 * 3^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_70 : rowValid (70, 7, 10) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (70 : ℕ) = 2^1 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (70 : ℕ).factorization 7 = 1 := by
      rw [show (70 : ℕ) = 2^1 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_72 : rowValid (72, 3, 8) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (72 : ℕ) = 2^3 * 3^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (72 : ℕ).factorization 3 = 2 := by
      rw [show (72 : ℕ) = 2^3 * 3^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_88 : rowValid (88, 11, 8) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (88 : ℕ) = 2^3 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (88 : ℕ).factorization 11 = 1 := by
      rw [show (88 : ℕ) = 2^3 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_96 : rowValid (96, 3, 32) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (96 : ℕ) = 2^5 * 3^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (96 : ℕ).factorization 3 = 1 := by
      rw [show (96 : ℕ) = 2^5 * 3^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_100 : rowValid (100, 5, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (100 : ℕ) = 2^2 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (100 : ℕ).factorization 5 = 2 := by
      rw [show (100 : ℕ) = 2^2 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_108 : rowValid (108, 3, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (108 : ℕ) = 2^2 * 3^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (108 : ℕ).factorization 3 = 3 := by
      rw [show (108 : ℕ) = 2^2 * 3^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_112 : rowValid (112, 7, 16) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (112 : ℕ) = 2^4 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (112 : ℕ).factorization 7 = 1 := by
      rw [show (112 : ℕ) = 2^4 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_126 : rowValid (126, 7, 18) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (126 : ℕ) = 2^1 * 3^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (126 : ℕ).factorization 7 = 1 := by
      rw [show (126 : ℕ) = 2^1 * 3^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_150 : rowValid (150, 5, 6) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (150 : ℕ) = 2^1 * 3^1 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (150 : ℕ).factorization 5 = 2 := by
      rw [show (150 : ℕ) = 2^1 * 3^1 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_162 : rowValid (162, 3, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (162 : ℕ) = 2^1 * 3^4 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (162 : ℕ).factorization 3 = 4 := by
      rw [show (162 : ℕ) = 2^1 * 3^4 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_180 : rowValid (180, 5, 36) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (180 : ℕ) = 2^2 * 3^2 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (180 : ℕ).factorization 5 = 1 := by
      rw [show (180 : ℕ) = 2^2 * 3^2 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_192 : rowValid (192, 3, 64) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (192 : ℕ) = 2^6 * 3^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (192 : ℕ).factorization 3 = 1 := by
      rw [show (192 : ℕ) = 2^6 * 3^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_196 : rowValid (196, 7, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (196 : ℕ) = 2^2 * 7^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (196 : ℕ).factorization 7 = 2 := by
      rw [show (196 : ℕ) = 2^2 * 7^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_198 : rowValid (198, 11, 18) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (198 : ℕ) = 2^1 * 3^2 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (198 : ℕ).factorization 11 = 1 := by
      rw [show (198 : ℕ) = 2^1 * 3^2 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_210 : rowValid (210, 7, 30) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (210 : ℕ) = 2^1 * 3^1 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (210 : ℕ).factorization 7 = 1 := by
      rw [show (210 : ℕ) = 2^1 * 3^1 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_240 : rowValid (240, 5, 48) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (240 : ℕ) = 2^4 * 3^1 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (240 : ℕ).factorization 5 = 1 := by
      rw [show (240 : ℕ) = 2^4 * 3^1 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_250 : rowValid (250, 5, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (250 : ℕ) = 2^1 * 5^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (250 : ℕ).factorization 5 = 3 := by
      rw [show (250 : ℕ) = 2^1 * 5^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_256 : rowValid (256, 2, 1) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (256 : ℕ) = 2^8 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors]
    decide +kernel
  · have hf : (256 : ℕ).factorization 2 = 8 := by
      rw [show (256 : ℕ) = 2^8 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_270 : rowValid (270, 5, 54) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (270 : ℕ) = 2^1 * 3^3 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (270 : ℕ).factorization 5 = 1 := by
      rw [show (270 : ℕ) = 2^1 * 3^3 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_280 : rowValid (280, 7, 40) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (280 : ℕ) = 2^3 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (280 : ℕ).factorization 7 = 1 := by
      rw [show (280 : ℕ) = 2^3 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_330 : rowValid (330, 11, 30) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (330 : ℕ) = 2^1 * 3^1 * 5^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (330 : ℕ).factorization 11 = 1 := by
      rw [show (330 : ℕ) = 2^1 * 3^1 * 5^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_336 : rowValid (336, 7, 48) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (336 : ℕ) = 2^4 * 3^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (336 : ℕ).factorization 7 = 1 := by
      rw [show (336 : ℕ) = 2^4 * 3^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_352 : rowValid (352, 11, 32) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (352 : ℕ) = 2^5 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (352 : ℕ).factorization 11 = 1 := by
      rw [show (352 : ℕ) = 2^5 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_378 : rowValid (378, 7, 54) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (378 : ℕ) = 2^1 * 3^3 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (378 : ℕ).factorization 7 = 1 := by
      rw [show (378 : ℕ) = 2^1 * 3^3 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_396 : rowValid (396, 11, 36) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (396 : ℕ) = 2^2 * 3^2 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (396 : ℕ).factorization 11 = 1 := by
      rw [show (396 : ℕ) = 2^2 * 3^2 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_400 : rowValid (400, 5, 16) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (400 : ℕ) = 2^4 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (400 : ℕ).factorization 5 = 2 := by
      rw [show (400 : ℕ) = 2^4 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_420 : rowValid (420, 7, 60) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (420 : ℕ) = 2^2 * 3^1 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (420 : ℕ).factorization 7 = 1 := by
      rw [show (420 : ℕ) = 2^2 * 3^1 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_432 : rowValid (432, 3, 16) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (432 : ℕ) = 2^4 * 3^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (432 : ℕ).factorization 3 = 3 := by
      rw [show (432 : ℕ) = 2^4 * 3^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_448 : rowValid (448, 7, 64) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (448 : ℕ) = 2^6 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (448 : ℕ).factorization 7 = 1 := by
      rw [show (448 : ℕ) = 2^6 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_462 : rowValid (462, 11, 42) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (462 : ℕ) = 2^1 * 3^1 * 7^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (462 : ℕ).factorization 11 = 1 := by
      rw [show (462 : ℕ) = 2^1 * 3^1 * 7^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_486 : rowValid (486, 3, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (486 : ℕ) = 2^1 * 3^5 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (486 : ℕ).factorization 3 = 5 := by
      rw [show (486 : ℕ) = 2^1 * 3^5 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_490 : rowValid (490, 7, 10) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (490 : ℕ) = 2^1 * 5^1 * 7^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (490 : ℕ).factorization 7 = 2 := by
      rw [show (490 : ℕ) = 2^1 * 5^1 * 7^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_540 : rowValid (540, 5, 108) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (540 : ℕ) = 2^2 * 3^3 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (540 : ℕ).factorization 5 = 1 := by
      rw [show (540 : ℕ) = 2^2 * 3^3 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_576 : rowValid (576, 3, 64) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (576 : ℕ) = 2^6 * 3^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (576 : ℕ).factorization 3 = 2 := by
      rw [show (576 : ℕ) = 2^6 * 3^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_600 : rowValid (600, 5, 24) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (600 : ℕ) = 2^3 * 3^1 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (600 : ℕ).factorization 5 = 2 := by
      rw [show (600 : ℕ) = 2^3 * 3^1 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_616 : rowValid (616, 11, 56) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (616 : ℕ) = 2^3 * 7^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (616 : ℕ).factorization 11 = 1 := by
      rw [show (616 : ℕ) = 2^3 * 7^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_630 : rowValid (630, 7, 90) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (630 : ℕ) = 2^1 * 3^2 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (630 : ℕ).factorization 7 = 1 := by
      rw [show (630 : ℕ) = 2^1 * 3^2 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_640 : rowValid (640, 5, 128) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (640 : ℕ) = 2^7 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (640 : ℕ).factorization 5 = 1 := by
      rw [show (640 : ℕ) = 2^7 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_660 : rowValid (660, 11, 60) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (660 : ℕ) = 2^2 * 3^1 * 5^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (660 : ℕ).factorization 11 = 1 := by
      rw [show (660 : ℕ) = 2^2 * 3^1 * 5^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_672 : rowValid (672, 7, 96) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (672 : ℕ) = 2^5 * 3^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (672 : ℕ).factorization 7 = 1 := by
      rw [show (672 : ℕ) = 2^5 * 3^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_700 : rowValid (700, 7, 100) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (700 : ℕ) = 2^2 * 5^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (700 : ℕ).factorization 7 = 1 := by
      rw [show (700 : ℕ) = 2^2 * 5^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_726 : rowValid (726, 11, 6) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (726 : ℕ) = 2^1 * 3^1 * 11^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (726 : ℕ).factorization 11 = 2 := by
      rw [show (726 : ℕ) = 2^1 * 3^1 * 11^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_750 : rowValid (750, 5, 6) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (750 : ℕ) = 2^1 * 3^1 * 5^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (750 : ℕ).factorization 5 = 3 := by
      rw [show (750 : ℕ) = 2^1 * 3^1 * 5^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_756 : rowValid (756, 7, 108) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (756 : ℕ) = 2^2 * 3^3 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (756 : ℕ).factorization 7 = 1 := by
      rw [show (756 : ℕ) = 2^2 * 3^3 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_768 : rowValid (768, 3, 256) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (768 : ℕ) = 2^8 * 3^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (768 : ℕ).factorization 3 = 1 := by
      rw [show (768 : ℕ) = 2^8 * 3^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_810 : rowValid (810, 5, 162) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (810 : ℕ) = 2^1 * 3^4 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (810 : ℕ).factorization 5 = 1 := by
      rw [show (810 : ℕ) = 2^1 * 3^4 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_880 : rowValid (880, 11, 80) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (880 : ℕ) = 2^4 * 5^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (880 : ℕ).factorization 11 = 1 := by
      rw [show (880 : ℕ) = 2^4 * 5^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_882 : rowValid (882, 7, 18) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (882 : ℕ) = 2^1 * 3^2 * 7^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (882 : ℕ).factorization 7 = 2 := by
      rw [show (882 : ℕ) = 2^1 * 3^2 * 7^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_990 : rowValid (990, 11, 90) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (990 : ℕ) = 2^1 * 3^2 * 5^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (990 : ℕ).factorization 11 = 1 := by
      rw [show (990 : ℕ) = 2^1 * 3^2 * 5^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1008 : rowValid (1008, 7, 144) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1008 : ℕ) = 2^4 * 3^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (1008 : ℕ).factorization 7 = 1 := by
      rw [show (1008 : ℕ) = 2^4 * 3^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1050 : rowValid (1050, 7, 150) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1050 : ℕ) = 2^1 * 3^1 * 5^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (1050 : ℕ).factorization 7 = 1 := by
      rw [show (1050 : ℕ) = 2^1 * 3^1 * 5^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1152 : rowValid (1152, 3, 128) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1152 : ℕ) = 2^7 * 3^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (1152 : ℕ).factorization 3 = 2 := by
      rw [show (1152 : ℕ) = 2^7 * 3^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1200 : rowValid (1200, 5, 48) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1200 : ℕ) = 2^4 * 3^1 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (1200 : ℕ).factorization 5 = 2 := by
      rw [show (1200 : ℕ) = 2^4 * 3^1 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1296 : rowValid (1296, 3, 16) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1296 : ℕ) = 2^4 * 3^4 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (1296 : ℕ).factorization 3 = 4 := by
      rw [show (1296 : ℕ) = 2^4 * 3^4 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1320 : rowValid (1320, 11, 120) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1320 : ℕ) = 2^3 * 3^1 * 5^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (1320 : ℕ).factorization 11 = 1 := by
      rw [show (1320 : ℕ) = 2^3 * 3^1 * 5^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1372 : rowValid (1372, 7, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1372 : ℕ) = 2^2 * 7^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (1372 : ℕ).factorization 7 = 3 := by
      rw [show (1372 : ℕ) = 2^2 * 7^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1408 : rowValid (1408, 11, 128) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1408 : ℕ) = 2^7 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (1408 : ℕ).factorization 11 = 1 := by
      rw [show (1408 : ℕ) = 2^7 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1452 : rowValid (1452, 11, 12) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1452 : ℕ) = 2^2 * 3^1 * 11^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (1452 : ℕ).factorization 11 = 2 := by
      rw [show (1452 : ℕ) = 2^2 * 3^1 * 11^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1458 : rowValid (1458, 3, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1458 : ℕ) = 2^1 * 3^6 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (1458 : ℕ).factorization 3 = 6 := by
      rw [show (1458 : ℕ) = 2^1 * 3^6 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1470 : rowValid (1470, 7, 30) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1470 : ℕ) = 2^1 * 3^1 * 5^1 * 7^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (1470 : ℕ).factorization 7 = 2 := by
      rw [show (1470 : ℕ) = 2^1 * 3^1 * 5^1 * 7^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1600 : rowValid (1600, 5, 64) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1600 : ℕ) = 2^6 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (1600 : ℕ).factorization 5 = 2 := by
      rw [show (1600 : ℕ) = 2^6 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1620 : rowValid (1620, 5, 324) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1620 : ℕ) = 2^2 * 3^4 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (1620 : ℕ).factorization 5 = 1 := by
      rw [show (1620 : ℕ) = 2^2 * 3^4 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1782 : rowValid (1782, 11, 162) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1782 : ℕ) = 2^1 * 3^4 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (1782 : ℕ).factorization 11 = 1 := by
      rw [show (1782 : ℕ) = 2^1 * 3^4 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_1800 : rowValid (1800, 5, 72) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1800 : ℕ) = 2^3 * 3^2 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (1800 : ℕ).factorization 5 = 2 := by
      rw [show (1800 : ℕ) = 2^3 * 3^2 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2016 : rowValid (2016, 7, 288) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2016 : ℕ) = 2^5 * 3^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (2016 : ℕ).factorization 7 = 1 := by
      rw [show (2016 : ℕ) = 2^5 * 3^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2112 : rowValid (2112, 11, 192) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2112 : ℕ) = 2^6 * 3^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (2112 : ℕ).factorization 11 = 1 := by
      rw [show (2112 : ℕ) = 2^6 * 3^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2160 : rowValid (2160, 5, 432) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2160 : ℕ) = 2^4 * 3^3 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (2160 : ℕ).factorization 5 = 1 := by
      rw [show (2160 : ℕ) = 2^4 * 3^3 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2178 : rowValid (2178, 11, 18) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2178 : ℕ) = 2^1 * 3^2 * 11^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (2178 : ℕ).factorization 11 = 2 := by
      rw [show (2178 : ℕ) = 2^1 * 3^2 * 11^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2250 : rowValid (2250, 5, 18) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2250 : ℕ) = 2^1 * 3^2 * 5^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (2250 : ℕ).factorization 5 = 3 := by
      rw [show (2250 : ℕ) = 2^1 * 3^2 * 5^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2268 : rowValid (2268, 7, 324) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2268 : ℕ) = 2^2 * 3^4 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (2268 : ℕ).factorization 7 = 1 := by
      rw [show (2268 : ℕ) = 2^2 * 3^4 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2310 : rowValid (2310, 11, 210) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2310 : ℕ) = 2^1 * 3^1 * 5^1 * 7^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (2310 : ℕ).factorization 11 = 1 := by
      rw [show (2310 : ℕ) = 2^1 * 3^1 * 5^1 * 7^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2376 : rowValid (2376, 11, 216) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2376 : ℕ) = 2^3 * 3^3 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (2376 : ℕ).factorization 11 = 1 := by
      rw [show (2376 : ℕ) = 2^3 * 3^3 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2520 : rowValid (2520, 7, 360) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2520 : ℕ) = 2^3 * 3^2 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (2520 : ℕ).factorization 7 = 1 := by
      rw [show (2520 : ℕ) = 2^3 * 3^2 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2592 : rowValid (2592, 3, 32) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2592 : ℕ) = 2^5 * 3^4 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (2592 : ℕ).factorization 3 = 4 := by
      rw [show (2592 : ℕ) = 2^5 * 3^4 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2646 : rowValid (2646, 7, 54) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2646 : ℕ) = 2^1 * 3^3 * 7^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (2646 : ℕ).factorization 7 = 2 := by
      rw [show (2646 : ℕ) = 2^1 * 3^3 * 7^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2662 : rowValid (2662, 11, 2) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2662 : ℕ) = 2^1 * 11^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (2662 : ℕ).factorization 11 = 3 := by
      rw [show (2662 : ℕ) = 2^1 * 11^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2688 : rowValid (2688, 7, 384) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2688 : ℕ) = 2^7 * 3^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (2688 : ℕ).factorization 7 = 1 := by
      rw [show (2688 : ℕ) = 2^7 * 3^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2800 : rowValid (2800, 7, 400) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2800 : ℕ) = 2^4 * 5^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (2800 : ℕ).factorization 7 = 1 := by
      rw [show (2800 : ℕ) = 2^4 * 5^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2916 : rowValid (2916, 3, 4) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2916 : ℕ) = 2^2 * 3^6 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (2916 : ℕ).factorization 3 = 6 := by
      rw [show (2916 : ℕ) = 2^2 * 3^6 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_2970 : rowValid (2970, 11, 270) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (2970 : ℕ) = 2^1 * 3^3 * 5^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (2970 : ℕ).factorization 11 = 1 := by
      rw [show (2970 : ℕ) = 2^1 * 3^3 * 5^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3000 : rowValid (3000, 5, 24) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3000 : ℕ) = 2^3 * 3^1 * 5^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (3000 : ℕ).factorization 5 = 3 := by
      rw [show (3000 : ℕ) = 2^3 * 3^1 * 5^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3136 : rowValid (3136, 7, 64) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3136 : ℕ) = 2^6 * 7^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (3136 : ℕ).factorization 7 = 2 := by
      rw [show (3136 : ℕ) = 2^6 * 7^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3168 : rowValid (3168, 11, 288) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3168 : ℕ) = 2^5 * 3^2 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (3168 : ℕ).factorization 11 = 1 := by
      rw [show (3168 : ℕ) = 2^5 * 3^2 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3300 : rowValid (3300, 11, 300) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3300 : ℕ) = 2^2 * 3^1 * 5^2 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (3300 : ℕ).factorization 11 = 1 := by
      rw [show (3300 : ℕ) = 2^2 * 3^1 * 5^2 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3360 : rowValid (3360, 7, 480) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3360 : ℕ) = 2^5 * 3^1 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (3360 : ℕ).factorization 7 = 1 := by
      rw [show (3360 : ℕ) = 2^5 * 3^1 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3388 : rowValid (3388, 11, 28) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3388 : ℕ) = 2^2 * 7^1 * 11^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (3388 : ℕ).factorization 11 = 2 := by
      rw [show (3388 : ℕ) = 2^2 * 7^1 * 11^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3456 : rowValid (3456, 3, 128) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3456 : ℕ) = 2^7 * 3^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (3456 : ℕ).factorization 3 = 3 := by
      rw [show (3456 : ℕ) = 2^7 * 3^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3528 : rowValid (3528, 7, 72) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3528 : ℕ) = 2^3 * 3^2 * 7^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (3528 : ℕ).factorization 7 = 2 := by
      rw [show (3528 : ℕ) = 2^3 * 3^2 * 7^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3630 : rowValid (3630, 11, 30) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3630 : ℕ) = 2^1 * 3^1 * 5^1 * 11^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (3630 : ℕ).factorization 11 = 2 := by
      rw [show (3630 : ℕ) = 2^1 * 3^1 * 5^1 * 11^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3696 : rowValid (3696, 11, 336) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3696 : ℕ) = 2^4 * 3^1 * 7^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (3696 : ℕ).factorization 11 = 1 := by
      rw [show (3696 : ℕ) = 2^4 * 3^1 * 7^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3850 : rowValid (3850, 11, 350) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3850 : ℕ) = 2^1 * 5^2 * 7^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (3850 : ℕ).factorization 11 = 1 := by
      rw [show (3850 : ℕ) = 2^1 * 5^2 * 7^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_3888 : rowValid (3888, 3, 16) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (3888 : ℕ) = 2^4 * 3^5 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors]
    decide +kernel
  · have hf : (3888 : ℕ).factorization 3 = 5 := by
      rw [show (3888 : ℕ) = 2^4 * 3^5 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4000 : rowValid (4000, 5, 32) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4000 : ℕ) = 2^5 * 5^3 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (4000 : ℕ).factorization 5 = 3 := by
      rw [show (4000 : ℕ) = 2^5 * 5^3 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4050 : rowValid (4050, 5, 162) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4050 : ℕ) = 2^1 * 3^4 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (4050 : ℕ).factorization 5 = 2 := by
      rw [show (4050 : ℕ) = 2^1 * 3^4 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4158 : rowValid (4158, 11, 378) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4158 : ℕ) = 2^1 * 3^3 * 7^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (4158 : ℕ).factorization 11 = 1 := by
      rw [show (4158 : ℕ) = 2^1 * 3^3 * 7^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4200 : rowValid (4200, 7, 600) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4200 : ℕ) = 2^3 * 3^1 * 5^2 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (4200 : ℕ).factorization 7 = 1 := by
      rw [show (4200 : ℕ) = 2^3 * 3^1 * 5^2 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4356 : rowValid (4356, 11, 36) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4356 : ℕ) = 2^2 * 3^2 * 11^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (4356 : ℕ).factorization 11 = 2 := by
      rw [show (4356 : ℕ) = 2^2 * 3^2 * 11^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4480 : rowValid (4480, 7, 640) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4480 : ℕ) = 2^7 * 5^1 * 7^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime5.primeFactors, prime7.primeFactors]
    decide +kernel
  · have hf : (4480 : ℕ).factorization 7 = 1 := by
      rw [show (4480 : ℕ) = 2^7 * 5^1 * 7^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime5.factorization, prime7.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4620 : rowValid (4620, 11, 420) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4620 : ℕ) = 2^2 * 3^1 * 5^1 * 7^1 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime7.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (4620 : ℕ).factorization 11 = 1 := by
      rw [show (4620 : ℕ) = 2^2 * 3^1 * 5^1 * 7^1 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime7.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4800 : rowValid (4800, 5, 192) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4800 : ℕ) = 2^6 * 3^1 * 5^2 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (4800 : ℕ).factorization 5 = 2 := by
      rw [show (4800 : ℕ) = 2^6 * 3^1 * 5^2 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4860 : rowValid (4860, 5, 972) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4860 : ℕ) = 2^2 * 3^5 * 5^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors]
    decide +kernel
  · have hf : (4860 : ℕ).factorization 5 = 1 := by
      rw [show (4860 : ℕ) = 2^2 * 3^5 * 5^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem row_4950 : rowValid (4950, 11, 450) := by
  unfold rowValid
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (4950 : ℕ) = 2^1 * 3^2 * 5^2 * 11^1 by norm_num]
    simp (disch := norm_num) only [Nat.primeFactors_mul, Nat.primeFactors_pow, prime2.primeFactors, prime3.primeFactors, prime5.primeFactors, prime11.primeFactors]
    decide +kernel
  · have hf : (4950 : ℕ).factorization 11 = 1 := by
      rw [show (4950 : ℕ) = 2^1 * 3^2 * 5^2 * 11^1 by norm_num]
      simp (disch := norm_num) only [Nat.factorization_mul, Nat.factorization_pow, prime2.factorization, prime3.factorization, prime5.factorization, prime11.factorization]
      norm_num [Finsupp.single_apply]
    rw [hf]
    norm_num

theorem rows_valid : ∀ r ∈ rows, rowValid r := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨row_4, row_6, row_10, row_12, row_16, row_18, row_22, row_28, row_30, row_36, row_40, row_42, row_60, row_66, row_70, row_72, row_88, row_96, row_100, row_108, row_112, row_126, row_150, row_162, row_180, row_192, row_196, row_198, row_210, row_240, row_250, row_256, row_270, row_280, row_330, row_336, row_352, row_378, row_396, row_400, row_420, row_432, row_448, row_462, row_486, row_490, row_540, row_576, row_600, row_616, row_630, row_640, row_660, row_672, row_700, row_726, row_750, row_756, row_768, row_810, row_880, row_882, row_990, row_1008, row_1050, row_1152, row_1200, row_1296, row_1320, row_1372, row_1408, row_1452, row_1458, row_1470, row_1600, row_1620, row_1782, row_1800, row_2016, row_2112, row_2160, row_2178, row_2250, row_2268, row_2310, row_2376, row_2520, row_2592, row_2646, row_2662, row_2688, row_2800, row_2916, row_2970, row_3000, row_3136, row_3168, row_3300, row_3360, row_3388, row_3456, row_3528, row_3630, row_3696, row_3850, row_3888, row_4000, row_4050, row_4158, row_4200, row_4356, row_4480, row_4620, row_4800, row_4860, row_4950⟩
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
theorem rows_distinct : (rows.map Prod.fst).Nodup := by decide +kernel


def mask (m : ℕ) : ℕ := (if 3 ∣ m then 1 else 0) + (if 5 ∣ m then 2 else 0)
def group (q : ℕ) : List (ℕ × ℕ × ℕ) := rows.filter (fun r => r.2.1 == q)
def firstCoefficient (q k : ℕ) : ℚ :=
  (((group q).filter (fun r => mask r.2.2 == k)).map (fun r => (1 : ℚ) / r.1)).sum
def secondCoefficient (q k : ℕ) : ℚ :=
  ((group q).flatMap (fun r =>
    (((group q).filter (fun s => mask (Nat.lcm r.2.2 s.2.2) == k)).map
      (fun s => (Nat.gcd r.2.2 s.2.2 : ℚ) / ((r.1 : ℚ) * s.1))))).sum

theorem first_3_0 : (389 : ℚ) / 1000 ≤ firstCoefficient 3 0 := by decide +kernel
theorem first_3_1 : (0 : ℚ) / 1000 ≤ firstCoefficient 3 1 := by decide +kernel
theorem first_3_2 : (0 : ℚ) / 1000 ≤ firstCoefficient 3 2 := by decide +kernel
theorem first_3_3 : (0 : ℚ) / 1000 ≤ firstCoefficient 3 3 := by decide +kernel
theorem second_3_0 : (373 : ℚ) / 1000 ≤ secondCoefficient 3 0 := by decide +kernel
theorem second_3_1 : (0 : ℚ) / 1000 ≤ secondCoefficient 3 1 := by decide +kernel
theorem second_3_2 : (0 : ℚ) / 1000 ≤ secondCoefficient 3 2 := by decide +kernel
theorem second_3_3 : (0 : ℚ) / 1000 ≤ secondCoefficient 3 3 := by decide +kernel
theorem first_5_0 : (143 : ℚ) / 1000 ≤ firstCoefficient 5 0 := by decide +kernel
theorem first_5_1 : (80 : ℚ) / 1000 ≤ firstCoefficient 5 1 := by decide +kernel
theorem first_5_2 : (0 : ℚ) / 1000 ≤ firstCoefficient 5 2 := by decide +kernel
theorem first_5_3 : (0 : ℚ) / 1000 ≤ firstCoefficient 5 3 := by decide +kernel
theorem second_5_0 : (48 : ℚ) / 1000 ≤ secondCoefficient 5 0 := by decide +kernel
theorem second_5_1 : (107 : ℚ) / 1000 ≤ secondCoefficient 5 1 := by decide +kernel
theorem second_5_2 : (0 : ℚ) / 1000 ≤ secondCoefficient 5 2 := by decide +kernel
theorem second_5_3 : (0 : ℚ) / 1000 ≤ secondCoefficient 5 3 := by decide +kernel
theorem first_11_0 : (62 : ℚ) / 1000 ≤ firstCoefficient 11 0 := by decide +kernel
theorem first_11_1 : (29 : ℚ) / 1000 ≤ firstCoefficient 11 1 := by decide +kernel
theorem first_11_2 : (1 : ℚ) / 1000 ≤ firstCoefficient 11 2 := by decide +kernel
theorem first_11_3 : (8 : ℚ) / 1000 ≤ firstCoefficient 11 3 := by decide +kernel
theorem second_11_0 : (10 : ℚ) / 1000 ≤ secondCoefficient 11 0 := by decide +kernel
theorem second_11_1 : (15 : ℚ) / 1000 ≤ secondCoefficient 11 1 := by decide +kernel
theorem second_11_2 : (0 : ℚ) / 1000 ≤ secondCoefficient 11 2 := by decide +kernel
theorem second_11_3 : (9 : ℚ) / 1000 ≤ secondCoefficient 11 3 := by decide +kernel
theorem first_7_0 : (53 : ℚ) / 1000 ≤ firstCoefficient 7 0 := by decide +kernel
theorem first_7_1 : (44 : ℚ) / 1000 ≤ firstCoefficient 7 1 := by decide +kernel
theorem first_7_2 : (21 : ℚ) / 1000 ≤ firstCoefficient 7 2 := by decide +kernel
theorem first_7_3 : (11 : ℚ) / 1000 ≤ firstCoefficient 7 3 := by decide +kernel
theorem second_7_0 : (13 : ℚ) / 1000 ≤ secondCoefficient 7 0 := by decide +kernel
theorem second_7_1 : (31 : ℚ) / 1000 ≤ secondCoefficient 7 1 := by decide +kernel
theorem second_7_2 : (12 : ℚ) / 1000 ≤ secondCoefficient 7 2 := by decide +kernel
theorem second_7_3 : (25 : ℚ) / 1000 ≤ secondCoefficient 7 3 := by decide +kernel


theorem first_binary_exact : firstCoefficient 2 0 = (81 : ℚ) / 256 := by decide +kernel
theorem second_binary_exact : secondCoefficient 2 0 = ((81 : ℚ) / 256)^2 := by decide +kernel
theorem nonbinary_cofactors : ∀ r ∈ rows, r.2.1 ≠ 2 → r.2.2 ≠ 0 ∧ 2 ∣ r.2.2 := by
  have h : rows.all (fun r => decide (r.2.1 ≠ 2 → r.2.2 ≠ 0 ∧ 2 ∣ r.2.2)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open Submissions.E273SieveMomentBarrier.CompactBarrier
 theorem rows_in_canonical_group (r : ℕ × ℕ × ℕ) (hr : r ∈ rows) :
    r.1 ∈ Submissions.E273SieveMomentBarrier.CompactBarrier.group r.2.1 ∧
    cofactor r.1 = r.2.2 := by
  obtain ⟨h4, hmax, hp, hq, hm⟩ := rows_valid r hr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmax, h4, hp⟩, hq⟩
  · unfold cofactor largestPrime
    rw [hq]
    exact hm
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open scoped BigOperators
local notation "Cgroup" => Submissions.E273SieveMomentBarrier.CompactBarrier.group
open Submissions.E273SieveMomentBarrier.CompactBarrier

def selected (q : ℕ) : Finset (ℕ × ℕ × ℕ) := rows.toFinset.filter (fun r => r.2.1 = q)

lemma selected_valid {q : ℕ} {r : ℕ × ℕ × ℕ} (hr : r ∈ selected q) :
    r.1 ∈ Cgroup q ∧ cofactor r.1 = r.2.2 := by
  obtain ⟨hr, hq⟩ := Finset.mem_filter.mp hr
  have h := rows_in_canonical_group r (List.mem_toFinset.mp hr)
  simpa only [hq] using h

lemma selected_injective (q : ℕ) : Set.InjOn Prod.fst (selected q : Set (ℕ × ℕ × ℕ)) := by
  intro r hr s hs hd
  have hqr := (Finset.mem_filter.mp hr).2
  have hqs := (Finset.mem_filter.mp hs).2
  apply Prod.ext hd
  apply Prod.ext (hqr.trans hqs.symm)
  exact (selected_valid hr).2.symm.trans ((congrArg cofactor hd).trans (selected_valid hs).2)

lemma selected_first_le (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) (q : ℕ) :
    (∑ r ∈ selected q, distortion δ r.2.2 / (r.1 : ℝ)) ≤ firstBound δ q := by
  have hs : (selected q).image Prod.fst ⊆ Cgroup q := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hd
    exact (selected_valid hr).1
  have h := first_subset δ hδ q _ hs
  rw [Finset.sum_image (selected_injective q)] at h
  simpa only using (calc
    (∑ r ∈ selected q, distortion δ r.2.2 / (r.1 : ℝ)) =
      ∑ r ∈ selected q, distortion δ (cofactor r.1) / (r.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [(selected_valid hr).2]
    _ ≤ firstBound δ q := h)

lemma selected_second_le (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) (q : ℕ) :
    (∑ r ∈ selected q, ∑ s ∈ selected q,
      distortion δ (Nat.lcm r.2.2 s.2.2) * (Nat.gcd r.2.2 s.2.2 : ℝ) /
        ((r.1 : ℝ) * (s.1 : ℝ))) ≤ secondBound δ q := by
  have hs : (selected q).image Prod.fst ⊆ Cgroup q := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hd
    exact (selected_valid hr).1
  have h := second_subset δ hδ q _ hs
  rw [Finset.sum_image (selected_injective q)] at h
  simp_rw [Finset.sum_image (selected_injective q)] at h
  apply le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [(selected_valid hr).2, (selected_valid hs).2]

end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open scoped BigOperators
open Submissions.E273SieveMomentBarrier.CompactBarrier
lemma selected_sum_eq_list {M : Type*} [AddCommMonoid M] (q : ℕ) (f : (ℕ × ℕ × ℕ) → M) :
    (∑ r ∈ selected q, f r) = ((group q).map f).sum := by
  have hn : rows.Nodup := List.Nodup.of_map Prod.fst rows_distinct
  have heq : selected q = (group q).toFinset := by
    simp [selected, group, List.toFinset_filter]
  rw [heq]
  exact List.sum_toFinset _ (hn.filter _)

lemma selected_even {q : ℕ} (hq : q ≠ 2) {r : ℕ × ℕ × ℕ} (hr : r ∈ selected q) :
    r.2.2 ≠ 0 ∧ 2 ∣ r.2.2 := by
  obtain ⟨hr, h⟩ := Finset.mem_filter.mp hr
  exact nonbinary_cofactors r (List.mem_toFinset.mp hr) (h.trans_ne hq)

lemma selected_first_weighted (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (q : ℕ) (hq : q ≠ 2) :
    (∑ r ∈ selected q, ((1 - δ 2)⁻¹ *
      (if 3 ∣ r.2.2 then (1 - δ 3)⁻¹ else 1) *
      (if 5 ∣ r.2.2 then (1 - δ 5)⁻¹ else 1)) / (r.1 : ℝ)) ≤ firstBound δ q := by
  apply le_trans (Finset.sum_le_sum (fun r hr => ?_)) (selected_first_le δ hδ q)
  exact div_le_div_of_nonneg_right
    (distortion_small_primes δ hδ _ (selected_even hq hr).1 (selected_even hq hr).2)
    (Nat.cast_nonneg _)

lemma selected_second_weighted (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (q : ℕ) (hq : q ≠ 2) :
    (∑ r ∈ selected q, ∑ s ∈ selected q, ((1 - δ 2)⁻¹ *
      (if 3 ∣ Nat.lcm r.2.2 s.2.2 then (1 - δ 3)⁻¹ else 1) *
      (if 5 ∣ Nat.lcm r.2.2 s.2.2 then (1 - δ 5)⁻¹ else 1)) *
      (Nat.gcd r.2.2 s.2.2 : ℝ) / ((r.1 : ℝ) * (s.1 : ℝ))) ≤ secondBound δ q := by
  apply le_trans (Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s hs => ?_)))
    (selected_second_le δ hδ q)
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply distortion_small_primes δ hδ
  · exact Nat.lcm_ne_zero (selected_even hq hr).1 (selected_even hq hs).1
  · exact dvd_trans (selected_even hq hr).2 (Nat.dvd_lcm_left _ _)

end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate

namespace Submissions.E273SieveMomentBarrier.CompactBarrier.Grouping

def mask (m : ℕ) : ℕ := (if 3 ∣ m then 1 else 0) + (if 5 ∣ m then 2 else 0)
def coefficient {α : Type*} (l : List α) (m : α → ℕ) (c : α → ℚ) (k : ℕ) : ℚ :=
  ((l.filter (fun r => mask (m r) == k)).map c).sum

lemma weighted_grouping {α : Type*} (l : List α) (m : α → ℕ) (c : α → ℚ) (u v : ℝ) :
    (l.map (fun r => (c r : ℝ) * (if 3 ∣ m r then u else 1) *
      (if 5 ∣ m r then v else 1))).sum =
    (coefficient l m c 0 : ℝ) + (coefficient l m c 1 : ℝ)*u +
      (coefficient l m c 2 : ℝ)*v + (coefficient l m c 3 : ℝ)*u*v := by
  induction l with
  | nil => simp [coefficient]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    by_cases h3 : 3 ∣ m a <;> by_cases h5 : 5 ∣ m a
    all_goals simp [coefficient, List.filter_cons, mask, h3, h5]
    all_goals ring
end Submissions.E273SieveMomentBarrier.CompactBarrier.Grouping

namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open scoped BigOperators
lemma first_polynomial_identity (q : ℕ) (w u v : ℝ) :
    (∑ r ∈ selected q, (w * (if 3 ∣ r.2.2 then u else 1) *
      (if 5 ∣ r.2.2 then v else 1)) / (r.1 : ℝ)) =
    w * ((firstCoefficient q 0 : ℝ) + (firstCoefficient q 1 : ℝ)*u +
      (firstCoefficient q 2 : ℝ)*v + (firstCoefficient q 3 : ℝ)*u*v) := by
  rw [selected_sum_eq_list]
  have h := Submissions.E273SieveMomentBarrier.CompactBarrier.Grouping.weighted_grouping (group q) (fun r => r.2.2)
    (fun r => (1 : ℚ) / r.1) u v
  have h' : ((group q).map (fun r => (((1 : ℚ) / r.1 : ℚ) : ℝ) *
      (if 3 ∣ r.2.2 then u else 1) * (if 5 ∣ r.2.2 then v else 1))).sum =
      (firstCoefficient q 0 : ℝ) + (firstCoefficient q 1 : ℝ)*u +
      (firstCoefficient q 2 : ℝ)*v + (firstCoefficient q 3 : ℝ)*u*v := h
  rw [← h', ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  push_cast
  ring
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate

namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
lemma polynomial_mono (a b : ℕ → ℝ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h0 : a 0 ≤ b 0) (h1 : a 1 ≤ b 1) (h2 : a 2 ≤ b 2) (h3 : a 3 ≤ b 3) :
    a 0 + a 1*u + a 2*v + a 3*u*v ≤ b 0 + b 1*u + b 2*v + b 3*u*v := by
  exact add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)

lemma first_polynomial_3 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (389 + 0*u + 0*v + 0*u*v) / 1000 ≤
      (firstCoefficient 3 0 : ℝ) + (firstCoefficient 3 1 : ℝ)*u +
      (firstCoefficient 3 2 : ℝ)*v + (firstCoefficient 3 3 : ℝ)*u*v := by
  have h0 : (389 : ℝ)/1000 ≤ (firstCoefficient 3 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_3_0
    norm_num at hh ⊢
    exact hh
  have h1 : (0 : ℝ)/1000 ≤ (firstCoefficient 3 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_3_1
    norm_num at hh ⊢
    exact hh
  have h2 : (0 : ℝ)/1000 ≤ (firstCoefficient 3 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_3_2
    norm_num at hh ⊢
    exact hh
  have h3 : (0 : ℝ)/1000 ≤ (firstCoefficient 3 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_3_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring

lemma second_polynomial_3 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (373 + 0*u + 0*v + 0*u*v) / 1000 ≤
      (secondCoefficient 3 0 : ℝ) + (secondCoefficient 3 1 : ℝ)*u +
      (secondCoefficient 3 2 : ℝ)*v + (secondCoefficient 3 3 : ℝ)*u*v := by
  have h0 : (373 : ℝ)/1000 ≤ (secondCoefficient 3 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_3_0
    norm_num at hh ⊢
    exact hh
  have h1 : (0 : ℝ)/1000 ≤ (secondCoefficient 3 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_3_1
    norm_num at hh ⊢
    exact hh
  have h2 : (0 : ℝ)/1000 ≤ (secondCoefficient 3 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_3_2
    norm_num at hh ⊢
    exact hh
  have h3 : (0 : ℝ)/1000 ≤ (secondCoefficient 3 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_3_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring

lemma first_polynomial_5 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (143 + 80*u + 0*v + 0*u*v) / 1000 ≤
      (firstCoefficient 5 0 : ℝ) + (firstCoefficient 5 1 : ℝ)*u +
      (firstCoefficient 5 2 : ℝ)*v + (firstCoefficient 5 3 : ℝ)*u*v := by
  have h0 : (143 : ℝ)/1000 ≤ (firstCoefficient 5 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_5_0
    norm_num at hh ⊢
    exact hh
  have h1 : (80 : ℝ)/1000 ≤ (firstCoefficient 5 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_5_1
    norm_num at hh ⊢
    exact hh
  have h2 : (0 : ℝ)/1000 ≤ (firstCoefficient 5 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_5_2
    norm_num at hh ⊢
    exact hh
  have h3 : (0 : ℝ)/1000 ≤ (firstCoefficient 5 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_5_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring

lemma second_polynomial_5 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (48 + 107*u + 0*v + 0*u*v) / 1000 ≤
      (secondCoefficient 5 0 : ℝ) + (secondCoefficient 5 1 : ℝ)*u +
      (secondCoefficient 5 2 : ℝ)*v + (secondCoefficient 5 3 : ℝ)*u*v := by
  have h0 : (48 : ℝ)/1000 ≤ (secondCoefficient 5 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_5_0
    norm_num at hh ⊢
    exact hh
  have h1 : (107 : ℝ)/1000 ≤ (secondCoefficient 5 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_5_1
    norm_num at hh ⊢
    exact hh
  have h2 : (0 : ℝ)/1000 ≤ (secondCoefficient 5 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_5_2
    norm_num at hh ⊢
    exact hh
  have h3 : (0 : ℝ)/1000 ≤ (secondCoefficient 5 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_5_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring

lemma first_polynomial_7 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (53 + 44*u + 21*v + 11*u*v) / 1000 ≤
      (firstCoefficient 7 0 : ℝ) + (firstCoefficient 7 1 : ℝ)*u +
      (firstCoefficient 7 2 : ℝ)*v + (firstCoefficient 7 3 : ℝ)*u*v := by
  have h0 : (53 : ℝ)/1000 ≤ (firstCoefficient 7 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_7_0
    norm_num at hh ⊢
    exact hh
  have h1 : (44 : ℝ)/1000 ≤ (firstCoefficient 7 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_7_1
    norm_num at hh ⊢
    exact hh
  have h2 : (21 : ℝ)/1000 ≤ (firstCoefficient 7 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_7_2
    norm_num at hh ⊢
    exact hh
  have h3 : (11 : ℝ)/1000 ≤ (firstCoefficient 7 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_7_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring

lemma second_polynomial_7 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (13 + 31*u + 12*v + 25*u*v) / 1000 ≤
      (secondCoefficient 7 0 : ℝ) + (secondCoefficient 7 1 : ℝ)*u +
      (secondCoefficient 7 2 : ℝ)*v + (secondCoefficient 7 3 : ℝ)*u*v := by
  have h0 : (13 : ℝ)/1000 ≤ (secondCoefficient 7 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_7_0
    norm_num at hh ⊢
    exact hh
  have h1 : (31 : ℝ)/1000 ≤ (secondCoefficient 7 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_7_1
    norm_num at hh ⊢
    exact hh
  have h2 : (12 : ℝ)/1000 ≤ (secondCoefficient 7 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_7_2
    norm_num at hh ⊢
    exact hh
  have h3 : (25 : ℝ)/1000 ≤ (secondCoefficient 7 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_7_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring

lemma first_polynomial_11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (62 + 29*u + 1*v + 8*u*v) / 1000 ≤
      (firstCoefficient 11 0 : ℝ) + (firstCoefficient 11 1 : ℝ)*u +
      (firstCoefficient 11 2 : ℝ)*v + (firstCoefficient 11 3 : ℝ)*u*v := by
  have h0 : (62 : ℝ)/1000 ≤ (firstCoefficient 11 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_11_0
    norm_num at hh ⊢
    exact hh
  have h1 : (29 : ℝ)/1000 ≤ (firstCoefficient 11 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_11_1
    norm_num at hh ⊢
    exact hh
  have h2 : (1 : ℝ)/1000 ≤ (firstCoefficient 11 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_11_2
    norm_num at hh ⊢
    exact hh
  have h3 : (8 : ℝ)/1000 ≤ (firstCoefficient 11 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr first_11_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring

lemma second_polynomial_11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (10 + 15*u + 0*v + 9*u*v) / 1000 ≤
      (secondCoefficient 11 0 : ℝ) + (secondCoefficient 11 1 : ℝ)*u +
      (secondCoefficient 11 2 : ℝ)*v + (secondCoefficient 11 3 : ℝ)*u*v := by
  have h0 : (10 : ℝ)/1000 ≤ (secondCoefficient 11 0 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_11_0
    norm_num at hh ⊢
    exact hh
  have h1 : (15 : ℝ)/1000 ≤ (secondCoefficient 11 1 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_11_1
    norm_num at hh ⊢
    exact hh
  have h2 : (0 : ℝ)/1000 ≤ (secondCoefficient 11 2 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_11_2
    norm_num at hh ⊢
    exact hh
  have h3 : (9 : ℝ)/1000 ≤ (secondCoefficient 11 3 : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr second_11_3
    norm_num at hh ⊢
    exact hh
  have h := add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_right h1 hu))
    (mul_le_mul_of_nonneg_right h2 hv))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hu) hv)
  convert h using 2 <;> first | rfl | ring
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open Submissions.E273SieveMomentBarrier.CompactBarrier
lemma first_polynomial_lower (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (q : ℕ) (hq : q ≠ 2) :
    (1 - δ 2)⁻¹ * ((firstCoefficient q 0 : ℝ) +
      (firstCoefficient q 1 : ℝ)*(1 - δ 3)⁻¹ +
      (firstCoefficient q 2 : ℝ)*(1 - δ 5)⁻¹ +
      (firstCoefficient q 3 : ℝ)*(1 - δ 3)⁻¹*(1 - δ 5)⁻¹) ≤ firstBound δ q := by
  have h := selected_first_weighted δ hδ q hq
  rw [first_polynomial_identity] at h
  exact h

lemma selected_prime_in_pool {q : ℕ} {r : ℕ × ℕ × ℕ} (hr : r ∈ selected q) :
    q ∈ pool.image largestPrime := by
  have h := Finset.mem_filter.mp (selected_valid hr).1
  exact Finset.mem_image.mpr ⟨r.1, h.1, h.2⟩

lemma compact_primes_in_pool : ({2,3,5,7,11} : Finset ℕ) ⊆ pool.image largestPrime := by
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact selected_prime_in_pool (r := (4,2,1)) (by decide +kernel)
  · exact selected_prime_in_pool (r := (6,3,2)) (by decide +kernel)
  · exact selected_prime_in_pool (r := (10,5,2)) (by decide +kernel)
  · exact selected_prime_in_pool (r := (28,7,4)) (by decide +kernel)
  · exact selected_prime_in_pool (r := (22,11,2)) (by decide +kernel)
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate

namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open scoped BigOperators
lemma second_grouping (q : ℕ) (u v : ℝ) :
 ((group q).flatMap (fun r => (group q).map (fun s =>
   ((Nat.gcd r.2.2 s.2.2 : ℚ) / ((r.1 : ℚ)*s.1) : ℝ) *
   (if 3 ∣ Nat.lcm r.2.2 s.2.2 then u else 1) *
   (if 5 ∣ Nat.lcm r.2.2 s.2.2 then v else 1)))).sum =
 (secondCoefficient q 0 : ℝ) + (secondCoefficient q 1 : ℝ)*u +
 (secondCoefficient q 2 : ℝ)*v + (secondCoefficient q 3 : ℝ)*u*v := by
 have h := Submissions.E273SieveMomentBarrier.CompactBarrier.Grouping.weighted_grouping
   ((group q).flatMap (fun r => (group q).map (fun s => (r,s))))
   (fun p => Nat.lcm p.1.2.2 p.2.2.2)
   (fun p => (Nat.gcd p.1.2.2 p.2.2.2 : ℚ) / ((p.1.1 : ℚ)*p.2.1)) u v
 simpa [Submissions.E273SieveMomentBarrier.CompactBarrier.Grouping.coefficient, Submissions.E273SieveMomentBarrier.CompactBarrier.Grouping.mask, secondCoefficient, mask,
   List.map_flatMap, List.filter_flatMap, List.filter_map, List.map_map, Function.comp_def] using h


lemma flatMap_sum_general {α : Type*} (l : List α) (f : α → List ℝ) :
 (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
 induction l with
 | nil => simp
 | cons a l ih => simp [List.flatMap_cons, ih]

lemma second_weighted_identity (q : ℕ) (w u v : ℝ) :
 ((group q).flatMap (fun r => (group q).map (fun s =>
   (w * (if 3 ∣ Nat.lcm r.2.2 s.2.2 then u else 1) *
   (if 5 ∣ Nat.lcm r.2.2 s.2.2 then v else 1)) *
   (Nat.gcd r.2.2 s.2.2 : ℝ) / ((r.1 : ℝ)*(s.1 : ℝ))))).sum =
 w * ((secondCoefficient q 0 : ℝ) + (secondCoefficient q 1 : ℝ)*u +
 (secondCoefficient q 2 : ℝ)*v + (secondCoefficient q 3 : ℝ)*u*v) := by
 rw [← second_grouping]
 simp only [flatMap_sum_general]
 rw [← List.sum_map_mul_left]
 apply congrArg List.sum
 apply List.map_congr_left
 intro r hr
 rw [← List.sum_map_mul_left]
 apply congrArg List.sum
 apply List.map_congr_left
 intro s hs
 push_cast
 ring

lemma second_selected_identity (q : ℕ) (w u v : ℝ) :
 (∑ r ∈ selected q, ∑ s ∈ selected q,
   (w * (if 3 ∣ Nat.lcm r.2.2 s.2.2 then u else 1) *
   (if 5 ∣ Nat.lcm r.2.2 s.2.2 then v else 1)) *
   (Nat.gcd r.2.2 s.2.2 : ℝ) / ((r.1 : ℝ)*(s.1 : ℝ))) =
 w * ((secondCoefficient q 0 : ℝ) + (secondCoefficient q 1 : ℝ)*u +
 (secondCoefficient q 2 : ℝ)*v + (secondCoefficient q 3 : ℝ)*u*v) := by
 simp_rw [selected_sum_eq_list]
 rw [← flatMap_sum_general]
 exact second_weighted_identity q w u v

end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate

namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open scoped BigOperators
open Submissions.E273SieveMomentBarrier.CompactBarrier
lemma selected_two_exact : selected 2 = {(4,2,1), (16,2,1), (256,2,1)} := by
  decide +kernel
lemma first_binary_bound (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (81 : ℝ)/256 ≤ firstBound δ 2 := by
  have h := selected_first_le δ hδ 2
  rw [selected_two_exact] at h
  norm_num [distortion] at h ⊢
  exact h
lemma second_binary_bound (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    ((81 : ℝ)/256)^2 ≤ secondBound δ 2 := by
  have h := selected_second_le δ hδ 2
  rw [selected_two_exact] at h
  norm_num [distortion] at h ⊢
  exact h
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open Submissions.E273SieveMomentBarrier.CompactBarrier
lemma second_polynomial_lower (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2)
    (q : ℕ) (hq : q ≠ 2) :
    (1 - δ 2)⁻¹ * ((secondCoefficient q 0 : ℝ) +
      (secondCoefficient q 1 : ℝ)*(1 - δ 3)⁻¹ +
      (secondCoefficient q 2 : ℝ)*(1 - δ 5)⁻¹ +
      (secondCoefficient q 3 : ℝ)*(1 - δ 3)⁻¹*(1 - δ 5)⁻¹) ≤ secondBound δ q := by
  have h := selected_second_weighted δ hδ q hq
  rw [second_selected_identity] at h
  exact h

lemma first_actual_3 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((389)/1000) ≤ firstBound δ 3 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (first_polynomial_3 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (first_polynomial_lower δ hδ 3 (by norm_num))
  simpa only [zero_mul, add_zero] using h

lemma second_actual_3 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((373)/1000) ≤ secondBound δ 3 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (second_polynomial_3 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (second_polynomial_lower δ hδ 3 (by norm_num))
  simpa only [zero_mul, add_zero] using h

lemma first_actual_5 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((143 + 80*(1-δ 3)⁻¹)/1000) ≤ firstBound δ 5 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (first_polynomial_5 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (first_polynomial_lower δ hδ 5 (by norm_num))
  simpa only [zero_mul, add_zero] using h

lemma second_actual_5 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((48 + 107*(1-δ 3)⁻¹)/1000) ≤ secondBound δ 5 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (second_polynomial_5 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (second_polynomial_lower δ hδ 5 (by norm_num))
  simpa only [zero_mul, add_zero] using h

lemma first_actual_7 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((53 + 44*(1-δ 3)⁻¹ + 21*(1-δ 5)⁻¹ + 11*(1-δ 3)⁻¹*(1-δ 5)⁻¹)/1000) ≤ firstBound δ 7 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (first_polynomial_7 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (first_polynomial_lower δ hδ 7 (by norm_num))
  simpa only [zero_mul, add_zero] using h

lemma second_actual_7 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((13 + 31*(1-δ 3)⁻¹ + 12*(1-δ 5)⁻¹ + 25*(1-δ 3)⁻¹*(1-δ 5)⁻¹)/1000) ≤ secondBound δ 7 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (second_polynomial_7 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (second_polynomial_lower δ hδ 7 (by norm_num))
  simpa only [zero_mul, add_zero] using h

lemma first_actual_11 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((62 + 29*(1-δ 3)⁻¹ + 1*(1-δ 5)⁻¹ + 8*(1-δ 3)⁻¹*(1-δ 5)⁻¹)/1000) ≤ firstBound δ 11 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (first_polynomial_11 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (first_polynomial_lower δ hδ 11 (by norm_num))
  simpa only [zero_mul, add_zero] using h

lemma second_actual_11 (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    (1-δ 2)⁻¹ * ((10 + 15*(1-δ 3)⁻¹ + 9*(1-δ 3)⁻¹*(1-δ 5)⁻¹)/1000) ≤ secondBound δ 11 := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have h := (mul_le_mul_of_nonneg_left
    (second_polynomial_11 (1-δ 3)⁻¹ (1-δ 5)⁻¹ (hw 3) (hw 5)) (hw 2)).trans
    (second_polynomial_lower δ hδ 11 (by norm_num))
  simpa only [zero_mul, add_zero] using h
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate


namespace Submissions.E273SieveMomentBarrier.CompactBarrier.Research

/-- Eliminate the distortion parameter at 2 when every later cofactor is even. -/
theorem eliminate_binary_parameter (a f x : ℝ)
    (_ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hf : 1 - a < f) :
    1 < (if x = 0 then a else min a (a ^ 2 / (4 * x * (1 - x)))) +
      f / (1 - x) := by
  have ht : 0 < 1 - x := by linarith
  have hf0 : 0 < f := by linarith
  by_cases hz : x = 0
  · subst x
    simp only [ite_true, sub_zero, div_one]
    linarith
  · rw [if_neg hz]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have hfirst : 1 < a + f / (1 - x) := by
      have hprod : 0 ≤ x * (1 - a) := mul_nonneg hx (by linarith)
      have hdiv : 1 - a < f / (1 - x) := (lt_div_iff₀ ht).2 (by nlinarith)
      linarith
    have hsecond : 1 < a ^ 2 / (4 * x * (1 - x)) + f / (1 - x) := by
      have hsquare : 0 ≤ (a - 2 * x) ^ 2 := sq_nonneg _
      have hstrict : 0 < 4 * x * (f - (1 - a)) := by positivity
      have hd : 0 < 4 * x * (1 - x) := by positivity
      have hnum : 4 * x * (1 - x) < a ^ 2 + 4 * x * f := by nlinarith
      have hh : 1 < (a ^ 2 + 4 * x * f) / (4 * x * (1 - x)) :=
        (lt_div_iff₀ hd).2 (by nlinarith)
      convert hh using 1 <;> field_simp
    rcases le_total a (a ^ 2 / (4 * x * (1 - x))) with h | h
    · simpa [min_eq_left h] using hfirst
    · simpa [min_eq_right h] using hsecond

/-- Uniform bound for the remaining prime-5 distortion contribution. -/
theorem fifth_parameter_bound (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    (23 : ℝ) / 100 <
      (if z = 0 then (223 : ℝ) / 1000
       else min ((223 : ℝ) / 1000) ((155 : ℝ) / 1000 / (4 * z * (1 - z)))) +
        ((46 : ℝ) / 1000) / (1 - z) := by
  have ht : 0 < 1 - z := by linarith
  by_cases hzero : z = 0
  · subst z
    norm_num
  · rw [if_neg hzero]
    have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzero)
    have hd : 0 < 4 * z * (1 - z) := by positivity
    have hfirst : (23 : ℝ) / 100 < (223 : ℝ) / 1000 + ((46 : ℝ) / 1000) / (1 - z) := by
      have hb : (46 : ℝ) / 1000 ≤ ((46 : ℝ) / 1000) / (1 - z) :=
        (le_div_iff₀ ht).2 (by nlinarith)
      linarith
    have hsecond : (23 : ℝ) / 100 < (155 : ℝ) / 1000 / (4 * z * (1 - z)) +
        ((46 : ℝ) / 1000) / (1 - z) := by
      have hp : (23 : ℝ) / 100 * (4 * z * (1 - z)) <
          (155 : ℝ) / 1000 + 4 * z * ((46 : ℝ) / 1000) := by
        nlinarith [sq_nonneg (z - (2 : ℝ) / 5)]
      have hh : (23 : ℝ) / 100 <
          ((155 : ℝ) / 1000 + 4 * z * ((46 : ℝ) / 1000)) / (4 * z * (1 - z)) :=
        (lt_div_iff₀ hd).2 hp
      convert hh using 1 <;> field_simp
    rcases le_total ((223 : ℝ) / 1000) ((155 : ℝ) / 1000 / (4 * z * (1 - z))) with h | h
    · simpa [min_eq_left h] using hfirst
    · simpa [min_eq_right h] using hsecond

noncomputable def stepBound (t a b : ℝ) : ℝ :=
  if t = 0 then a else min a (b / (4 * t * (1 - t)))

theorem stepBound_mono {t a b a' b' : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (ha : a ≤ a') (hb : b ≤ b') : stepBound t a b ≤ stepBound t a' b' := by
  unfold stepBound
  split_ifs with h
  · exact ha
  · apply min_le_min ha
    exact div_le_div_of_nonneg_right hb (by nlinarith)

theorem stepBound_lower {t a b c : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hc : 0 ≤ c) (ha : c ≤ a) (hb : c ≤ b) : c ≤ stepBound t a b := by
  unfold stepBound
  split_ifs with h
  · exact ha
  · have hp : 0 < 4 * t * (1 - t) := by
      have : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
      have htp : 0 < 1 - t := by linarith
      positivity
    apply le_min ha
    apply (le_div_iff₀ hp).2
    have hd : 4 * t * (1 - t) ≤ 1 := by nlinarith [sq_nonneg (2 * t - 1)]
    nlinarith

noncomputable def compactTail (y z : ℝ) : ℝ :=
  let u := 1 / (1 - y)
  let v := 1 / (1 - z)
  stepBound y (389 / 1000) (373 / 1000) +
  stepBound z ((143 + 80 * u) / 1000) ((48 + 107 * u) / 1000) +
  min ((53 + 44 * u + 21 * v + 11 * u * v) / 1000)
      ((13 + 31 * u + 12 * v + 25 * u * v) / 1000) +
  min ((62 + 29 * u + v + 8 * u * v) / 1000)
      ((10 + 15 * u + 9 * u * v) / 1000)

theorem compactTail_gt (y z : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hz : 0 ≤ z) (hz1 : z ≤ 1 / 2) : 1 - (81 : ℝ) / 256 < compactTail y z := by
  let u := 1 / (1 - y)
  let v := 1 / (1 - z)
  have hyp : 0 < 1 - y := by linarith
  have hzp : 0 < 1 - z := by linarith
  have hu : 1 ≤ u := (le_div_iff₀ hyp).2 (by linarith)
  have hv : 1 ≤ v := (le_div_iff₀ hzp).2 (by linarith)
  have hv2 : v ≤ 2 := (div_le_iff₀ hzp).2 (by linarith)
  have huv : v ≤ u * v := by nlinarith [mul_nonneg (show 0 ≤ u - 1 by linarith) (show 0 ≤ v by linarith)]
  change 1 - (81 : ℝ) / 256 <
    stepBound y (389 / 1000) (373 / 1000) +
    stepBound z ((143 + 80 * u) / 1000) ((48 + 107 * u) / 1000) +
    min ((53 + 44 * u + 21 * v + 11 * u * v) / 1000)
        ((13 + 31 * u + 12 * v + 25 * u * v) / 1000) +
    min ((62 + 29 * u + v + 8 * u * v) / 1000)
        ((10 + 15 * u + 9 * u * v) / 1000)
  by_cases hsmall : y ≤ 1 / 5
  · have h3 : (389 : ℝ) / 1000 ≤ stepBound y (389 / 1000) (373 / 1000) := by
      unfold stepBound
      split_ifs with hzero
      · exact le_rfl
      · have hp : 0 < 4 * y * (1 - y) := by
          have : 0 < y := lt_of_le_of_ne hy (Ne.symm hzero)
          positivity
        apply le_min le_rfl
        apply (le_div_iff₀ hp).2
        have hd : 4 * y * (1 - y) ≤ 16 / 25 := by nlinarith
        nlinarith
    have h5 := stepBound_mono hz hz1
      (show (223 : ℝ) / 1000 ≤ (143 + 80 * u) / 1000 by linarith)
      (show (155 : ℝ) / 1000 ≤ (48 + 107 * u) / 1000 by linarith)
    have h7 : (44 + 37 * v) / 1000 ≤
        min ((53 + 44 * u + 21 * v + 11 * u * v) / 1000)
          ((13 + 31 * u + 12 * v + 25 * u * v) / 1000) := by
      apply le_min <;> nlinarith
    have h11 : (25 + 9 * v) / 1000 ≤
        min ((62 + 29 * u + v + 8 * u * v) / 1000)
          ((10 + 15 * u + 9 * u * v) / 1000) := by
      apply le_min <;> nlinarith
    have hf := fifth_parameter_bound z hz hz1
    change (23 : ℝ) / 100 < stepBound z (223 / 1000) (155 / 1000) + (46 / 1000) / (1 - z) at hf
    have heq : ((46 : ℝ) / 1000) / (1 - z) = 46 * v / 1000 := by dsimp [v]; ring
    rw [heq] at hf
    linarith
  · have huy : (5 : ℝ) / 4 ≤ u := (le_div_iff₀ hyp).2 (by linarith)
    have huv5 : (5 : ℝ) / 4 ≤ u * v := by nlinarith [mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ v - 1 by linarith)]
    have h3 := stepBound_lower hy hy1
      (show (0 : ℝ) ≤ 373 / 1000 by norm_num)
      (show (373 : ℝ) / 1000 ≤ 389 / 1000 by norm_num) (le_refl ((373 : ℝ) / 1000))
    have h5 := stepBound_lower hz hz1
      (show (0 : ℝ) ≤ 727 / 4000 by norm_num)
      (show (727 : ℝ) / 4000 ≤ (143 + 80 * u) / 1000 by linarith)
      (show (727 : ℝ) / 4000 ≤ (48 + 107 * u) / 1000 by linarith)
    have h7 : (95 : ℝ) / 1000 ≤
        min ((53 + 44 * u + 21 * v + 11 * u * v) / 1000)
          ((13 + 31 * u + 12 * v + 25 * u * v) / 1000) := by
      apply le_min <;> nlinarith
    have h11 : (40 : ℝ) / 1000 ≤
        min ((62 + 29 * u + v + 8 * u * v) / 1000)
          ((10 + 15 * u + 9 * u * v) / 1000) := by
      apply le_min <;> nlinarith
    linarith

end Submissions.E273SieveMomentBarrier.CompactBarrier.Research
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open Submissions.E273SieveMomentBarrier.CompactBarrier Submissions.E273SieveMomentBarrier.CompactBarrier.Research
lemma criterion_five_lower (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    stepBound (δ 2) (firstBound δ 2) (secondBound δ 2) +
    stepBound (δ 3) (firstBound δ 3) (secondBound δ 3) +
    stepBound (δ 5) (firstBound δ 5) (secondBound δ 5) +
    stepBound (δ 7) (firstBound δ 7) (secondBound δ 7) +
    stepBound (δ 11) (firstBound δ 11) (secondBound δ 11) ≤ criterion δ := by
  have h := criterion_lower_bound δ hδ _ compact_primes_in_pool (firstBound δ) (secondBound δ)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa [stepBound, add_assoc] using h
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate

namespace Submissions.E273SieveMomentBarrier.CompactBarrier.Research
lemma stepBound_mul (t w a b : ℝ) (hw : 0 ≤ w) :
 stepBound t (w*a) (w*b) = w * stepBound t a b := by
 unfold stepBound
 split_ifs
 · rfl
 · rw [mul_div_assoc, mul_min_of_nonneg _ _ hw]

lemma min_le_stepBound {t a b : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/2)
 (ha : 0 ≤ a) (hb : 0 ≤ b) : min a b ≤ stepBound t a b := by
 exact stepBound_lower ht ht1 (le_min ha hb) (min_le_left _ _) (min_le_right _ _)

theorem compact_assembly (x y z C : ℝ)
 (hx : 0 ≤ x) (hx1 : x ≤ 1/2) (hy : 0 ≤ y) (hy1 : y ≤ 1/2)
 (hz : 0 ≤ z) (hz1 : z ≤ 1/2)
 (hC : stepBound x (81/256) ((81/256)^2) + (1-x)⁻¹ * compactTail y z ≤ C) :
 1 < C := by
 have h := eliminate_binary_parameter (81/256) (compactTail y z) x
   (by norm_num) (by norm_num) hx hx1 (compactTail_gt y z hy hy1 hz hz1)
 apply lt_of_lt_of_le _ hC
 simpa only [stepBound, div_eq_mul_inv, mul_comm] using h

theorem five_term_assembly (x y z C T2 T3 T5 T7 T11 : ℝ)
 (hx : 0 ≤ x) (hx1 : x ≤ 1/2) (hy : 0 ≤ y) (hy1 : y ≤ 1/2)
 (hz : 0 ≤ z) (hz1 : z ≤ 1/2)
 (h2 : stepBound x (81/256) ((81/256)^2) ≤ T2)
 (h3 : (1-x)⁻¹ * stepBound y (389/1000) (373/1000) ≤ T3)
 (h5 : (1-x)⁻¹ * stepBound z ((143+80/(1-y))/1000) ((48+107/(1-y))/1000) ≤ T5)
 (h7 : (1-x)⁻¹ * min ((53+44/(1-y)+21/(1-z)+11/(1-y)/(1-z))/1000)
   ((13+31/(1-y)+12/(1-z)+25/(1-y)/(1-z))/1000) ≤ T7)
 (h11 : (1-x)⁻¹ * min ((62+29/(1-y)+1/(1-z)+8/(1-y)/(1-z))/1000)
   ((10+15/(1-y)+9/(1-y)/(1-z))/1000) ≤ T11)
 (hC : T2+T3+T5+T7+T11 ≤ C) : 1 < C := by
 apply compact_assembly x y z C hx hx1 hy hy1 hz hz1
 have hsum := add_le_add (add_le_add (add_le_add (add_le_add h2 h3) h5) h7) h11
 apply le_trans _ hC
 convert hsum using 1 <;> simp only [compactTail, mul_add, div_eq_mul_inv, mul_assoc, one_mul, add_assoc]

end Submissions.E273SieveMomentBarrier.CompactBarrier.Research
namespace Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
open Submissions.E273SieveMomentBarrier.CompactBarrier Submissions.E273SieveMomentBarrier.CompactBarrier.Research
lemma weighted_step_from_bounds (t w a b A B : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1/2)
    (hw : 0 ≤ w) (ha : w*a ≤ A) (hb : w*b ≤ B) :
    w * stepBound t a b ≤ stepBound t A B := by
  rw [← stepBound_mul t w a b hw]
  exact stepBound_mono ht ht1 ha hb
lemma weighted_min_from_bounds (t w a b A B : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1/2)
    (hw : 0 ≤ w) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : w*a ≤ A) (hb : w*b ≤ B) :
    w * min a b ≤ stepBound t A B := by
  exact (mul_le_mul_of_nonneg_left (min_le_stepBound ht ht1 ha0 hb0) hw).trans
    (weighted_step_from_bounds t w a b A B ht ht1 hw ha hb)

 theorem full_criterion_gt (δ : ℕ → ℝ) (hδ : ∀ q, 0 ≤ δ q ∧ δ q ≤ 1/2) :
    1 < criterion δ := by
  have hw (p : ℕ) : 0 ≤ (1-δ p)⁻¹ := le_trans zero_le_one (weight_one_le δ hδ p)
  have hp (p : ℕ) : 0 < 1-δ p := by linarith [(hδ p).2]
  have hpos3 := hp 3
  have hpos5 := hp 5
  refine five_term_assembly (δ 2) (δ 3) (δ 5) (criterion δ) _ _ _ _ _
    (hδ 2).1 (hδ 2).2 (hδ 3).1 (hδ 3).2 (hδ 5).1 (hδ 5).2
    ?_ ?_ ?_ ?_ ?_ (criterion_five_lower δ hδ)
  · exact stepBound_mono (hδ 2).1 (hδ 2).2 (first_binary_bound δ hδ) (second_binary_bound δ hδ)
  · exact weighted_step_from_bounds _ _ _ _ _ _ (hδ 3).1 (hδ 3).2 (hw 2)
      (first_actual_3 δ hδ) (second_actual_3 δ hδ)
  · apply weighted_step_from_bounds _ _ _ _ _ _ (hδ 5).1 (hδ 5).2 (hw 2)
    · simpa only [div_eq_mul_inv] using first_actual_5 δ hδ
    · simpa only [div_eq_mul_inv] using second_actual_5 δ hδ
  · apply weighted_min_from_bounds _ _ _ _ _ _ (hδ 7).1 (hδ 7).2 (hw 2)
    · positivity
    · positivity
    · simpa only [div_eq_mul_inv] using first_actual_7 δ hδ
    · simpa only [div_eq_mul_inv] using second_actual_7 δ hδ
  · apply weighted_min_from_bounds _ _ _ _ _ _ (hδ 11).1 (hδ 11).2 (hw 2)
    · positivity
    · positivity
    · simpa only [div_eq_mul_inv, one_mul] using first_actual_11 δ hδ
    · simpa only [div_eq_mul_inv, one_mul] using second_actual_11 δ hδ
end Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate
namespace Submissions.E273SieveMomentBarrier.CompactBarrier
theorem target : statement := Submissions.E273SieveMomentBarrier.CompactBarrier.FiniteCertificate.full_criterion_gt
end Submissions.E273SieveMomentBarrier.CompactBarrier

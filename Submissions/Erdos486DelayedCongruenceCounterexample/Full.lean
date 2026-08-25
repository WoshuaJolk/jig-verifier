import Mathlib


/-! Flattened from Erdos486.Skeleton. -/

/-!
# The arithmetic skeleton for Erdős Problem 486

This file formalizes the elementary number-theoretic construction in the
arithmetic-skeleton lemma of the proposed solution.  Rational inequalities
are stated after cross multiplication, so every quantitative assertion lives
in `ℕ`.
-/

open scoped BigOperators

namespace Erdos486

/-- The even parameter `k = 2 * floor (sqrt j / 8)` from the paper. -/
def skeletonK (j : ℕ) : ℕ :=
  2 * (Nat.sqrt j / 8)

/-- The paper's central family, written without integer subtraction:
`|S.card - k / 2| ≤ sqrt k`. -/
def SkeletonCentralFamily (k : ℕ) :=
  {S : Finset (Fin k) //
    k / 2 ≤ S.card + Nat.sqrt k ∧ S.card ≤ k / 2 + Nat.sqrt k}

/-- Membership in the integer interval `[11Q/10, 19Q/10]`, with both
inequalities cross multiplied. -/
def InSkeletonInterval (Q m : ℕ) : Prop :=
  11 * Q ≤ 10 * m ∧ 10 * m ≤ 19 * Q

/-- A prime selected from the Bertrand interval belonging to `i`. -/
noncomputable def skeletonPrime (k : ℕ) (i : Fin k) : ℕ :=
  Classical.choose
    (Nat.exists_prime_lt_and_le_two_mul (4 ^ (k + i.val + 1)) (by positivity))

theorem skeletonPrime_spec (k : ℕ) (i : Fin k) :
    (skeletonPrime k i).Prime ∧
      4 ^ (k + i.val + 1) < skeletonPrime k i ∧
      skeletonPrime k i ≤ 2 * 4 ^ (k + i.val + 1) := by
  exact Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul (4 ^ (k + i.val + 1)) (by positivity))

theorem skeletonPrime_lt_two_mul (k : ℕ) (i : Fin k) :
    skeletonPrime k i < 2 * 4 ^ (k + i.val + 1) := by
  let n := 4 ^ (k + i.val + 1)
  have hnFour : 4 ≤ n := by
    have hexp : 1 ≤ k + i.val + 1 := by omega
    simpa [n] using Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) hexp
  have hpPrime : (skeletonPrime k i).Prime := (skeletonPrime_spec k i).1
  have hnlt : n < skeletonPrime k i := (skeletonPrime_spec k i).2.1
  have hple : skeletonPrime k i ≤ 2 * n := (skeletonPrime_spec k i).2.2
  apply lt_of_le_of_ne hple
  intro hEq
  have hnDvd : n ∣ skeletonPrime k i := by
    refine ⟨2, ?_⟩
    omega
  rcases (Nat.dvd_prime hpPrime).mp hnDvd with hnOne | hnEq
  · omega
  · omega

theorem skeletonPrime_strictMono (k : ℕ) : StrictMono (skeletonPrime k) := by
  intro i i' hii'
  have hi := (skeletonPrime_spec k i).2.2
  have hi' := (skeletonPrime_spec k i').2.1
  have hexp : k + i.val + 1 + 1 ≤ k + i'.val + 1 := by
    omega
  have hpow : 2 * 4 ^ (k + i.val + 1) < 4 ^ (k + i.val + 1 + 1) := by
    calc
      2 * 4 ^ (k + i.val + 1) < 4 ^ (k + i.val + 1) * 4 := by
        nlinarith [show 0 < 4 ^ (k + i.val + 1) by positivity]
      _ = 4 ^ (k + i.val + 1 + 1) := (pow_succ _ _).symm
  have hmono : 4 ^ (k + i.val + 1 + 1) ≤ 4 ^ (k + i'.val + 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  exact hi.trans_lt (hpow.trans_le hmono |>.trans hi')

theorem skeletonPrime_injective (k : ℕ) : Function.Injective (skeletonPrime k) :=
  (skeletonPrime_strictMono k).injective

/-- The exact exponent sum used in the paper's product estimate. -/
theorem skeleton_exponent_sum (k : ℕ) :
    (∑ i : Fin k, (2 * (k + i.val + 1) + 1)) = 3 * k ^ 2 + 2 * k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ 2 * (k + 1 + i + 1) + 1)]
      simp_rw [show ∀ i : ℕ,
        2 * (k + 1 + i + 1) + 1 = (2 * (k + 1) + 3) + 2 * i by omega]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsum := Finset.sum_range_id_mul_two (k + 1)
      simp only [Nat.add_sub_cancel] at hsum
      nlinarith

/-- The product `P` of the selected Bertrand primes. -/
noncomputable def skeletonProduct (k : ℕ) : ℕ :=
  ∏ i : Fin k, skeletonPrime k i

theorem skeletonPrime_le_twoPow (k : ℕ) (i : Fin k) :
    skeletonPrime k i ≤ 2 ^ (2 * (k + i.val + 1) + 1) := by
  calc
    skeletonPrime k i ≤ 2 * 4 ^ (k + i.val + 1) := (skeletonPrime_spec k i).2.2
    _ = 2 ^ (2 * (k + i.val + 1) + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, pow_add]
      simp [mul_comm]

/-- The paper's exact product estimate `P ≤ 2^(3k²+2k)`. -/
theorem skeletonProduct_le (k : ℕ) :
    skeletonProduct k ≤ 2 ^ (3 * k ^ 2 + 2 * k) := by
  have hprod :
      skeletonProduct k ≤ ∏ i : Fin k, 2 ^ (2 * (k + i.val + 1) + 1) := by
    unfold skeletonProduct
    exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      fun i _ ↦ skeletonPrime_le_twoPow k i
  have hpow :
      (∏ i : Fin k, 2 ^ (2 * (k + i.val + 1) + 1)) =
        2 ^ (∑ i : Fin k, (2 * (k + i.val + 1) + 1)) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin k))
        (fun i : Fin k ↦ 2 * (k + i.val + 1) + 1) 2)
  rw [hpow, skeleton_exponent_sum] at hprod
  exact hprod

/-- The squared version `P² ≤ 2^(6k²+4k)` of the paper's product estimate. -/
theorem skeletonProduct_sq_le (k : ℕ) :
    skeletonProduct k ^ 2 ≤ 2 ^ (6 * k ^ 2 + 4 * k) := by
  have h := Nat.pow_le_pow_left (skeletonProduct_le k) 2
  calc
    skeletonProduct k ^ 2 ≤ (2 ^ (3 * k ^ 2 + 2 * k)) ^ 2 := h
    _ = 2 ^ (6 * k ^ 2 + 4 * k) := by
      rw [← pow_mul]
      congr 2
      omega

theorem skeletonK_even (j : ℕ) : Even (skeletonK j) := by
  exact ⟨Nat.sqrt j / 8, by simp [skeletonK, two_mul]⟩

theorem four_mul_skeletonK_le_sqrt (j : ℕ) :
    4 * skeletonK j ≤ Nat.sqrt j := by
  have h := Nat.div_mul_le_self (Nat.sqrt j) 8
  calc
    4 * skeletonK j = (Nat.sqrt j / 8) * 8 := by
      simp only [skeletonK]
      ring
    _ ≤ Nat.sqrt j := h

theorem skeletonK_ge_two {j : ℕ} (hj : 64 ≤ j) : 2 ≤ skeletonK j := by
  have hsqrt : 8 ≤ Nat.sqrt j := by
    have hsqrt64 : Nat.sqrt 64 = 8 := by norm_num
    rw [← hsqrt64]
    exact Nat.sqrt_le_sqrt hj
  have hdiv : 1 ≤ Nat.sqrt j / 8 := (Nat.le_div_iff_mul_le (by norm_num)).2 hsqrt
  simp only [skeletonK]
  omega

/-- For the explicit cutoff `j ≥ 64`, the exponent in the squared product
bound, plus the five bits needed to dominate the factor `20`, is at most
`j`. -/
theorem skeleton_exponent_sq_add_five_le {j : ℕ} (hj : 64 ≤ j) :
    6 * skeletonK j ^ 2 + 4 * skeletonK j + 5 ≤ j := by
  let k := skeletonK j
  have hk : 2 ≤ k := skeletonK_ge_two hj
  have hfour : 4 * k ≤ Nat.sqrt j := four_mul_skeletonK_le_sqrt j
  have hsqrt := Nat.sqrt_le j
  dsimp only [k] at hk hfour ⊢
  nlinarith

/-- The quantitative smallness needed by the construction, entirely in
cross-multiplied natural-number form: `20 P² ≤ Q`. -/
theorem twenty_mul_skeletonProduct_sq_le (j : ℕ) (hj : 64 ≤ j) :
    20 * skeletonProduct (skeletonK j) ^ 2 ≤ 2 ^ j := by
  let k := skeletonK j
  have hP : skeletonProduct k ^ 2 ≤ 2 ^ (6 * k ^ 2 + 4 * k) :=
    skeletonProduct_sq_le k
  have hexp : 6 * k ^ 2 + 4 * k + 5 ≤ j := by
    simpa [k] using skeleton_exponent_sq_add_five_le hj
  calc
    20 * skeletonProduct k ^ 2 ≤ 2 ^ 5 * 2 ^ (6 * k ^ 2 + 4 * k) :=
      Nat.mul_le_mul (by norm_num) hP
    _ = 2 ^ (6 * k ^ 2 + 4 * k + 5) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hexp

/-- A positive representative in the progression `d * (1 + Pℤ)`.  This is
the floor-based analogue of the paper's closest representative. -/
def progressionApprox (Q P d : ℕ) : ℕ :=
  d * (1 + P * (Q / (d * P)))

theorem progressionApprox_pos {Q P d : ℕ} (hd : 0 < d) :
    0 < progressionApprox Q P d := by
  simp only [progressionApprox]
  positivity

theorem progressionApprox_le_add_sq {Q P d : ℕ} (hP : 0 < P) (hdP : d ≤ P) :
    progressionApprox Q P d ≤ Q + P ^ 2 := by
  have hdiv := Nat.div_mul_le_self Q (d * P)
  have hPsq : P ≤ P ^ 2 := by
    nlinarith
  calc
    progressionApprox Q P d = d + (Q / (d * P)) * (d * P) := by
      simp only [progressionApprox]
      ring
    _ ≤ d + Q := Nat.add_le_add_left hdiv d
    _ ≤ Q + P ^ 2 := by omega

theorem le_progressionApprox_add_sq {Q P d : ℕ}
    (hP : 0 < P) (hd : 0 < d) (hdP : d ≤ P) :
    Q ≤ progressionApprox Q P d + P ^ 2 := by
  have hden : 0 < d * P := Nat.mul_pos hd hP
  have hdiv : Q < d * P * (Q / (d * P) + 1) := Nat.lt_mul_div_succ Q hden
  have hdp : d * P ≤ P ^ 2 := by
    nlinarith
  rw [progressionApprox]
  nlinarith

/-- If `20P² ≤ Q`, the floor-based progression representative lies in the
paper's window `[19Q/20, 21Q/20]`, stated by cross multiplication. -/
theorem progressionApprox_bounds {Q P d : ℕ}
    (hP : 0 < P) (hd : 0 < d) (hdP : d ≤ P) (hsmall : 20 * P ^ 2 ≤ Q) :
    19 * Q ≤ 20 * progressionApprox Q P d ∧
      20 * progressionApprox Q P d ≤ 21 * Q := by
  have hlower := le_progressionApprox_add_sq (Q := Q) hP hd hdP
  have hupper := progressionApprox_le_add_sq (Q := Q) hP hdP
  constructor <;> nlinarith

/-- The product `d_S` of the selected primes indexed by `S`. -/
noncomputable def skeletonSubsetProduct (k : ℕ) (S : Finset (Fin k)) : ℕ :=
  ∏ i ∈ S, skeletonPrime k i

theorem skeletonSubsetProduct_pos (k : ℕ) (S : Finset (Fin k)) :
    0 < skeletonSubsetProduct k S := by
  unfold skeletonSubsetProduct
  exact Finset.prod_pos fun i _ ↦ (skeletonPrime_spec k i).1.pos

theorem skeletonSubsetProduct_dvd_product (k : ℕ) (S : Finset (Fin k)) :
    skeletonSubsetProduct k S ∣ skeletonProduct k := by
  simpa [skeletonSubsetProduct, skeletonProduct] using
    (Finset.prod_dvd_prod_of_subset S (Finset.univ : Finset (Fin k))
      (skeletonPrime k) S.subset_univ)

theorem skeletonSubsetProduct_le_product (k : ℕ) (S : Finset (Fin k)) :
    skeletonSubsetProduct k S ≤ skeletonProduct k := by
  exact Nat.le_of_dvd (by
    unfold skeletonProduct
    exact Finset.prod_pos fun i _ ↦ (skeletonPrime_spec k i).1.pos)
    (skeletonSubsetProduct_dvd_product k S)

/-- The modulus attached to a subset.  It is constructed for every subset;
the final theorem restricts it to the paper's central family. -/
noncomputable def skeletonModulus (j : ℕ) (S : Finset (Fin (skeletonK j))) : ℕ :=
  progressionApprox (2 ^ j) (skeletonProduct (skeletonK j))
    (skeletonSubsetProduct (skeletonK j) S)

theorem skeletonProduct_pos (k : ℕ) : 0 < skeletonProduct k := by
  unfold skeletonProduct
  exact Finset.prod_pos fun i _ ↦ (skeletonPrime_spec k i).1.pos

theorem skeletonPrime_dvd_product (k : ℕ) (i : Fin k) :
    skeletonPrime k i ∣ skeletonProduct k := by
  unfold skeletonProduct
  exact Finset.dvd_prod_of_mem (skeletonPrime k) (Finset.mem_univ i)

/-- A selected prime divides a subset product exactly when its index belongs
to that subset. -/
theorem skeletonPrime_dvd_subsetProduct_iff (k : ℕ) (S : Finset (Fin k))
    (i : Fin k) : skeletonPrime k i ∣ skeletonSubsetProduct k S ↔ i ∈ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [skeletonSubsetProduct, (skeletonPrime_spec k i).1.not_dvd_one]
  | @insert a S ha ih =>
      rw [show skeletonSubsetProduct k (insert a S) =
          skeletonPrime k a * skeletonSubsetProduct k S by
        simp [skeletonSubsetProduct, ha]]
      rw [(skeletonPrime_spec k i).1.dvd_mul,
        Nat.prime_dvd_prime_iff_eq (skeletonPrime_spec k i).1
          (skeletonPrime_spec k a).1, ih]
      constructor
      · rintro (hpEq | hiS)
        · exact Finset.mem_insert.mpr (Or.inl ((skeletonPrime_injective k) hpEq))
        · exact Finset.mem_insert.mpr (Or.inr hiS)
      · intro hi
        rcases Finset.mem_insert.mp hi with hiEq | hiS
        · exact Or.inl (congrArg (skeletonPrime k) hiEq)
        · exact Or.inr hiS

theorem skeletonPrime_not_dvd_progressionFactor
    (Q k d : ℕ) (i : Fin k) :
    ¬skeletonPrime k i ∣
      1 + skeletonProduct k * (Q / (d * skeletonProduct k)) := by
  intro hdiv
  have hterm : skeletonPrime k i ∣
      skeletonProduct k * (Q / (d * skeletonProduct k)) :=
    (skeletonPrime_dvd_product k i).mul_right _
  have hone : skeletonPrime k i ∣ 1 :=
    (Nat.dvd_add_iff_right hterm).mpr (by simpa [Nat.add_comm] using hdiv)
  exact (skeletonPrime_spec k i).1.not_dvd_one hone

/-- The divisibility encoding asserted in the paper: the `i`th selected
prime divides `q_S` exactly when `i ∈ S`. -/
theorem skeletonPrime_dvd_modulus_iff (j : ℕ)
    (S : Finset (Fin (skeletonK j))) (i : Fin (skeletonK j)) :
    skeletonPrime (skeletonK j) i ∣ skeletonModulus j S ↔ i ∈ S := by
  let k := skeletonK j
  let P := skeletonProduct k
  let d := skeletonSubsetProduct k S
  have hprime := (skeletonPrime_spec k i).1
  change skeletonPrime k i ∣
      d * (1 + P * (2 ^ j / (d * P))) ↔ i ∈ S
  constructor
  · intro hdiv
    rcases hprime.dvd_mul.mp hdiv with hd | hfactor
    · exact (skeletonPrime_dvd_subsetProduct_iff k S i).mp hd
    · exact (skeletonPrime_not_dvd_progressionFactor (2 ^ j) k d i hfactor).elim
  · intro hiS
    exact ((skeletonPrime_dvd_subsetProduct_iff k S i).mpr hiS).mul_right _

theorem skeletonModulus_pos (j : ℕ) (S : Finset (Fin (skeletonK j))) :
    0 < skeletonModulus j S := by
  exact progressionApprox_pos (skeletonSubsetProduct_pos (skeletonK j) S)

/-- The cross-multiplied window bounds for every subset (and hence for every
member of the central family). -/
theorem skeletonModulus_bounds (j : ℕ) (hj : 64 ≤ j)
    (S : Finset (Fin (skeletonK j))) :
    19 * 2 ^ j ≤ 20 * skeletonModulus j S ∧
      20 * skeletonModulus j S ≤ 21 * 2 ^ j := by
  apply progressionApprox_bounds
  · exact skeletonProduct_pos (skeletonK j)
  · exact skeletonSubsetProduct_pos (skeletonK j) S
  · exact skeletonSubsetProduct_le_product (skeletonK j) S
  · exact twenty_mul_skeletonProduct_sq_le j hj

/-- Distinct subsets receive distinct moduli. -/
theorem skeletonModulus_injective (j : ℕ) : Function.Injective (skeletonModulus j) := by
  intro S T hST
  ext i
  rw [← skeletonPrime_dvd_modulus_iff j S i,
    ← skeletonPrime_dvd_modulus_iff j T i, hST]

/-- The paper's interval containment follows formally from the
cross-multiplied modulus window. -/
theorem inSkeletonInterval_between_modulus {Q q m : ℕ} (hQ : 0 < Q)
    (hqLower : 19 * Q ≤ 20 * q) (hqUpper : 20 * q ≤ 21 * Q)
    (hm : InSkeletonInterval Q m) : q < m ∧ m ≤ 2 * q := by
  unfold InSkeletonInterval at hm
  omega

/-- Any two integers in `[11Q/10,19Q/10]` are less than `q` apart whenever
`19Q/20 ≤ q`.  This is the diameter assertion in natural-number form. -/
theorem inSkeletonInterval_dist_lt_modulus {Q q m n : ℕ} (hQ : 0 < Q)
    (hqLower : 19 * Q ≤ 20 * q)
    (hm : InSkeletonInterval Q m) (hn : InSkeletonInterval Q n) :
    Nat.dist m n < q := by
  unfold InSkeletonInterval at hm hn
  rcases le_total m n with hmn | hnm
  · rw [Nat.dist_eq_sub_of_le hmn]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hnm]
    omega

/-- All conclusions of the paper's arithmetic-skeleton lemma, including the
quantitative estimates used in its proof.  Here `Q` is definitionally `2^j`
and `k` is definitionally `skeletonK j`. -/
structure ArithmeticSkeleton (j : ℕ) where
  p : Fin (skeletonK j) → ℕ
  q : SkeletonCentralFamily (skeletonK j) → ℕ
  k_even : Even (skeletonK j)
  k_pos : 0 < skeletonK j
  p_prime : ∀ i, (p i).Prime
  p_lower : ∀ i, 4 ^ (skeletonK j + i.val + 1) < p i
  p_upper : ∀ i, p i < 2 * 4 ^ (skeletonK j + i.val + 1)
  p_injective : Function.Injective p
  product_bound :
    (∏ i, p i) ≤ 2 ^ (3 * skeletonK j ^ 2 + 2 * skeletonK j)
  product_square_small : 20 * (∏ i, p i) ^ 2 ≤ 2 ^ j
  q_pos : ∀ S, 0 < q S
  q_lower : ∀ S, 19 * 2 ^ j ≤ 20 * q S
  q_upper : ∀ S, 20 * q S ≤ 21 * 2 ^ j
  prime_dvd_q_iff : ∀ S i, p i ∣ q S ↔ i ∈ S.1
  q_injective : Function.Injective q
  interval_subset : ∀ S m, InSkeletonInterval (2 ^ j) m → q S < m ∧ m ≤ 2 * q S
  interval_diameter : ∀ S m n, InSkeletonInterval (2 ^ j) m →
    InSkeletonInterval (2 ^ j) n → Nat.dist m n < q S

/-- A complete arithmetic skeleton exists for every `j ≥ 64`.  This explicit
cutoff is stronger than the paper's qualitative “for all sufficiently large
integers `j`.” -/
theorem arithmetic_skeleton (j : ℕ) (hj : 64 ≤ j) :
    Nonempty (ArithmeticSkeleton j) := by
  let q : SkeletonCentralFamily (skeletonK j) → ℕ :=
    fun S ↦ skeletonModulus j S.1
  refine ⟨{
    p := skeletonPrime (skeletonK j)
    q := q
    k_even := skeletonK_even j
    k_pos := lt_of_lt_of_le (by norm_num) (skeletonK_ge_two hj)
    p_prime := fun i ↦ (skeletonPrime_spec (skeletonK j) i).1
    p_lower := fun i ↦ (skeletonPrime_spec (skeletonK j) i).2.1
    p_upper := fun i ↦ skeletonPrime_lt_two_mul (skeletonK j) i
    p_injective := skeletonPrime_injective (skeletonK j)
    product_bound := by
      simpa only [skeletonProduct] using skeletonProduct_le (skeletonK j)
    product_square_small := by
      simpa only [skeletonProduct] using twenty_mul_skeletonProduct_sq_le j hj
    q_pos := fun S ↦ by
      simpa only [q] using skeletonModulus_pos j S.1
    q_lower := fun S ↦ by
      simpa only [q] using (skeletonModulus_bounds j hj S.1).1
    q_upper := fun S ↦ by
      simpa only [q] using (skeletonModulus_bounds j hj S.1).2
    prime_dvd_q_iff := fun S i ↦ by
      simpa only [q] using skeletonPrime_dvd_modulus_iff j S.1 i
    q_injective := by
      intro S T hST
      apply Subtype.ext
      apply skeletonModulus_injective j
      simpa only [q] using hST
    interval_subset := fun S m hm ↦ by
      have hbounds := skeletonModulus_bounds j hj S.1
      simpa only [q] using
        (inSkeletonInterval_between_modulus (Q := 2 ^ j)
          (q := skeletonModulus j S.1) (by positivity) hbounds.1 hbounds.2 hm)
    interval_diameter := fun S m n hm hn ↦ by
      have hlower := (skeletonModulus_bounds j hj S.1).1
      simpa only [q] using
        (inSkeletonInterval_dist_lt_modulus (Q := 2 ^ j)
          (q := skeletonModulus j S.1) (by positivity) hlower hm hn)
  }⟩

/-- The literal filter formulation of “for all sufficiently large `j`.” -/
theorem arithmetic_skeleton_eventually :
    ∀ᶠ j : ℕ in Filter.atTop, Nonempty (ArithmeticSkeleton j) := by
  filter_upwards [Filter.eventually_ge_atTop (64 : ℕ)] with j hj
  exact arithmetic_skeleton j hj

end Erdos486


/-! Flattened from Erdos486.BiasedSkeleton. -/

/-!
# A biased-colouring arithmetic skeleton for Erdős Problem 486

This is a formalization-friendly strengthening of the finite arithmetic
block.  The endpoint interval is deterministic.  A later finite-colouring
argument chooses, for each endpoint, a subset of the auxiliary primes; this
file supplies a distinct modulus for every such subset and proves all of the
geometric estimates needed by the global construction.
-/

open scoped BigOperators

namespace Erdos486

/-- The square-root scale used by the biased-colouring block. -/
def biasedRadius (j : ℕ) : ℕ :=
  Nat.sqrt j / 20

/-- There are six auxiliary primes per square-root unit. -/
def biasedK (j : ℕ) : ℕ :=
  6 * biasedRadius j

theorem biasedRadius_pos {j : ℕ} (hj : 400 ≤ j) :
    0 < biasedRadius j := by
  have hsqrt : 20 ≤ Nat.sqrt j := by
    have hsqrt400 : Nat.sqrt 400 = 20 := by norm_num
    rw [← hsqrt400]
    exact Nat.sqrt_le_sqrt hj
  simp only [biasedRadius]
  omega

theorem twenty_mul_biasedRadius_le_sqrt (j : ℕ) :
    20 * biasedRadius j ≤ Nat.sqrt j := by
  simpa [biasedRadius, Nat.mul_comm] using
    Nat.div_mul_le_self (Nat.sqrt j) 20

theorem biased_exponent_add_five_le {j : ℕ} (hj : 400 ≤ j) :
    3 * biasedK j ^ 2 + 2 * biasedK j + 5 ≤ j := by
  have hr : 1 ≤ biasedRadius j := biasedRadius_pos hj
  have htwenty := twenty_mul_biasedRadius_le_sqrt j
  have hsqrt := Nat.sqrt_le j
  simp only [biasedK] at ⊢
  nlinarith

/-- The product of the auxiliary primes is at most one thirty-second of
the dyadic scale. -/
theorem thirtyTwo_mul_biasedProduct_le (j : ℕ) (hj : 400 ≤ j) :
    32 * skeletonProduct (biasedK j) ≤ 2 ^ j := by
  have hP := skeletonProduct_le (biasedK j)
  have hexp := biased_exponent_add_five_le hj
  calc
    32 * skeletonProduct (biasedK j) ≤
        2 ^ 5 * 2 ^ (3 * biasedK j ^ 2 + 2 * biasedK j) :=
      Nat.mul_le_mul (by norm_num) hP
    _ = 2 ^ (5 + (3 * biasedK j ^ 2 + 2 * biasedK j)) :=
      (pow_add 2 5 (3 * biasedK j ^ 2 + 2 * biasedK j)).symm
    _ = 2 ^ (3 * biasedK j ^ 2 + 2 * biasedK j + 5) := by
      congr 1
      omega
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hexp

/-- The largest multiple of the prime product not exceeding `2^j`. -/
noncomputable def biasedBase (j : ℕ) : ℕ :=
  skeletonProduct (biasedK j) *
    (2 ^ j / skeletonProduct (biasedK j))

/-- The modulus indexed by a subset of the auxiliary primes. -/
noncomputable def biasedModulus (j : ℕ)
    (S : Finset (Fin (biasedK j))) : ℕ :=
  biasedBase j + skeletonSubsetProduct (biasedK j) S

theorem biasedBase_le (j : ℕ) : biasedBase j ≤ 2 ^ j := by
  simpa [biasedBase, Nat.mul_comm] using
    Nat.div_mul_le_self (2 ^ j) (skeletonProduct (biasedK j))

theorem twoPow_lt_biasedBase_add_product (j : ℕ) :
    2 ^ j < biasedBase j + skeletonProduct (biasedK j) := by
  have hP : 0 < skeletonProduct (biasedK j) := skeletonProduct_pos _
  simpa [biasedBase, Nat.mul_add] using
    Nat.lt_mul_div_succ (2 ^ j) hP

theorem skeletonPrime_dvd_biasedBase (j : ℕ) (i : Fin (biasedK j)) :
    skeletonPrime (biasedK j) i ∣ biasedBase j := by
  exact (skeletonPrime_dvd_product (biasedK j) i).mul_right _

/-- The prime support of a modulus recovers its indexing subset exactly. -/
theorem skeletonPrime_dvd_biasedModulus_iff (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    skeletonPrime (biasedK j) i ∣ biasedModulus j S ↔ i ∈ S := by
  rw [biasedModulus, ← Nat.dvd_add_iff_right
    (skeletonPrime_dvd_biasedBase j i),
    skeletonPrime_dvd_subsetProduct_iff]

theorem biasedModulus_injective (j : ℕ) :
    Function.Injective (biasedModulus j) := by
  intro S T hST
  ext i
  rw [← skeletonPrime_dvd_biasedModulus_iff,
    hST, skeletonPrime_dvd_biasedModulus_iff]

theorem biasedModulus_pos (j : ℕ) (S : Finset (Fin (biasedK j))) :
    0 < biasedModulus j S := by
  unfold biasedModulus
  exact Nat.add_pos_right _ (skeletonSubsetProduct_pos _ _)

/-- Every biased modulus lies in the narrower interval
`[19*2^j/20, 21*2^j/20]` required by the global interface. -/
theorem biasedModulus_bounds {j : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) :
    19 * 2 ^ j ≤ 20 * biasedModulus j S ∧
      20 * biasedModulus j S ≤ 21 * 2 ^ j := by
  have hsmall := thirtyTwo_mul_biasedProduct_le j hj
  have hbaseUpper := biasedBase_le j
  have hbaseLower := twoPow_lt_biasedBase_add_product j
  have hdpos := skeletonSubsetProduct_pos (biasedK j) S
  have hdUpper := skeletonSubsetProduct_le_product (biasedK j) S
  unfold biasedModulus
  constructor <;> omega

/-- The integral radius `2^(j-3)`, so that `2^j = 8 * blockUnit j`
at every relevant scale. -/
def blockUnit (j : ℕ) : ℕ :=
  2 ^ (j - 3)

theorem twoPow_eq_eight_mul_blockUnit {j : ℕ} (hj : 3 ≤ j) :
    2 ^ j = 8 * blockUnit j := by
  rw [blockUnit, show j = (j - 3) + 3 by omega, pow_add]
  norm_num [Nat.mul_comm]

/-- All integers in `[9*2^(j-3), 15*2^(j-3)]`. -/
def biasedEndpoints (j : ℕ) : Finset ℕ :=
  Finset.Icc (9 * blockUnit j) (15 * blockUnit j)

theorem mem_biasedEndpoints_iff {j m : ℕ} :
    m ∈ biasedEndpoints j ↔
      9 * blockUnit j ≤ m ∧ m ≤ 15 * blockUnit j := by
  simp [biasedEndpoints]

theorem biasedEndpoints_card (j : ℕ) :
    (biasedEndpoints j).card = 6 * blockUnit j + 1 := by
  simp [biasedEndpoints]
  omega

theorem biasedEndpoint_bounds {j m : ℕ} (hj : 400 ≤ j)
    (hm : m ∈ biasedEndpoints j) :
    11 * 2 ^ j ≤ 10 * m ∧
      10 * m ≤ 19 * 2 ^ j := by
  have hQ := twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega)
  rw [mem_biasedEndpoints_iff] at hm
  omega

theorem biasedEndpoints_enough {j : ℕ} (hj : 400 ≤ j) :
    3 * 2 ^ j ≤ 8 * (biasedEndpoints j).card := by
  rw [twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega),
    biasedEndpoints_card]
  omega

end Erdos486


/-! Flattened from Erdos486.BiasedColoring. -/

/-!
# Finite colourings for the biased Erdős 486 block

The colour set has four elements; colour zero is called black.  Thus uniform
enumeration of all colourings gives black probability exactly `1/4`, without
introducing any measure-theoretic probability space.
-/

open scoped BigOperators

namespace Erdos486

instance biasedPrimeNeZero (k : ℕ) (i : Fin k) :
    NeZero (skeletonPrime k i) :=
  ⟨(skeletonPrime_spec k i).1.ne_zero⟩

/-- A coordinate consists of a prime index and a residue modulo that prime. -/
def BiasedCoordinate (j : ℕ) :=
  Σ i : Fin (biasedK j), ZMod (skeletonPrime (biasedK j) i)

noncomputable instance instDecidableEqBiasedCoordinate (j : ℕ) :
    DecidableEq (BiasedCoordinate j) :=
  Classical.decEq _

/-- The complete coordinate space at a fixed scale is finite.  Registering
this instance once keeps all later finite-colouring averages on the same
canonical enumeration. -/
noncomputable instance instFintypeBiasedCoordinate (j : ℕ) :
    Fintype (BiasedCoordinate j) := by
  classical
  unfold BiasedCoordinate
  infer_instance

/-- A four-colouring of all prime-residue coordinates at scale `j`. -/
abbrev BiasedColoring (j : ℕ) := BiasedCoordinate j → Fin 4

/-- The coordinate queried by endpoint `m` at prime index `i`. -/
noncomputable def endpointCoordinate (j m : ℕ) (i : Fin (biasedK j)) :
    BiasedCoordinate j :=
  ⟨i, (m : ZMod (skeletonPrime (biasedK j) i))⟩

/-- Indices whose queried coordinate is black. -/
noncomputable def selectedPrimes (j : ℕ) (c : BiasedColoring j) (m : ℕ) :
    Finset (Fin (biasedK j)) :=
  Finset.univ.filter fun i ↦ c (endpointCoordinate j m i) = 0

@[simp]
theorem mem_selectedPrimes_iff (j : ℕ) (c : BiasedColoring j)
    (m : ℕ) (i : Fin (biasedK j)) :
    i ∈ selectedPrimes j c m ↔ c (endpointCoordinate j m i) = 0 := by
  simp [selectedPrimes]

/-- The endpoint modulus selected by a colouring. -/
noncomputable def colouredModulus (j : ℕ) (c : BiasedColoring j) (m : ℕ) : ℕ :=
  biasedModulus j (selectedPrimes j c m)

theorem colouredModulus_pos (j : ℕ) (c : BiasedColoring j) (m : ℕ) :
    0 < colouredModulus j c m :=
  biasedModulus_pos _ _

theorem colouredModulus_bounds {j : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (m : ℕ) :
    19 * 2 ^ j ≤ 20 * colouredModulus j c m ∧
      20 * colouredModulus j c m ≤ 21 * 2 ^ j :=
  biasedModulus_bounds hj _

/-- An endpoint lies strictly after its selected modulus. -/
theorem colouredModulus_lt_endpoint {j m : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (hm : m ∈ biasedEndpoints j) :
    colouredModulus j c m < m := by
  have hq := (colouredModulus_bounds hj c m).2
  have hm' := (biasedEndpoint_bounds hj hm).1
  have hQ : 0 < 2 ^ j := by positivity
  omega

/-- An endpoint lies strictly before twice its selected modulus. -/
theorem endpoint_lt_two_colouredModulus {j m : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (hm : m ∈ biasedEndpoints j) :
    m < 2 * colouredModulus j c m := by
  have hq := (colouredModulus_bounds hj c m).1
  have hQ := twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega)
  have hunit : 0 < blockUnit j := by simp [blockUnit]
  rw [mem_biasedEndpoints_iff] at hm
  rw [hQ] at hq
  omega

/-- The endpoint interval has diameter smaller than every subset modulus. -/
theorem biasedEndpoint_dist_lt_modulus {j m n : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j)))
    (hm : m ∈ biasedEndpoints j) (hn : n ∈ biasedEndpoints j) :
    Nat.dist m n < biasedModulus j S := by
  have hq := (biasedModulus_bounds hj S).1
  have hQ := twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega)
  have hunit : 0 < blockUnit j := by simp [blockUnit]
  rw [hQ] at hq
  rw [mem_biasedEndpoints_iff] at hm hn
  rcases le_total m n with hmn | hnm
  · rw [Nat.dist_eq_sub_of_le hmn]
    have hdiff : n - m ≤ 6 * blockUnit j := by omega
    have hq' : 6 * blockUnit j < biasedModulus j S := by omega
    exact hdiff.trans_lt hq'
  · rw [Nat.dist_eq_sub_of_le_right hnm]
    have hdiff : m - n ≤ 6 * blockUnit j := by omega
    have hq' : 6 * blockUnit j < biasedModulus j S := by omega
    exact hdiff.trans_lt hq'

/-- Consequently a residue class modulo a subset modulus contains at most
one endpoint in the block interval. -/
theorem biasedEndpoint_eq_of_cast_eq {j m n : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j)))
    (hm : m ∈ biasedEndpoints j) (hn : n ∈ biasedEndpoints j)
    (hcast : (m : ZMod (biasedModulus j S)) =
      (n : ZMod (biasedModulus j S))) :
    m = n := by
  have hmod : m ≡ n [MOD biasedModulus j S] :=
    (ZMod.natCast_eq_natCast_iff m n (biasedModulus j S)).mp hcast
  have hdist := biasedEndpoint_dist_lt_modulus hj S hm hn
  rcases le_total m n with hmn | hnm
  · have hdvd : biasedModulus j S ∣ n - m :=
      (Nat.modEq_iff_dvd' hmn).mp hmod
    have hlt : n - m < biasedModulus j S := by
      simpa [Nat.dist_eq_sub_of_le hmn] using hdist
    have hz : n - m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdvd : biasedModulus j S ∣ m - n :=
      (Nat.modEq_iff_dvd' hnm).mp hmod.symm
    have hlt : m - n < biasedModulus j S := by
      simpa [Nat.dist_eq_sub_of_le_right hnm] using hdist
    have hz : m - n = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

/-- Endpoints representing a prescribed residue modulo `q_S`. -/
noncomputable def candidateEndpoints (j : ℕ)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S)) :
    Finset ℕ :=
  (biasedEndpoints j).filter fun m ↦
    (m : ZMod (biasedModulus j S)) = z

theorem candidateEndpoints_card_le_one {j : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S)) :
    (candidateEndpoints j S z).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro m n hm hn
  rw [candidateEndpoints, Finset.mem_filter] at hm hn
  exact biasedEndpoint_eq_of_cast_eq hj S hm.1 hn.1 (hm.2.trans hn.2.symm)

/-- A common finite period for all subset moduli at one scale. -/
noncomputable def biasedPeriod (j : ℕ) : ℕ :=
  ∏ S : Finset (Fin (biasedK j)), biasedModulus j S

theorem biasedPeriod_pos (j : ℕ) : 0 < biasedPeriod j := by
  unfold biasedPeriod
  exact Finset.prod_pos fun S _ ↦ biasedModulus_pos j S

theorem biasedModulus_dvd_period (j : ℕ)
    (S : Finset (Fin (biasedK j))) :
    biasedModulus j S ∣ biasedPeriod j := by
  unfold biasedPeriod
  exact Finset.dvd_prod_of_mem (biasedModulus j) (Finset.mem_univ S)

/-- Reduction from the common period to a subset modulus. -/
noncomputable def reduceBiasedPeriod (j : ℕ)
    (S : Finset (Fin (biasedK j))) :
    ZMod (biasedPeriod j) →+* ZMod (biasedModulus j S) :=
  ZMod.castHom (biasedModulus_dvd_period j S) _

/-- The periodic footprint covered by the endpoint cylinders of a colouring. -/
def IsBiasedCovered (j : ℕ) (c : BiasedColoring j)
    (x : ZMod (biasedPeriod j)) : Prop :=
  ∃ m ∈ biasedEndpoints j,
    reduceBiasedPeriod j (selectedPrimes j c m) x =
      (m : ZMod (colouredModulus j c m))

/-- Number of covered residues in one common period. -/
noncomputable def biasedFootprintCount (j : ℕ) (c : BiasedColoring j) : ℕ := by
  letI : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  classical
  exact (Finset.univ.filter (IsBiasedCovered j c)).card

/-- Normalized periodic footprint, represented as an exact finite ratio. -/
noncomputable def biasedFootprint (j : ℕ) (c : BiasedColoring j) : ℝ :=
  biasedFootprintCount j c / biasedPeriod j

/-- Rational version of the same exact finite ratio.  Finite enumeration is
most convenient over `ℚ`; it is cast to the real-valued block interface only
after the deterministic colouring has been selected. -/
noncomputable def biasedFootprintRat (j : ℕ) (c : BiasedColoring j) : ℚ :=
  biasedFootprintCount j c / biasedPeriod j

theorem biasedFootprintRat_cast_real (j : ℕ) (c : BiasedColoring j) :
    ((biasedFootprintRat j c : ℚ) : ℝ) = biasedFootprint j c := by
  simp [biasedFootprintRat, biasedFootprint]

theorem biasedFootprintCount_le_period (j : ℕ) (c : BiasedColoring j) :
    biasedFootprintCount j c ≤ biasedPeriod j := by
  let _ : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  classical
  unfold biasedFootprintCount
  simpa using (Finset.card_filter_le
    (s := (Finset.univ : Finset (ZMod (biasedPeriod j))))
    (p := IsBiasedCovered j c))

theorem biasedFootprint_nonneg (j : ℕ) (c : BiasedColoring j) :
    0 ≤ biasedFootprint j c := by
  unfold biasedFootprint
  positivity

theorem biasedFootprint_le_one (j : ℕ) (c : BiasedColoring j) :
    biasedFootprint j c ≤ 1 := by
  rw [biasedFootprint, div_le_one (by exact_mod_cast biasedPeriod_pos j)]
  exact_mod_cast biasedFootprintCount_le_period j c

end Erdos486


/-! Flattened from Erdos486.BiasedCollision. -/

/-!
# Arithmetic collision counts for the biased-colouring block

For a subset `S` and an index `i ∉ S`, reduction modulo `q_S` and modulo
`p_i` is independent: the two moduli are coprime.  We choose a canonical
endpoint representing each residue modulo `q_S` (and use zero if there is no
such endpoint).  The residues for which the `p_i`-coordinate agrees with this
candidate form the graph of a function

`ZMod q_S → ZMod p_i`.

The Chinese remainder theorem therefore gives exactly one admissible
`p_i`-coordinate above every `q_S`-coordinate.  This file carries that count
from the pair period `q_S * p_i` to the explicit common period
`biasedPeriod j`.
-/

namespace Erdos486

/-- A canonical endpoint representing `z` modulo `q_S`.  If the endpoint
interval contains no representative, use zero.  At scales `j ≥ 400`, the
representative is unique by `candidateEndpoints_card_le_one`. -/
noncomputable def biasedCandidate (j : ℕ)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S)) : ℕ :=
  if h : (candidateEndpoints j S z).Nonempty then h.choose else 0

theorem biasedCandidate_mem_of_nonempty {j : ℕ}
    {S : Finset (Fin (biasedK j))} {z : ZMod (biasedModulus j S)}
    (h : (candidateEndpoints j S z).Nonempty) :
    biasedCandidate j S z ∈ candidateEndpoints j S z := by
  simp only [biasedCandidate, dif_pos h]
  exact h.choose_spec

/-- At relevant scales, any endpoint representing `z` is the canonical one. -/
theorem biasedCandidate_eq_of_mem {j m : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) (z : ZMod (biasedModulus j S))
    (hm : m ∈ candidateEndpoints j S z) :
    biasedCandidate j S z = m := by
  classical
  have hne : (candidateEndpoints j S z).Nonempty := ⟨m, hm⟩
  have hc := biasedCandidate_mem_of_nonempty hne
  have hcard := candidateEndpoints_card_le_one hj S z
  rw [Finset.card_le_one_iff] at hcard
  exact hcard hc hm

/-- If `i ∉ S`, the subset modulus `q_S` is coprime to `p_i`. -/
theorem biasedModulus_coprime_skeletonPrime {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    Nat.Coprime (biasedModulus j S) (skeletonPrime (biasedK j) i) := by
  have hp : (skeletonPrime (biasedK j) i).Prime :=
    (skeletonPrime_spec (biasedK j) i).1
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  rwa [skeletonPrime_dvd_biasedModulus_iff]

/-- The extra prime `p_i` divides the explicit common period, since it divides
the factor indexed by `insert i S`. -/
theorem skeletonPrime_dvd_biasedPeriod (j : ℕ) (i : Fin (biasedK j)) :
    skeletonPrime (biasedK j) i ∣ biasedPeriod j := by
  apply dvd_trans (b := biasedModulus j {i})
  · rw [skeletonPrime_dvd_biasedModulus_iff]
    simp
  · exact biasedModulus_dvd_period j {i}

/-- The pair period `q_S p_i` divides the common period. -/
theorem biasedPairPeriod_dvd_biasedPeriod {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    biasedModulus j S * skeletonPrime (biasedK j) i ∣ biasedPeriod j := by
  exact (biasedModulus_coprime_skeletonPrime S i hi).mul_dvd_of_dvd_of_dvd
    (biasedModulus_dvd_period j S) (skeletonPrime_dvd_biasedPeriod j i)

/-- Collision with the `p_i`-coordinate of the canonical endpoint determined
by the residue of `x` modulo `q_S`. -/
def IsBiasedCollision (j : ℕ) (S : Finset (Fin (biasedK j)))
    (i : Fin (biasedK j)) (x : ℕ) : Prop :=
  (x : ZMod (skeletonPrime (biasedK j) i)) =
    (biasedCandidate j S (x : ZMod (biasedModulus j S)) :
      ZMod (skeletonPrime (biasedK j) i))

noncomputable instance instDecidableIsBiasedCollision (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (x : ℕ) :
    Decidable (IsBiasedCollision j S i x) := by
  unfold IsBiasedCollision
  infer_instance

/-- The collision relation is periodic with pair period `q_S p_i`. -/
theorem isBiasedCollision_periodic (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    Function.Periodic (IsBiasedCollision j S i)
      (biasedModulus j S * skeletonPrime (biasedK j) i) := by
  intro x
  simp [IsBiasedCollision, Nat.cast_add, Nat.cast_mul]

/-- The graph of a function has one point over each element of its domain. -/
private def functionGraphEquiv {α β : Type*} (f : α → β) :
    {y : α × β // y.2 = f y.1} ≃ α where
  toFun y := y.1.1
  invFun a := ⟨(a, f a), rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    exact Prod.ext rfl hab.symm
  right_inv := by
    intro a
    rfl

/-- CRT identifies the collision residues in a pair period with the graph of
an arbitrary function `ZMod q → ZMod p`. -/
private noncomputable def finChineseRemainderEquiv (q p : ℕ)
    [NeZero q] [NeZero p] (hqp : Nat.Coprime q p) :
    Fin (q * p) ≃ ZMod q × ZMod p where
  toFun x := ((x.val : ZMod q), (x.val : ZMod p))
  invFun y :=
    ⟨((ZMod.chineseRemainder hqp).symm y).val, ZMod.val_lt _⟩
  left_inv x := by
    apply Fin.ext
    change ((ZMod.chineseRemainder hqp).symm
      ((x.val : ZMod q), (x.val : ZMod p))).val = x.val
    have hz : (ZMod.chineseRemainder hqp).symm
        ((x.val : ZMod q), (x.val : ZMod p)) =
        (x.val : ZMod (q * p)) := by
      apply (ZMod.chineseRemainder hqp).injective
      rw [(ZMod.chineseRemainder hqp).apply_symm_apply]
      change ((x.val : ZMod q), (x.val : ZMod p)) =
        (ZMod.cast (x.val : ZMod (q * p)) : ZMod q × ZMod p)
      apply Prod.ext <;> simp
    rw [hz, ZMod.val_natCast_of_lt x.isLt]
  right_inv y := by
    let z := (ZMod.chineseRemainder hqp).symm y
    change ((z.val : ZMod q), (z.val : ZMod p)) = y
    calc
      ((z.val : ZMod q), (z.val : ZMod p)) =
          (ZMod.chineseRemainder hqp) z := by
        change ((z.val : ZMod q), (z.val : ZMod p)) =
          (ZMod.cast z : ZMod q × ZMod p)
        apply Prod.ext <;> simp [ZMod.natCast_val]
      _ = y := (ZMod.chineseRemainder hqp).apply_symm_apply y

private noncomputable def modCollisionEquiv (q p : ℕ)
    [NeZero q] [NeZero p] (hqp : Nat.Coprime q p)
    (f : ZMod q → ZMod p) :
    {x : Fin (q * p) //
      (x.val : ZMod p) = f (x.val : ZMod q)} ≃ ZMod q := by
  let e : Fin (q * p) ≃ ZMod q × ZMod p :=
    finChineseRemainderEquiv q p hqp
  refine (e.subtypeEquiv ?_).trans (functionGraphEquiv f)
  intro x
  rfl

/-- In one pair period, the collision graph has exactly `q` representatives. -/
theorem count_mod_collision_eq (q p : ℕ) [NeZero q] [NeZero p]
    (hqp : Nat.Coprime q p) (f : ZMod q → ZMod p) :
    (q * p).count
      (fun x : ℕ ↦ (x : ZMod p) = f (x : ZMod q)) = q := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let P : ℕ → Prop := fun x ↦ (x : ZMod p) = f (x : ZMod q)
  let s := (Finset.range (q * p)).filter P
  have hslt : ∀ x ∈ s, x < q * p := by
    intro x hx
    exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  have hsattach : s.attachFin hslt =
      (Finset.univ.filter fun x : Fin (q * p) ↦
        (x.val : ZMod p) = f (x.val : ZMod q)) := by
    ext x
    simp [s, P]
  change s.card = q
  rw [← Finset.card_attachFin s hslt, hsattach,
    ← Fintype.card_subtype]
  exact (Fintype.card_congr (modCollisionEquiv q p hqp f)).trans
    (ZMod.card q)

/-- Repeating a periodic predicate through `t` complete periods multiplies
its count by `t`. -/
theorem count_mul_of_periodic (P : ℕ → Prop) [DecidablePred P]
    (a t : ℕ) (hP : Function.Periodic P a) :
    (t * a).count P = t * a.count P := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_mul, Nat.count_add, ih]
      have hshift : (fun k ↦ P (t * a + k)) = P := by
        funext k
        simpa [Nat.nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using
          (hP.nsmul t) k
      simp only [hshift]
      simp [Nat.add_mul]

/-- In the pair period `q_S p_i`, the biased collision relation has exactly
`q_S` representatives. -/
theorem biasedCollision_pair_count {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    (biasedModulus j S * skeletonPrime (biasedK j) i).count
      (IsBiasedCollision j S i) = biasedModulus j S := by
  let _ : NeZero (biasedModulus j S) :=
    ⟨(biasedModulus_pos j S).ne'⟩
  let _ : NeZero (skeletonPrime (biasedK j) i) :=
    biasedPrimeNeZero (biasedK j) i
  change (biasedModulus j S * skeletonPrime (biasedK j) i).count
    (fun x : ℕ ↦
      (x : ZMod (skeletonPrime (biasedK j) i)) =
        (biasedCandidate j S (x : ZMod (biasedModulus j S)) :
          ZMod (skeletonPrime (biasedK j) i))) = biasedModulus j S
  exact count_mod_collision_eq (biasedModulus j S)
    (skeletonPrime (biasedK j) i)
    (biasedModulus_coprime_skeletonPrime S i hi)
    (fun z ↦ (biasedCandidate j S z :
      ZMod (skeletonPrime (biasedK j) i)))

/-- Number of collisions among the canonical representatives
`0, ..., biasedPeriod j - 1`. -/
noncomputable def biasedCollisionCount (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) : ℕ := by
  classical
  exact (biasedPeriod j).count (IsBiasedCollision j S i)

/-- The collision set has exact proportion `1 / p_i` in the explicit common
period.  The cross-multiplied form avoids division and coercions. -/
theorem skeletonPrime_mul_biasedCollisionCount_eq_period {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    skeletonPrime (biasedK j) i * biasedCollisionCount j S i =
      biasedPeriod j := by
  classical
  let q := biasedModulus j S
  let p := skeletonPrime (biasedK j) i
  let N := biasedPeriod j
  have hdiv : q * p ∣ N := biasedPairPeriod_dvd_biasedPeriod S i hi
  rcases hdiv with ⟨t, ht⟩
  have hpair : (q * p).count (IsBiasedCollision j S i) = q := by
    simpa only [q, p] using biasedCollision_pair_count S i hi
  have hperiod : Function.Periodic (IsBiasedCollision j S i) (q * p) := by
    simpa only [q, p] using isBiasedCollision_periodic j S i
  calc
    skeletonPrime (biasedK j) i * biasedCollisionCount j S i =
        p * ((t * (q * p)).count (IsBiasedCollision j S i)) := by
      simp only [p, biasedCollisionCount, N] at ht ⊢
      rw [ht, Nat.mul_comm (q * p) t]
    _ = p * (t * (q * p).count (IsBiasedCollision j S i)) := by
      rw [count_mul_of_periodic _ _ _ hperiod]
    _ = p * (t * q) := by rw [hpair]
    _ = (q * p) * t := by ring
    _ = N := ht.symm

/-- In particular, the requested collision-cardinality bound holds. -/
theorem skeletonPrime_mul_biasedCollisionCount_le_period {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    skeletonPrime (biasedK j) i * biasedCollisionCount j S i ≤
      biasedPeriod j :=
  (skeletonPrime_mul_biasedCollisionCount_eq_period S i hi).le

/-- An actual endpoint matching `x` modulo both `q_S` and `p_i` satisfies the
canonical collision relation. -/
theorem isBiasedCollision_of_endpoint {j x m : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j))
    (hm : m ∈ biasedEndpoints j)
    (hq : (x : ZMod (biasedModulus j S)) =
      (m : ZMod (biasedModulus j S)))
    (hp : (x : ZMod (skeletonPrime (biasedK j) i)) =
      (m : ZMod (skeletonPrime (biasedK j) i))) :
    IsBiasedCollision j S i x := by
  have hmCandidate : m ∈
      candidateEndpoints j S (x : ZMod (biasedModulus j S)) := by
    simp only [candidateEndpoints, Finset.mem_filter]
    exact ⟨hm, hq.symm⟩
  have hcandidate := biasedCandidate_eq_of_mem hj S
    (x : ZMod (biasedModulus j S)) hmCandidate
  rw [IsBiasedCollision, hcandidate]
  exact hp

end Erdos486


/-! Flattened from Erdos486.FiniteAveraging. -/

/-!
# Finite averaging for Erdős Problem 486

This file gives elementary finite versions of the averaging principle and
Markov's inequality.  Everything is expressed using `Finset` and `Fintype`;
no measure-theoretic probability space is involved.

The final section evaluates the uniform average over four-colourings when one
of the four colours is designated black.
-/

open scoped BigOperators

namespace Erdos486

section Averages

variable {α 𝕜 : Type*}

/-- The average of `f` over a finite set.  It is defined to be zero on the
empty set, as follows from division by zero in a field. -/
def finsetAverage [Field 𝕜] (s : Finset α) (f : α → 𝕜) : 𝕜 :=
  (∑ x ∈ s, f x) / s.card

/-- The uniform average of a function on a finite type. -/
def fintypeAverage [Fintype α] [Field 𝕜] (f : α → 𝕜) : 𝕜 :=
  (∑ x, f x) / Fintype.card α

@[simp]
theorem finsetAverage_empty [Field 𝕜] (f : α → 𝕜) :
    finsetAverage ∅ f = 0 := by
  simp [finsetAverage]

@[simp]
theorem finsetAverage_const [Field 𝕜] [CharZero 𝕜] (s : Finset α)
    (hs : s.Nonempty) (c : 𝕜) :
    finsetAverage s (fun _ ↦ c) = c := by
  have hcard : (s.card : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
  rw [finsetAverage, Finset.sum_const, nsmul_eq_mul,
    mul_div_cancel_left₀ c hcard]

@[simp]
theorem fintypeAverage_const [Fintype α] [Nonempty α]
    [Field 𝕜] [CharZero 𝕜] (c : 𝕜) :
    fintypeAverage (fun _ : α ↦ c) = c := by
  have hcard : (Fintype.card α : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [fintypeAverage, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    mul_div_cancel_left₀ c hcard]

/-- A point of a nonempty finite set has value at most the average. -/
theorem exists_mem_le_finsetAverage [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (s : Finset α) (hs : s.Nonempty) (f : α → 𝕜) :
    ∃ x ∈ s, f x ≤ finsetAverage s f := by
  by_contra h
  push Not at h
  have hsum :
      ∑ x ∈ s, finsetAverage s f < ∑ x ∈ s, f x :=
    Finset.sum_lt_sum (fun x hx ↦ (h x hx).le)
      (hs.imp fun x hx ↦ ⟨hx, h x hx⟩)
  have hcard : (s.card : 𝕜) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have havg :
      ∑ x ∈ s, finsetAverage s f = ∑ x ∈ s, f x := by
    rw [Finset.sum_const, nsmul_eq_mul, finsetAverage,
      mul_div_cancel₀ _ hcard]
  rw [havg] at hsum
  exact (lt_irrefl _) hsum

/-- A function on a nonempty finite type takes a value at most its uniform
average. -/
theorem exists_le_fintypeAverage [Fintype α] [Nonempty α]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (f : α → 𝕜) :
    ∃ x, f x ≤ fintypeAverage f := by
  simpa [fintypeAverage, finsetAverage] using
    (exists_mem_le_finsetAverage (𝕜 := 𝕜) (Finset.univ : Finset α)
      Finset.univ_nonempty f)

/-- The direct probabilistic-method form: an upper bound for a finite average
is attained as an upper bound by at least one outcome. -/
theorem exists_le_of_fintypeAverage_le [Fintype α] [Nonempty α]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : α → 𝕜) {B : 𝕜}
    (haverage : fintypeAverage f ≤ B) :
    ∃ x, f x ≤ B := by
  obtain ⟨x, hx⟩ := exists_le_fintypeAverage f
  exact ⟨x, hx.trans haverage⟩

/-- The corresponding probabilistic-method form for an explicitly specified
nonempty finite set. -/
theorem exists_mem_le_of_finsetAverage_le [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (s : Finset α) (hs : s.Nonempty) (f : α → 𝕜) {B : 𝕜}
    (haverage : finsetAverage s f ≤ B) :
    ∃ x ∈ s, f x ≤ B := by
  obtain ⟨x, hxs, hx⟩ := exists_mem_le_finsetAverage s hs f
  exact ⟨x, hxs, hx.trans haverage⟩

/-- The average of a nonnegative function over a finite set is nonnegative. -/
theorem finsetAverage_nonneg [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (s : Finset α) (f : α → 𝕜)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ finsetAverage s f := by
  exact div_nonneg (Finset.sum_nonneg fun x hx ↦ hf x hx) (Nat.cast_nonneg _)

/-- The uniform average of a nonnegative function is nonnegative. -/
theorem fintypeAverage_nonneg [Fintype α] [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (f : α → 𝕜) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ fintypeAverage f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ ↦ hf x) (Nat.cast_nonneg _)

end Averages

section Markov

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Finite-sum Markov inequality.  The number of points in `s` at which
`t ≤ f x`, multiplied by `t`, is at most the total sum of a nonnegative
function.  No positivity assumption on `t` is needed for this unnormalized
form. -/
theorem finset_markov (s : Finset α) (f : α → 𝕜)
    (hf : ∀ x ∈ s, 0 ≤ f x) (t : 𝕜) :
    ((s.filter fun x ↦ t ≤ f x).card : 𝕜) * t ≤ ∑ x ∈ s, f x := by
  classical
  calc
    ((s.filter fun x ↦ t ≤ f x).card : 𝕜) * t =
        ∑ x ∈ s.filter fun x ↦ t ≤ f x, t := by
      simp
    _ ≤ ∑ x ∈ s.filter fun x ↦ t ≤ f x, f x := by
      exact Finset.sum_le_sum fun x hx ↦ (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x ∈ s, f x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun x hxs _ ↦ hf x hxs

/-- Markov's inequality on a finite type, stated purely as a cardinality and
a finite sum. -/
theorem fintype_markov [Fintype α] (f : α → 𝕜)
    (hf : ∀ x, 0 ≤ f x) (t : 𝕜) :
    ((Finset.univ.filter fun x ↦ t ≤ f x).card : 𝕜) * t ≤
      ∑ x, f x := by
  simpa using finset_markov (𝕜 := 𝕜) (Finset.univ : Finset α) f
    (fun x _ ↦ hf x) t

end Markov

noncomputable section FourColorings

variable {ι 𝕜 : Type*} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

/-- A four-colouring of a finite index type. -/
abbrev FourColoring (ι : Type*) := ι → Fin 4

/-- Colour `0` is black; this counts the black coordinates of a colouring. -/
def blackCount (c : FourColoring ι) : ℕ :=
  ((Finset.univ : Finset ι).filter fun i ↦ c i = 0).card

/-- There are exactly `4 ^ |ι|` four-colourings of `ι`. -/
theorem card_fourColoring :
    Fintype.card (FourColoring ι) = 4 ^ Fintype.card ι := by
  simp [FourColoring]

/-- The weight `2` for black and `1` for every other colour factors over the
coordinates of a colouring. -/
theorem two_pow_blackCount_eq_prod [CommSemiring 𝕜]
    (c : FourColoring ι) :
    (2 : 𝕜) ^ blackCount c =
      ∏ i : ι, if c i = 0 then (2 : 𝕜) else 1 := by
  classical
  rw [blackCount, ← Finset.prod_filter]
  simp

/-- Exact finite counting identity: summing `2^(number of black coordinates)`
over all four-colourings gives `5 ^ |ι|`. -/
theorem sum_two_pow_blackCount [CommSemiring 𝕜] :
    (∑ c : FourColoring ι, (2 : 𝕜) ^ blackCount c) =
      (5 : 𝕜) ^ Fintype.card ι := by
  classical
  calc
    (∑ c : FourColoring ι, (2 : 𝕜) ^ blackCount c) =
        ∑ c : FourColoring ι,
          ∏ i : ι, if c i = 0 then (2 : 𝕜) else 1 := by
      exact Finset.sum_congr rfl fun c _ ↦ two_pow_blackCount_eq_prod c
    _ = ∏ i : ι, ∑ colour : Fin 4,
          if colour = 0 then (2 : 𝕜) else 1 := by
      simpa [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset (R := 𝕜) (Finset.univ : Finset (Fin 4))
          (fun _ colour ↦ if colour = 0 then (2 : 𝕜) else 1))
    _ = ∏ _i : ι, (5 : 𝕜) := by
      congr 1
      funext i
      rw [Fin.sum_univ_four]
      norm_num [Fin.ext_iff]
    _ = (5 : 𝕜) ^ Fintype.card ι := by
      simp

/-- The exact uniform average of the black weight, simultaneously valid over
`ℚ`, `ℝ`, or any linear ordered field. -/
theorem fintypeAverage_two_pow_blackCount [Field 𝕜] [CharZero 𝕜] :
    fintypeAverage (fun c : FourColoring ι ↦ (2 : 𝕜) ^ blackCount c) =
      ((5 : 𝕜) / 4) ^ Fintype.card ι := by
  classical
  rw [fintypeAverage, sum_two_pow_blackCount, card_fourColoring]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact (div_pow (5 : 𝕜) 4 (Fintype.card ι)).symm

end FourColorings

end Erdos486


/-! Flattened from Erdos486.ColoringEnumeration. -/

/-!
# Weighted enumeration for the biased four-colouring argument

This file is a purely finite replacement for conditioning on anchor colours.
It proves that a product of one-coordinate weights read through an injective
oracle has the product of the corresponding one-coordinate averages.  The
biased candidate weight then has exact average

`(1 / 8) ^ |S| * (21 / 32) ^ (k - |S|)`.

For `k = 6r`, summing over all `S` and multiplying by `2 ^ (2r)` gives
exactly `(15625 / 16384) ^ (2r)`, which is at most
`(63 / 64) ^ (2r)`.  No probability or measure theory is used.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section ColoringEnumeration

/-! ## Product averages through an injective oracle -/

variable {α β κ ι : Type*}

/-- Uniform averages are invariant under a finite equivalence. -/
theorem fintypeAverage_comp_equiv [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℚ) :
    fintypeAverage (fun x ↦ f (e x)) = fintypeAverage f := by
  rw [fintypeAverage, fintypeAverage, e.sum_comp,
    Fintype.card_congr e]

/-- Averaging a function of the first coordinate over a nonempty finite
product is the same as averaging over the first coordinate. -/
theorem fintypeAverage_prod_fst [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℚ) :
    fintypeAverage (fun x : α × β ↦ f x.1) = fintypeAverage f := by
  classical
  have hα : (Fintype.card α : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum :
      (∑ x : α × β, f x.1) =
        (Fintype.card β : ℚ) * ∑ x : α, f x := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [Finset.mul_sum]
  rw [fintypeAverage, fintypeAverage, hsum, Fintype.card_prod,
    Nat.cast_mul]
  field_simp

/-- The complement of the range of an embedding, as an explicit subtype. -/
abbrev EmbeddingComplement (e : κ ↪ ι) :=
  {x : ι // x ∉ Set.range e}

/-- Split the target of an embedding into its range and its complement, with
the original domain as the range summand. -/
noncomputable def embeddingSplitEquiv [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι) : κ ⊕ EmbeddingComplement e ≃ ι := by
  classical
  exact
    (Equiv.sumCongr e.toEquivRange
      (Equiv.refl (EmbeddingComplement e))).trans
      (Equiv.sumCompl fun x : ι ↦ x ∈ Set.range e)

@[simp]
theorem embeddingSplitEquiv_apply_inl [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι) (j : κ) :
    embeddingSplitEquiv e (Sum.inl j) = e j := by
  classical
  rfl

/-- A colouring of the target of an embedding is equivalently a colouring of
the embedded coordinates together with a colouring of the complement. -/
noncomputable def oracleColoringEquiv [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι) :
    (FourColoring κ × FourColoring (EmbeddingComplement e)) ≃
      FourColoring ι :=
  (Equiv.sumArrowEquivProdArrow κ (EmbeddingComplement e) (Fin 4)).symm |>.trans
    ((embeddingSplitEquiv e).arrowCongr (Equiv.refl (Fin 4)))

@[simp]
theorem oracleColoringEquiv_apply_embedding [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι)
    (c : FourColoring κ × FourColoring (EmbeddingComplement e)) (j : κ) :
    oracleColoringEquiv e c (e j) = c.1 j := by
  classical
  have hsplit : (embeddingSplitEquiv e).symm (e j) = Sum.inl j := by
    apply (embeddingSplitEquiv e).injective
    simp
  change
    (Equiv.sumArrowEquivProdArrow κ (EmbeddingComplement e) (Fin 4)).symm c
        ((embeddingSplitEquiv e).symm (e j)) = c.1 j
  rw [hsplit]
  rcases c with ⟨c₁, c₂⟩
  exact Equiv.sumArrowEquivProdArrow_symm_apply_inl c₁ c₂ j

/-- Independent coordinate enumeration on a full finite function space. -/
theorem fintypeAverage_pi_prod [Fintype κ] [DecidableEq κ]
    (weight : κ → Fin 4 → ℚ) :
    fintypeAverage
        (fun c : FourColoring κ ↦ ∏ j, weight j (c j)) =
      ∏ j, (∑ colour : Fin 4, weight j colour) / 4 := by
  classical
  have hsum :
      (∑ c : FourColoring κ, ∏ j, weight j (c j)) =
        ∏ j, ∑ colour : Fin 4, weight j colour := by
    simpa [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (R := ℚ)
        (Finset.univ : Finset (Fin 4)) weight)
  have hcard : Fintype.card (FourColoring κ) =
      4 ^ Fintype.card κ := by
    simp [FourColoring]
  rw [fintypeAverage, hsum, hcard]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  symm
  calc
    (∏ j, (∑ colour : Fin 4, weight j colour) / 4) =
        (∏ j, ∑ colour : Fin 4, weight j colour) /
          ∏ _j : κ, (4 : ℚ) := by
      exact Finset.prod_div_distrib _ _
    _ = (∏ j, ∑ colour : Fin 4, weight j colour) /
        4 ^ Fintype.card κ := by
      simp

/-- Generic oracle-product lemma.  Distinct oracle indices read distinct
coordinates of the four-colouring, so their uniform weighted average factors
exactly. -/
theorem expect_oracle_prod_embedding [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (oracle : κ ↪ ι) (weight : κ → Fin 4 → ℚ) :
    fintypeAverage
        (fun c : FourColoring ι ↦
          ∏ j, weight j (c (oracle j))) =
      ∏ j, (∑ colour : Fin 4, weight j colour) / 4 := by
  let E := oracleColoringEquiv oracle
  calc
    fintypeAverage
        (fun c : FourColoring ι ↦
          ∏ j, weight j (c (oracle j))) =
        fintypeAverage
          (fun c : FourColoring κ × FourColoring (EmbeddingComplement oracle) ↦
            ∏ j, weight j ((E c) (oracle j))) := by
      exact (fintypeAverage_comp_equiv E _).symm
    _ = fintypeAverage
          (fun c : FourColoring κ × FourColoring (EmbeddingComplement oracle) ↦
            ∏ j, weight j (c.1 j)) := by
      congr 1
      funext c
      apply Fintype.prod_congr
      intro j
      exact congrArg (weight j) (by simp [E])
    _ = fintypeAverage
          (fun c : FourColoring κ ↦ ∏ j, weight j (c j)) := by
      exact fintypeAverage_prod_fst
        (α := FourColoring κ)
        (β := FourColoring (EmbeddingComplement oracle))
        (fun c : FourColoring κ ↦ ∏ j, weight j (c j))
    _ = ∏ j, (∑ colour : Fin 4, weight j colour) / 4 :=
      fintypeAverage_pi_prod weight

/-! ## One-coordinate weights -/

/-- Weight `1/2` on black and `1` on each non-black colour. -/
def halfBlackWeight (colour : Fin 4) : ℚ :=
  if colour = 0 then 1 / 2 else 1

/-- A selected anchor must be black and contributes its `1/2` weight. -/
def selectedAnchorWeight (colour : Fin 4) : ℚ :=
  if colour = 0 then 1 / 2 else 0

/-- A fresh query must be non-black. -/
def nonblackQueryWeight (colour : Fin 4) : ℚ :=
  if colour = 0 then 0 else 1

theorem average_selectedAnchorWeight :
    (∑ colour : Fin 4, selectedAnchorWeight colour) / 4 =
      (1 : ℚ) / 8 := by
  rw [Fin.sum_univ_four]
  norm_num [selectedAnchorWeight, Fin.ext_iff]

theorem average_halfBlackWeight :
    (∑ colour : Fin 4, halfBlackWeight colour) / 4 =
      (7 : ℚ) / 8 := by
  rw [Fin.sum_univ_four]
  norm_num [halfBlackWeight, Fin.ext_iff]

theorem average_nonblackQueryWeight :
    (∑ colour : Fin 4, nonblackQueryWeight colour) / 4 =
      (3 : ℚ) / 4 := by
  rw [Fin.sum_univ_four]
  norm_num [nonblackQueryWeight, Fin.ext_iff]

/-! ## Candidate oracle and its exact weighted average -/

/-- Oracle indices consist of all anchors and one fresh query for each index
outside `S`. -/
abbrev CandidateOracleIndex {k : ℕ} (S : Finset (Fin k)) :=
  Fin k ⊕ ↥(Sᶜ)

/-- The oracle sends the left summand to anchors and the right summand to
fresh query coordinates. -/
def candidateOracle {k : ℕ} {ι : Type*} (anchor query : Fin k → ι)
    (S : Finset (Fin k)) : CandidateOracleIndex S → ι
  | Sum.inl i => anchor i
  | Sum.inr i => query i.1

/-- Local factors whose product is the weighted indicator of candidate `S`. -/
def candidateOracleWeight {k : ℕ} (S : Finset (Fin k)) :
    CandidateOracleIndex S → Fin 4 → ℚ
  | Sum.inl i =>
      if i ∈ S then selectedAnchorWeight else halfBlackWeight
  | Sum.inr _ => nonblackQueryWeight

/-- Weighted indicator of candidate `S` in a four-colouring. -/
def weightedCandidate {k : ℕ} {ι : Type*} (anchor query : Fin k → ι)
    (S : Finset (Fin k)) (c : FourColoring ι) : ℚ :=
  ∏ o : CandidateOracleIndex S,
    candidateOracleWeight S o (c (candidateOracle anchor query S o))

/-- Product of two constants selected by membership in a subset of `Fin k`. -/
theorem prod_ite_mem_fin {k : ℕ} (S : Finset (Fin k)) (a b : ℚ) :
    (∏ i : Fin k, if i ∈ S then a else b) =
      a ^ S.card * b ^ (k - S.card) := by
  classical
  rw [Finset.prod_ite]
  have hS : (Finset.univ.filter fun i : Fin k ↦ i ∈ S) = S := by
    ext i
    simp
  have hSc : (Finset.univ.filter fun i : Fin k ↦ ¬i ∈ S) = Sᶜ := by
    ext i
    simp
  rw [hS, hSc]
  simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

/-- The biased candidate has the advertised exact weighted average.  The
injectivity hypothesis packages injectivity of anchors, fresh queries, and
disjointness between those two coordinate families. -/
theorem average_weightedCandidate {k : ℕ} [Fintype ι] [DecidableEq ι]
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (horacle : Function.Injective (candidateOracle anchor query S)) :
    fintypeAverage (weightedCandidate anchor query S) =
      ((1 : ℚ) / 8) ^ S.card *
        ((21 : ℚ) / 32) ^ (k - S.card) := by
  classical
  let oracle : CandidateOracleIndex S ↪ ι :=
    ⟨candidateOracle anchor query S, horacle⟩
  unfold weightedCandidate
  change fintypeAverage
      (fun c : FourColoring ι ↦
        ∏ o, candidateOracleWeight S o (c (oracle o))) = _
  rw [expect_oracle_prod_embedding oracle (candidateOracleWeight S)]
  rw [Fintype.prod_sum_type]
  have hanchor :
      (∏ i : Fin k,
        (∑ colour : Fin 4,
          candidateOracleWeight S (Sum.inl i) colour) / 4) =
        ((1 : ℚ) / 8) ^ S.card *
          ((7 : ℚ) / 8) ^ (k - S.card) := by
    have hlocal : ∀ i : Fin k,
        (∑ colour : Fin 4,
          candidateOracleWeight S (Sum.inl i) colour) / 4 =
          if i ∈ S then (1 : ℚ) / 8 else 7 / 8 := by
      intro i
      by_cases hi : i ∈ S
      · simp [candidateOracleWeight, hi, average_selectedAnchorWeight]
      · simp [candidateOracleWeight, hi, average_halfBlackWeight]
    simp_rw [hlocal]
    exact prod_ite_mem_fin S ((1 : ℚ) / 8) (7 / 8)
  have hquery :
      (∏ i : ↥(Sᶜ),
        (∑ colour : Fin 4,
          candidateOracleWeight S (Sum.inr i) colour) / 4) =
        ((3 : ℚ) / 4) ^ (k - S.card) := by
    simp only [candidateOracleWeight, average_nonblackQueryWeight,
      Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_coe, Finset.card_compl,
      Fintype.card_fin]
  rw [hanchor, hquery]
  have hcombine :
      ((7 : ℚ) / 8) ^ (k - S.card) *
          ((3 : ℚ) / 4) ^ (k - S.card) =
        ((21 : ℚ) / 32) ^ (k - S.card) := by
    rw [← mul_pow]
    norm_num
  rw [mul_assoc, hcombine]

/-! ## Pointwise domination on the good event -/

/-- Number of black anchor coordinates. -/
def anchorBlackCount {k : ℕ} {ι : Type*} (anchor : Fin k → ι)
    (c : FourColoring ι) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦
    c (anchor i) = 0).card

/-- Candidate `S` occurs when its anchors are black and every fresh query is
non-black. -/
def CandidateOccurs {k : ℕ} {ι : Type*} (anchor query : Fin k → ι)
    (S : Finset (Fin k)) (c : FourColoring ι) : Prop :=
  (∀ i ∈ S, c (anchor i) = 0) ∧
    ∀ i, i ∉ S → c (query i) ≠ 0

theorem half_pow_anchorBlackCount_eq_prod {k : ℕ} {ι : Type*}
    (anchor : Fin k → ι) (c : FourColoring ι) :
    ((1 : ℚ) / 2) ^ anchorBlackCount anchor c =
      ∏ i : Fin k, halfBlackWeight (c (anchor i)) := by
  classical
  rw [anchorBlackCount]
  calc
    ((1 : ℚ) / 2) ^
        ((Finset.univ : Finset (Fin k)).filter fun i ↦
          c (anchor i) = 0).card =
        ∏ i ∈ (Finset.univ : Finset (Fin k)).filter
          (fun i ↦ c (anchor i) = 0), ((1 : ℚ) / 2) := by
      simp
    _ = ∏ i : Fin k,
        if c (anchor i) = 0 then (1 : ℚ) / 2 else 1 := by
      rw [Finset.prod_filter]
    _ = ∏ i : Fin k, halfBlackWeight (c (anchor i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      simp [halfBlackWeight]

/-- On an occurring candidate, the weighted indicator is exactly
`(1/2)^(number of black anchors)`. -/
theorem weightedCandidate_eq_half_pow {k : ℕ} {ι : Type*}
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (c : FourColoring ι) (hoccurs : CandidateOccurs anchor query S c) :
    weightedCandidate anchor query S c =
      ((1 : ℚ) / 2) ^ anchorBlackCount anchor c := by
  classical
  rw [weightedCandidate, Fintype.prod_sum_type]
  have hanchor :
      (∏ i : Fin k,
        candidateOracleWeight S (Sum.inl i)
          (c (candidateOracle anchor query S (Sum.inl i)))) =
        ∏ i : Fin k, halfBlackWeight (c (anchor i)) := by
    apply Finset.prod_congr rfl
    intro i _hi
    by_cases hiS : i ∈ S
    · simp [candidateOracle, candidateOracleWeight, hiS,
        hoccurs.1 i hiS, selectedAnchorWeight, halfBlackWeight]
    · simp [candidateOracle, candidateOracleWeight, hiS]
  have hquery :
      (∏ i : ↥(Sᶜ),
        candidateOracleWeight S (Sum.inr i)
          (c (candidateOracle anchor query S (Sum.inr i)))) = 1 := by
    apply Finset.prod_eq_one
    intro i _hi
    have hiS : (i : Fin k) ∉ S := Finset.mem_compl.mp i.property
    simp [candidateOracle, candidateOracleWeight, nonblackQueryWeight,
      hoccurs.2 i hiS]
  rw [hanchor, hquery, mul_one, ← half_pow_anchorBlackCount_eq_prod]

/-- If `t ≤ 2r`, then `1 ≤ 2^(2r) (1/2)^t`. -/
theorem one_le_two_pow_mul_half_pow {r t : ℕ} (ht : t ≤ 2 * r) :
    (1 : ℚ) ≤ 2 ^ (2 * r) * ((1 : ℚ) / 2) ^ t := by
  have hexponent : 2 * r = t + (2 * r - t) := by omega
  have hcancel :
      (2 : ℚ) ^ t * ((1 : ℚ) / 2) ^ t = 1 := by
    rw [← mul_pow]
    norm_num
  have hscaled :
      (2 : ℚ) ^ (2 * r) * ((1 : ℚ) / 2) ^ t =
        2 ^ (2 * r - t) := by
    calc
      (2 : ℚ) ^ (2 * r) * ((1 : ℚ) / 2) ^ t =
          2 ^ (t + (2 * r - t)) * ((1 : ℚ) / 2) ^ t := by
        rw [← hexponent]
      _ = 2 ^ t * 2 ^ (2 * r - t) * ((1 : ℚ) / 2) ^ t := by
        rw [pow_add]
      _ = 2 ^ (2 * r - t) *
          ((2 : ℚ) ^ t * ((1 : ℚ) / 2) ^ t) := by
        ring
      _ = 2 ^ (2 * r - t) := by rw [hcancel, mul_one]
  calc
    (1 : ℚ) ≤ 2 ^ (2 * r - t) := one_le_pow₀ (by norm_num)
    _ = 2 ^ (2 * r) * ((1 : ℚ) / 2) ^ t := hscaled.symm

/-- Pointwise domination used on the good event. -/
theorem one_le_scaled_weightedCandidate_of_good {k r : ℕ} {ι : Type*}
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (c : FourColoring ι)
    (hgood : anchorBlackCount anchor c ≤ 2 * r)
    (hoccurs : CandidateOccurs anchor query S c) :
    (1 : ℚ) ≤ 2 ^ (2 * r) * weightedCandidate anchor query S c := by
  rw [weightedCandidate_eq_half_pow anchor query S c hoccurs]
  exact one_le_two_pow_mul_half_pow hgood

/-! ## Weighted subset sum -/

/-- The subset expansion used in the weighted union bound.  This is the
constant-factor specialization of `Finset.prod_add`. -/
theorem weighted_subset_sum (k : ℕ) (a b : ℚ) :
    (∑ S : Finset (Fin k), a ^ S.card * b ^ (k - S.card)) =
      (a + b) ^ k := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin k) a b

/-- Exact arithmetic for `k = 6r`. -/
theorem scaled_weighted_subset_sum_eq (r : ℕ) :
    (2 : ℚ) ^ (2 * r) *
        (∑ S : Finset (Fin (6 * r)),
          ((1 : ℚ) / 8) ^ S.card *
            ((21 : ℚ) / 32) ^ (6 * r - S.card)) =
      ((15625 : ℚ) / 16384) ^ (2 * r) := by
  rw [weighted_subset_sum]
  have hbase : (1 : ℚ) / 8 + 21 / 32 = 25 / 32 := by norm_num
  rw [hbase]
  have hexponent : 6 * r = 3 * (2 * r) := by omega
  have hpow : ((25 : ℚ) / 32) ^ (6 * r) =
      (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := by
    rw [hexponent, pow_mul]
  rw [hpow, ← mul_pow]
  norm_num

/-- Numerical weighted subset-sum bound used by the finite block. -/
theorem scaled_weighted_subset_sum_le (r : ℕ) :
    (2 : ℚ) ^ (2 * r) *
        (∑ S : Finset (Fin (6 * r)),
          ((1 : ℚ) / 8) ^ S.card *
            ((21 : ℚ) / 32) ^ (6 * r - S.card)) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  rw [scaled_weighted_subset_sum_eq]
  exact pow_le_pow_left₀ (by norm_num)
    (by norm_num : (15625 : ℚ) / 16384 ≤ 63 / 64) _

/-- Direct form after replacing every candidate's weighted average by its
exact oracle-product value. -/
theorem scaled_sum_average_weightedCandidate_le [Fintype ι] [DecidableEq ι]
    (r : ℕ) (anchor : Fin (6 * r) → ι)
    (query : Finset (Fin (6 * r)) → Fin (6 * r) → ι)
    (horacle : ∀ S,
      Function.Injective (candidateOracle anchor (query S) S)) :
    (2 : ℚ) ^ (2 * r) *
        (∑ S : Finset (Fin (6 * r)),
          fintypeAverage (weightedCandidate anchor (query S) S)) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  have havg : ∀ S : Finset (Fin (6 * r)),
      fintypeAverage (weightedCandidate anchor (query S) S) =
        ((1 : ℚ) / 8) ^ S.card *
          ((21 : ℚ) / 32) ^ (6 * r - S.card) := by
    intro S
    exact average_weightedCandidate anchor (query S) S (horacle S)
  simp_rw [havg]
  exact scaled_weighted_subset_sum_le r

end ColoringEnumeration

end Erdos486


/-! Flattened from Erdos486.BiasedCandidateGeometry. -/

/-!
# Candidate-oracle geometry for the biased block

Outside the arithmetic collision union, the anchor coordinates and all fresh
candidate queries form an injective oracle family.  This is the exact bridge
between the modular arithmetic and the generic finite-colouring enumeration.
-/

namespace Erdos486

/-- Anchor queried at prime `i` by a common-period representative `x`. -/
noncomputable def biasedAnchor (j x : ℕ) (i : Fin (biasedK j)) :
    BiasedCoordinate j :=
  endpointCoordinate j x i

/-- Query made by the canonical candidate for subset `S`. -/
noncomputable def biasedQuery (j x : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    BiasedCoordinate j :=
  endpointCoordinate j
    (biasedCandidate j S (x : ZMod (biasedModulus j S))) i

/-- `S` has an actual endpoint representative for the residue of `x`. -/
def HasBiasedCandidate (j x : ℕ)
    (S : Finset (Fin (biasedK j))) : Prop :=
  biasedCandidate j S (x : ZMod (biasedModulus j S)) ∈
    candidateEndpoints j S (x : ZMod (biasedModulus j S))

/-- No subset/index collision occurs at `x`. -/
def HasNoBiasedCollision (j x : ℕ) : Prop :=
  ∀ (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)),
    i ∉ S → ¬IsBiasedCollision j S i x

theorem biasedQuery_eq_anchor_of_mem {j x : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j))
    (hi : i ∈ S) (hvalid : HasBiasedCandidate j x S) :
    biasedQuery j x S i = biasedAnchor j x i := by
  apply Sigma.ext
  · rfl
  · simp only [biasedQuery, biasedAnchor, endpointCoordinate]
    have hq :
        (biasedCandidate j S (x : ZMod (biasedModulus j S)) :
            ZMod (biasedModulus j S)) =
          (x : ZMod (biasedModulus j S)) := by
      exact (Finset.mem_filter.mp hvalid).2
    have hpq : skeletonPrime (biasedK j) i ∣ biasedModulus j S :=
      (skeletonPrime_dvd_biasedModulus_iff j S i).2 hi
    have := congrArg (ZMod.castHom hpq
      (ZMod (skeletonPrime (biasedK j) i))) hq
    simpa [ZMod.castHom_apply] using this

/-- Outside collisions, the combined anchor/fresh-query oracle is injective. -/
theorem biasedCandidateOracle_injective {j x : ℕ}
    (hno : HasNoBiasedCollision j x)
    (S : Finset (Fin (biasedK j))) :
    Function.Injective
      (candidateOracle (biasedAnchor j x) (biasedQuery j x S) S) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl i' =>
          have hi : i = i' := congrArg Sigma.fst hab
          cases hi
          rfl
      | inr i' =>
          have hi : i = i'.1 := congrArg Sigma.fst hab
          subst i
          have hcollision : IsBiasedCollision j S i'.1 x := by
            unfold IsBiasedCollision
            have hab' :
                endpointCoordinate j x i'.1 =
                  endpointCoordinate j
                    (biasedCandidate j S (x : ZMod (biasedModulus j S))) i'.1 := by
              simpa [candidateOracle, biasedAnchor, biasedQuery] using hab
            exact eq_of_heq (Sigma.mk.inj_iff.mp hab').2
          have hi' : i'.1 ∉ S := Finset.mem_compl.mp i'.property
          exact (hno S i'.1 hi' hcollision).elim
  | inr i =>
      cases b with
      | inl i' =>
          have hi : i.1 = i' := congrArg Sigma.fst hab
          subst i'
          have hcollision : IsBiasedCollision j S i.1 x := by
            unfold IsBiasedCollision
            have hab' :
                endpointCoordinate j x i.1 =
                  endpointCoordinate j
                    (biasedCandidate j S (x : ZMod (biasedModulus j S))) i.1 := by
              simpa [candidateOracle, biasedAnchor, biasedQuery] using hab.symm
            exact eq_of_heq (Sigma.mk.inj_iff.mp hab').2
          have hi' : i.1 ∉ S := Finset.mem_compl.mp i.property
          exact (hno S i.1 hi' hcollision).elim
      | inr i' =>
          have hi : i.1 = i'.1 := congrArg Sigma.fst hab
          have hii' : i = i' := Subtype.ext hi
          subst i'
          rfl

/-- If a colouring selects exactly `S` at its canonical valid candidate,
then the generic candidate event occurs. -/
theorem candidateOccurs_of_selectedPrimes_eq {j x : ℕ}
    (S : Finset (Fin (biasedK j))) (c : BiasedColoring j)
    (hvalid : HasBiasedCandidate j x S)
    (hselected : selectedPrimes j c
      (biasedCandidate j S (x : ZMod (biasedModulus j S))) = S) :
    CandidateOccurs (biasedAnchor j x) (biasedQuery j x S) S c := by
  constructor
  · intro i hi
    have hmem : i ∈ selectedPrimes j c
        (biasedCandidate j S (x : ZMod (biasedModulus j S))) := by
      rw [hselected]
      exact hi
    have hquery : c (biasedQuery j x S i) = 0 := by
      simpa [biasedQuery] using
        (mem_selectedPrimes_iff j c
          (biasedCandidate j S (x : ZMod (biasedModulus j S))) i).1 hmem
    rw [biasedQuery_eq_anchor_of_mem S i hi hvalid] at hquery
    exact hquery
  · intro i hi hblack
    have hmem : i ∈ selectedPrimes j c
        (biasedCandidate j S (x : ZMod (biasedModulus j S))) := by
      rw [mem_selectedPrimes_iff]
      exact hblack
    rw [hselected] at hmem
    exact hi hmem

/-- Footprint membership supplies a valid canonical subset candidate. -/
theorem exists_candidate_of_isBiasedCovered {j : ℕ} (hj : 400 ≤ j)
    (c : BiasedColoring j) (x : ZMod (biasedPeriod j))
    (hcovered : IsBiasedCovered j c x) :
    ∃ S : Finset (Fin (biasedK j)),
      HasBiasedCandidate j x.val S ∧
        selectedPrimes j c
          (biasedCandidate j S (x.val : ZMod (biasedModulus j S))) = S := by
  rcases hcovered with ⟨m, hm, hx⟩
  let S := selectedPrimes j c m
  let _ : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  have hx' :
      (x.val : ZMod (biasedModulus j S)) =
        (m : ZMod (biasedModulus j S)) := by
    calc
      (x.val : ZMod (biasedModulus j S)) =
          reduceBiasedPeriod j S x := by
            simp [reduceBiasedPeriod, ZMod.castHom_apply]
      _ = (m : ZMod (biasedModulus j S)) := hx
  have hmCandidate : m ∈
      candidateEndpoints j S (x.val : ZMod (biasedModulus j S)) := by
    rw [candidateEndpoints, Finset.mem_filter]
    exact ⟨hm, hx'.symm⟩
  have hcandidate :
      biasedCandidate j S (x.val : ZMod (biasedModulus j S)) = m :=
    biasedCandidate_eq_of_mem hj S _ hmCandidate
  refine ⟨S, ?_, ?_⟩
  · change biasedCandidate j S (x.val : ZMod (biasedModulus j S)) ∈
        candidateEndpoints j S (x.val : ZMod (biasedModulus j S))
    rw [hcandidate]
    exact hmCandidate
  · exact hcandidate ▸ rfl

end Erdos486


/-! Flattened from Erdos486.BiasedNumerics. -/

/-!
# Exact numerical inequalities for the biased finite block

All estimates are over `ℚ`, so the later finite counting argument uses no
floating-point approximations or transcendental inequalities.
-/

namespace Erdos486

/-- A crude exponential bound that absorbs the linear collision factor. -/
theorem six_mul_le_two_pow_four_mul_add_two (r : ℕ) :
    6 * r ≤ 2 ^ (4 * r + 2) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [show 4 * (r + 1) + 2 = (4 * r + 2) + 4 by omega, pow_add]
      norm_num
      have hpow : 0 < 2 ^ (4 * r + 2) := by positivity
      omega

theorem six_mul_two_pow_le (r : ℕ) :
    6 * r * 2 ^ (2 * r) ≤ 2 ^ (6 * r + 2) := by
  calc
    6 * r * 2 ^ (2 * r) ≤ 2 ^ (4 * r + 2) * 2 ^ (2 * r) :=
      Nat.mul_le_mul_right _ (six_mul_le_two_pow_four_mul_add_two r)
    _ = 2 ^ (6 * r + 2) := by
      rw [← pow_add]
      congr 1
      omega

/-- The union-bound collision term is absorbed by one copy of the target
geometric error. -/
theorem collision_numeric_le (r : ℕ) :
    ((6 * r : ℕ) : ℚ) / (2 : ℚ) ^ (6 * r + 2) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ (6 * r + 2) := by positivity
  have htwo :
      ((6 * r : ℕ) : ℚ) / (2 : ℚ) ^ (6 * r + 2) ≤
        1 / (2 : ℚ) ^ (2 * r) := by
    rw [div_le_div_iff₀ hpowpos (by positivity : (0 : ℚ) < (2 : ℚ) ^ (2 * r))]
    simp only [one_mul]
    exact_mod_cast six_mul_two_pow_le r
  calc
    ((6 * r : ℕ) : ℚ) / (2 : ℚ) ^ (6 * r + 2) ≤
        1 / (2 : ℚ) ^ (2 * r) := htwo
    _ = ((1 : ℚ) / 2) ^ (2 * r) := by
      rw [div_pow]
      simp
    _ ≤ ((63 : ℚ) / 64) ^ (2 * r) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Markov's bad-anchor term is no larger than the target error. -/
theorem bad_anchor_numeric_le (r : ℕ) :
    ((125 : ℚ) / 128) ^ (2 * r) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- The weighted good-anchor sum is no larger than the target error. -/
theorem weighted_good_numeric_le (r : ℕ) :
    (2 : ℚ) ^ (2 * r) * ((25 : ℚ) / 32) ^ (6 * r) ≤
      ((63 : ℚ) / 64) ^ (2 * r) := by
  have h25 :
      ((25 : ℚ) / 32) ^ (6 * r) =
        (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := by
    calc
      ((25 : ℚ) / 32) ^ (6 * r) =
          ((25 : ℚ) / 32) ^ (3 * (2 * r)) := by
        congr 1
        omega
      _ = (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := pow_mul _ _ _
  calc
    (2 : ℚ) ^ (2 * r) * ((25 : ℚ) / 32) ^ (6 * r) =
        (2 : ℚ) ^ (2 * r) * (((25 : ℚ) / 32) ^ 3) ^ (2 * r) := by
      rw [h25]
    _ = ((2 : ℚ) * (((25 : ℚ) / 32) ^ 3)) ^ (2 * r) :=
      (mul_pow (2 : ℚ) (((25 : ℚ) / 32) ^ 3) (2 * r)).symm
    _ =
        ((15625 : ℚ) / 16384) ^ (2 * r) := by
      norm_num
    _ ≤ ((63 : ℚ) / 64) ^ (2 * r) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- The complete collision/bad-anchor/good-anchor budget. -/
theorem three_error_terms_le_eta (r : ℕ)
    {collision bad good : ℚ}
    (hcollision : collision ≤ ((63 : ℚ) / 64) ^ (2 * r))
    (hbad : bad ≤ ((63 : ℚ) / 64) ^ (2 * r))
    (hgood : good ≤ ((63 : ℚ) / 64) ^ (2 * r)) :
    collision + bad + good ≤
      3 * ((63 : ℚ) / 64) ^ (2 * r) := by
  linarith

end Erdos486


/-! Flattened from Erdos486.BiasedCollisionUnion. -/

/-!
# Union bound for biased-colouring collisions

This file takes the union, in one explicit common period, of the collision
events indexed by all pairs `(S, i)` with `i ∉ S`.  The exact single-event
count from `BiasedCollision` and a finite union bound reduce its normalized
cardinality to the numerical estimate `collision_numeric_le`.
-/

open scoped BigOperators

namespace Erdos486

/-- Representatives in the common period satisfying the collision relation
for one pair `(S, i)`. -/
noncomputable def biasedCollisionResidues (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) : Finset ℕ := by
  classical
  exact (Finset.range (biasedPeriod j)).filter (IsBiasedCollision j S i)

theorem biasedCollisionResidues_card (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    (biasedCollisionResidues j S i).card = biasedCollisionCount j S i := by
  classical
  simp only [biasedCollisionResidues, biasedCollisionCount,
    Nat.count_eq_card_filter_range]

/-- All valid collision indices `(S, i)`, with `S` ranging over the complete
powerset and `i` restricted by `i ∉ S`. -/
def biasedCollisionIndices (j : ℕ) :
    Finset (Finset (Fin (biasedK j)) × Fin (biasedK j)) :=
  ((Finset.univ.powerset).product Finset.univ).filter fun a ↦ a.2 ∉ a.1

@[simp]
theorem mem_biasedCollisionIndices_iff (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    (S, i) ∈ biasedCollisionIndices j ↔ i ∉ S := by
  simp [biasedCollisionIndices]

/-- The union of all collisions in one common period. -/
noncomputable def biasedCollisionUnion (j : ℕ) : Finset ℕ := by
  classical
  exact (biasedCollisionIndices j).biUnion fun a ↦
    biasedCollisionResidues j a.1 a.2

/-- Rational normalized cardinality of the full collision union. -/
noncomputable def biasedCollisionUnionRatio (j : ℕ) : ℚ :=
  ((biasedCollisionUnion j).card : ℚ) / (biasedPeriod j : ℚ)

/-- Every collision index contributes exactly reciprocal-prime density. -/
theorem biasedCollisionResidues_ratio_eq {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    ((biasedCollisionResidues j S i).card : ℚ) / (biasedPeriod j : ℚ) =
      1 / (skeletonPrime (biasedK j) i : ℚ) := by
  rw [biasedCollisionResidues_card]
  have hN : (biasedPeriod j : ℚ) ≠ 0 := by
    exact_mod_cast (biasedPeriod_pos j).ne'
  have hp : (skeletonPrime (biasedK j) i : ℚ) ≠ 0 := by
    exact_mod_cast (skeletonPrime_spec (biasedK j) i).1.ne_zero
  rw [div_eq_div_iff hN hp]
  norm_num
  have hcount := skeletonPrime_mul_biasedCollisionCount_eq_period S i hi
  rw [Nat.mul_comm] at hcount
  exact_mod_cast hcount

/-- A prime at any coordinate is bounded below by the common scale
`2^(2k+2)`. -/
theorem twoPow_two_mul_add_two_le_skeletonPrime (j : ℕ)
    (i : Fin (biasedK j)) :
    2 ^ (2 * biasedK j + 2) ≤ skeletonPrime (biasedK j) i := by
  have hexp : biasedK j + 1 ≤ biasedK j + i.val + 1 := by omega
  have hfour : 4 ^ (biasedK j + 1) ≤
      4 ^ (biasedK j + i.val + 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hprime := (skeletonPrime_spec (biasedK j) i).2.1
  calc
    2 ^ (2 * biasedK j + 2) = 4 ^ (biasedK j + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      congr 2
    _ ≤ 4 ^ (biasedK j + i.val + 1) := hfour
    _ ≤ skeletonPrime (biasedK j) i := hprime.le

/-- Uniform reciprocal bound for every valid pair. -/
theorem biasedCollisionResidues_ratio_le {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    ((biasedCollisionResidues j S i).card : ℚ) / (biasedPeriod j : ℚ) ≤
      1 / (2 : ℚ) ^ (2 * biasedK j + 2) := by
  rw [biasedCollisionResidues_ratio_eq S i hi]
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast twoPow_two_mul_add_two_le_skeletonPrime j i

/-- There are at most `2^k k` valid pairs `(S, i)`. -/
theorem biasedCollisionIndices_card_le (j : ℕ) :
    (biasedCollisionIndices j).card ≤ 2 ^ biasedK j * biasedK j := by
  calc
    (biasedCollisionIndices j).card ≤
        ((Finset.univ.powerset : Finset (Finset (Fin (biasedK j)))).product
          (Finset.univ : Finset (Fin (biasedK j)))).card := by
      unfold biasedCollisionIndices
      exact Finset.card_filter_le _ _
    _ = 2 ^ biasedK j * biasedK j := by
      simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_powerset,
        Finset.card_univ, Fintype.card_fin]

/-- The normalized union cardinal is bounded by the number of valid pairs
times the uniform reciprocal-prime bound. -/
theorem biasedCollisionUnionRatio_le_index_bound (j : ℕ) :
    biasedCollisionUnionRatio j ≤
      ((biasedCollisionIndices j).card : ℚ) *
        (1 / (2 : ℚ) ^ (2 * biasedK j + 2)) := by
  classical
  have hcard : (biasedCollisionUnion j).card ≤
      ∑ a ∈ biasedCollisionIndices j,
        (biasedCollisionResidues j a.1 a.2).card := by
    unfold biasedCollisionUnion
    exact Finset.card_biUnion_le
  have hcardQ : ((biasedCollisionUnion j).card : ℚ) ≤
      ∑ a ∈ biasedCollisionIndices j,
        ((biasedCollisionResidues j a.1 a.2).card : ℚ) := by
    exact_mod_cast hcard
  calc
    biasedCollisionUnionRatio j =
        ((biasedCollisionUnion j).card : ℚ) / (biasedPeriod j : ℚ) := rfl
    _ ≤ (∑ a ∈ biasedCollisionIndices j,
          ((biasedCollisionResidues j a.1 a.2).card : ℚ)) /
          (biasedPeriod j : ℚ) :=
      div_le_div_of_nonneg_right hcardQ (by positivity)
    _ = ∑ a ∈ biasedCollisionIndices j,
          ((biasedCollisionResidues j a.1 a.2).card : ℚ) /
            (biasedPeriod j : ℚ) := by
      rw [Finset.sum_div]
    _ ≤ ∑ _a ∈ biasedCollisionIndices j,
          1 / (2 : ℚ) ^ (2 * biasedK j + 2) := by
      apply Finset.sum_le_sum
      intro a ha
      exact biasedCollisionResidues_ratio_le a.1 a.2
        ((mem_biasedCollisionIndices_iff j a.1 a.2).mp ha)
    _ = ((biasedCollisionIndices j).card : ℚ) *
          (1 / (2 : ℚ) ^ (2 * biasedK j + 2)) := by
      simp

/-- Cancellation of the powers of two appearing in the union bound. -/
theorem powerset_collision_ratio_identity (k : ℕ) :
    (((2 ^ k * k : ℕ) : ℚ) *
        (1 / (2 : ℚ) ^ (2 * k + 2))) =
      (k : ℚ) / (2 : ℚ) ^ (k + 2) := by
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show 2 * k + 2 = k + (k + 2) by omega, pow_add]
  field_simp

/-- The full finite union is bounded by the elementary collision term
`k / 2^(k+2)`. -/
theorem biasedCollisionUnionRatio_le_crude (j : ℕ) :
    biasedCollisionUnionRatio j ≤
      (biasedK j : ℚ) / (2 : ℚ) ^ (biasedK j + 2) := by
  calc
    biasedCollisionUnionRatio j ≤
        ((biasedCollisionIndices j).card : ℚ) *
          (1 / (2 : ℚ) ^ (2 * biasedK j + 2)) :=
      biasedCollisionUnionRatio_le_index_bound j
    _ ≤ (((2 ^ biasedK j * biasedK j : ℕ) : ℚ) *
          (1 / (2 : ℚ) ^ (2 * biasedK j + 2))) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast biasedCollisionIndices_card_le j
      · positivity
    _ = (biasedK j : ℚ) / (2 : ℚ) ^ (biasedK j + 2) :=
      powerset_collision_ratio_identity (biasedK j)

/-- The normalized cardinality of the union of all `(S, i)` collisions is at
most the target geometric error. -/
theorem biasedCollisionUnionRatio_le {j : ℕ} (_hj : 400 ≤ j) :
    biasedCollisionUnionRatio j ≤
      ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  exact (biasedCollisionUnionRatio_le_crude j).trans (by
    simpa only [biasedK] using collision_numeric_le (biasedRadius j))

end Erdos486


/-! Flattened from Erdos486.FourColorTail. -/

/-!
# A finite tail bound for four-colourings

This file derives the biased-colouring tail estimate used when the number of
coordinates is `6 * r`.  The argument is only finite counting: apply the
finite Markov inequality to the weight `2 ^ blackCount`, then use its exact
uniform sum from `FiniteAveraging`.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section

variable {ι : Type*} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

/-- The four-colourings having more than `2 * r` black coordinates. -/
def fourColorTail (r : ℕ) : Finset (FourColoring ι) :=
  Finset.univ.filter fun c ↦ 2 * r < blackCount c

/-- The exact cross-multiplied Markov bound before imposing
`Fintype.card ι = 6 * r`. -/
theorem fourColorTail_card_mul_two_pow_le (r : ℕ) :
    ((fourColorTail (ι := ι) r).card : ℚ) * (2 : ℚ) ^ (2 * r) ≤
      (5 : ℚ) ^ Fintype.card ι := by
  let threshold : ℚ := (2 : ℚ) ^ (2 * r)
  let thresholdSet : Finset (FourColoring ι) :=
    Finset.univ.filter fun c ↦ threshold ≤ (2 : ℚ) ^ blackCount c
  have hsubset : fourColorTail (ι := ι) r ⊆ thresholdSet := by
    intro c hc
    have hcTail : 2 * r < blackCount c := (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ c, ?_⟩
    exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hcTail.le
  have hcard :
      ((fourColorTail (ι := ι) r).card : ℚ) ≤
        (thresholdSet.card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hmarkov :=
    fintype_markov (𝕜 := ℚ)
      (fun c : FourColoring ι ↦ (2 : ℚ) ^ blackCount c)
      (fun _ ↦ by positivity) threshold
  calc
    ((fourColorTail (ι := ι) r).card : ℚ) * (2 : ℚ) ^ (2 * r) =
        ((fourColorTail (ι := ι) r).card : ℚ) * threshold := by
      rfl
    _ ≤ (thresholdSet.card : ℚ) * threshold := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ∑ c : FourColoring ι, (2 : ℚ) ^ blackCount c := by
      exact hmarkov
    _ = (5 : ℚ) ^ Fintype.card ι :=
      sum_two_pow_blackCount

/-- Natural-number form of the exact cross-multiplied tail bound when there
are `6 * r` coordinates. -/
theorem fourColorTail_card_mul_two_pow_le_of_card_eq (r : ℕ)
    (hι : Fintype.card ι = 6 * r) :
    (fourColorTail (ι := ι) r).card * 2 ^ (2 * r) ≤ 5 ^ (6 * r) := by
  have h := fourColorTail_card_mul_two_pow_le (ι := ι) r
  rw [hι] at h
  exact_mod_cast h

/-- Rational proportion form of the biased-colouring tail estimate. -/
theorem fourColorTail_ratio_le_rat (r : ℕ)
    (hι : Fintype.card ι = 6 * r) :
    ((fourColorTail (ι := ι) r).card : ℚ) /
        Fintype.card (FourColoring ι) ≤
      ((125 : ℚ) / 128) ^ (2 * r) := by
  have hmarkov := fourColorTail_card_mul_two_pow_le (ι := ι) r
  rw [hι] at hmarkov
  have htwo : 0 < (2 : ℚ) ^ (2 * r) := by positivity
  have htail :
      ((fourColorTail (ι := ι) r).card : ℚ) ≤
        (5 : ℚ) ^ (6 * r) / (2 : ℚ) ^ (2 * r) :=
    (le_div_iff₀ htwo).2 hmarkov
  have hcolorCard :
      (Fintype.card (FourColoring ι) : ℚ) = (4 : ℚ) ^ (6 * r) := by
    rw [card_fourColoring, hι, Nat.cast_pow]
    norm_num
  have hfour : (4 : ℚ) ^ (6 * r) = (64 : ℚ) ^ (2 * r) := by
    rw [show 6 * r = 3 * (2 * r) by omega, pow_mul]
    norm_num
  have hfive : (5 : ℚ) ^ (6 * r) = (125 : ℚ) ^ (2 * r) := by
    rw [show 6 * r = 3 * (2 * r) by omega, pow_mul]
    norm_num
  have hdenominator :
      (2 : ℚ) ^ (2 * r) * (4 : ℚ) ^ (6 * r) =
        (128 : ℚ) ^ (2 * r) := by
    rw [hfour, ← mul_pow]
    norm_num
  rw [hcolorCard]
  calc
    ((fourColorTail (ι := ι) r).card : ℚ) / (4 : ℚ) ^ (6 * r) ≤
        ((5 : ℚ) ^ (6 * r) / (2 : ℚ) ^ (2 * r)) /
          (4 : ℚ) ^ (6 * r) := by
      exact div_le_div_of_nonneg_right htail (by positivity)
    _ = ((125 : ℚ) / 128) ^ (2 * r) := by
      rw [div_div, hfive, hdenominator, div_pow]

end

end Erdos486


/-! Flattened from Erdos486.BiasedSummability. -/

/-!
# Summability of the biased-colouring errors

The error at scale `j` decays geometrically in `biasedRadius j`.  Since a
radius-`n` block has only quadratically many possible indices, the errors form
a summable series.  We make this argument elementary by injecting every index
into an explicit finite block and summing a polynomial times a geometric
sequence.
-/

open scoped BigOperators
open Filter

namespace Erdos486

noncomputable section

/-- The error allowance supplied by the biased-colouring tail estimate. -/
def biasedEta (j : ℕ) : ℝ :=
  3 * ((63 : ℝ) / 64) ^ (2 * biasedRadius j)

theorem biasedEta_nonneg (j : ℕ) : 0 ≤ biasedEta j := by
  unfold biasedEta
  positivity

/-- A convenient upper bound for the number of indices in a radius block. -/
def biasedRadiusCapacity (n : ℕ) : ℕ :=
  400 * (n + 1) ^ 2

/-- Every index fits in the explicit block attached to its biased radius. -/
theorem lt_biasedRadiusCapacity (j : ℕ) :
    j < biasedRadiusCapacity (biasedRadius j) := by
  have hsqrt :
      Nat.sqrt j < 20 * (Nat.sqrt j / 20 + 1) :=
    Nat.lt_mul_div_succ (Nat.sqrt j) (by norm_num)
  have hsqrtSucc :
      Nat.sqrt j + 1 ≤ 20 * (biasedRadius j + 1) := by
    simp only [biasedRadius]
    omega
  have hj : j < (Nat.sqrt j + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' j
  calc
    j < (Nat.sqrt j + 1) ^ 2 := hj
    _ ≤ (20 * (biasedRadius j + 1)) ^ 2 :=
      Nat.pow_le_pow_left hsqrtSucc 2
    _ = biasedRadiusCapacity (biasedRadius j) := by
      simp [biasedRadiusCapacity]
      ring

/-- The block encoding used to compare the error series with a sigma-type
series having explicitly finite fibers. -/
def biasedRadiusCode (j : ℕ) :
    Σ n : ℕ, Fin (biasedRadiusCapacity n) :=
  ⟨biasedRadius j, ⟨j, lt_biasedRadiusCapacity j⟩⟩

theorem biasedRadiusCode_injective :
    Function.Injective biasedRadiusCode := by
  intro i j hij
  have hval := congrArg
    (fun x : Σ n : ℕ, Fin (biasedRadiusCapacity n) ↦ x.2.val) hij
  simpa [biasedRadiusCode] using hval

/-- The constant weight assigned to every slot of a radius block. -/
def biasedRadiusEnvelope
    (x : Σ n : ℕ, Fin (biasedRadiusCapacity n)) : ℝ :=
  3 * ((63 : ℝ) / 64) ^ (2 * x.1)

theorem summable_biasedRadiusEnvelope :
    Summable biasedRadiusEnvelope := by
  apply (summable_sigma_of_nonneg (fun x ↦ by
    unfold biasedRadiusEnvelope
    positivity)).2
  constructor
  · intro n
    exact Summable.of_finite
  · let ρ : ℝ := ((63 : ℝ) / 64) ^ 2
    have hρ : ‖ρ‖ < 1 := by
      norm_num [ρ, Real.norm_eq_abs]
    have hzero : Summable (fun n : ℕ ↦ ρ ^ n) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hρ)
    have hone : Summable (fun n : ℕ ↦ (n : ℝ) * ρ ^ n) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hρ)
    have htwo : Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * ρ ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hρ
    have hpoly :
        Summable (fun n : ℕ ↦
          1200 * (((n : ℝ) + 1) ^ 2 * ρ ^ n)) := by
      refine (htwo.add ((hone.mul_left 2).add hzero)).mul_left 1200 |>.congr ?_
      intro n
      ring
    have hfiber :
        (fun n : ℕ ↦
            ∑' _x : Fin (biasedRadiusCapacity n),
              biasedRadiusEnvelope ⟨n, _x⟩) =
          fun n : ℕ ↦ 1200 * (((n : ℝ) + 1) ^ 2 * ρ ^ n) := by
      funext n
      simp [biasedRadiusEnvelope, biasedRadiusCapacity, ρ, pow_mul]
      ring
    rw [hfiber]
    exact hpoly

/-- The biased-colouring error allowances are summable. -/
theorem summable_biasedEta : Summable biasedEta := by
  have h := summable_biasedRadiusEnvelope.comp_injective
    biasedRadiusCode_injective
  exact h.congr fun _ ↦ rfl

/-- The sums of the shifted tails tend to zero. -/
theorem tendsto_biasedEta_tail :
    Tendsto (fun J ↦ ∑' n : ℕ, biasedEta (n + J)) atTop (nhds 0) :=
  tendsto_sum_nat_add biasedEta

/-- There is a cutoff after which every finite collection of error terms has
total mass at most `1 / 100`. -/
theorem exists_biasedEta_tail_finset_le :
    ∃ J0 : ℕ, ∀ s : Finset ℕ,
      (∀ j ∈ s, J0 ≤ j) → (∑ j ∈ s, biasedEta j) ≤ (1 : ℝ) / 100 := by
  have heventually :
      ∀ᶠ J in atTop, (∑' n : ℕ, biasedEta (n + J)) < (1 : ℝ) / 100 :=
    (tendsto_order.1 tendsto_biasedEta_tail).2 _ (by norm_num)
  obtain ⟨J0, hJ0⟩ := heventually.exists
  refine ⟨J0, fun s hs ↦ ?_⟩
  have hinjective : Set.InjOn (fun j : ℕ ↦ j - J0) (s : Set ℕ) := by
    intro i hi j hj hij
    have hiJ : J0 ≤ i := hs i hi
    have hjJ : J0 ≤ j := hs j hj
    calc
      i = (i - J0) + J0 := (Nat.sub_add_cancel hiJ).symm
      _ = (j - J0) + J0 := congrArg (· + J0) hij
      _ = j := Nat.sub_add_cancel hjJ
  have hsum :
      (∑ n ∈ s.image (fun j : ℕ ↦ j - J0), biasedEta (n + J0)) =
        ∑ j ∈ s, biasedEta j := by
    rw [Finset.sum_image hinjective]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [Nat.sub_add_cancel (hs j hj)]
  have hsummableTail : Summable (fun n : ℕ ↦ biasedEta (n + J0)) :=
    (summable_nat_add_iff J0).2 summable_biasedEta
  have hfinite := hsummableTail.sum_le_tsum
    (s.image fun j : ℕ ↦ j - J0)
    (fun n _ ↦ biasedEta_nonneg (n + J0))
  rw [hsum] at hfinite
  exact hfinite.trans hJ0.le

end

end Erdos486


/-! Flattened from Erdos486.BiasedFootprintAverage. -/

/-!
# Finite averages of the biased footprint

This module identifies the periodic footprint ratio with the average of its
zero-one coverage indicator.  It also records the finite Fubini step used to
exchange the averages over residues and colourings.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section

local instance biasedPeriodNeZero (j : ℕ) : NeZero (biasedPeriod j) :=
  ⟨(biasedPeriod_pos j).ne'⟩

/-- The rational zero-one indicator that a residue is covered by a biased
colouring. -/
noncomputable def biasedCoverageIndicator (j : ℕ)
    (x : ZMod (biasedPeriod j)) (c : BiasedColoring j) : ℚ := by
  classical
  exact if IsBiasedCovered j c x then 1 else 0

/-- Finite Fubini for uniform rational averages over nonempty finite types. -/
theorem fintypeAverage_comm {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β → ℚ) :
    fintypeAverage (fun a ↦ fintypeAverage (f a)) =
      fintypeAverage (fun b ↦ fintypeAverage (fun a ↦ f a b)) := by
  classical
  have hα : (Fintype.card α : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold fintypeAverage
  calc
    (∑ a : α, (∑ b : β, f a b) / Fintype.card β) /
          Fintype.card α =
        (∑ a : α, ∑ b : β, f a b) /
          ((Fintype.card β : ℚ) * Fintype.card α) := by
      rw [← Finset.sum_div, div_div]
    _ = (∑ b : β, ∑ a : α, f a b) /
          ((Fintype.card α : ℚ) * Fintype.card β) := by
      apply (div_eq_div_iff (mul_ne_zero hβ hα)
        (mul_ne_zero hα hβ)).2
      rw [Finset.sum_comm]
      ring
    _ = (∑ b : β, (∑ a : α, f a b) / Fintype.card α) /
          Fintype.card β := by
      rw [← Finset.sum_div, div_div]

/-- For a fixed colouring, the average coverage indicator over one period is
exactly its rational footprint. -/
theorem fintypeAverage_biasedCoverageIndicator (j : ℕ)
    (c : BiasedColoring j) :
    fintypeAverage (fun x ↦ biasedCoverageIndicator j x c) =
      biasedFootprintRat j c := by
  classical
  have hcard :
      Fintype.card (ZMod (biasedPeriod j)) = biasedPeriod j :=
    ZMod.card (biasedPeriod j)
  have hperiodQ : (biasedPeriod j : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (biasedPeriod_pos j).ne'
  have hcardQ :
      (Fintype.card (ZMod (biasedPeriod j)) : ℚ) ≠ 0 := by
    rw [hcard]
    exact hperiodQ
  unfold fintypeAverage biasedCoverageIndicator
  rw [Finset.sum_boole, biasedFootprintRat]
  unfold biasedFootprintCount
  apply (div_eq_div_iff hcardQ hperiodQ).2
  rw [hcard]

/-- Averaging the rational footprint over colourings is the same as first
averaging the coverage indicator over colourings and then over residues. -/
theorem fintypeAverage_biasedFootprintRat (j : ℕ) :
    fintypeAverage (fun c : BiasedColoring j ↦ biasedFootprintRat j c) =
      fintypeAverage (fun x : ZMod (biasedPeriod j) ↦
        fintypeAverage (fun c : BiasedColoring j ↦
          biasedCoverageIndicator j x c)) := by
  calc
    fintypeAverage (fun c : BiasedColoring j ↦ biasedFootprintRat j c) =
        fintypeAverage (fun c : BiasedColoring j ↦
          fintypeAverage (fun x : ZMod (biasedPeriod j) ↦
            biasedCoverageIndicator j x c)) := by
      apply congrArg fintypeAverage
      funext c
      exact (fintypeAverage_biasedCoverageIndicator j c).symm
    _ = fintypeAverage (fun x : ZMod (biasedPeriod j) ↦
          fintypeAverage (fun c : BiasedColoring j ↦
            biasedCoverageIndicator j x c)) :=
      fintypeAverage_comm (fun c x ↦ biasedCoverageIndicator j x c)

end

end Erdos486


/-! Flattened from Erdos486.BiasedAnchorTail. -/

/-!
# The bad-anchor tail for biased colourings

The anchor coordinates at a fixed residue are distinct.  Splitting a biased
colouring into its restriction to those coordinates and the complementary
coordinates therefore identifies the bad-anchor event with `fourColorTail`.
-/

namespace Erdos486

noncomputable section

/-- The anchor coordinates at any fixed scale and residue representative are
pairwise distinct. -/
theorem biasedAnchor_injective (j x : ℕ) :
    Function.Injective (biasedAnchor j x) := by
  intro i i' hii'
  simpa [biasedAnchor, endpointCoordinate] using congrArg Sigma.fst hii'

/-- The uniform rational average of the indicator that more than twice the
biased radius many anchor coordinates are black. -/
theorem biasedBadAnchorAverage_le (j : ℕ)
    (x : ZMod (biasedPeriod j)) :
    fintypeAverage
        (fun c : BiasedColoring j ↦
          if 2 * biasedRadius j <
              anchorBlackCount (biasedAnchor j x.val) c then
            (1 : ℚ)
          else 0) ≤
      ((125 : ℚ) / 128) ^ (2 * biasedRadius j) := by
  classical
  let anchor : Fin (biasedK j) ↪ BiasedCoordinate j :=
    ⟨biasedAnchor j x.val, biasedAnchor_injective j x.val⟩
  let split := oracleColoringEquiv anchor
  have hrestrict
      (c : FourColoring (Fin (biasedK j)) ×
        FourColoring (EmbeddingComplement anchor))
      (i : Fin (biasedK j)) :
      split c (biasedAnchor j x.val i) = c.1 i := by
    change split c (anchor i) = c.1 i
    simp [split]
  have hcount
      (c : FourColoring (Fin (biasedK j)) ×
        FourColoring (EmbeddingComplement anchor)) :
      anchorBlackCount (biasedAnchor j x.val) (split c) =
        blackCount c.1 := by
    unfold anchorBlackCount blackCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      hrestrict c i]
  calc
    fintypeAverage
        (fun c : BiasedColoring j ↦
          if 2 * biasedRadius j <
              anchorBlackCount (biasedAnchor j x.val) c then
            (1 : ℚ)
          else 0) =
        fintypeAverage
          (fun c : FourColoring (Fin (biasedK j)) ×
              FourColoring (EmbeddingComplement anchor) ↦
            if 2 * biasedRadius j <
                anchorBlackCount (biasedAnchor j x.val) (split c) then
              (1 : ℚ)
            else 0) := by
      exact (fintypeAverage_comp_equiv split _).symm
    _ = fintypeAverage
          (fun c : FourColoring (Fin (biasedK j)) ×
              FourColoring (EmbeddingComplement anchor) ↦
            if 2 * biasedRadius j < blackCount c.1 then
              (1 : ℚ)
            else 0) := by
      apply congrArg fintypeAverage
      funext c
      rw [hcount c]
    _ = fintypeAverage
          (fun c : FourColoring (Fin (biasedK j)) ↦
            if 2 * biasedRadius j < blackCount c then
              (1 : ℚ)
            else 0) := by
      exact fintypeAverage_prod_fst
        (α := FourColoring (Fin (biasedK j)))
        (β := FourColoring (EmbeddingComplement anchor))
        (fun c : FourColoring (Fin (biasedK j)) ↦
          if 2 * biasedRadius j < blackCount c then (1 : ℚ) else 0)
    _ = ((fourColorTail (ι := Fin (biasedK j)) (biasedRadius j)).card : ℚ) /
          Fintype.card (FourColoring (Fin (biasedK j))) := by
      have htail :
          (Finset.univ.filter fun c : FourColoring (Fin (biasedK j)) ↦
            2 * biasedRadius j < blackCount c) =
            fourColorTail (ι := Fin (biasedK j)) (biasedRadius j) := by
        ext c
        simp [fourColorTail]
      rw [fintypeAverage, Finset.sum_boole, htail]
    _ ≤ ((125 : ℚ) / 128) ^ (2 * biasedRadius j) := by
      have htail := fourColorTail_ratio_le_rat
        (ι := Fin (biasedK j)) (biasedRadius j) (by
          rw [biasedK]
          exact Fintype.card_fin _)
      simpa only [Fintype.card_eq_nat_card] using htail

end

end Erdos486


/-! Flattened from Erdos486.BiasedFiniteBlock. -/

/-!
# The finite biased-colouring block

This file completes the finite probabilistic-method argument by explicit
enumeration.  For every scale `j ≥ 400`, the uniform rational average of the
periodic footprint over all four-colourings is at most

`3 * (63 / 64) ^ (2 * biasedRadius j)`.

The three terms are the arithmetic collision union, the bad-anchor tail, and
the weighted union bound for good anchors.  All averages are finite sums; no
probability measure is used.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section

private instance biasedFiniteBlockPeriodNeZero (j : ℕ) :
    NeZero (biasedPeriod j) :=
  ⟨(biasedPeriod_pos j).ne'⟩

private noncomputable instance biasedFiniteBlockColoringFintype (j : ℕ) :
    Fintype (BiasedColoring j) := by
  classical
  exact Pi.instFintype

private theorem fintypeAverage_mono {α : Type*} [Fintype α]
    {f g : α → ℚ} (h : ∀ x, f x ≤ g x) :
    fintypeAverage f ≤ fintypeAverage g := by
  unfold fintypeAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _hx ↦ h x) (Nat.cast_nonneg _)

private theorem fintypeAverage_add {α : Type*} [Fintype α]
    (f g : α → ℚ) :
    fintypeAverage (fun x ↦ f x + g x) =
      fintypeAverage f + fintypeAverage g := by
  simp only [fintypeAverage, Finset.sum_add_distrib, add_div]

private theorem fintypeAverage_mul_sum {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α]
    (a : ℚ) (f : β → α → ℚ) :
    fintypeAverage (fun x ↦ a * ∑ y, f y x) =
      a * ∑ y, fintypeAverage (f y) := by
  unfold fintypeAverage
  calc
    (∑ x : α, a * ∑ y : β, f y x) / Fintype.card α =
        (a * ∑ x : α, ∑ y : β, f y x) / Fintype.card α := by
      rw [Finset.mul_sum]
    _ = (a * ∑ y : β, ∑ x : α, f y x) / Fintype.card α := by
      rw [Finset.sum_comm]
    _ = a * ((∑ y : β, ∑ x : α, f y x) / Fintype.card α) := by
      ring
    _ = a * ∑ y : β, (∑ x : α, f y x) / Fintype.card α := by
      rw [Finset.sum_div]

private noncomputable def biasedCollisionIndicator (j : ℕ)
    (x : ZMod (biasedPeriod j)) : ℚ :=
  if x.val ∈ biasedCollisionUnion j then 1 else 0

private noncomputable def biasedGoodMajorant (j : ℕ)
    (x : ZMod (biasedPeriod j)) (c : BiasedColoring j) : ℚ :=
  if x.val ∈ biasedCollisionUnion j then 0 else
    (2 : ℚ) ^ (2 * biasedRadius j) *
      ∑ S : Finset (Fin (biasedK j)),
        weightedCandidate (biasedAnchor j x.val) (biasedQuery j x.val S) S c

private theorem weightedCandidate_nonneg {k : ℕ} {ι : Type*}
    (anchor query : Fin k → ι) (S : Finset (Fin k))
    (c : FourColoring ι) :
    0 ≤ weightedCandidate anchor query S c := by
  classical
  unfold weightedCandidate
  apply Finset.prod_nonneg
  intro o _ho
  cases o with
  | inl i =>
      by_cases hi : i ∈ S
      · by_cases hc : c (candidateOracle anchor query S (Sum.inl i)) = 0
        · simp [candidateOracleWeight, hi, selectedAnchorWeight, hc]
        · simp [candidateOracleWeight, hi, selectedAnchorWeight, hc]
      · by_cases hc : c (candidateOracle anchor query S (Sum.inl i)) = 0
        · simp [candidateOracleWeight, hi, halfBlackWeight, hc]
        · simp [candidateOracleWeight, hi, halfBlackWeight, hc]
  | inr i =>
      by_cases hc : c (candidateOracle anchor query S (Sum.inr i)) = 0
      · simp [candidateOracleWeight, nonblackQueryWeight, hc]
      · simp [candidateOracleWeight, nonblackQueryWeight, hc]

private theorem biasedGoodMajorant_nonneg (j : ℕ)
    (x : ZMod (biasedPeriod j)) (c : BiasedColoring j) :
    0 ≤ biasedGoodMajorant j x c := by
  classical
  unfold biasedGoodMajorant
  split
  · simp
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun S _hS ↦
        weightedCandidate_nonneg
          (biasedAnchor j x.val) (biasedQuery j x.val S) S c)

/-! ## The collision term -/

private theorem mem_biasedCollisionUnion_lt {j n : ℕ}
    (hn : n ∈ biasedCollisionUnion j) :
    n < biasedPeriod j := by
  classical
  rw [biasedCollisionUnion, Finset.mem_biUnion] at hn
  obtain ⟨a, _ha, hn⟩ := hn
  exact Finset.mem_range.mp
    (Finset.mem_filter.mp hn).1

private theorem biasedCollisionIndicator_average (j : ℕ) :
    fintypeAverage (biasedCollisionIndicator j) =
      biasedCollisionUnionRatio j := by
  classical
  let e :
      {x : ZMod (biasedPeriod j) //
          x.val ∈ biasedCollisionUnion j} ≃
        ↥(biasedCollisionUnion j) :=
    { toFun := fun x ↦ ⟨x.1.val, x.2⟩
      invFun := fun n ↦
        ⟨(n.1 : ZMod (biasedPeriod j)), by
          rw [ZMod.val_natCast_of_lt
            (mem_biasedCollisionUnion_lt n.2)]
          exact n.2⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        exact ZMod.natCast_zmod_val x.1
      right_inv := fun n ↦ by
        apply Subtype.ext
        exact ZMod.val_natCast_of_lt
          (mem_biasedCollisionUnion_lt n.2) }
  have hcard :
      ((Finset.univ : Finset (ZMod (biasedPeriod j))).filter
          fun x ↦ x.val ∈ biasedCollisionUnion j).card =
        (biasedCollisionUnion j).card := by
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr e).trans
      (Fintype.card_coe (biasedCollisionUnion j))
  change
    (∑ x : ZMod (biasedPeriod j),
        if x.val ∈ biasedCollisionUnion j then (1 : ℚ) else 0) /
        Fintype.card (ZMod (biasedPeriod j)) =
      biasedCollisionUnionRatio j
  rw [Finset.sum_boole, hcard, biasedCollisionUnionRatio,
    ZMod.card]

private theorem biasedCollisionIndicator_average_le {j : ℕ}
    (hj : 400 ≤ j) :
    fintypeAverage (biasedCollisionIndicator j) ≤
      ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  rw [biasedCollisionIndicator_average]
  exact biasedCollisionUnionRatio_le hj

/-! ## The weighted good-anchor term -/

private theorem hasNoBiasedCollision_of_not_mem {j : ℕ}
    {x : ZMod (biasedPeriod j)}
    (hx : x.val ∉ biasedCollisionUnion j) :
    HasNoBiasedCollision j x.val := by
  classical
  intro S i hi hcollision
  apply hx
  rw [biasedCollisionUnion, Finset.mem_biUnion]
  refine ⟨(S, i),
    (mem_biasedCollisionIndices_iff j S i).2 hi, ?_⟩
  rw [biasedCollisionResidues, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (ZMod.val_lt x), hcollision⟩

private theorem biasedGoodMajorant_average_le {j : ℕ}
    (_hj : 400 ≤ j) (x : ZMod (biasedPeriod j)) :
    fintypeAverage (biasedGoodMajorant j x) ≤
      ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  classical
  by_cases hcollision : x.val ∈ biasedCollisionUnion j
  · have hnonneg :
        (0 : ℚ) ≤ ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      positivity
    have hmajorant :
        biasedGoodMajorant j x = fun _c : BiasedColoring j ↦ 0 := by
      funext c
      simp [biasedGoodMajorant, hcollision]
    rw [hmajorant, fintypeAverage_const]
    exact hnonneg
  · have hno : HasNoBiasedCollision j x.val :=
      hasNoBiasedCollision_of_not_mem hcollision
    have hmajorant :
        biasedGoodMajorant j x =
          fun c : BiasedColoring j ↦
            (2 : ℚ) ^ (2 * biasedRadius j) *
              ∑ S : Finset (Fin (biasedK j)),
                weightedCandidate (biasedAnchor j x.val)
                  (biasedQuery j x.val S) S c := by
      funext c
      simp [biasedGoodMajorant, hcollision]
    rw [hmajorant]
    rw [fintypeAverage_mul_sum]
    exact scaled_sum_average_weightedCandidate_le
      (ι := BiasedCoordinate j) (biasedRadius j)
      (biasedAnchor j x.val)
      (fun S ↦ biasedQuery j x.val S)
      (fun S ↦ biasedCandidateOracle_injective hno S)

/-! ## Pointwise collision/bad/good domination -/

private theorem biasedCoverageIndicator_le_majorants {j : ℕ}
    (hj : 400 ≤ j) (x : ZMod (biasedPeriod j))
    (c : BiasedColoring j) :
    biasedCoverageIndicator j x c ≤
      biasedCollisionIndicator j x +
        (if 2 * biasedRadius j <
            anchorBlackCount (biasedAnchor j x.val) c then
          (1 : ℚ)
        else 0) +
        biasedGoodMajorant j x c := by
  classical
  have hmajorantNonneg : 0 ≤ biasedGoodMajorant j x c :=
    biasedGoodMajorant_nonneg j x c
  by_cases hcollision : x.val ∈ biasedCollisionUnion j
  · have hcovered_le : biasedCoverageIndicator j x c ≤ 1 := by
      unfold biasedCoverageIndicator
      split <;> norm_num
    have hcollisionIndicator : biasedCollisionIndicator j x = 1 := by
      simp [biasedCollisionIndicator, hcollision]
    rw [hcollisionIndicator]
    have hbadNonneg :
        0 ≤ if 2 * biasedRadius j <
            anchorBlackCount (biasedAnchor j x.val) c then
          (1 : ℚ)
        else 0 := by
      split <;> norm_num
    linarith
  · have hcollisionIndicator : biasedCollisionIndicator j x = 0 := by
      simp [biasedCollisionIndicator, hcollision]
    rw [hcollisionIndicator, zero_add]
    by_cases hcovered : IsBiasedCovered j c x
    · have hcoverageIndicator : biasedCoverageIndicator j x c = 1 := by
        simp [biasedCoverageIndicator, hcovered]
      rw [hcoverageIndicator]
      by_cases hbad : 2 * biasedRadius j <
          anchorBlackCount (biasedAnchor j x.val) c
      · rw [if_pos hbad]
        exact le_add_of_nonneg_right hmajorantNonneg
      · rw [if_neg hbad, zero_add]
        have hanchorGood :
            anchorBlackCount (biasedAnchor j x.val) c ≤
              2 * biasedRadius j := Nat.le_of_not_gt hbad
        obtain ⟨S, hvalid, hselected⟩ :=
          exists_candidate_of_isBiasedCovered hj c x hcovered
        have hoccurs :
            CandidateOccurs (biasedAnchor j x.val)
              (biasedQuery j x.val S) S c :=
          candidateOccurs_of_selectedPrimes_eq S c hvalid hselected
        have hone :
            (1 : ℚ) ≤ (2 : ℚ) ^ (2 * biasedRadius j) *
              weightedCandidate (biasedAnchor j x.val)
                (biasedQuery j x.val S) S c :=
          one_le_scaled_weightedCandidate_of_good
            (biasedAnchor j x.val) (biasedQuery j x.val S) S c
            hanchorGood hoccurs
        have hsum :
            weightedCandidate (biasedAnchor j x.val)
                (biasedQuery j x.val S) S c ≤
              ∑ T : Finset (Fin (biasedK j)),
                weightedCandidate (biasedAnchor j x.val)
                  (biasedQuery j x.val T) T c := by
          exact Finset.single_le_sum
            (fun T _hT ↦ weightedCandidate_nonneg
              (biasedAnchor j x.val) (biasedQuery j x.val T) T c)
            (Finset.mem_univ S)
        have hscaled := mul_le_mul_of_nonneg_left hsum
          (by positivity : (0 : ℚ) ≤
            (2 : ℚ) ^ (2 * biasedRadius j))
        have hmajorant :
            biasedGoodMajorant j x c =
              (2 : ℚ) ^ (2 * biasedRadius j) *
                ∑ T : Finset (Fin (biasedK j)),
                  weightedCandidate (biasedAnchor j x.val)
                    (biasedQuery j x.val T) T c := by
          simp [biasedGoodMajorant, hcollision]
        rw [hmajorant]
        exact hone.trans hscaled
    · have hcoverageIndicator : biasedCoverageIndicator j x c = 0 := by
        simp [biasedCoverageIndicator, hcovered]
      rw [hcoverageIndicator]
      exact add_nonneg (by split <;> norm_num) hmajorantNonneg

private theorem biasedCoverageAverage_le_collision_add_two {j : ℕ}
    (hj : 400 ≤ j) (x : ZMod (biasedPeriod j)) :
    fintypeAverage (fun c : BiasedColoring j ↦
        biasedCoverageIndicator j x c) ≤
      biasedCollisionIndicator j x +
        ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
        ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  have hpointwise :
      fintypeAverage (fun c : BiasedColoring j ↦
          biasedCoverageIndicator j x c) ≤
        fintypeAverage (fun c : BiasedColoring j ↦
          biasedCollisionIndicator j x +
            (if 2 * biasedRadius j <
                anchorBlackCount (biasedAnchor j x.val) c then
              (1 : ℚ)
            else 0) +
            biasedGoodMajorant j x c) :=
    fintypeAverage_mono fun c ↦
      biasedCoverageIndicator_le_majorants hj x c
  rw [fintypeAverage_add, fintypeAverage_add,
    fintypeAverage_const] at hpointwise
  have hbad :
      fintypeAverage
          (fun c : BiasedColoring j ↦
            if 2 * biasedRadius j <
                anchorBlackCount (biasedAnchor j x.val) c then
              (1 : ℚ)
            else 0) ≤
        ((63 : ℚ) / 64) ^ (2 * biasedRadius j) :=
    (biasedBadAnchorAverage_le j x).trans
      (bad_anchor_numeric_le (biasedRadius j))
  have hgood := biasedGoodMajorant_average_le hj x
  linarith

/-! ## The finite block average and deterministic colouring -/

/-- Uniformly averaging the exact rational footprint over all biased
four-colourings costs at most the sum of the collision, bad-anchor, and
good-anchor errors. -/
theorem fintypeAverage_biasedFootprintRat_le {j : ℕ}
    (hj : 400 ≤ j) :
    fintypeAverage
        (fun c : BiasedColoring j ↦ biasedFootprintRat j c) ≤
      3 * ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  rw [fintypeAverage_biasedFootprintRat]
  calc
    fintypeAverage
        (fun x : ZMod (biasedPeriod j) ↦
          fintypeAverage (fun c : BiasedColoring j ↦
            biasedCoverageIndicator j x c)) ≤
        fintypeAverage
          (fun x : ZMod (biasedPeriod j) ↦
            biasedCollisionIndicator j x +
              ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
              ((63 : ℚ) / 64) ^ (2 * biasedRadius j)) :=
      fintypeAverage_mono fun x ↦
        biasedCoverageAverage_le_collision_add_two hj x
    _ = fintypeAverage (biasedCollisionIndicator j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      rw [fintypeAverage_add, fintypeAverage_add,
        fintypeAverage_const]
    _ ≤ ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) +
          ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      linarith [biasedCollisionIndicator_average_le hj]
    _ = 3 * ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
      ring

/-- A deterministic biased colouring attaining the finite-block footprint
allowance. -/
theorem exists_biasedColoring_footprint_le {j : ℕ} (hj : 400 ≤ j) :
    ∃ c : BiasedColoring j, biasedFootprint j c ≤ biasedEta j := by
  obtain ⟨c, hc⟩ := exists_le_of_fintypeAverage_le
    (fun c : BiasedColoring j ↦ biasedFootprintRat j c)
    (fintypeAverage_biasedFootprintRat_le hj)
  refine ⟨c, ?_⟩
  have hcReal :
      ((biasedFootprintRat j c : ℚ) : ℝ) ≤
        ((3 * ((63 : ℚ) / 64) ^ (2 * biasedRadius j) : ℚ) : ℝ) := by
    exact_mod_cast hc
  rw [biasedFootprintRat_cast_real] at hcReal
  simpa [biasedEta] using hcReal

end

end Erdos486


/-! Flattened from Erdos486.Statement. -/

/-!
# Erdős Problem 486: exact statement

The activation condition is strict: a modulus `n` constrains `m` only when
`n < m`.  Keeping `A` explicit makes the quantifiers match the original
problem verbatim.
-/

open Filter Set

namespace Erdos486

/-- The positive integers surviving the delayed congruence system `(A, X)`.
The subtype index says that residue sets are supplied exactly for moduli in `A`.
-/
def survivors (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))) : Set ℕ :=
  {m | 0 < m ∧ ∀ n : A, (n : ℕ) < m → (m : ZMod (n : ℕ)) ∉ X n}

/-- The logarithmic counting sum below a real cutoff. -/
noncomputable def logSum (B : Set ℕ) (x : ℝ) : ℝ :=
  by
    classical
    exact ∑ m ∈ Finset.range ⌈x⌉₊,
      if m ∈ B ∧ (m : ℝ) < x then (m : ℝ)⁻¹ else 0

/-- The normalized logarithmic average used in Erdős Problem 486. -/
noncomputable def logAverage (B : Set ℕ) (x : ℝ) : ℝ :=
  logSum B x / Real.log x

/-- A set has logarithmic density `d` in the exact normalization of the problem. -/
def HasLogDensity (B : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (logAverage B) atTop (nhds d)

/-- The original yes/no assertion in Erdős Problem 486. -/
def Erdos486Assertion : Prop :=
  ∀ (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))), 0 ∉ A →
    ∃ d : ℝ, HasLogDensity (survivors A X) d

/-- The quantitative strengthening claimed in the accompanying manuscript. -/
def QuantitativeCounterexample : Prop :=
  ∃ (A : Set ℕ), A.Infinite ∧ 0 ∉ A ∧
    ∃ X : (n : A) → Set (ZMod (n : ℕ)),
      let B := survivors A X
      (¬ ∃ d : ℝ, HasLogDensity B d) ∧
      liminf (logAverage B) atTop ≤ (177 : ℝ) / 200 ∧
      (49 : ℝ) / 50 ≤ limsup (logAverage B) atTop

theorem quantitativeCounterexample_not_assertion :
    QuantitativeCounterexample → ¬Erdos486Assertion := by
  rintro ⟨A, _, hA, X, hnone, _, _⟩ hall
  exact hnone (hall A X hA)

end Erdos486


/-! Flattened from Erdos486.Periodic. -/

/-!
# Logarithmic density of eventually periodic sets

An eventually periodic set of positive natural numbers has logarithmic density equal to the
fraction of occupied residue classes.  The final theorem is stated using the real cutoffs and the
normalization `logAverage` from `Erdos486.Statement`.
-/

open Filter Set Asymptotics
open scoped Topology

namespace Erdos486

noncomputable section

/-- The reciprocal counting sum below a natural cutoff.  The term at zero is harmless, since its
inverse in `ℝ` is zero. -/
private def natLogSum (B : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact ∑ m ∈ Finset.range N, if m ∈ B then (m : ℝ)⁻¹ else 0

/-- The contribution of one complete block of length `L`. -/
private def periodicBlockSum (B : Set ℕ) (L q : ℕ) : ℝ := by
  classical
  exact ∑ r ∈ Finset.range L,
    if q * L + r ∈ B then ((q * L + r : ℕ) : ℝ)⁻¹ else 0

/-- The harmonic number, regarded as a real number. -/
private def realHarmonic (N : ℕ) : ℝ :=
  (harmonic N : ℝ)

/-- The occupied residues in the canonical interval `[0, L)`. -/
private def residueFinset (R : Set ℕ) (L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range L).filter fun r ↦ r ∈ R

/-- The number of occupied residues in one period. -/
private def occupiedResidues (R : Set ℕ) (L : ℕ) : ℕ :=
  (residueFinset R L).card

private lemma realHarmonic_eq_sum_range (N : ℕ) :
    realHarmonic N = ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simp [realHarmonic, harmonic]

private lemma tendsto_realHarmonic_div_log :
    Tendsto (fun N : ℕ ↦ realHarmonic N / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror :
      Tendsto (fun N : ℕ ↦ (realHarmonic N - Real.log N) / Real.log N) atTop (𝓝 0) :=
    Real.tendsto_harmonic_sub_log.div_atTop hlog
  have h : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) + (realHarmonic N - Real.log N) / Real.log N)
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add herror
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog_ne : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp
  ring

private lemma natLogSum_nonneg (B : Set ℕ) (N : ℕ) : 0 ≤ natLogSum B N := by
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · positivity
  · exact le_rfl

private lemma natLogSum_mono (B : Set ℕ) : Monotone (natLogSum B) := by
  intro M N hMN
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
  intro m hmN hmM
  split_ifs
  · positivity
  · exact le_rfl

private lemma natLogSum_mul_eq_sum_blocks (B : Set ℕ) (L Q : ℕ) :
    natLogSum B (Q * L) = ∑ q ∈ Finset.range Q, periodicBlockSum B L q := by
  classical
  induction Q with
  | zero => simp [natLogSum]
  | succ Q ih =>
      calc
        natLogSum B ((Q + 1) * L) =
            natLogSum B (Q * L) + periodicBlockSum B L Q := by
          simp only [Nat.succ_mul, natLogSum, periodicBlockSum, Finset.sum_range_add]
        _ = ∑ q ∈ Finset.range (Q + 1), periodicBlockSum B L q := by
          rw [ih, Finset.sum_range_succ]

private lemma periodicBlockSum_eq_filter (B R : Set ℕ) (L N₀ q : ℕ) (hL : 0 < L)
    (hq : N₀ ≤ q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    periodicBlockSum B L q =
      ∑ r ∈ residueFinset R L, ((q * L + r : ℕ) : ℝ)⁻¹ := by
  classical
  simp only [residueFinset]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  have hrL : r < L := Finset.mem_range.mp hr
  have hq_le_mul : q ≤ q * L := by
    exact Nat.le_mul_of_pos_right q hL
  have hcutoff : N₀ ≤ q * L + r := hq.trans (hq_le_mul.trans (Nat.le_add_right _ _))
  have hmod : (q * L + r) % L = r := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hrL]
  rw [if_congr ((hperiodic _ hcutoff).trans (by rw [hmod])) rfl rfl]

private lemma periodicBlockSum_nonneg (B : Set ℕ) (L q : ℕ) :
    0 ≤ periodicBlockSum B L q := by
  apply Finset.sum_nonneg
  intro r hr
  split_ifs
  · positivity
  · exact le_rfl

private lemma periodicBlockSum_lower (B R : Set ℕ) (L N₀ q : ℕ) (hL : 0 < L)
    (hq₀ : N₀ ≤ q) (hq : 0 < q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    (occupiedResidues R L : ℝ) * (((q + 1) * L : ℕ) : ℝ)⁻¹ ≤
      periodicBlockSum B L q := by
  classical
  rw [periodicBlockSum_eq_filter B R L N₀ q hL hq₀ hperiodic]
  calc
    (occupiedResidues R L : ℝ) * (((q + 1) * L : ℕ) : ℝ)⁻¹ =
        ∑ _r ∈ residueFinset R L,
          (((q + 1) * L : ℕ) : ℝ)⁻¹ := by
            simp [occupiedResidues]
    _ ≤ ∑ r ∈ residueFinset R L,
          ((q * L + r : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hr
      have hrL : r < L := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp (by simpa [residueFinset] using hr)).1
      apply (inv_le_inv₀ (by positivity)
        (by exact_mod_cast (Nat.mul_pos hq hL).trans_le (Nat.le_add_right _ _))).2
      exact_mod_cast (show q * L + r ≤ (q + 1) * L by
        simpa [Nat.add_mul] using Nat.add_le_add_left hrL.le (q * L))

private lemma periodicBlockSum_upper (B R : Set ℕ) (L N₀ q : ℕ) (hL : 0 < L)
    (hq₀ : N₀ ≤ q) (hq : 0 < q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    periodicBlockSum B L q ≤
      (occupiedResidues R L : ℝ) * ((q * L : ℕ) : ℝ)⁻¹ := by
  classical
  rw [periodicBlockSum_eq_filter B R L N₀ q hL hq₀ hperiodic]
  calc
    (∑ r ∈ residueFinset R L,
        ((q * L + r : ℕ) : ℝ)⁻¹) ≤
        ∑ _r ∈ residueFinset R L,
          ((q * L : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hr
      apply (inv_le_inv₀ (by positivity) (by exact_mod_cast Nat.mul_pos hq hL)).2
      exact_mod_cast Nat.le_add_right (q * L) r
    _ = (occupiedResidues R L : ℝ) * ((q * L : ℕ) : ℝ)⁻¹ := by
      simp [occupiedResidues]

private lemma cast_mul_inv_mul (k a L : ℕ) (ha : 0 < a) (hL : 0 < L) :
    (k : ℝ) * (((a * L : ℕ) : ℝ)⁻¹) =
      ((k : ℝ) / (L : ℝ)) * ((a : ℝ)⁻¹) := by
  push_cast
  field_simp

private lemma realHarmonic_eq_sum_Ico (N : ℕ) :
    realHarmonic N = ∑ n ∈ Finset.Ico 1 (N + 1), (n : ℝ)⁻¹ := by
  rw [realHarmonic_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

private lemma realHarmonic_sub_eq_sum_Ico {M N : ℕ} (hMN : M ≤ N) :
    realHarmonic N - realHarmonic M =
      ∑ n ∈ Finset.Ico M N, ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [realHarmonic_eq_sum_range, realHarmonic_eq_sum_range,
    ← Finset.sum_Ico_eq_sub _ hMN]

private lemma natLogSum_mul_lower (B R : Set ℕ) (L N₀ M Q : ℕ) (hL : 0 < L)
    (hN₀M : N₀ ≤ M) (hM : 0 < M) (hMQ : M ≤ Q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    ((occupiedResidues R L : ℝ) / (L : ℝ)) *
        (realHarmonic Q - realHarmonic M) ≤ natLogSum B (Q * L) := by
  rw [realHarmonic_sub_eq_sum_Ico hMQ, Finset.mul_sum,
    natLogSum_mul_eq_sum_blocks]
  calc
    (∑ q ∈ Finset.Ico M Q,
        ((occupiedResidues R L : ℝ) / (L : ℝ)) * ((q + 1 : ℕ) : ℝ)⁻¹) =
        ∑ q ∈ Finset.Ico M Q,
          (occupiedResidues R L : ℝ) * ((((q + 1) * L : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [cast_mul_inv_mul (occupiedResidues R L) (q + 1) L (Nat.succ_pos q) hL]
    _ ≤ ∑ q ∈ Finset.Ico M Q, periodicBlockSum B L q := by
      apply Finset.sum_le_sum
      intro q hq
      have hMq : M ≤ q := (Finset.mem_Ico.mp hq).1
      exact periodicBlockSum_lower B R L N₀ q hL (hN₀M.trans hMq)
        (hM.trans_le hMq) hperiodic
    _ ≤ ∑ q ∈ Finset.range Q, periodicBlockSum B L q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hq).2
      · intro q hq hq'
        exact periodicBlockSum_nonneg B L q

private lemma natLogSum_mul_upper (B R : Set ℕ) (L N₀ M Q : ℕ) (hL : 0 < L)
    (hN₀M : N₀ ≤ M) (hM : 0 < M) (hMQ : M ≤ Q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    natLogSum B (Q * L) ≤ natLogSum B (M * L) +
      ((occupiedResidues R L : ℝ) / (L : ℝ)) * realHarmonic Q := by
  have hd_nonneg : 0 ≤ (occupiedResidues R L : ℝ) / (L : ℝ) := by positivity
  calc
    natLogSum B (Q * L) = natLogSum B (M * L) +
        ∑ q ∈ Finset.Ico M Q, periodicBlockSum B L q := by
      rw [natLogSum_mul_eq_sum_blocks, natLogSum_mul_eq_sum_blocks,
        Finset.sum_range_add_sum_Ico _ hMQ]
    _ ≤ natLogSum B (M * L) +
        ∑ q ∈ Finset.Ico M Q,
          (occupiedResidues R L : ℝ) * (((q * L : ℕ) : ℝ)⁻¹) := by
      gcongr with q hq
      have hMq : M ≤ q := (Finset.mem_Ico.mp hq).1
      exact periodicBlockSum_upper B R L N₀ q hL (hN₀M.trans hMq)
        (hM.trans_le hMq) hperiodic
    _ = natLogSum B (M * L) +
        ((occupiedResidues R L : ℝ) / (L : ℝ)) *
          ∑ q ∈ Finset.Ico M Q, ((q : ℕ) : ℝ)⁻¹ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hq_pos : 0 < q := hM.trans_le (Finset.mem_Ico.mp hq).1
      rw [cast_mul_inv_mul (occupiedResidues R L) q L hq_pos hL]
    _ ≤ natLogSum B (M * L) +
        ((occupiedResidues R L : ℝ) / (L : ℝ)) * realHarmonic Q := by
      gcongr
      rw [realHarmonic_eq_sum_Ico]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have hqmem := Finset.mem_Ico.mp hq
        exact Finset.mem_Ico.mpr ⟨hM.trans_le hqmem.1, hqmem.2.trans_le (Nat.le_succ Q)⟩
      · intro q hq hq'
        positivity

private lemma tendsto_nat_mul_right_atTop (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ Q * L) atTop atTop := by
  exact (show StrictMono (fun Q : ℕ ↦ Q * L) from
    fun _ _ h ↦ Nat.mul_lt_mul_of_pos_right h hL).tendsto_atTop

private lemma tendsto_log_nat_mul_atTop (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ Real.log ((Q * L : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_nat_mul_right_atTop L hL))

private lemma tendsto_log_div_log_nat_mul (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ Real.log Q / Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hlogQL := tendsto_log_nat_mul_atTop L hL
  have hlim : Tendsto
      (fun Q : ℕ ↦ 1 - Real.log (L : ℝ) / Real.log ((Q * L : ℕ) : ℝ))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hlogQL.const_div_atTop (Real.log (L : ℝ)))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hL_pos : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogQL_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast (show 1 < Q * L by nlinarith)
  rw [show (((Q * L : ℕ) : ℝ)) = (Q : ℝ) * (L : ℝ) by norm_num,
    Real.log_mul hQ_pos.ne' hL_pos.ne'] at hlogQL_ne ⊢
  field_simp
  ring

private lemma tendsto_realHarmonic_div_log_mul (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ realHarmonic Q / Real.log ((Q * L : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have hlim : Tendsto
      (fun Q : ℕ ↦ (realHarmonic Q / Real.log Q) *
        (Real.log Q / Real.log ((Q * L : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa only [one_mul] using
      tendsto_realHarmonic_div_log.mul (tendsto_log_div_log_nat_mul L hL)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  have hlogQ_ne : Real.log (Q : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hQ)).ne'
  have hlogQL_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast (show 1 < Q * L by nlinarith)
  field_simp

private lemma tendsto_natLogSum_mul_div_log (B R : Set ℕ) (L N₀ M : ℕ) (hL : 0 < L)
    (hN₀M : N₀ ≤ M) (hM : 0 < M)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    Tendsto
      (fun Q : ℕ ↦ natLogSum B (Q * L) / Real.log ((Q * L : ℕ) : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
  let d : ℝ := (occupiedResidues R L : ℝ) / (L : ℝ)
  let C : ℝ := natLogSum B (M * L)
  have hden := tendsto_log_nat_mul_atTop L hL
  have hH := tendsto_realHarmonic_div_log_mul L hL
  have hlower : Tendsto
      (fun Q : ℕ ↦ d * (realHarmonic Q - realHarmonic M) /
        Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 d) := by
    have hlim : Tendsto
        (fun Q : ℕ ↦ d * (realHarmonic Q / Real.log ((Q * L : ℕ) : ℝ)) -
          (d * realHarmonic M) / Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 d) := by
      simpa using (hH.const_mul d).sub (hden.const_div_atTop (d * realHarmonic M))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with Q hQ
    have hlog_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < Q * L by nlinarith)
    field_simp
  have hupper : Tendsto
      (fun Q : ℕ ↦ (C + d * realHarmonic Q) /
        Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 d) := by
    have hlim : Tendsto
        (fun Q : ℕ ↦ C / Real.log ((Q * L : ℕ) : ℝ) +
          d * (realHarmonic Q / Real.log ((Q * L : ℕ) : ℝ))) atTop (𝓝 d) := by
      simpa using (hden.const_div_atTop C).add (hH.const_mul d)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with Q hQ
    have hlog_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < Q * L by nlinarith)
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop (max M 2)] with Q hQ
    have hMQ : M ≤ Q := le_max_left M 2 |>.trans hQ
    have hlog_pos : 0 < Real.log (((Q * L : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Q * L by
        have hQ2 : 2 ≤ Q := (le_max_right M 2).trans hQ
        nlinarith)
    apply (div_le_div_iff_of_pos_right hlog_pos).2
    exact natLogSum_mul_lower B R L N₀ M Q hL hN₀M hM hMQ hperiodic
  · filter_upwards [eventually_ge_atTop (max M 2)] with Q hQ
    have hMQ : M ≤ Q := le_max_left M 2 |>.trans hQ
    have hlog_pos : 0 < Real.log (((Q * L : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Q * L by
        have hQ2 : 2 ≤ Q := (le_max_right M 2).trans hQ
        nlinarith)
    apply (div_le_div_iff_of_pos_right hlog_pos).2
    simpa [C, d] using natLogSum_mul_upper B R L N₀ M Q hL hN₀M hM hMQ hperiodic

private lemma tendsto_nat_div_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ ((((N / L) * L : ℕ) : ℝ) / (N : ℝ))) atTop (𝓝 1) := by
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N : ℕ ↦ 1 - (L : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hcast.const_div_atTop (L : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hnear : N < (N / L) * L + L := by
      calc
        N = N % L + L * (N / L) := (Nat.mod_add_div N L).symm
        _ < L + L * (N / L) := Nat.add_lt_add_right (Nat.mod_lt N hL) _
        _ = (N / L) * L + L := by ring
    rw [le_div_iff₀ hNpos]
    have hnear' : (N : ℝ) - (L : ℝ) ≤ (((N / L) * L : ℕ) : ℝ) := by
      have hnear_real : (N : ℝ) < (((N / L) * L : ℕ) : ℝ) + (L : ℝ) := by
        exact_mod_cast hnear
      linarith
    calc
      (1 - (L : ℝ) / (N : ℝ)) * (N : ℝ) = (N : ℝ) - (L : ℝ) := by
        field_simp
      _ ≤ (((N / L) * L : ℕ) : ℝ) := hnear'
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_one hNpos]
    exact_mod_cast Nat.div_mul_le_self N L

private lemma tendsto_nat_div_add_one_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ ((((N / L + 1) * L : ℕ) : ℝ) / (N : ℝ))) atTop (𝓝 1) := by
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun N : ℕ ↦ ((((N / L) * L : ℕ) : ℝ) / (N : ℝ)) + (L : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_nat_div_mul_ratio L hL).add (hcast.const_div_atTop (L : ℝ))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  push_cast
  field_simp

private lemma tendsto_log_div_log_of_isEquivalent {α : Type*} {l : Filter α}
    {f g : α → ℝ} (hfg : f ~[l] g) (hg : Tendsto g l atTop) :
    Tendsto (fun x ↦ Real.log (f x) / Real.log (g x)) l (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one
    ((Real.tendsto_log_atTop.comp hg).eventually_ne_atTop 0)).1
  exact hfg.log hg

private lemma tendsto_log_nat_div_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto
      (fun N : ℕ ↦ Real.log (((N / L) * L : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  apply tendsto_log_div_log_of_isEquivalent
  · apply (isEquivalent_iff_tendsto_one
      (tendsto_natCast_atTop_atTop.eventually_ne_atTop 0)).2
    exact tendsto_nat_div_mul_ratio L hL
  · exact tendsto_natCast_atTop_atTop

private lemma tendsto_log_nat_div_add_one_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto
      (fun N : ℕ ↦ Real.log (((N / L + 1) * L : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  apply tendsto_log_div_log_of_isEquivalent
  · apply (isEquivalent_iff_tendsto_one
      (tendsto_natCast_atTop_atTop.eventually_ne_atTop 0)).2
    exact tendsto_nat_div_add_one_mul_ratio L hL
  · exact tendsto_natCast_atTop_atTop

/-- Natural-cutoff form of logarithmic-density recovery for an eventual residue pattern. -/
private lemma tendsto_natLogSum_div_log_of_eventually_modPeriodic
    (B R : Set ℕ) (L N₀ : ℕ) (hL : 0 < L)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    Tendsto (fun N : ℕ ↦ natLogSum B N / Real.log (N : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
  let M : ℕ := max N₀ 1
  have hN₀M : N₀ ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hblocks := tendsto_natLogSum_mul_div_log B R L N₀ M hL hN₀M hM hperiodic
  have hquot : Tendsto (fun N : ℕ ↦ N / L) atTop atTop :=
    Nat.tendsto_div_const_atTop hL.ne'
  have hquot_succ : Tendsto (fun N : ℕ ↦ N / L + 1) atTop atTop := by
    simpa [Function.comp_def] using (tendsto_add_atTop_nat 1).comp hquot
  have hlower : Tendsto
      (fun N : ℕ ↦ natLogSum B ((N / L) * L) / Real.log (N : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
    have hlim : Tendsto
        (fun N : ℕ ↦
          (natLogSum B ((N / L) * L) / Real.log (((N / L) * L : ℕ) : ℝ)) *
            (Real.log (((N / L) * L : ℕ) : ℝ) / Real.log (N : ℝ))) atTop
        (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
      simpa only [Function.comp_apply, mul_one] using
        (hblocks.comp hquot).mul (tendsto_log_nat_div_mul_ratio L hL)
    apply hlim.congr'
    filter_upwards [hquot.eventually_ge_atTop 2, eventually_ge_atTop 2] with N hq hN
    have hlogq_ne : Real.log ((((N / L) * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < (N / L) * L by nlinarith)
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
  have hupper : Tendsto
      (fun N : ℕ ↦ natLogSum B ((N / L + 1) * L) / Real.log (N : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
    have hlim : Tendsto
        (fun N : ℕ ↦
          (natLogSum B ((N / L + 1) * L) /
              Real.log (((N / L + 1) * L : ℕ) : ℝ)) *
            (Real.log (((N / L + 1) * L : ℕ) : ℝ) / Real.log (N : ℝ))) atTop
        (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
      simpa only [Function.comp_apply, mul_one] using
        (hblocks.comp hquot_succ).mul (tendsto_log_nat_div_add_one_mul_ratio L hL)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogq_ne : Real.log ((((N / L + 1) * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < (N / L + 1) * L by
        have hnear : N < (N / L + 1) * L := by
          calc
            N = N % L + L * (N / L) := (Nat.mod_add_div N L).symm
            _ < L + L * (N / L) := Nat.add_lt_add_right (Nat.mod_lt N hL) _
            _ = (N / L + 1) * L := by ring
        omega)
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    apply (div_le_div_iff_of_pos_right hlogN_pos).2
    exact natLogSum_mono B (Nat.div_mul_le_self N L)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hnear : N ≤ (N / L + 1) * L := by
      apply le_of_lt
      calc
        N = N % L + L * (N / L) := (Nat.mod_add_div N L).symm
        _ < L + L * (N / L) := Nat.add_lt_add_right (Nat.mod_lt N hL) _
        _ = (N / L + 1) * L := by ring
    apply (div_le_div_iff_of_pos_right hlogN_pos).2
    exact natLogSum_mono B hnear

private lemma logSum_eq_natLogSum_ceil (B : Set ℕ) (x : ℝ) :
    logSum B x = natLogSum B ⌈x⌉₊ := by
  classical
  rw [logSum, natLogSum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmx : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
  simp [hmx]

/-- Bridge from natural cutoffs to the exact real-cutoff normalization in `Statement.lean`. -/
private lemma hasLogDensity_of_tendsto_natLogSum_div_log (B : Set ℕ) (d : ℝ)
    (h : Tendsto (fun N : ℕ ↦ natLogSum B N / Real.log (N : ℝ)) atTop (𝓝 d)) :
    HasLogDensity B d := by
  have hceil : Tendsto (fun x : ℝ ↦ ⌈x⌉₊) atTop atTop := tendsto_nat_ceil_atTop
  have hceil_equiv :
      (fun x : ℝ ↦ (⌈x⌉₊ : ℝ)) ~[atTop] (fun x : ℝ ↦ x) := by
    apply (isEquivalent_iff_tendsto_one
      ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne')).2
    exact tendsto_nat_ceil_div_atTop
  have hlog_ratio : Tendsto
      (fun x : ℝ ↦ Real.log (⌈x⌉₊ : ℝ) / Real.log x) atTop (𝓝 1) :=
    tendsto_log_div_log_of_isEquivalent hceil_equiv tendsto_id
  have hlim : Tendsto
      (fun x : ℝ ↦
        (natLogSum B ⌈x⌉₊ / Real.log (⌈x⌉₊ : ℝ)) *
          (Real.log (⌈x⌉₊ : ℝ) / Real.log x)) atTop (𝓝 d) := by
    simpa only [Function.comp_apply, mul_one] using (h.comp hceil).mul hlog_ratio
  unfold HasLogDensity logAverage
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hceil_two : 2 ≤ ⌈x⌉₊ := by
    apply Nat.add_one_le_ceil_iff.mpr
    simpa using hx
  have hlogceil_ne : Real.log (⌈x⌉₊ : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hceil_two)).ne'
  have hlogx_ne : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [logSum_eq_natLogSum_ceil]
  field_simp

/-- **Finite-periodic logarithmic-density recovery.**

If `B` consists of positive naturals and, from `N₀` onward, membership in `B` is exactly
membership of `n % L` in the finite residue set `R`, then `B` has logarithmic density
`R.card / L` in the exact real-cutoff sense of `HasLogDensity`.  Positivity of the period and the
fact that every listed residue lies in `[0, L)` are explicit assumptions.
-/
theorem hasLogDensity_of_eventually_periodic
    (B : Set ℕ) (R : Finset ℕ) (L N₀ : ℕ)
    (hL : 0 < L)
    (hR : ∀ r ∈ R, r < L)
    (_hpositive : ∀ n ∈ B, 0 < n)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    HasLogDensity B ((R.card : ℝ) / (L : ℝ)) := by
  have hpattern : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ (R : Set ℕ)) := by
    simpa using hperiodic
  have hresidues : residueFinset (R : Set ℕ) L = R := by
    ext r
    simp only [residueFinset, Finset.mem_filter, Finset.mem_range, Finset.mem_coe]
    constructor
    · exact fun hr ↦ hr.2
    · intro hr
      exact ⟨hR r hr, hr⟩
  have hcount : occupiedResidues (R : Set ℕ) L = R.card := by
    simp [occupiedResidues, hresidues]
  have hnat := tendsto_natLogSum_div_log_of_eventually_modPeriodic
    B (R : Set ℕ) L N₀ hL hpattern
  have hdensity := hasLogDensity_of_tendsto_natLogSum_div_log B
    ((occupiedResidues (R : Set ℕ) L : ℝ) / (L : ℝ)) hnat
  rw [hcount] at hdensity
  exact hdensity

end

end Erdos486


/-! Flattened from Erdos486.PeriodicCounting. -/

/-!
# Exact finite counts for periodic predicates

These lemmas let later modules compare a footprint in one period with its
pullback to any common multiple, using only finite cardinalities.
-/

namespace Erdos486

/-- Repeating a predicate of period `d` through `k` complete blocks multiplies
its count by `k`. -/
theorem card_filter_range_mul_of_periodic (P : ℕ → Prop) [DecidablePred P]
    (d k : ℕ) (hP : Function.Periodic P d) :
    ((Finset.range (k * d)).filter P).card =
      k * ((Finset.range d).filter P).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit :
          Finset.Ico 0 (k * d + d) =
            Finset.Ico 0 (k * d) ∪ Finset.Ico (k * d) (k * d + d) := by
        exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Nat.le_add_right _ _)).symm
      have hdisj :
          Disjoint
            ((Finset.Ico 0 (k * d)).filter P)
            ((Finset.Ico (k * d) (k * d + d)).filter P) := by
        apply Finset.disjoint_left.2
        intro n hn₁ hn₂
        simp only [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
        omega
      rw [Nat.succ_mul, Finset.range_eq_Ico, hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint hdisj]
      rw [Finset.range_eq_Ico] at ih
      rw [ih, Nat.filter_Ico_card_eq_of_periodic (k * d) d P hP,
        Nat.count_eq_card_filter_range, Finset.range_eq_Ico]
      ring

/-- If `d ∣ L`, pulling a predicate on residues modulo `d` back to
`range L` preserves its normalized density exactly. -/
theorem card_filter_range_mod_of_dvd (P : ℕ → Prop) [DecidablePred P]
    {d L : ℕ} (hdiv : d ∣ L) :
    d * ((Finset.range L).filter fun n ↦ P (n % d)).card =
      L * ((Finset.range d).filter P).card := by
  obtain ⟨k, rfl⟩ := hdiv
  have hperiodic : Function.Periodic (fun n ↦ P (n % d)) d := by
    intro n
    simp
  have hcount :
      ((Finset.range (d * k)).filter fun n ↦ P (n % d)).card =
        k * ((Finset.range d).filter fun n ↦ P (n % d)).card := by
    simpa [Nat.mul_comm] using
      card_filter_range_mul_of_periodic (fun n ↦ P (n % d)) d k hperiodic
  rw [hcount]
  have hbase :
      ((Finset.range d).filter fun n ↦ P (n % d)).card =
        ((Finset.range d).filter P).card := by
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hp⟩
      exact ⟨hn, by simpa [Nat.mod_eq_of_lt hn] using hp⟩
    · rintro ⟨hn, hp⟩
      exact ⟨hn, by simpa [Nat.mod_eq_of_lt hn] using hp⟩
  rw [hbase]
  ring

end Erdos486


/-! Flattened from Erdos486.Survivors. -/

/-!
# Delayed congruence survivors

Elementary pointwise facts about the strict activation condition in Erdős
Problem 486.
-/

open Set

namespace Erdos486

theorem pos_of_mem_survivors {A : Set ℕ}
    {X : (n : A) → Set (ZMod (n : ℕ))} {m : ℕ}
    (hm : m ∈ survivors A X) : 0 < m :=
  hm.1

theorem not_mem_survivors_of_assigned {A : Set ℕ}
    {X : (n : A) → Set (ZMod (n : ℕ))} {n : A} {m : ℕ}
    (hnm : (n : ℕ) < m) (hm : (m : ZMod (n : ℕ)) ∈ X n) :
    m ∉ survivors A X := by
  intro hs
  exact (hs.2 n hnm) hm

theorem mem_survivors_congr_below {A : Set ℕ}
    {X Y : (n : A) → Set (ZMod (n : ℕ))} {x m : ℕ}
    (hrows : ∀ n : A, (n : ℕ) < x → X n = Y n) (hmx : m < x) :
    m ∈ survivors A X ↔ m ∈ survivors A Y := by
  constructor
  · rintro ⟨hm, hX⟩
    refine ⟨hm, fun n hnm hmem => ?_⟩
    rw [← hrows n (hnm.trans hmx)] at hmem
    exact hX n hnm hmem
  · rintro ⟨hm, hY⟩
    refine ⟨hm, fun n hnm hmem => ?_⟩
    rw [hrows n (hnm.trans hmx)] at hmem
    exact hY n hnm hmem

theorem logSum_congr_below {B C : Set ℕ} {x : ℝ}
    (h : ∀ m : ℕ, (m : ℝ) < x → (m ∈ B ↔ m ∈ C)) :
    logSum B x = logSum C x := by
  classical
  unfold logSum
  apply Finset.sum_congr rfl
  intro m _
  by_cases hmx : (m : ℝ) < x
  · have hmem := h m hmx
    by_cases hmB : m ∈ B
    · have hmC : m ∈ C := hmem.mp hmB
      simp [hmx, hmB, hmC]
    · have hmC : m ∉ C := fun hm => hmB (hmem.mpr hm)
      simp [hmx, hmB, hmC]
  · simp only [hmx, and_false, ↓reduceIte]

theorem logAverage_congr_below {B C : Set ℕ} {x : ℝ}
    (h : ∀ m : ℕ, (m : ℝ) < x → (m ∈ B ↔ m ∈ C)) :
    logAverage B x = logAverage C x := by
  rw [logAverage, logAverage, logSum_congr_below h]

end Erdos486


/-! Flattened from Erdos486.BlockInterface. -/

/-!
# Abstract dyadic deletion blocks

This module isolates the finite input needed by the global gliding-hump
argument.  All endpoint and modulus estimates are inequalities in `ℕ`, with
the rational constants cross-multiplied.  The analytic input is deliberately
only a finite-past recovery statement; it does not assume a global
counterexample.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

/-- The integral dyadic scale `2^j`. -/
def dyadicNat (j : ℕ) : ℕ :=
  2 ^ j

/-- The same dyadic scale, viewed as a real cutoff. -/
def dyadic (j : ℕ) : ℝ :=
  (dyadicNat j : ℝ)

@[simp]
theorem dyadicNat_pos (j : ℕ) : 0 < dyadicNat j := by
  simp [dyadicNat]

@[simp]
theorem dyadic_pos (j : ℕ) : 0 < dyadic j := by
  simp [dyadic, dyadicNat]

@[simp]
theorem dyadic_succ (j : ℕ) : dyadicNat (j + 1) = 2 * dyadicNat j := by
  simp [dyadicNat, pow_succ, Nat.mul_comm]

/-- Finite endpoint data at every scale.  The quantitative block properties
are required only from `firstScale` onward.  Values below `firstScale` are
irrelevant and let downstream definitions remain nondependent.

The bounds encode
`11*2^j/10 <= m <= 19*2^j/10` and
`19*2^j/20 <= q(j,m) <= 21*2^j/20` without division. -/
structure DyadicBlockGeometry where
  firstScale : ℕ
  endpoints : ℕ → Finset ℕ
  modulus : ℕ → ℕ → ℕ
  endpoint_lower : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    11 * dyadicNat j ≤ 10 * m
  endpoint_upper : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    10 * m ≤ 19 * dyadicNat j
  modulus_pos : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    0 < modulus j m
  modulus_lower : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    19 * dyadicNat j ≤ 20 * modulus j m
  modulus_upper : ∀ {j m : ℕ}, firstScale ≤ j → m ∈ endpoints j →
    20 * modulus j m ≤ 21 * dyadicNat j
  enough_endpoints : ∀ {j : ℕ}, firstScale ≤ j →
    3 * dyadicNat j ≤ 8 * (endpoints j).card

/-- Moduli assigned by `G` at scales in `scales`. -/
def blockModuli (G : DyadicBlockGeometry) (scales : Set ℕ) : Set ℕ :=
  {q | ∃ j ∈ scales, ∃ m ∈ G.endpoints j, G.modulus j m = q}

/-- Residues assigned to one of the moduli occurring at the selected scales.
Equal moduli are automatically grouped into one row. -/
def blockResidues (G : DyadicBlockGeometry) (scales : Set ℕ)
    (q : blockModuli G scales) : Set (ZMod (q : ℕ)) :=
  {r | ∃ j ∈ scales, ∃ m ∈ G.endpoints j,
    G.modulus j m = (q : ℕ) ∧ r = (m : ZMod (q : ℕ))}

/-- The delayed-congruence survivor set induced by selected block scales. -/
def blockSurvivors (G : DyadicBlockGeometry) (scales : Set ℕ) : Set ℕ :=
  survivors (blockModuli G scales) (blockResidues G scales)

/-- The abstract input to the gliding-hump construction.

`footprint j` is an upper bound for the completed periodic footprint of the
`j`th block.  `summable_footprint` records the manuscript's summability
property, while `tail_budget` exposes the finite-sum consequence after the
starting scale has been enlarged.  `finite_recovery` is the periodic recovery
lemma in precisely the form used globally: every finite subsystem has a
limit at least one minus the sum of its block footprints. -/
structure DyadicBlockInterface where
  geometry : DyadicBlockGeometry
  footprint : ℕ → ℝ
  footprint_nonneg : ∀ j, 0 ≤ footprint j
  summable_footprint : Summable footprint
  tail_budget : ∀ J : Finset ℕ,
    (∀ j ∈ J, geometry.firstScale ≤ j) →
      (∑ j ∈ J, footprint j) ≤ (1 : ℝ) / 100
  finite_recovery : ∀ J : Finset ℕ,
    ∃ d : ℝ,
      Tendsto (logAverage (blockSurvivors geometry (J : Set ℕ))) atTop (nhds d) ∧
      1 - (∑ j ∈ J, footprint j) ≤ d

namespace DyadicBlockGeometry

variable (G : DyadicBlockGeometry)

/-- Every available endpoint is positive. -/
theorem endpoint_pos {j m : ℕ} (hj : G.firstScale ≤ j)
    (hm : m ∈ G.endpoints j) : 0 < m := by
  have h := G.endpoint_lower hj hm
  have hpow : 0 < dyadicNat j := dyadicNat_pos j
  omega

/-- The assigned modulus is strictly active at its endpoint. -/
theorem modulus_lt_endpoint {j m : ℕ} (hj : G.firstScale ≤ j)
    (hm : m ∈ G.endpoints j) : G.modulus j m < m := by
  have hq := G.modulus_upper hj hm
  have hm' := G.endpoint_lower hj hm
  have hpow : 0 < dyadicNat j := dyadicNat_pos j
  omega

/-- Endpoints at different available scales lie in disjoint, ordered
intervals. -/
theorem endpoint_lt_of_scale_lt {j k m n : ℕ}
    (hj0 : G.firstScale ≤ j) (hjk : j < k)
    (hm : m ∈ G.endpoints j) (hn : n ∈ G.endpoints k) : m < n := by
  have hm_upper := G.endpoint_upper hj0 hm
  have hk0 : G.firstScale ≤ k := hj0.trans (Nat.le_of_lt hjk)
  have hn_lower := G.endpoint_lower hk0 hn
  have hexp : j + 1 ≤ k := hjk
  have hpow : dyadicNat (j + 1) ≤ dyadicNat k := by
    exact Nat.pow_le_pow_right (by norm_num) hexp
  have hgap : 19 * dyadicNat j < 11 * dyadicNat k := by
    calc
      19 * dyadicNat j < 11 * dyadicNat (j + 1) := by
        rw [dyadic_succ]
        have hp := dyadicNat_pos j
        nlinarith
      _ ≤ 11 * dyadicNat k := Nat.mul_le_mul_left 11 hpow
  omega

/-- Modulus ranges at different available scales are disjoint and ordered. -/
theorem modulus_lt_of_scale_lt {j k m n : ℕ}
    (hj0 : G.firstScale ≤ j) (hjk : j < k)
    (hm : m ∈ G.endpoints j) (hn : n ∈ G.endpoints k) :
    G.modulus j m < G.modulus k n := by
  have hq_upper := G.modulus_upper hj0 hm
  have hk0 : G.firstScale ≤ k := hj0.trans (Nat.le_of_lt hjk)
  have hr_lower := G.modulus_lower hk0 hn
  have hexp : j + 1 ≤ k := hjk
  have hpow : dyadicNat (j + 1) ≤ dyadicNat k := by
    exact Nat.pow_le_pow_right (by norm_num) hexp
  have hgap : 21 * dyadicNat j < 19 * dyadicNat k := by
    calc
      21 * dyadicNat j < 19 * dyadicNat (j + 1) := by
        rw [dyadic_succ]
        have hp := dyadicNat_pos j
        nlinarith
      _ ≤ 19 * dyadicNat k := Nat.mul_le_mul_left 19 hpow
  omega

/-- Every endpoint at scale `j` lies below `2^(j+1)`. -/
theorem endpoint_lt_next_dyadic {j m : ℕ} (hj : G.firstScale ≤ j)
    (hm : m ∈ G.endpoints j) : m < dyadicNat (j + 1) := by
  have h := G.endpoint_upper hj hm
  rw [dyadic_succ]
  have hp := dyadicNat_pos j
  omega

/-- The manuscript's cardinality and endpoint bounds give a fixed amount of
harmonic mass at each available scale. -/
theorem endpoint_harmonic_mass {j : ℕ} (hj : G.firstScale ≤ j) :
    (15 : ℝ) / 76 ≤ ∑ m ∈ G.endpoints j, (m : ℝ)⁻¹ := by
  let Q : ℝ := dyadicNat j
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast dyadicNat_pos j
  have heach : ∀ m ∈ G.endpoints j, (10 : ℝ) / (19 * Q) ≤ (m : ℝ)⁻¹ := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast G.endpoint_pos hj hm
    have hmupper : (10 : ℝ) * m ≤ 19 * Q := by
      dsimp [Q]
      exact_mod_cast G.endpoint_upper hj hm
    have hmle : (m : ℝ) ≤ 19 * Q / 10 := by linarith
    have hinv := one_div_le_one_div_of_le hmpos hmle
    calc
      (10 : ℝ) / (19 * Q) = 1 / (19 * Q / 10) := by
        field_simp [hQ.ne']
      _ ≤ 1 / (m : ℝ) := hinv
      _ = (m : ℝ)⁻¹ := by simp [one_div]
  have hsum :
      ((G.endpoints j).card : ℝ) * ((10 : ℝ) / (19 * Q)) ≤
        ∑ m ∈ G.endpoints j, (m : ℝ)⁻¹ := by
    calc
      ((G.endpoints j).card : ℝ) * ((10 : ℝ) / (19 * Q)) =
          ∑ _m ∈ G.endpoints j, ((10 : ℝ) / (19 * Q)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun m hm ↦ heach m hm
  have hcard : (3 : ℝ) * Q ≤ 8 * (G.endpoints j).card := by
    dsimp [Q]
    exact_mod_cast G.enough_endpoints hj
  calc
    (15 : ℝ) / 76 ≤
        ((G.endpoints j).card : ℝ) * ((10 : ℝ) / (19 * Q)) := by
      field_simp [ne_of_gt hQ]
      nlinarith
    _ ≤ _ := hsum

/-- No selected available block can assign modulus zero. -/
theorem zero_not_mem_blockModuli {scales : Set ℕ}
    (hscales : ∀ j ∈ scales, G.firstScale ≤ j) :
    0 ∉ blockModuli G scales := by
  rintro ⟨j, hj, m, hm, hq⟩
  have := G.modulus_pos (hscales j hj) hm
  omega

/-- An endpoint selected from an installed scale is deleted by its own
assigned row. -/
theorem endpoint_not_mem_blockSurvivors {scales : Set ℕ} {j m : ℕ}
    (hj : j ∈ scales) (hm : m ∈ G.endpoints j)
    (hj0 : G.firstScale ≤ j) :
    m ∉ blockSurvivors G scales := by
  let q : blockModuli G scales :=
    ⟨G.modulus j m, ⟨j, hj, m, hm, rfl⟩⟩
  apply not_mem_survivors_of_assigned (n := q) (G.modulus_lt_endpoint hj0 hm)
  exact ⟨j, hj, m, hm, rfl, rfl⟩

end DyadicBlockGeometry

end Erdos486


/-! Flattened from Erdos486.BiasedGeometry. -/

/-! # Dyadic geometry supplied by the biased arithmetic skeleton -/

namespace Erdos486

/-- Any subset selector produces valid global dyadic geometry above an
arbitrary cutoff at least `400`.  The cutoff can therefore be enlarged until
the summable footprint tail is below the global error budget. -/
noncomputable def biasedGeometryAbove (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (selector : (j : ℕ) → ℕ → Finset (Fin (biasedK j))) :
    DyadicBlockGeometry where
  firstScale := firstScale
  endpoints := biasedEndpoints
  modulus j m := biasedModulus j (selector j m)
  endpoint_lower hj hm := by
    simpa [dyadicNat] using (biasedEndpoint_bounds (hfirst.trans hj) hm).1
  endpoint_upper hj hm := by
    simpa [dyadicNat] using (biasedEndpoint_bounds (hfirst.trans hj) hm).2
  modulus_pos _ _ := biasedModulus_pos _ _
  modulus_lower hj _ := by
    simpa [dyadicNat] using (biasedModulus_bounds (hfirst.trans hj) _).1
  modulus_upper hj _ := by
    simpa [dyadicNat] using (biasedModulus_bounds (hfirst.trans hj) _).2
  enough_endpoints hj := by
    simpa [dyadicNat] using biasedEndpoints_enough (hfirst.trans hj)

/-- The basic geometry with the explicit arithmetic cutoff `400`. -/
noncomputable def biasedGeometry
    (selector : (j : ℕ) → ℕ → Finset (Fin (biasedK j))) :
    DyadicBlockGeometry :=
  biasedGeometryAbove 400 le_rfl selector

end Erdos486


/-! Flattened from Erdos486.BiasedRecovery. -/

/-!
# Deterministic recovery for finitely many biased blocks

For a fixed colouring at every scale, a finite collection of blocks removes
a finite union of periodic cylinder sets.  This file places those cylinders
over one common product period, counts their pullbacks exactly, and obtains
the logarithmic-density recovery estimate used by `DyadicBlockInterface`.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

noncomputable section

/-- The geometry selected by a fixed family of biased colourings. -/
def biasedColoredGeometryAbove (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) : DyadicBlockGeometry :=
  biasedGeometryAbove firstScale hfirst
    (fun j m ↦ selectedPrimes j (c j) m)

@[simp]
theorem biasedColoredGeometryAbove_endpoints
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (j : ℕ) :
    (biasedColoredGeometryAbove firstScale hfirst c).endpoints j =
      biasedEndpoints j := rfl

@[simp]
theorem biasedColoredGeometryAbove_modulus
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (j m : ℕ) :
    (biasedColoredGeometryAbove firstScale hfirst c).modulus j m =
      colouredModulus j (c j) m := rfl

/-- A common period for all biased blocks indexed by `J`. -/
def finiteBiasedPeriod (J : Finset ℕ) : ℕ :=
  ∏ j ∈ J, biasedPeriod j

theorem finiteBiasedPeriod_pos (J : Finset ℕ) :
    0 < finiteBiasedPeriod J := by
  simp [finiteBiasedPeriod, biasedPeriod_pos]

theorem biasedPeriod_dvd_finiteBiasedPeriod {J : Finset ℕ} {j : ℕ}
    (hj : j ∈ J) : biasedPeriod j ∣ finiteBiasedPeriod J := by
  rw [finiteBiasedPeriod]
  exact Finset.dvd_prod_of_mem (fun i ↦ biasedPeriod i) hj

theorem colouredModulus_dvd_finiteBiasedPeriod
    (c : (j : ℕ) → BiasedColoring j) {J : Finset ℕ} {j m : ℕ}
    (hj : j ∈ J) :
    colouredModulus j (c j) m ∣ finiteBiasedPeriod J :=
  (biasedModulus_dvd_period j (selectedPrimes j (c j) m)).trans
    (biasedPeriod_dvd_finiteBiasedPeriod hj)

/-- Coverage by the `j`th block, evaluated on a natural representative. -/
def IsBiasedCoveredNat (j : ℕ) (c : BiasedColoring j) (n : ℕ) : Prop :=
  IsBiasedCovered j c (n : ZMod (biasedPeriod j))

/-- Covered natural representatives below an arbitrary cutoff. -/
def biasedCoveredNatResidues (j : ℕ) (c : BiasedColoring j) (L : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range L).filter (IsBiasedCoveredNat j c)

/-- The natural representatives of the covered residues in one scale period
have exactly the previously defined footprint cardinality. -/
theorem card_biasedCoveredNat_one_period (j : ℕ) (c : BiasedColoring j) :
    (biasedCoveredNatResidues j c (biasedPeriod j)).card =
      biasedFootprintCount j c := by
  let _ : NeZero (biasedPeriod j) := ⟨(biasedPeriod_pos j).ne'⟩
  classical
  unfold biasedCoveredNatResidues
  unfold biasedFootprintCount
  refine Finset.card_bij
      (s := (Finset.range (biasedPeriod j)).filter
        (IsBiasedCoveredNat j c))
      (t := (Finset.univ : Finset (ZMod (biasedPeriod j))).filter
        (IsBiasedCovered j c))
      (fun n _hn ↦ (n : ZMod (biasedPeriod j))) ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.mem_univ _, hn.2⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    change (a : ZMod (biasedPeriod j)) =
      (b : ZMod (biasedPeriod j)) at hab
    have hval := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha.1),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb.1)] at hval
    exact hval
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨z.val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr z.val_lt, by
        simpa [IsBiasedCoveredNat, ZMod.natCast_zmod_val] using hz.2⟩
    · exact ZMod.natCast_zmod_val z

/-- Pulling one scale's footprint back to a common multiple preserves its
normalized cardinality exactly. -/
theorem card_biasedCoveredNat_of_dvd (j : ℕ) (c : BiasedColoring j)
    {L : ℕ} (hdiv : biasedPeriod j ∣ L) :
    biasedPeriod j *
        (biasedCoveredNatResidues j c L).card =
      L * biasedFootprintCount j c := by
  classical
  unfold biasedCoveredNatResidues
  let P : ℕ → Prop := IsBiasedCoveredNat j c
  have hperiodic : Function.Periodic P (biasedPeriod j) := by
    intro n
    have hcast :
        ((n + biasedPeriod j : ℕ) : ZMod (biasedPeriod j)) =
          (n : ZMod (biasedPeriod j)) := by
      have hzero :
          ((biasedPeriod j : ℕ) : ZMod (biasedPeriod j)) = 0 :=
        (ZMod.natCast_eq_zero_iff (biasedPeriod j) (biasedPeriod j)).2 dvd_rfl
      rw [Nat.cast_add, hzero, add_zero]
    exact congrArg (IsBiasedCovered j c) hcast
  have hmod :
      ((Finset.range L).filter fun n ↦ P (n % biasedPeriod j)).card =
        ((Finset.range L).filter P).card := by
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    have hp : P (n % biasedPeriod j) ↔ P n := by
      have hcast :
          ((n % biasedPeriod j : ℕ) : ZMod (biasedPeriod j)) =
            (n : ZMod (biasedPeriod j)) := by
        simp
      exact Iff.of_eq (congrArg (IsBiasedCovered j c) hcast)
    tauto
  rw [← hmod]
  rw [card_filter_range_mod_of_dvd P hdiv]
  rw [show ((Finset.range (biasedPeriod j)).filter P).card =
      biasedFootprintCount j c by
    simpa [P, biasedCoveredNatResidues] using
      card_biasedCoveredNat_one_period j c]

/-- The union of all covered residue representatives over the common period. -/
def finiteBiasedCoveredResidues
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) : Finset ℕ := by
  classical
  exact J.biUnion fun j ↦
    biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)

/-- Residues in the common period that avoid every selected biased block. -/
def finiteBiasedSafeResidues
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) : Finset ℕ :=
  Finset.range (finiteBiasedPeriod J) \ finiteBiasedCoveredResidues c J

theorem finiteBiasedCoveredResidues_subset_range
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    finiteBiasedCoveredResidues c J ⊆
      Finset.range (finiteBiasedPeriod J) := by
  classical
  intro n hn
  rw [finiteBiasedCoveredResidues, Finset.mem_biUnion] at hn
  obtain ⟨j, _hj, hn⟩ := hn
  exact Finset.filter_subset _ _ hn

theorem finiteBiasedCoveredResidues_card_le
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    (finiteBiasedCoveredResidues c J).card ≤
      ∑ j ∈ J,
        (biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)).card := by
  classical
  unfold finiteBiasedCoveredResidues
  exact Finset.card_biUnion_le

theorem finiteBiasedSafe_add_covered_card
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    (finiteBiasedSafeResidues c J).card +
        (finiteBiasedCoveredResidues c J).card = finiteBiasedPeriod J := by
  classical
  let U := finiteBiasedCoveredResidues c J
  let S := finiteBiasedSafeResidues c J
  have hsub : U ⊆ Finset.range (finiteBiasedPeriod J) :=
    finiteBiasedCoveredResidues_subset_range c J
  have hunion : S ∪ U = Finset.range (finiteBiasedPeriod J) := by
    simpa [S, U, finiteBiasedSafeResidues] using
      Finset.sdiff_union_of_subset hsub
  have hdisj : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro n hnS hnU
    exact (Finset.mem_sdiff.mp hnS).2 hnU
  calc
    S.card + U.card = (S ∪ U).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = (Finset.range (finiteBiasedPeriod J)).card := by rw [hunion]
    _ = finiteBiasedPeriod J := Finset.card_range _

/-- Exact normalized pullback count for every scale in a finite family. -/
theorem biasedCoveredNat_ratio_eq_footprint
    (c : (j : ℕ) → BiasedColoring j) {J : Finset ℕ} {j : ℕ}
    (hj : j ∈ J) :
    ((biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)).card : ℝ) /
        (finiteBiasedPeriod J : ℝ) = biasedFootprint j (c j) := by
  have hL : 0 < finiteBiasedPeriod J := finiteBiasedPeriod_pos J
  have hd : 0 < biasedPeriod j := biasedPeriod_pos j
  have hcrossNat := card_biasedCoveredNat_of_dvd j (c j)
    (biasedPeriod_dvd_finiteBiasedPeriod hj)
  have hcrossReal :
      (biasedPeriod j : ℝ) *
          (biasedCoveredNatResidues j (c j) (finiteBiasedPeriod J)).card =
        (finiteBiasedPeriod J : ℝ) * biasedFootprintCount j (c j) := by
    exact_mod_cast hcrossNat
  rw [biasedFootprint]
  field_simp [ne_of_gt hL, ne_of_gt hd]
  nlinarith

/-- The safe residue density is at least one minus the sum of the individual
biased footprints. -/
theorem one_sub_sum_biasedFootprint_le_safeDensity
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    1 - (∑ j ∈ J, biasedFootprint j (c j)) ≤
      ((finiteBiasedSafeResidues c J).card : ℝ) /
        (finiteBiasedPeriod J : ℝ) := by
  let L := finiteBiasedPeriod J
  let S := finiteBiasedSafeResidues c J
  let U := finiteBiasedCoveredResidues c J
  let C : ℕ := ∑ j ∈ J,
    (biasedCoveredNatResidues j (c j) L).card
  have hLNat : 0 < L := finiteBiasedPeriod_pos J
  have hUle : U.card ≤ C := by
    simpa [U, C, L] using finiteBiasedCoveredResidues_card_le c J
  have hpartition : S.card + U.card = L := by
    simpa [S, U, L] using finiteBiasedSafe_add_covered_card c J
  have hcoverNat : L ≤ S.card + C := by omega
  have hcoverReal : (L : ℝ) ≤ (S.card : ℝ) + (C : ℝ) := by
    exact_mod_cast hcoverNat
  have hsumRatio :
      (C : ℝ) / (L : ℝ) = ∑ j ∈ J, biasedFootprint j (c j) := by
    calc
      (C : ℝ) / (L : ℝ) =
          (∑ j ∈ J,
            ((biasedCoveredNatResidues j (c j) L).card : ℝ)) / (L : ℝ) := by
            simp [C]
      _ = ∑ j ∈ J,
          ((biasedCoveredNatResidues j (c j) L).card : ℝ) / (L : ℝ) := by
            rw [Finset.sum_div]
      _ = ∑ j ∈ J, biasedFootprint j (c j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa [L] using biasedCoveredNat_ratio_eq_footprint c hj
  rw [← hsumRatio]
  change 1 - (C : ℝ) / (L : ℝ) ≤ (S.card : ℝ) / (L : ℝ)
  rw [sub_le_iff_le_add]
  calc
    (1 : ℝ) ≤ ((S.card : ℝ) + (C : ℝ)) / (L : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hLNat)).2
      simpa using hcoverReal
    _ = (S.card : ℝ) / (L : ℝ) + (C : ℝ) / (L : ℝ) := by ring

/-- Unfolding the reduction map identifies coverage with the endpoint
congruence used by `blockResidues`. -/
theorem isBiasedCoveredNat_iff (j : ℕ) (c : BiasedColoring j) (n : ℕ) :
    IsBiasedCoveredNat j c n ↔
      ∃ m ∈ biasedEndpoints j,
        (n : ZMod (colouredModulus j c m)) =
          (m : ZMod (colouredModulus j c m)) := by
  simp only [IsBiasedCoveredNat, IsBiasedCovered, reduceBiasedPeriod,
    colouredModulus, ZMod.castHom_apply]
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [ZMod.cast_natCast
      (biasedModulus_dvd_period j (selectedPrimes j c m)) n] at h
    exact h
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [ZMod.cast_natCast
      (biasedModulus_dvd_period j (selectedPrimes j c m)) n]
    exact h

theorem mem_finiteBiasedSafeResidues_iff
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) (n : ℕ) :
    n ∈ finiteBiasedSafeResidues c J ↔
      n < finiteBiasedPeriod J ∧
        ∀ j ∈ J, ¬IsBiasedCoveredNat j (c j) n := by
  classical
  rw [finiteBiasedSafeResidues, Finset.mem_sdiff, Finset.mem_range]
  constructor
  · rintro ⟨hn, hnot⟩
    refine ⟨hn, ?_⟩
    intro j hj hcovered
    apply hnot
    rw [finiteBiasedCoveredResidues, Finset.mem_biUnion]
    refine ⟨j, hj, ?_⟩
    rw [biasedCoveredNatResidues, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hn, hcovered⟩
  · rintro ⟨hn, hsafe⟩
    refine ⟨hn, ?_⟩
    intro hcovered
    rw [finiteBiasedCoveredResidues, Finset.mem_biUnion] at hcovered
    obtain ⟨j, hj, hn⟩ := hcovered
    rw [biasedCoveredNatResidues, Finset.mem_filter] at hn
    exact hsafe j hj hn.2

theorem isBiasedCoveredNat_mod_finiteBiasedPeriod_iff
    (c : (j : ℕ) → BiasedColoring j) {J : Finset ℕ} {j : ℕ}
    (hj : j ∈ J) (n : ℕ) :
    IsBiasedCoveredNat j (c j) (n % finiteBiasedPeriod J) ↔
      IsBiasedCoveredNat j (c j) n := by
  have hcast :
      ((n % finiteBiasedPeriod J : ℕ) : ZMod (biasedPeriod j)) =
        (n : ZMod (biasedPeriod j)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_mod_of_dvd n (biasedPeriod_dvd_finiteBiasedPeriod hj)
  exact Iff.of_eq (congrArg (IsBiasedCovered j (c j)) hcast)

theorem mod_mem_finiteBiasedSafeResidues_iff
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) (n : ℕ) :
    n % finiteBiasedPeriod J ∈ finiteBiasedSafeResidues c J ↔
      ∀ j ∈ J, ¬IsBiasedCoveredNat j (c j) n := by
  rw [mem_finiteBiasedSafeResidues_iff]
  have hL : 0 < finiteBiasedPeriod J := finiteBiasedPeriod_pos J
  simp only [Nat.mod_lt n hL, true_and]
  constructor
  · intro h j hj hcovered
    exact h j hj ((isBiasedCoveredNat_mod_finiteBiasedPeriod_iff c hj n).2 hcovered)
  · intro h j hj hcovered
    exact h j hj ((isBiasedCoveredNat_mod_finiteBiasedPeriod_iff c hj n).1 hcovered)

/-- Once the cutoff is beyond the common period, every modulus in the finite
block system is active, and survivor membership is exactly avoidance of all
biased block footprints. -/
theorem mem_blockSurvivors_biasedColoredGeometryAbove_iff
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) (n : ℕ)
    (hn : finiteBiasedPeriod J < n) :
    n ∈ blockSurvivors (biasedColoredGeometryAbove firstScale hfirst c)
        (J : Set ℕ) ↔
      ∀ j ∈ J, ¬IsBiasedCoveredNat j (c j) n := by
  let G := biasedColoredGeometryAbove firstScale hfirst c
  have hnpos : 0 < n := (finiteBiasedPeriod_pos J).trans hn
  constructor
  · intro hs j hj hcovered
    rw [isBiasedCoveredNat_iff] at hcovered
    obtain ⟨m, hm, hcast⟩ := hcovered
    let q : blockModuli G (J : Set ℕ) :=
      ⟨colouredModulus j (c j) m, by
        refine ⟨j, ?_, m, ?_, ?_⟩
        · simpa using hj
        · simpa [G] using hm
        · simp [G]⟩
    have hqle : (q : ℕ) ≤ finiteBiasedPeriod J :=
      Nat.le_of_dvd (finiteBiasedPeriod_pos J)
        (colouredModulus_dvd_finiteBiasedPeriod c hj)
    have hq_lt_n : (q : ℕ) < n := hqle.trans_lt hn
    apply (hs.2 q hq_lt_n)
    exact ⟨j, by simpa using hj, m, by simpa [G] using hm,
      by simp [q], by simpa [q] using hcast⟩
  · intro hsafe
    refine ⟨hnpos, ?_⟩
    rintro ⟨q, hqmem⟩ _hqn hres
    obtain ⟨j, hj, m, hm, hqm, hcast⟩ := hres
    have hjJ : j ∈ J := by simpa using hj
    have hm' : m ∈ biasedEndpoints j := by simpa [G] using hm
    change colouredModulus j (c j) m = q at hqm
    subst q
    apply hsafe j hjJ
    rw [isBiasedCoveredNat_iff]
    exact ⟨m, hm', hcast⟩

/-- Explicit eventual periodicity of the finite biased survivor system.  The
threshold `L + 1` is what turns the original strict activation `q < n` on for
every modulus dividing the common period `L`. -/
theorem blockSurvivors_biasedColoredGeometryAbove_eventually_periodic
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    ∀ n, finiteBiasedPeriod J + 1 ≤ n →
      (n ∈ blockSurvivors
          (biasedColoredGeometryAbove firstScale hfirst c) (J : Set ℕ) ↔
        n % finiteBiasedPeriod J ∈ finiteBiasedSafeResidues c J) := by
  intro n hn
  have hperiod_lt : finiteBiasedPeriod J < n := by omega
  rw [mem_blockSurvivors_biasedColoredGeometryAbove_iff
    firstScale hfirst c J n hperiod_lt]
  exact (mod_mem_finiteBiasedSafeResidues_iff c J n).symm

/-- The finite biased block system has logarithmic density equal to its safe
residue proportion in the common product period. -/
theorem hasLogDensity_blockSurvivors_biasedColoredGeometryAbove
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    HasLogDensity
      (blockSurvivors (biasedColoredGeometryAbove firstScale hfirst c)
        (J : Set ℕ))
      (((finiteBiasedSafeResidues c J).card : ℝ) /
        (finiteBiasedPeriod J : ℝ)) := by
  apply hasLogDensity_of_eventually_periodic
      (blockSurvivors (biasedColoredGeometryAbove firstScale hfirst c)
        (J : Set ℕ))
      (finiteBiasedSafeResidues c J)
      (finiteBiasedPeriod J)
      (finiteBiasedPeriod J + 1)
      (finiteBiasedPeriod_pos J)
  · intro r hr
    exact (mem_finiteBiasedSafeResidues_iff c J r).mp hr |>.1
  · intro n hn
    exact hn.1
  · exact blockSurvivors_biasedColoredGeometryAbove_eventually_periodic
      firstScale hfirst c J

/-- The deterministic finite-past recovery statement in exactly the shape of
`DyadicBlockInterface.finite_recovery`. -/
theorem biasedColored_finite_recovery
    (firstScale : ℕ) (hfirst : 400 ≤ firstScale)
    (c : (j : ℕ) → BiasedColoring j) (J : Finset ℕ) :
    ∃ d : ℝ,
      Tendsto
          (logAverage
            (blockSurvivors
              (biasedColoredGeometryAbove firstScale hfirst c) (J : Set ℕ)))
          atTop (nhds d) ∧
        1 - (∑ j ∈ J, biasedFootprint j (c j)) ≤ d := by
  refine ⟨((finiteBiasedSafeResidues c J).card : ℝ) /
      (finiteBiasedPeriod J : ℝ), ?_,
    one_sub_sum_biasedFootprint_le_safeDensity c J⟩
  exact hasLogDensity_blockSurvivors_biasedColoredGeometryAbove
    firstScale hfirst c J

end

end Erdos486


/-! Flattened from Erdos486.BiasedInterface. -/

/-!
# The concrete block interface for Erdős problem 486

We choose one of the finite colourings supplied at every sufficiently large
scale, enlarge the first scale until the summable error tail is below `1/100`,
and package the resulting arithmetic blocks into `DyadicBlockInterface`.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

noncomputable section

/-- A deterministic colouring chosen from the finite averaging theorem at
large scales.  Values below the arithmetic cutoff are irrelevant to the
geometry, so we use the constant colouring there. -/
def chosenBiasedColoring (j : ℕ) : BiasedColoring j :=
  if hj : 400 ≤ j then
    Classical.choose (exists_biasedColoring_footprint_le hj)
  else
    fun _ ↦ 0

theorem chosenBiasedColoring_footprint_le_eta_of_large {j : ℕ}
    (hj : 400 ≤ j) :
    biasedFootprint j (chosenBiasedColoring j) ≤ biasedEta j := by
  rw [chosenBiasedColoring, dif_pos hj]
  exact Classical.choose_spec (exists_biasedColoring_footprint_le hj)

/-- The chosen footprint is bounded by `biasedEta` at every index.  Below
`400`, the radius is zero, so `biasedEta = 3`, while every footprint is at
most one. -/
theorem chosenBiasedColoring_footprint_le_eta (j : ℕ) :
    biasedFootprint j (chosenBiasedColoring j) ≤ biasedEta j := by
  by_cases hj : 400 ≤ j
  · exact chosenBiasedColoring_footprint_le_eta_of_large hj
  · have hjlt : j < 400 := Nat.lt_of_not_ge hj
    have hsqrt : Nat.sqrt j < 20 := by
      rw [Nat.sqrt_lt]
      omega
    have hradius : biasedRadius j = 0 := by
      simp [biasedRadius, Nat.div_eq_of_lt hsqrt]
    calc
      biasedFootprint j (chosenBiasedColoring j) ≤ 1 :=
        biasedFootprint_le_one j (chosenBiasedColoring j)
      _ ≤ biasedEta j := by simp [biasedEta, hradius]

/-- A cutoff whose entire finite tail has total error at most `1/100`. -/
def biasedTailCutoff : ℕ :=
  Classical.choose exists_biasedEta_tail_finset_le

theorem biasedTailCutoff_spec (s : Finset ℕ)
    (hs : ∀ j ∈ s, biasedTailCutoff ≤ j) :
    (∑ j ∈ s, biasedEta j) ≤ (1 : ℝ) / 100 :=
  Classical.choose_spec exists_biasedEta_tail_finset_le s hs

/-- The final first scale combines the arithmetic and analytic cutoffs. -/
def erdos486FirstScale : ℕ :=
  max 400 biasedTailCutoff

theorem four_hundred_le_erdos486FirstScale : 400 ≤ erdos486FirstScale :=
  Nat.le_max_left _ _

theorem biasedTailCutoff_le_erdos486FirstScale :
    biasedTailCutoff ≤ erdos486FirstScale :=
  Nat.le_max_right _ _

/-- The concrete coloured block geometry used in the counterexample. -/
def erdos486Geometry : DyadicBlockGeometry :=
  biasedColoredGeometryAbove erdos486FirstScale
    four_hundred_le_erdos486FirstScale chosenBiasedColoring

/-- The biased construction supplies every field of the abstract block
interface. -/
def erdos486BlockInterface : DyadicBlockInterface where
  geometry := erdos486Geometry
  footprint := biasedEta
  footprint_nonneg := biasedEta_nonneg
  summable_footprint := summable_biasedEta
  tail_budget := by
    intro J hJ
    apply biasedTailCutoff_spec J
    intro j hj
    exact biasedTailCutoff_le_erdos486FirstScale.trans (hJ j hj)
  finite_recovery := by
    intro J
    obtain ⟨d, hd, hlower⟩ := biasedColored_finite_recovery
      erdos486FirstScale four_hundred_le_erdos486FirstScale
      chosenBiasedColoring J
    refine ⟨d, ?_, ?_⟩
    · simpa [erdos486Geometry] using hd
    · have hsum :
          (∑ j ∈ J, biasedFootprint j (chosenBiasedColoring j)) ≤
            ∑ j ∈ J, biasedEta j := by
        exact Finset.sum_le_sum fun j _hj ↦
          chosenBiasedColoring_footprint_le_eta j
      exact (sub_le_sub_left hsum 1).trans hlower

end

end Erdos486


/-! Flattened from Erdos486.Analysis. -/

/-!
# Elementary analysis for Erdős Problem 486

This file records a criterion that rules out a finite limit at infinity when
two cofinal sequences force a fixed gap between function values.
-/

open Filter

namespace Erdos486

/-- A real-valued function cannot have a finite limit at `atTop` if its values
along one cofinal sequence are at least `high`, while its values along another
cofinal sequence are at most `low`, for `low < high`. -/
theorem not_tendsto_atTop_of_cofinal_ge_of_cofinal_le
    (f : ℝ → ℝ) {low high : ℝ} (hlow_high : low < high)
    (upper lower : ℕ → ℝ)
    (hupper_cofinal : Tendsto upper atTop atTop)
    (hlower_cofinal : Tendsto lower atTop atTop)
    (hupper : ∀ n, high ≤ f (upper n))
    (hlower : ∀ n, f (lower n) ≤ low) :
    ∀ d : ℝ, ¬Tendsto f atTop (nhds d) := by
  intro d hf
  have hhigh_d : high ≤ d :=
    ge_of_tendsto' (hf.comp hupper_cofinal) hupper
  have hd_low : d ≤ low :=
    le_of_tendsto' (hf.comp hlower_cofinal) hlower
  exact (not_le_of_gt hlow_high) (hhigh_d.trans hd_low)

/-- A specialization of
`not_tendsto_atTop_of_cofinal_ge_of_cofinal_le` to logarithmic averages. -/
theorem not_hasLogDensity_of_cofinal_ge_of_cofinal_le
    (B : Set ℕ) {low high : ℝ} (hlow_high : low < high)
    (upper lower : ℕ → ℝ)
    (hupper_cofinal : Tendsto upper atTop atTop)
    (hlower_cofinal : Tendsto lower atTop atTop)
    (hupper : ∀ n, high ≤ logAverage B (upper n))
    (hlower : ∀ n, logAverage B (lower n) ≤ low) :
    ∀ d : ℝ, ¬HasLogDensity B d := by
  exact not_tendsto_atTop_of_cofinal_ge_of_cofinal_le
    (logAverage B) hlow_high upper lower hupper_cofinal hlower_cofinal hupper hlower

end Erdos486


/-! Flattened from Erdos486.LogBounds. -/

/-!
# Elementary bounds for logarithmic counting sums

This file records bounds for the exact real-cutoff definitions in
`Erdos486.Statement`.  In particular, the final lemmas show that every
`logAverage B` is eventually bounded above and below along `atTop`, as needed
by the conditionally complete lattice API for `liminf` and `limsup`.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

/-- The sum of the reciprocals in `range (n + 1)` is the real coercion of the
`n`th harmonic number.  The term at zero vanishes. -/
theorem sum_range_succ_natCast_inv_eq_harmonic (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), ((m : ℕ) : ℝ)⁻¹) = (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ,
        ih, harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]

/-- The reciprocals in `range n` are bounded by the `n`th harmonic number. -/
theorem sum_range_natCast_inv_le_harmonic (n : ℕ) :
    (∑ m ∈ Finset.range n, ((m : ℕ) : ℝ)⁻¹) ≤ (harmonic n : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [sum_range_succ_natCast_inv_eq_harmonic]
      simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      exact le_add_of_nonneg_right (by positivity)

/-- At an integral cutoff, the strict real inequality in `logSum` is exactly
membership in `Finset.range n`. -/
theorem logSum_natCast (B : Set ℕ) (n : ℕ) :
    logSum B (n : ℝ) =
      (by
        classical
        exact ∑ m ∈ Finset.range n, if m ∈ B then ((m : ℕ) : ℝ)⁻¹ else 0) := by
  classical
  simp only [logSum, Nat.ceil_natCast]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m < n := Finset.mem_range.mp hm
  simp [hmn]

/-- A logarithmic counting sum is nonnegative at every real cutoff. -/
theorem logSum_nonneg (B : Set ℕ) (x : ℝ) : 0 ≤ logSum B x := by
  classical
  simp only [logSum]
  exact Finset.sum_nonneg fun m _ ↦ by split_ifs <;> positivity

/-- Dropping membership in `B` can only increase the logarithmic counting
sum. -/
theorem logSum_le_sum_range_inv (B : Set ℕ) (x : ℝ) :
    logSum B x ≤ ∑ m ∈ Finset.range ⌈x⌉₊, ((m : ℕ) : ℝ)⁻¹ := by
  classical
  simp only [logSum]
  apply Finset.sum_le_sum
  intro m hm
  split_ifs
  · exact le_rfl
  · positivity

/-- The exact real-cutoff logarithmic sum is bounded by the harmonic number at
the natural ceiling of the cutoff. -/
theorem logSum_le_harmonic_ceil (B : Set ℕ) (x : ℝ) :
    logSum B x ≤ (harmonic ⌈x⌉₊ : ℝ) :=
  (logSum_le_sum_range_inv B x).trans
    (sum_range_natCast_inv_le_harmonic ⌈x⌉₊)

/-- A convenient logarithmic upper bound valid at every real cutoff. -/
theorem logSum_le_one_add_log_ceil (B : Set ℕ) (x : ℝ) :
    logSum B x ≤ 1 + Real.log (⌈x⌉₊ : ℝ) :=
  (logSum_le_harmonic_ceil B x).trans (harmonic_le_one_add_log ⌈x⌉₊)

/-- The corresponding upper bound at a natural-number cutoff. -/
theorem logSum_natCast_le_one_add_log (B : Set ℕ) (n : ℕ) :
    logSum B (n : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  simpa using logSum_le_one_add_log_ceil B (n : ℝ)

/-- Once the cutoff is at least one, the normalized logarithmic average is
nonnegative. -/
theorem logAverage_nonneg (B : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ logAverage B x := by
  exact div_nonneg (logSum_nonneg B x) (Real.log_nonneg hx)

/-- Natural cutoffs satisfy the direct harmonic-over-log estimate. -/
theorem logAverage_natCast_le (B : Set ℕ) {n : ℕ} (hn : 2 ≤ n) :
    logAverage B (n : ℝ) ≤
      (1 + Real.log (n : ℝ)) / Real.log (n : ℝ) := by
  rw [logAverage]
  have hn' : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  apply (div_le_div_iff_of_pos_right (Real.log_pos hn')).2
  exact logSum_natCast_le_one_add_log B n

/-- A simple uniform upper bound for all sufficiently large real cutoffs. -/
theorem logAverage_le_three (B : Set ℕ) {x : ℝ}
    (hx : Real.exp 1 ≤ x) : logAverage B x ≤ 3 := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hxone : 1 ≤ x := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      norm_num at h
      exact h
    linarith
  have hlogx : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hx
  have hceil_le : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have hceil_lt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    linarith
  have hceil_pos : 0 < (⌈x⌉₊ : ℝ) :=
    hxpos.trans_le (Nat.le_ceil x)
  have hlog_ceil : Real.log (⌈x⌉₊ : ℝ) ≤ Real.log (2 * x) :=
    Real.log_le_log hceil_pos hceil_le
  have hlog_two : Real.log (2 : ℝ) ≤ 1 := by
    calc
      Real.log (2 : ℝ) ≤ Real.log (Real.exp 1) :=
        Real.log_le_log (by norm_num) (by
          have h := Real.add_one_le_exp 1
          norm_num at h
          exact h)
      _ = 1 := Real.log_exp 1
  rw [Real.log_mul (by norm_num) hxpos.ne'] at hlog_ceil
  have hsum : logSum B x ≤ 3 * Real.log x := by
    linarith [logSum_le_one_add_log_ceil B x]
  rw [logAverage]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hlogx)).2 (by simpa using hsum)

/-- Every logarithmic average is eventually between zero and three. -/
theorem eventually_logAverage_mem_Icc (B : Set ℕ) :
    ∀ᶠ x in atTop, logAverage B x ∈ Set.Icc (0 : ℝ) 3 := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hxone : 1 ≤ x := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      norm_num at h
      exact h
    linarith
  exact ⟨logAverage_nonneg B hxone, logAverage_le_three B hx⟩

/-- The logarithmic average is eventually bounded above along `atTop`. -/
theorem logAverage_isBoundedUnder_le (B : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (logAverage B) :=
  Filter.isBoundedUnder_of_eventually_le <|
    (eventually_logAverage_mem_Icc B).mono fun _ hx ↦ hx.2

/-- The logarithmic average is eventually bounded below along `atTop`. -/
theorem logAverage_isBoundedUnder_ge (B : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (logAverage B) :=
  Filter.isBoundedUnder_of_eventually_ge <|
    (eventually_logAverage_mem_Icc B).mono fun _ hx ↦ hx.1

end Erdos486


/-! Flattened from Erdos486.Global. -/

/-!
# Conditional global gliding-hump construction

Starting from `DyadicBlockInterface`, this module recursively installs long
runs of finite dyadic blocks.  Every new run begins at a cutoff where the
finite past has recovered.  The resulting fixed congruence system has a high
cofinal sequence and a low cofinal sequence of logarithmic averages.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

/-- The scales installed in an epoch beginning just above exponent `a`. -/
def epochScales (a : ℕ) : Finset ℕ :=
  Finset.Icc (a + 1) (2 * a + 1)

@[simp]
theorem mem_epochScales {a j : ℕ} :
    j ∈ epochScales a ↔ a + 1 ≤ j ∧ j ≤ 2 * a + 1 := by
  simp [epochScales]

@[simp]
theorem card_epochScales (a : ℕ) : (epochScales a).card = a + 1 := by
  simp [epochScales]
  omega

/-- Dyadic real cutoffs tend to infinity. -/
theorem tendsto_dyadic : Tendsto dyadic atTop atTop := by
  have hfun : dyadic = fun j : ℕ ↦ (2 : ℝ) ^ j := by
    funext j
    simp [dyadic, dyadicNat]
  rw [hfun]
  exact tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)

/-- Finite-past recovery supplies arbitrarily late dyadic recovery cutoffs.
The extra lower bounds are harmless and make the deletion estimate uniform. -/
theorem exists_recovery_start (I : DyadicBlockInterface) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, I.geometry.firstScale ≤ j) (bound : ℕ) :
    ∃ a : ℕ,
      bound ≤ a ∧ 100 ≤ a ∧ I.geometry.firstScale ≤ a + 1 ∧
        (49 : ℝ) / 50 ≤
          logAverage (blockSurvivors I.geometry (J : Set ℕ)) (dyadic a) := by
  obtain ⟨d, hd, hd_lower⟩ := I.finite_recovery J
  have hfoot := I.tail_budget J hJ
  have htarget : (49 : ℝ) / 50 < d := by
    linarith
  have hseq :
      Tendsto
        (fun a : ℕ ↦ logAverage (blockSurvivors I.geometry (J : Set ℕ)) (dyadic a))
        atTop (nhds d) :=
    hd.comp tendsto_dyadic
  have heventually :
      ∀ᶠ a : ℕ in atTop,
        (49 : ℝ) / 50 <
          logAverage (blockSurvivors I.geometry (J : Set ℕ)) (dyadic a) :=
    hseq.eventually (Ioi_mem_nhds htarget)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 heventually)
  let a := max N (max bound (max 100 I.geometry.firstScale))
  refine ⟨a, ?_, ?_, ?_, (hN a ?_).le⟩ <;>
    dsimp [a] <;> omega

/-- The finite state retained by the recursive gliding-hump construction. -/
structure GlideState (I : DyadicBlockInterface) where
  scales : Finset ℕ
  valid : ∀ j ∈ scales, I.geometry.firstScale ≤ j
  last : ℕ

/-- The empty initial finite past. -/
def initialGlideState (I : DyadicBlockInterface) : GlideState I where
  scales := ∅
  valid := by simp
  last := max 100 I.geometry.firstScale

/-- A recovery exponent chosen after the current finite past. -/
noncomputable def nextEpochStart (I : DyadicBlockInterface) (s : GlideState I) : ℕ :=
  Classical.choose (exists_recovery_start I s.scales s.valid (2 * s.last + 2))

theorem nextEpochStart_spec (I : DyadicBlockInterface) (s : GlideState I) :
    2 * s.last + 2 ≤ nextEpochStart I s ∧
      100 ≤ nextEpochStart I s ∧
      I.geometry.firstScale ≤ nextEpochStart I s + 1 ∧
      (49 : ℝ) / 50 ≤
        logAverage (blockSurvivors I.geometry (s.scales : Set ℕ))
          (dyadic (nextEpochStart I s)) :=
  Classical.choose_spec (exists_recovery_start I s.scales s.valid (2 * s.last + 2))

/-- Install one full epoch after its chosen recovery cutoff. -/
noncomputable def advanceGlideState (I : DyadicBlockInterface)
    (s : GlideState I) : GlideState I where
  scales := s.scales ∪ epochScales (nextEpochStart I s)
  valid := by
    intro j hj
    rcases Finset.mem_union.1 hj with hj | hj
    · exact s.valid j hj
    · exact (nextEpochStart_spec I s).2.2.1.trans (mem_epochScales.1 hj).1
  last := nextEpochStart I s

/-- The state before epoch `t`, defined by primitive recursion. -/
noncomputable def glideState (I : DyadicBlockInterface) : ℕ → GlideState I
  | 0 => initialGlideState I
  | t + 1 => advanceGlideState I (glideState I t)

/-- Start exponent of epoch `t`. -/
noncomputable def epochStart (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  nextEpochStart I (glideState I t)

@[simp]
theorem glideState_zero_scales (I : DyadicBlockInterface) :
    (glideState I 0).scales = ∅ := rfl

@[simp]
theorem glideState_succ_scales (I : DyadicBlockInterface) (t : ℕ) :
    (glideState I (t + 1)).scales =
      (glideState I t).scales ∪ epochScales (epochStart I t) := rfl

@[simp]
theorem glideState_succ_last (I : DyadicBlockInterface) (t : ℕ) :
    (glideState I (t + 1)).last = epochStart I t := rfl

theorem epochStart_spec (I : DyadicBlockInterface) (t : ℕ) :
    2 * (glideState I t).last + 2 ≤ epochStart I t ∧
      100 ≤ epochStart I t ∧
      I.geometry.firstScale ≤ epochStart I t + 1 ∧
      (49 : ℝ) / 50 ≤
        logAverage
          (blockSurvivors I.geometry ((glideState I t).scales : Set ℕ))
          (dyadic (epochStart I t)) :=
  nextEpochStart_spec I (glideState I t)

/-- Consecutive epoch starts have enough room for the preceding run. -/
theorem epochStart_growth (I : DyadicBlockInterface) (t : ℕ) :
    2 * epochStart I t + 2 ≤ epochStart I (t + 1) := by
  simpa using (epochStart_spec I (t + 1)).1

theorem epochStart_strictMono (I : DyadicBlockInterface) :
    StrictMono (epochStart I) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have h := epochStart_growth I t
  omega

theorem epochStart_tendsto (I : DyadicBlockInterface) :
    Tendsto (epochStart I) atTop atTop :=
  (epochStart_strictMono I).tendsto_atTop

/-- The state before epoch `t` consists exactly of the earlier epochs. -/
theorem mem_glideState_scales_iff (I : DyadicBlockInterface) {t j : ℕ} :
    j ∈ (glideState I t).scales ↔
      ∃ s < t, j ∈ epochScales (epochStart I s) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [glideState_succ_scales, Finset.mem_union]
      constructor
      · rintro (hj | hj)
        · obtain ⟨s, hst, hs⟩ := ih.1 hj
          exact ⟨s, Nat.lt_succ_of_lt hst, hs⟩
        · exact ⟨t, Nat.lt_succ_self t, hj⟩
      · rintro ⟨s, hst, hs⟩
        by_cases h : s < t
        · exact Or.inl (ih.2 ⟨s, h, hs⟩)
        · have hst' : s = t := by omega
          exact Or.inr (hst' ▸ hs)

/-- All scales installed over the infinite recursion. -/
def installedScales (I : DyadicBlockInterface) : Set ℕ :=
  {j | ∃ t, j ∈ epochScales (epochStart I t)}

theorem installedScales_valid (I : DyadicBlockInterface) {j : ℕ}
    (hj : j ∈ installedScales I) : I.geometry.firstScale ≤ j := by
  obtain ⟨t, ht⟩ := hj
  exact (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 ht).1

theorem glideState_scales_subset_installed (I : DyadicBlockInterface) (t : ℕ) :
    ((glideState I t).scales : Set ℕ) ⊆ installedScales I := by
  intro j hj
  obtain ⟨s, _hst, hs⟩ := (mem_glideState_scales_iff I).1 hj
  exact ⟨s, hs⟩

/-- The one fixed set of moduli installed by all epochs. -/
def globalModuli (I : DyadicBlockInterface) : Set ℕ :=
  blockModuli I.geometry (installedScales I)

/-- The one fixed residue assignment; equal moduli are grouped by
`blockResidues`. -/
def globalResidues (I : DyadicBlockInterface)
    (q : globalModuli I) : Set (ZMod (q : ℕ)) :=
  blockResidues I.geometry (installedScales I) q

/-- The final survivor set of the fixed global system. -/
def globalSurvivors (I : DyadicBlockInterface) : Set ℕ :=
  survivors (globalModuli I) (globalResidues I)

theorem globalSurvivors_eq (I : DyadicBlockInterface) :
    globalSurvivors I = blockSurvivors I.geometry (installedScales I) := rfl

theorem zero_not_mem_globalModuli (I : DyadicBlockInterface) :
    0 ∉ globalModuli I :=
  I.geometry.zero_not_mem_blockModuli fun _j hj ↦ installedScales_valid I hj

/-- The first scale of each epoch has at least one endpoint. -/
theorem epochBaseEndpoints_nonempty (I : DyadicBlockInterface) (t : ℕ) :
    (I.geometry.endpoints (epochStart I t + 1)).Nonempty := by
  apply Finset.card_pos.1
  have hcard :=
    I.geometry.enough_endpoints (epochStart_spec I t).2.2.1
  have hpow := dyadicNat_pos (epochStart I t + 1)
  omega

/-- A fixed endpoint chosen from the first scale of epoch `t`. -/
noncomputable def epochBaseEndpoint (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  Classical.choose (epochBaseEndpoints_nonempty I t)

theorem epochBaseEndpoint_mem (I : DyadicBlockInterface) (t : ℕ) :
    epochBaseEndpoint I t ∈
      I.geometry.endpoints (epochStart I t + 1) :=
  Classical.choose_spec (epochBaseEndpoints_nonempty I t)

/-- The modulus assigned to `epochBaseEndpoint`. -/
noncomputable def epochBaseModulus (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  I.geometry.modulus (epochStart I t + 1) (epochBaseEndpoint I t)

theorem epochBaseScale_mem (I : DyadicBlockInterface) (t : ℕ) :
    epochStart I t + 1 ∈ epochScales (epochStart I t) := by
  rw [mem_epochScales]
  constructor
  · rfl
  · have h := (epochStart_spec I t).2.1
    omega

theorem epochBaseModulus_mem_global (I : DyadicBlockInterface) (t : ℕ) :
    epochBaseModulus I t ∈ globalModuli I := by
  exact ⟨epochStart I t + 1, ⟨t, epochBaseScale_mem I t⟩,
    epochBaseEndpoint I t, epochBaseEndpoint_mem I t, rfl⟩

/-- Scale separation makes the selected epoch moduli strictly increasing. -/
theorem epochBaseModulus_strictMono (I : DyadicBlockInterface) :
    StrictMono (epochBaseModulus I) := by
  intro s t hst
  apply I.geometry.modulus_lt_of_scale_lt (epochStart_spec I s).2.2.1
  · have h := epochStart_strictMono I hst
    omega
  · exact epochBaseEndpoint_mem I s
  · exact epochBaseEndpoint_mem I t

/-- The fixed global system contains infinitely many distinct moduli. -/
theorem globalModuli_infinite (I : DyadicBlockInterface) :
    (globalModuli I).Infinite := by
  apply
    (Set.infinite_range_of_injective
      (epochBaseModulus_strictMono I).injective).mono
  intro q hq
  obtain ⟨t, rfl⟩ := hq
  exact epochBaseModulus_mem_global I t

/-- Future rows are inactive below the recovery cutoff, so the final survivor
set agrees there with the finite state used to choose that cutoff. -/
theorem globalSurvivors_iff_finitePast {I : DyadicBlockInterface} {t m : ℕ}
    (hmcut : (m : ℝ) < dyadic (epochStart I t)) :
    m ∈ globalSurvivors I ↔
      m ∈ blockSurvivors I.geometry ((glideState I t).scales : Set ℕ) := by
  let G := I.geometry
  have hmcut_nat : m < dyadicNat (epochStart I t) := by
    have hmcut' : (m : ℝ) < (dyadicNat (epochStart I t) : ℝ) := by
      simpa [dyadic] using hmcut
    exact_mod_cast hmcut'
  constructor
  · intro hm
    refine ⟨hm.1, ?_⟩
    intro q hqm hres
    let qGlobal : blockModuli G (installedScales I) :=
      ⟨(q : ℕ), by
        obtain ⟨j, hj, e, he, hq⟩ := q.property
        exact ⟨j, glideState_scales_subset_installed I t hj, e, he, hq⟩⟩
    apply hm.2 qGlobal hqm
    obtain ⟨j, hj, e, he, hq, hr⟩ := hres
    exact ⟨j, glideState_scales_subset_installed I t hj, e, he, hq, hr⟩
  · intro hm
    refine ⟨hm.1, ?_⟩
    intro q hqm hres
    obtain ⟨j, hj, e, he, hq, hr⟩ := hres
    obtain ⟨s, hs⟩ := hj
    by_cases hst : s < t
    · have hjpast : j ∈ (glideState I t).scales :=
        (mem_glideState_scales_iff I).2 ⟨s, hst, hs⟩
      let qPast : blockModuli G ((glideState I t).scales : Set ℕ) :=
        ⟨(q : ℕ), ⟨j, hjpast, e, he, hq⟩⟩
      apply hm.2 qPast hqm
      exact ⟨j, hjpast, e, he, hq, hr⟩
    · have hts : t ≤ s := by omega
      have hstart : epochStart I t ≤ epochStart I s :=
        (epochStart_strictMono I).monotone hts
      have hjlower : epochStart I s + 1 ≤ j := (mem_epochScales.1 hs).1
      have hexp : epochStart I t + 1 ≤ j := by omega
      have hpow : dyadicNat (epochStart I t + 1) ≤ dyadicNat j :=
        Nat.pow_le_pow_right (by norm_num) hexp
      have hjvalid : G.firstScale ≤ j := installedScales_valid I ⟨s, hs⟩
      have hmod := G.modulus_lower hjvalid he
      have hqcut : dyadicNat (epochStart I t) < (q : ℕ) := by
        rw [dyadic_succ] at hpow
        rw [hq] at hmod
        have hp := dyadicNat_pos (epochStart I t)
        omega
      omega

/-- Recovery cutoffs witness the high logarithmic averages of the final
fixed system. -/
theorem global_high (I : DyadicBlockInterface) (t : ℕ) :
    (49 : ℝ) / 50 ≤
      logAverage (globalSurvivors I) (dyadic (epochStart I t)) := by
  calc
    (49 : ℝ) / 50 ≤
        logAverage
          (blockSurvivors I.geometry ((glideState I t).scales : Set ℕ))
          (dyadic (epochStart I t)) := (epochStart_spec I t).2.2.2
    _ = logAverage (globalSurvivors I) (dyadic (epochStart I t)) := by
      symm
      apply logAverage_congr_below
      intro m hm
      exact globalSurvivors_iff_finitePast hm

/-- Endpoints contributed by every scale in epoch `t`. -/
noncomputable def epochEndpoints (I : DyadicBlockInterface) (t : ℕ) : Finset ℕ :=
  (epochScales (epochStart I t)).biUnion I.geometry.endpoints

/-- Endpoint intervals at different scales of one epoch are disjoint. -/
theorem epochEndpoints_pairwiseDisjoint (I : DyadicBlockInterface) (t : ℕ) :
    ((epochScales (epochStart I t) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      I.geometry.endpoints := by
  intro j hj k hk hjk
  apply Finset.disjoint_left.2
  intro m hmj hmk
  have hjvalid : I.geometry.firstScale ≤ j :=
    (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1
  have hkvalid : I.geometry.firstScale ≤ k :=
    (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hk).1
  rcases lt_or_gt_of_ne hjk with hjk' | hkj'
  · exact (Nat.lt_irrefl m)
      (I.geometry.endpoint_lt_of_scale_lt hjvalid hjk' hmj hmk)
  · exact (Nat.lt_irrefl m)
      (I.geometry.endpoint_lt_of_scale_lt hkvalid hkj' hmk hmj)

/-- A full epoch carries the sum of its per-scale harmonic deletion masses. -/
theorem epochEndpoints_harmonic_mass (I : DyadicBlockInterface) (t : ℕ) :
    ((epochStart I t + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76) ≤
      ∑ m ∈ epochEndpoints I t, (m : ℝ)⁻¹ := by
  let S := epochScales (epochStart I t)
  have hpair : (S : Set ℕ).PairwiseDisjoint I.geometry.endpoints := by
    simpa [S] using epochEndpoints_pairwiseDisjoint I t
  calc
    ((epochStart I t + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76) =
        ∑ _j ∈ S, ((15 : ℝ) / 76) := by
      simp [S]
    _ ≤ ∑ j ∈ S, ∑ m ∈ I.geometry.endpoints j, (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      exact I.geometry.endpoint_harmonic_mass
        ((epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1)
    _ = ∑ m ∈ epochEndpoints I t, (m : ℝ)⁻¹ := by
      symm
      exact Finset.sum_biUnion hpair

/-- Every endpoint in epoch `t` lies below its deletion cutoff. -/
theorem epochEndpoints_subset_range (I : DyadicBlockInterface) (t : ℕ) :
    epochEndpoints I t ⊆
      Finset.range (dyadicNat (2 * epochStart I t + 2)) := by
  intro m hm
  obtain ⟨j, hj, hm⟩ := Finset.mem_biUnion.1 hm
  have hjvalid : I.geometry.firstScale ≤ j :=
    (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1
  have hmj := I.geometry.endpoint_lt_next_dyadic hjvalid hm
  have hexp : j + 1 ≤ 2 * epochStart I t + 2 := by
    have := (mem_epochScales.1 hj).2
    omega
  have hpow : dyadicNat (j + 1) ≤ dyadicNat (2 * epochStart I t + 2) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  exact Finset.mem_range.2 (hmj.trans_le hpow)

/-- Every endpoint of an installed epoch is absent from the final survivor. -/
theorem epochEndpoints_not_mem_global (I : DyadicBlockInterface) (t : ℕ) :
    ∀ m ∈ epochEndpoints I t, m ∉ globalSurvivors I := by
  intro m hm
  obtain ⟨j, hj, hm⟩ := Finset.mem_biUnion.1 hm
  change m ∉ blockSurvivors I.geometry (installedScales I)
  exact I.geometry.endpoint_not_mem_blockSurvivors
    ⟨t, hj⟩ hm
    ((epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1)

/-- Removing a finite set below an integral cutoff subtracts its full
harmonic mass from the universal harmonic-number upper bound. -/
theorem logSum_add_deleted_le_harmonic (B : Set ℕ) (N : ℕ) (D : Finset ℕ)
    (hsub : D ⊆ Finset.range N) (hdisj : ∀ m ∈ D, m ∉ B) :
    logSum B (N : ℝ) + ∑ m ∈ D, (m : ℝ)⁻¹ ≤ (harmonic N : ℝ) := by
  have hlog :
      logSum B (N : ℝ) ≤
        ∑ m ∈ Finset.range N, if m ∉ D then (m : ℝ)⁻¹ else 0 := by
    unfold logSum
    simp only [Nat.ceil_natCast]
    apply Finset.sum_le_sum
    intro m hm
    have hmN : m < N := Finset.mem_range.1 hm
    have hmN' : (m : ℝ) < N := by exact_mod_cast hmN
    by_cases hmB : m ∈ B
    · have hmD : m ∉ D := fun hmD ↦ hdisj m hmD hmB
      simp [hmB, hmD, hmN']
    · by_cases hmD : m ∈ D <;> simp [hmB, hmD]
  have hsplit :
      (∑ m ∈ Finset.range N, if m ∉ D then (m : ℝ)⁻¹ else 0) +
          ∑ m ∈ D, (m : ℝ)⁻¹ =
        ∑ m ∈ Finset.range N, (m : ℝ)⁻¹ := by
    rw [← Finset.sum_filter]
    have hfilter :
        (Finset.range N).filter (fun m ↦ m ∉ D) = Finset.range N \ D := by
      ext m
      simp
    rw [hfilter]
    exact Finset.sum_sdiff hsub
  have htotal :
      (∑ m ∈ Finset.range N, (m : ℝ)⁻¹) ≤ (harmonic N : ℝ) := by
    by_cases hN : N = 0
    · simp [hN]
    · have hzero : 0 ∈ Finset.range N :=
        Finset.mem_range.2 (Nat.pos_of_ne_zero hN)
      have herase :
          (∑ m ∈ Finset.range N, (m : ℝ)⁻¹) =
            ∑ m ∈ (Finset.range N).erase 0, (m : ℝ)⁻¹ := by
        symm
        simpa using
          (Finset.sum_erase_add (s := Finset.range N)
            (f := fun m : ℕ ↦ (m : ℝ)⁻¹) hzero)
      rw [herase, harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        simp only [Finset.mem_erase, Finset.mem_range] at hm
        exact Finset.mem_Icc.2
          ⟨Nat.one_le_iff_ne_zero.2 hm.1, Nat.le_of_lt hm.2⟩
      · intro m _hm _hnot
        positivity
  calc
    logSum B (N : ℝ) + ∑ m ∈ D, (m : ℝ)⁻¹ ≤
        (∑ m ∈ Finset.range N, if m ∉ D then (m : ℝ)⁻¹ else 0) +
          ∑ m ∈ D, (m : ℝ)⁻¹ := add_le_add hlog le_rfl
    _ = ∑ m ∈ Finset.range N, (m : ℝ)⁻¹ := hsplit
    _ ≤ (harmonic N : ℝ) := htotal

/-- The deletion cutoff at epoch `t` has logarithmic average at most
`177 / 200`. -/
theorem global_low (I : DyadicBlockInterface) (t : ℕ) :
    logAverage (globalSurvivors I)
        (dyadic (2 * epochStart I t + 2)) ≤ (177 : ℝ) / 200 := by
  let a := epochStart I t
  let e := 2 * a + 2
  let N := dyadicNat e
  let D := epochEndpoints I t
  have hsub : D ⊆ Finset.range N := by
    simpa [D, N, e, a] using epochEndpoints_subset_range I t
  have hdisj : ∀ m ∈ D, m ∉ globalSurvivors I := by
    simpa [D] using epochEndpoints_not_mem_global I t
  have hdeleted :=
    logSum_add_deleted_le_harmonic (globalSurvivors I) N D hsub hdisj
  have htotal :
      logSum (globalSurvivors I) (dyadic e) +
          ∑ m ∈ D, (m : ℝ)⁻¹ ≤
        1 + Real.log (dyadic e) := by
    have h := hdeleted.trans (harmonic_le_one_add_log N)
    simpa [N, dyadic] using h
  have hmass :
      (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) ≤
        ∑ m ∈ D, (m : ℝ)⁻¹ := by
    simpa [a, D] using epochEndpoints_harmonic_mass I t
  have hnum :
      logSum (globalSurvivors I) (dyadic e) ≤
        1 + Real.log (dyadic e) -
          (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) := by
    linarith
  have hlog_eq :
      Real.log (dyadic e) = (e : ℝ) * Real.log 2 := by
    simp [dyadic, dyadicNat, Real.log_pow]
  have hlog_two_lower : (1 : ℝ) / 2 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog_two_upper : Real.log 2 < (3 : ℝ) / 4 := by
    linarith [Real.log_two_lt_d9]
  have ha100 : 100 ≤ a := by
    simpa [a] using (epochStart_spec I t).2.1
  have ha100_real : (100 : ℝ) ≤ a := by exact_mod_cast ha100
  have he_cast : (e : ℝ) = 2 * (a : ℝ) + 2 := by
    simp [e]
  have hlog_gt : 100 < Real.log (dyadic e) := by
    rw [hlog_eq, he_cast]
    nlinarith
  have hlog_pos : 0 < Real.log (dyadic e) := by linarith
  have herror :
      1 / Real.log (dyadic e) < (1 : ℝ) / 100 := by
    apply (div_lt_iff₀ hlog_pos).2
    nlinarith
  have hconstant :
      (1 : ℝ) / 4 * Real.log 2 < (15 : ℝ) / 76 := by
    nlinarith
  have ha_pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
  have hmass_ratio :
      (1 : ℝ) / 8 <
        (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) /
          Real.log (dyadic e) := by
    apply (lt_div_iff₀ hlog_pos).2
    calc
      (1 : ℝ) / 8 * Real.log (dyadic e) =
          ((a + 1 : ℕ) : ℝ) * ((1 : ℝ) / 4 * Real.log 2) := by
        rw [hlog_eq, he_cast]
        push_cast
        ring
      _ < ((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76) :=
        mul_lt_mul_of_pos_left hconstant ha_pos
  have hnormalized :
      logAverage (globalSurvivors I) (dyadic e) ≤
        1 + 1 / Real.log (dyadic e) -
          (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) /
            Real.log (dyadic e) := by
    rw [logAverage]
    calc
      logSum (globalSurvivors I) (dyadic e) / Real.log (dyadic e) ≤
          (1 + Real.log (dyadic e) -
              (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76))) /
            Real.log (dyadic e) :=
        (div_le_div_iff_of_pos_right hlog_pos).2 hnum
      _ = 1 + 1 / Real.log (dyadic e) -
          (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) /
            Real.log (dyadic e) := by
        field_simp [ne_of_gt hlog_pos]
        ring
  have hfinal :
      logAverage (globalSurvivors I) (dyadic e) ≤ (177 : ℝ) / 200 := by
    linarith
  simpa [e, a] using hfinal

/-- Exponents of the high recovery cutoffs. -/
noncomputable def recoveryExponent (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  epochStart I t

/-- Exponents of the low deletion cutoffs. -/
noncomputable def deletionExponent (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  2 * epochStart I t + 2

/-- The cofinal high cutoff sequence. -/
noncomputable def recoveryCutoff (I : DyadicBlockInterface) (t : ℕ) : ℝ :=
  dyadic (recoveryExponent I t)

/-- The cofinal low cutoff sequence. -/
noncomputable def deletionCutoff (I : DyadicBlockInterface) (t : ℕ) : ℝ :=
  dyadic (deletionExponent I t)

theorem recoveryExponent_strictMono (I : DyadicBlockInterface) :
    StrictMono (recoveryExponent I) := by
  intro s t hst
  change epochStart I s < epochStart I t
  exact epochStart_strictMono I hst

theorem deletionExponent_strictMono (I : DyadicBlockInterface) :
    StrictMono (deletionExponent I) := by
  intro s t hst
  have h := epochStart_strictMono I hst
  simp only [deletionExponent]
  omega

theorem recoveryCutoff_tendsto (I : DyadicBlockInterface) :
    Tendsto (recoveryCutoff I) atTop atTop := by
  exact tendsto_dyadic.comp (recoveryExponent_strictMono I).tendsto_atTop

theorem deletionCutoff_tendsto (I : DyadicBlockInterface) :
    Tendsto (deletionCutoff I) atTop atTop := by
  exact tendsto_dyadic.comp (deletionExponent_strictMono I).tendsto_atTop

theorem recoveryCutoff_high (I : DyadicBlockInterface) (t : ℕ) :
    (49 : ℝ) / 50 ≤
      logAverage (globalSurvivors I) (recoveryCutoff I t) := by
  simpa [recoveryCutoff, recoveryExponent] using global_high I t

theorem deletionCutoff_low (I : DyadicBlockInterface) (t : ℕ) :
    logAverage (globalSurvivors I) (deletionCutoff I t) ≤
      (177 : ℝ) / 200 := by
  simpa [deletionCutoff, deletionExponent] using global_low I t

/-- The cofinal deletion cutoffs make the low inequality frequent at
`atTop`. -/
theorem frequently_global_low (I : DyadicBlockInterface) :
    ∃ᶠ x in (atTop : Filter ℝ),
      logAverage (globalSurvivors I) x ≤ (177 : ℝ) / 200 := by
  intro hnot
  have heventually :
      ∀ᶠ t : ℕ in atTop,
        ¬logAverage (globalSurvivors I) (deletionCutoff I t) ≤
          (177 : ℝ) / 200 :=
    deletionCutoff_tendsto I hnot
  obtain ⟨t, ht⟩ := heventually.exists
  exact ht (deletionCutoff_low I t)

/-- The cofinal recovery cutoffs make the high inequality frequent at
`atTop`. -/
theorem frequently_global_high (I : DyadicBlockInterface) :
    ∃ᶠ x in (atTop : Filter ℝ),
      (49 : ℝ) / 50 ≤ logAverage (globalSurvivors I) x := by
  intro hnot
  have heventually :
      ∀ᶠ t : ℕ in atTop,
        ¬(49 : ℝ) / 50 ≤
          logAverage (globalSurvivors I) (recoveryCutoff I t) :=
    recoveryCutoff_tendsto I hnot
  obtain ⟨t, ht⟩ := heventually.exists
  exact ht (recoveryCutoff_high I t)

/-- The low cofinal sequence bounds the actual filter liminf. -/
theorem global_liminf_le (I : DyadicBlockInterface) :
    liminf (logAverage (globalSurvivors I)) atTop ≤ (177 : ℝ) / 200 := by
  exact liminf_le_of_frequently_le
    (frequently_global_low I)
    (logAverage_isBoundedUnder_ge (globalSurvivors I))

/-- The high cofinal sequence bounds the actual filter limsup. -/
theorem le_global_limsup (I : DyadicBlockInterface) :
    (49 : ℝ) / 50 ≤
      limsup (logAverage (globalSurvivors I)) atTop := by
  exact le_limsup_of_frequently_le
    (frequently_global_high I)
    (logAverage_isBoundedUnder_le (globalSurvivors I))

/-- The two cofinal sequences rule out every logarithmic density value. -/
theorem global_hasNoLogDensity (I : DyadicBlockInterface) :
    ¬∃ d : ℝ, HasLogDensity (globalSurvivors I) d := by
  rintro ⟨d, hd⟩
  exact (not_hasLogDensity_of_cofinal_ge_of_cofinal_le
    (globalSurvivors I) (by norm_num)
    (recoveryCutoff I) (deletionCutoff I)
    (recoveryCutoff_tendsto I) (deletionCutoff_tendsto I)
    (recoveryCutoff_high I) (deletionCutoff_low I) d) hd

/-- Conditional global theorem.  The moduli and residue sets in the
conclusion are fixed before either cofinal cutoff sequence is considered. -/
theorem exists_fixed_system_of_dyadicBlockInterface (I : DyadicBlockInterface) :
    ∃ (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))),
      0 ∉ A ∧
      ∃ upper lower : ℕ → ℝ,
        Tendsto upper atTop atTop ∧
        Tendsto lower atTop atTop ∧
        (∀ t, (49 : ℝ) / 50 ≤ logAverage (survivors A X) (upper t)) ∧
        (∀ t, logAverage (survivors A X) (lower t) ≤ (177 : ℝ) / 200) ∧
        (∀ d : ℝ, ¬HasLogDensity (survivors A X) d) := by
  refine ⟨globalModuli I, globalResidues I, zero_not_mem_globalModuli I,
    recoveryCutoff I, deletionCutoff I,
    recoveryCutoff_tendsto I, deletionCutoff_tendsto I, ?_, ?_, ?_⟩
  · intro t
    exact recoveryCutoff_high I t
  · intro t
    exact deletionCutoff_low I t
  · exact not_hasLogDensity_of_cofinal_ge_of_cofinal_le
      (globalSurvivors I) (by norm_num)
      (recoveryCutoff I) (deletionCutoff I)
      (recoveryCutoff_tendsto I) (deletionCutoff_tendsto I)
      (recoveryCutoff_high I) (deletionCutoff_low I)

/-- Every instance of the finite dyadic-block interface yields the complete
quantitative counterexample claimed in the manuscript. -/
theorem quantitativeCounterexample_of_dyadicBlockInterface
    (I : DyadicBlockInterface) : QuantitativeCounterexample := by
  refine ⟨globalModuli I, globalModuli_infinite I,
    zero_not_mem_globalModuli I, globalResidues I,
    global_hasNoLogDensity I, global_liminf_le I, le_global_limsup I⟩

/-- The finite-block interface implies a negative answer to the original
universal assertion. -/
theorem not_erdos486Assertion_of_dyadicBlockInterface
    (I : DyadicBlockInterface) : ¬Erdos486Assertion := by
  exact quantitativeCounterexample_not_assertion
    (quantitativeCounterexample_of_dyadicBlockInterface I)

end Erdos486


/-! Flattened from Erdos486.Main. -/

/-! # Final theorems for Erdős Problem 486 -/

namespace Erdos486

/-- The fully instantiated quantitative counterexample. -/
theorem erdos486_quantitativeCounterexample : QuantitativeCounterexample :=
  quantitativeCounterexample_of_dyadicBlockInterface erdos486BlockInterface

/-- Erdős Problem 486 has a negative answer. -/
theorem erdos486_negative : ¬Erdos486Assertion :=
  not_erdos486Assertion_of_dyadicBlockInterface erdos486BlockInterface

end Erdos486


namespace Submissions.Erdos486DelayedCongruenceCounterexample.Full

theorem proof :
    ∃ (A : Set ℕ), 0 ∉ A ∧
      ∃ X : (n : A) → Set (ZMod (n : ℕ)),
        ¬ ∃ d : ℝ, Erdos486.HasLogDensity (Erdos486.survivors A X) d := by
  rcases Erdos486.erdos486_quantitativeCounterexample with
    ⟨A, _hAInfinite, hAZero, X, hNoDensity, _hLow, _hHigh⟩
  exact ⟨A, hAZero, X, hNoDensity⟩

end Submissions.Erdos486DelayedCongruenceCounterexample.Full

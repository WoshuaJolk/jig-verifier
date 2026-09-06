import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.BigOperators

open Filter

/-
This proof generalizes the smooth-band construction introduced by Declan Gessel
in Jig statement 40 and quantitatively strengthened by Cole Benefield in
statement 42. The inherited ingredients are the smooth-number exponent encoding,
near-band closure, and coprime-residue injection. The new step varies the dyadic
band width and proves a uniform Wallis-type lower bound for the relevant finite
Euler product, making the achievable density amplification unbounded.
-/

namespace Submissions.E488Unbounded.Cole


lemma exists_two_pow_gt_const_mul_pow (d C : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧ C * n ^ d < 2 ^ n := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (by norm_num : (1 : ℝ) < 2))
  have he : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ d‖ ≤ (1 / ((C : ℝ) + 1)) * ‖(2 : ℝ) ^ n‖ :=
    h.def (by positivity)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 he)
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  have hh := hN (max N 2) (le_max_left _ _)
  norm_num [Real.norm_eq_abs, abs_of_nonneg] at hh ⊢
  have hc : (C : ℝ) < C + 1 := by norm_num
  have hn : (0 : ℝ) < ((max N 2 : ℕ) : ℝ) ^ d := by positivity
  have hr : (C : ℝ) * ((max N 2 : ℕ) : ℝ) ^ d < (2 : ℝ) ^ (max N 2) := by
    calc
      (C : ℝ) * ((max N 2 : ℕ) : ℝ) ^ d
          < (C + 1) * ((max N 2 : ℕ) : ℝ) ^ d := by nlinarith
      _ ≤ (2 : ℝ) ^ (max N 2) := by
        apply (le_div_iff₀' (by positivity : (0 : ℝ) < C + 1)).mp
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  exact_mod_cast hr

open Finset

lemma wallis_odd_lower (N : ℕ) :
    (1 : ℚ) / ((2 * N + 1 : ℕ) : ℚ) ≤
      (∏ i ∈ range N, ((2 * i + 2 : ℕ) : ℚ) / (2 * i + 3)) ^ 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [prod_range_succ]
    have hpos : (0 : ℚ) < 2 * N + 1 := by positivity
    have hstep : (1 : ℚ) / ((2 * (N + 1) + 1 : ℕ) : ℚ) ≤
        (1 / ((2 * N + 1 : ℕ) : ℚ)) *
          ((((2 * N + 2 : ℕ) : ℚ) / (2 * N + 3)) *
            (((2 * N + 2 : ℕ) : ℚ) / (2 * N + 3))) := by
      norm_num [div_eq_mul_inv] at *
      field_simp
      nlinarith
    calc
      (1 : ℚ) / ((2 * (N + 1) + 1 : ℕ) : ℚ) ≤
          (1 / ((2 * N + 1 : ℕ) : ℚ)) *
            ((((2 * N + 2 : ℕ) : ℚ) / (2 * N + 3)) *
              (((2 * N + 2 : ℕ) : ℚ) / (2 * N + 3))) := hstep
      _ ≤ ((∏ i ∈ range N, ((2 * i + 2 : ℕ) : ℚ) / (2 * i + 3)) ^ 2) *
            ((((2 * N + 2 : ℕ) : ℚ) / (2 * N + 3)) *
              (((2 * N + 2 : ℕ) : ℚ) / (2 * N + 3))) :=
        mul_le_mul_of_nonneg_right ih (mul_nonneg (by positivity) (by positivity))
      _ = ((∏ i ∈ range N, ((2 * i + 2 : ℕ) : ℚ) / (2 * i + 3)) *
            (((2 * N + 2 : ℕ) : ℚ) / (2 * N + 3))) ^ 2 := by ring

def base (r : ℕ) : ℕ := 2 ^ r
def primes (r : ℕ) : Finset ℕ := Nat.primesBelow (base r + 1)
def oddPrimes (r : ℕ) : Finset ℕ := (primes r).erase 2
def oddNumbers (r : ℕ) : Finset ℕ :=
  (range (base r / 2 - 1)).image (fun i => 2 * i + 3)
def Q (r : ℕ) : ℕ := ∏ p ∈ oddPrimes r, p
def phiOdd (r : ℕ) : ℕ := ∏ p ∈ oddPrimes r, (p - 1)

lemma oddPrimes_subset_oddNumbers {r : ℕ} (hr : 2 ≤ r) :
    oddPrimes r ⊆ oddNumbers r := by
  intro p hp
  have hp' := Finset.mem_erase.mp hp
  have hprime : p.Prime := (Nat.mem_primesBelow.mp hp'.2).2
  have hplt : p < base r + 1 := (Nat.mem_primesBelow.mp hp'.2).1
  obtain ⟨j, hj⟩ := hprime.odd_of_ne_two hp'.1
  have hp3 : 3 ≤ p := (hprime.odd_iff.mp ⟨j, hj⟩)
  have hbase : 4 ≤ base r := by
    simpa [base] using (Nat.pow_le_pow_right (n := 2) (by omega) hr)
  have hbeven : Even (base r) := by
    refine ⟨2 ^ (r - 1), ?_⟩
    rw [base, show r = (r - 1) + 1 by omega, pow_succ]
    have hs : r - 1 + 1 - 1 = r - 1 := by omega
    rw [hs]
    omega
  apply Finset.mem_image.mpr
  refine ⟨j - 1, Finset.mem_range.mpr ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hbeven
    have hdiv : base r / 2 = q := by omega
    rw [hdiv]
    omega
  · omega

lemma odd_product_eq {r : ℕ} :
    ∏ d ∈ oddNumbers r, (((d - 1 : ℕ) : ℚ) / d) =
      ∏ i ∈ range (base r / 2 - 1),
        (((2 * i + 2 : ℕ) : ℚ) / (2 * i + 3)) := by
  rw [oddNumbers, prod_image]
  · congr 1
    funext i
    norm_num
  · exact (by
      intro i j hij
      dsimp at hij
      omega : Function.Injective (fun i : ℕ => 2 * i + 3)).injOn

lemma prime_ratio_eq (r : ℕ) :
    ∏ p ∈ oddPrimes r, (((p - 1 : ℕ) : ℚ) / p) =
      (phiOdd r : ℚ) / Q r := by
  rw [prod_div_distrib]
  simp only [phiOdd, Q, Nat.cast_prod]

lemma prime_ratio_ge_odd_product {r : ℕ} (hr : 2 ≤ r) :
    (∏ d ∈ oddNumbers r, (((d - 1 : ℕ) : ℚ) / d)) ≤
      ∏ p ∈ oddPrimes r, (((p - 1 : ℕ) : ℚ) / p) := by
  apply Finset.prod_le_prod_of_subset_of_le_one (oddPrimes_subset_oddNumbers hr)
  · intro d hd
    positivity
  · intro d hd hnot
    have hd3 : 3 ≤ d := by
      rw [oddNumbers] at hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      omega
    apply (div_le_one (by positivity : (0 : ℚ) < d)).mpr
    exact_mod_cast (Nat.sub_le d 1)

lemma base_mul_phiOdd_sq_ge_Q_sq {r : ℕ} (hr : 2 ≤ r) :
    (Q r) ^ 2 ≤ base r * (phiOdd r) ^ 2 := by
  have hbase : 4 ≤ base r := by
    simpa [base] using (Nat.pow_le_pow_right (n := 2) (by omega) hr)
  have hbeven : Even (base r) := by
    refine ⟨2 ^ (r - 1), ?_⟩
    rw [base, show r = (r - 1) + 1 by omega, pow_succ]
    have hs : r - 1 + 1 - 1 = r - 1 := by omega
    rw [hs]
    omega
  obtain ⟨b, hb⟩ := hbeven
  have hdiv : base r / 2 = b := by omega
  have hN : 2 * (base r / 2 - 1) + 1 = base r - 1 := by omega
  have hwall := wallis_odd_lower (base r / 2 - 1)
  rw [hN, ← odd_product_eq] at hwall
  have hsubset := prime_ratio_ge_odd_product hr
  have hsquares :
      ((∏ d ∈ oddNumbers r, (((d - 1 : ℕ) : ℚ) / d)) ^ 2) ≤
        ((∏ p ∈ oddPrimes r, (((p - 1 : ℕ) : ℚ) / p)) ^ 2) := by
    gcongr
  have hrat : (1 : ℚ) / base r ≤ ((phiOdd r : ℚ) / Q r) ^ 2 := by
    rw [← prime_ratio_eq]
    refine (div_le_div_of_nonneg_left (by norm_num) (by
      exact_mod_cast (by omega : 0 < base r - 1)) ?_).trans (hwall.trans hsquares)
    exact_mod_cast (Nat.sub_le (base r) 1)
  have hQpos : 0 < Q r := by
    dsimp [Q]
    exact prod_pos fun p hp => (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).2.pos
  have hBrat : (0 : ℚ) < base r := by positivity
  rw [div_pow] at hrat
  have hcross := (div_le_div_iff₀ hBrat (by positivity : (0 : ℚ) < (Q r : ℚ) ^ 2)).mp hrat
  norm_num at hcross
  simpa [mul_comm] using (by exact_mod_cast hcross : (Q r) ^ 2 ≤ (phiOdd r) ^ 2 * base r)

def oddSmoothUpTo (r T : ℕ) : Finset ℕ :=
  (Icc 1 T).filter (fun d => d ∈ Nat.factoredNumbers (oddPrimes r))

def H (r k : ℕ) : ℕ := (oddSmoothUpTo r ((base r) ^ k)).card

def band (r T : ℕ) : Finset ℕ :=
  (Ioc T (base r * T)).filter (fun a => a ∈ Nat.factoredNumbers (primes r))

def multiples (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun j => ∃ a ∈ A, a ∣ j)

lemma primes_two {r : ℕ} (hr : 1 ≤ r) : 2 ∈ primes r := by
  rw [primes, Nat.mem_primesBelow]
  refine ⟨?_, Nat.prime_two⟩
  have hpow : 2 ≤ base r := by
    simpa [base] using (Nat.pow_le_pow_right (n := 2) (by omega) hr)
  omega

lemma oddPrimes_no_two (r : ℕ) : 2 ∉ oddPrimes r := by simp [oddPrimes]

lemma insert_two_oddPrimes {r : ℕ} (hr : 1 ≤ r) :
    insert 2 (oddPrimes r) = primes r := by
  exact Finset.insert_erase (primes_two hr)

lemma mem_primes_prime {r p : ℕ} (hp : p ∈ primes r) : p.Prime :=
  (Nat.mem_primesBelow.mp hp).2

lemma mem_oddPrimes_prime {r p : ℕ} (hp : p ∈ oddPrimes r) : p.Prime :=
  mem_primes_prime (Finset.mem_of_mem_erase hp)

lemma base_pos (r : ℕ) : 0 < base r := by simp [base]

lemma power_residue_unique {r T d e f : ℕ} (hr : 1 ≤ r)
    (he : T < 2 ^ e * d) (he' : 2 ^ e * d ≤ base r * T)
    (hf : T < 2 ^ f * d) (hf' : 2 ^ f * d ≤ base r * T)
    (hmod : e % r = f % r) : e = f := by
  have exclude (a b : ℕ) (ha : T < 2 ^ a * d)
      (hb : 2 ^ b * d ≤ base r * T) (hab : a + r ≤ b) : False := by
    have hp : (2 : ℕ) ^ (a + r) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hab
    have hm := Nat.mul_le_mul_right d hp
    have hBT : base r * T < base r * (2 ^ a * d) :=
      Nat.mul_lt_mul_of_pos_left ha (base_pos r)
    have horder : base r * (2 ^ a * d) = 2 ^ (a + r) * d := by
      simp only [base, pow_add]
      ring
    rw [horder] at hBT
    omega
  by_contra hne
  have ha : e + r ≤ f ∨ f + r ≤ e := by
    have hm : e ≡ f [MOD r] := hmod
    rcases lt_or_gt_of_ne hne with hef | hfe
    · exact Or.inl (hm.add_le_of_lt hef)
    · exact Or.inr (hm.symm.add_le_of_lt hfe)
  rcases ha with ha | ha
  · exact exclude e f he hf' ha
  · exact exclude f e hf he' ha

lemma band_zero_not_mem (r T : ℕ) : 0 ∉ band r T := by simp [band]

lemma band_le {r T a : ℕ} (ha : a ∈ band r T) : a ≤ base r * T :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).2

lemma band_pos {r T a : ℕ} (ha : a ∈ band r T) : 0 < a := by
  have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).1
  omega

lemma band_mem_factored {r T a : ℕ} (ha : a ∈ band r T) :
    a ∈ Nat.factoredNumbers (primes r) := (Finset.mem_filter.mp ha).2

lemma small_mem_factored {r a : ℕ} (ha : 0 < a) (ha' : a < base r + 1) :
    a ∈ Nat.factoredNumbers (primes r) := by
  rw [Nat.mem_factoredNumbers_iff_forall_le]
  refine ⟨by omega, ?_⟩
  intro p hp hprime hdvd
  exact Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt (Nat.le_of_dvd ha hdvd) ha', hprime⟩

lemma multiples_band_eq {r T : ℕ} : multiples (band r T) (base r * T) = band r T := by
  ext j
  constructor
  · intro hj
    obtain ⟨hj, a, ha, hadvd⟩ := Finset.mem_filter.mp hj
    have hjpos := (Finset.mem_Icc.mp hj).1
    have hjle := (Finset.mem_Icc.mp hj).2
    have hagt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).1
    have has := band_mem_factored ha
    obtain ⟨c, rfl⟩ := hadvd
    have hcpos : 0 < c := by nlinarith
    have hclt : c < base r + 1 := by nlinarith
    have hcs := small_mem_factored hcpos hclt
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, hjle⟩,
      Nat.mul_mem_factoredNumbers has hcs⟩
    have : a ≤ a * c := Nat.le_mul_of_pos_right a hcpos
    omega
  · intro hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨band_pos hj, band_le hj⟩,
      j, hj, dvd_refl _⟩

noncomputable def bandSplit {r T : ℕ} (hr : 1 ≤ r) (j : band r T) :
    ℕ × Nat.factoredNumbers (oddPrimes r) :=
  (Nat.equivProdNatFactoredNumbers Nat.prime_two (oddPrimes_no_two r)).symm
    ⟨j, by simpa [insert_two_oddPrimes hr] using band_mem_factored j.2⟩

lemma bandSplit_eq {r T : ℕ} (hr : 1 ≤ r) (j : band r T) :
    2 ^ (bandSplit hr j).1 * (bandSplit hr j).2.val = j.val := by
  have h := (Nat.equivProdNatFactoredNumbers Nat.prime_two (oddPrimes_no_two r)).apply_symm_apply
    ⟨j.val, by simpa [insert_two_oddPrimes hr] using band_mem_factored j.2⟩
  exact congrArg Subtype.val h

lemma bandSplit_mem {r T : ℕ} (hr : 1 ≤ r) (j : band r T) :
    (bandSplit hr j).2.val ∈ oddSmoothUpTo r (base r * T) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, (bandSplit hr j).2.property⟩
  · exact Nat.pos_of_ne_zero (bandSplit hr j).2.property.1
  · have hp : 0 < (2 : ℕ) ^ (bandSplit hr j).1 := pow_pos (by omega) _
    have hd := Nat.le_mul_of_pos_left (bandSplit hr j).2.val hp
    rw [bandSplit_eq hr j] at hd
    exact hd.trans (band_le j.2)

noncomputable def bandEncode {r T : ℕ} (hr : 1 ≤ r) (j : band r T) :
    oddSmoothUpTo r (base r * T) × Fin r :=
  (⟨(bandSplit hr j).2.val, bandSplit_mem hr j⟩,
    ⟨(bandSplit hr j).1 % r, Nat.mod_lt _ (by omega)⟩)

lemma bandEncode_injective {r T : ℕ} (hr : 1 ≤ r) :
    Function.Injective (@bandEncode r T hr) := by
  intro j k heq
  have hd : (bandSplit hr j).2.val = (bandSplit hr k).2.val :=
    congrArg (fun z => z.1.val) heq
  have hmod : (bandSplit hr j).1 % r = (bandSplit hr k).1 % r :=
    congrArg (fun z => z.2.val) heq
  have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp j.2).1
  have hk := Finset.mem_Ioc.mp (Finset.mem_filter.mp k.2).1
  have hje := bandSplit_eq hr j
  have hke := bandSplit_eq hr k
  rw [← hd] at hke
  have he : (bandSplit hr j).1 = (bandSplit hr k).1 :=
    power_residue_unique hr (hje ▸ hj.1) (hje ▸ hj.2)
      (hke ▸ hk.1) (hke ▸ hk.2) hmod
  apply Subtype.ext
  rw [← hje, ← hke, he]

lemma band_card_le {r T : ℕ} (hr : 1 ≤ r) :
    (band r T).card ≤ r * (oddSmoothUpTo r (base r * T)).card := by
  have h := Fintype.card_le_of_injective (@bandEncode r T hr) (bandEncode_injective hr)
  simpa [Fintype.card_prod, Nat.mul_comm] using h

lemma near_bound {r : ℕ} (hr : 1 ≤ r) (T : ℕ) :
    (multiples (band r T) (base r * T)).card ≤
      r * (oddSmoothUpTo r (base r * T)).card := by
  rw [multiples_band_eq]
  exact band_card_le hr

lemma two_mul_pow_mem_band {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    2 * (base r) ^ k ∈ band r ((base r) ^ k) := by
  have ht : 0 < (base r) ^ k := pow_pos (base_pos r) _
  have hbase : 2 ≤ base r := by
    simpa [base] using (Nat.pow_le_pow_right (n := 2) (by omega) hr)
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by nlinarith⟩, ?_⟩
  apply Nat.mul_mem_factoredNumbers
  · exact small_mem_factored (by omega) (by omega)
  · rw [Nat.mem_factoredNumbers']
    intro p hp hpd
    have hpd' := hp.dvd_of_dvd_pow hpd
    exact Nat.mem_primesBelow.mpr
      ⟨lt_of_le_of_lt (Nat.le_of_dvd (base_pos r) hpd') (by omega), hp⟩

lemma band_nonempty_pow {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (band r ((base r) ^ k)).Nonempty :=
  ⟨2 * (base r) ^ k, two_mul_pow_mem_band hr k⟩

lemma primeFactors_card_le (s : Finset ℕ) (b : ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    ((Icc 1 (2 ^ b)).filter (fun n => n ≠ 0 ∧ n.primeFactors ⊆ s)).card ≤
      (b + 1) ^ s.card := by
  classical
  let X := (Icc 1 (2 ^ b)).filter (fun n => n ≠ 0 ∧ n.primeFactors ⊆ s)
  have hx (n : X) : 1 ≤ (n : ℕ) ∧ (n : ℕ) ≤ 2 ^ b ∧
      (n : ℕ) ≠ 0 ∧ (n : ℕ).primeFactors ⊆ s := by
    have hh := (mem_filter.mp n.property)
    exact ⟨(mem_Icc.mp hh.1).1, (mem_Icc.mp hh.1).2, hh.2⟩
  let f : X → (s → Fin (b + 1)) := fun n p =>
    ⟨(n : ℕ).factorization p, Nat.lt_succ_of_le <| Nat.factorization_le_of_le_pow <|
      (hx n).2.1.trans (Nat.pow_le_pow_left (hs p p.property) b)⟩
  have hf : Function.Injective f := by
    intro a c hac
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (by have := (hx a).1; omega)
      (by have := (hx c).1; omega)
    intro p
    by_cases hp : p ∈ s
    · have he := congrArg (fun z : s → Fin (b + 1) => (z ⟨p, hp⟩).val) hac
      exact he
    · have hz (n : X) : (n : ℕ).factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rw [Nat.support_factorization]
        intro hmem
        exact hp ((hx n).2.2.2 hmem)
      rw [hz a, hz c]
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hcard

lemma H_polynomial_bound (r k : ℕ) :
    H r k ≤ (r * k + 1) ^ (oddPrimes r).card := by
  have hb := primeFactors_card_le (oddPrimes r) (r * k)
    (fun p hp => (mem_oddPrimes_prime hp).two_le)
  have he : 2 ^ (r * k) = (base r) ^ k := by rw [base, pow_mul]
  simpa only [he, H, oddSmoothUpTo,
    Nat.mem_factoredNumbers_iff_primeFactors_subset] using hb

lemma H_zero_pos (r : ℕ) : 1 ≤ H r 0 := by
  have hone : 1 ∈ oddSmoothUpTo r ((base r) ^ 0) := by
    simp [oddSmoothUpTo, Nat.mem_factoredNumbers]
  exact Finset.one_le_card.mpr ⟨1, hone⟩

lemma exists_slow_H (r : ℕ) : ∃ k : ℕ, H r (k + 1) ≤ 2 * H r k := by
  obtain ⟨N, hNpos, hgap⟩ :=
    exists_two_pow_gt_const_mul_pow (oddPrimes r).card ((r + 1) ^ (oddPrimes r).card)
  have hpoly : H r N < 2 ^ N := by
    refine (H_polynomial_bound r N).trans_lt ?_
    have haff : r * N + 1 ≤ (r + 1) * N := by nlinarith
    exact (Nat.pow_le_pow_left haff _).trans_lt (by
      simpa [mul_pow] using hgap)
  by_contra hnone
  push_neg at hnone
  have hgrowth : ∀ k ≤ N, 2 ^ k ≤ H r k := by
    intro k hk
    induction k with
    | zero => simpa using H_zero_pos r
    | succ k ih =>
      have hi := ih (by omega)
      have hs := hnone k
      calc
        2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
        _ ≤ 2 * H r k := Nat.mul_le_mul_left 2 hi
        _ ≤ H r (k + 1) := by omega
  exact (not_le_of_gt hpoly) (hgrowth N le_rfl)

lemma Q_gt_one {r : ℕ} (hr : 2 ≤ r) : 1 < Q r := by
  have h3 : 3 ∈ oddPrimes r := by
    rw [oddPrimes, Finset.mem_erase, primes, Nat.mem_primesBelow]
    refine ⟨by omega, ?_, Nat.prime_three⟩
    have hbase : 4 ≤ base r := by
      simpa [base] using (Nat.pow_le_pow_right (n := 2) (by omega) hr)
    omega
  have hdvd : 3 ∣ Q r := Finset.dvd_prod_of_mem (fun q : ℕ => q) h3
  exact lt_of_lt_of_le (by omega) (Nat.le_of_dvd (by
    dsimp [Q]; exact prod_pos fun p hp => (mem_oddPrimes_prime hp).pos) hdvd)

lemma oddSmooth_coprime_residue {r d u : ℕ}
    (hd : d ∈ Nat.factoredNumbers (oddPrimes r)) (hu : (Q r).Coprime u) :
    d.Coprime u := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpu
  have hpP : p ∈ oddPrimes r := Nat.mem_factoredNumbers'.mp hd p hp hpd
  have hpQ : p ∣ Q r := Finset.dvd_prod_of_mem (fun q : ℕ => q) hpP
  have hcop : p.Coprime u := hu.of_dvd_left hpQ
  exact (hp.coprime_iff_not_dvd.mp hcop) hpu

lemma oddSmooth_coprime_two {r d : ℕ}
    (hd : d ∈ Nat.factoredNumbers (oddPrimes r)) : d.Coprime 2 :=
  (Nat.prime_two.factoredNumbers_coprime (oddPrimes_no_two r) hd).symm

lemma dyadic_crossing {T d : ℕ} (hd : 0 < d) (hdT : d ≤ T) :
    ∃ e : ℕ, T < 2 ^ e * d ∧ 2 ^ e * d ≤ 2 * T := by
  have hex : ∃ e : ℕ, T < 2 ^ e * d := by
    refine ⟨T, lt_of_lt_of_le T.lt_two_pow_self ?_⟩
    exact Nat.le_mul_of_pos_right _ hd
  let e := Nat.find hex
  have hlt : T < 2 ^ e * d := Nat.find_spec hex
  have he : 0 < e := by
    by_contra hn
    have he0 : e = 0 := by omega
    simp only [he0, pow_zero, one_mul] at hlt
    omega
  have hprev : 2 ^ (e - 1) * d ≤ T := by
    exact Nat.le_of_not_gt (Nat.find_min hex (by omega))
  refine ⟨e, hlt, ?_⟩
  have heq : e = e - 1 + 1 := by omega
  rw [heq, pow_succ]
  nlinarith

lemma far_pair_injective {r d d' u u' e e' : ℕ}
    (hd : d ∈ Nat.factoredNumbers (oddPrimes r))
    (hd' : d' ∈ Nat.factoredNumbers (oddPrimes r))
    (hu : (Q r).Coprime u) (hu' : (Q r).Coprime u')
    (heq : (2 ^ e * d) * u = (2 ^ e' * d') * u') : d = d' := by
  have hdiv : d ∣ d' := by
    have h : d ∣ (2 ^ e' * d') * u' := by
      rw [← heq]
      exact dvd_mul_of_dvd_left (dvd_mul_left d (2 ^ e)) u
    have h' : d ∣ 2 ^ e' * d' :=
      (oddSmooth_coprime_residue hd hu').dvd_of_dvd_mul_right h
    exact ((oddSmooth_coprime_two hd).pow_right e').dvd_of_dvd_mul_left h'
  have hdiv' : d' ∣ d := by
    have h : d' ∣ (2 ^ e * d) * u := by
      rw [heq]
      exact dvd_mul_of_dvd_left (dvd_mul_left d' (2 ^ e')) u'
    have h' : d' ∣ 2 ^ e * d :=
      (oddSmooth_coprime_residue hd' hu).dvd_of_dvd_mul_right h
    exact ((oddSmooth_coprime_two hd').pow_right e).dvd_of_dvd_mul_left h'
  exact Nat.dvd_antisymm hdiv hdiv'

lemma combined_multiplier_injective {q u u' v v' : ℕ} (hq : 0 < q)
    (hu : u < q) (hu' : u' < q)
    (heq : u + q * v = u' + q * v') : u = u' ∧ v = v' := by
  have humod : (u + q * v) % q = u := by simp [Nat.mod_eq_of_lt hu]
  have hu'mod : (u' + q * v') % q = u' := by simp [Nat.mod_eq_of_lt hu']
  have huu : u = u' := by rw [← humod, heq, hu'mod]
  subst u'
  constructor
  · rfl
  · have hmul : q * v = q * v' := Nat.add_left_cancel heq
    exact Nat.eq_of_mul_eq_mul_left hq hmul

lemma far_bound {r T : ℕ} (hr : 2 ≤ r) (hT : 0 < T) :
    (base r * (oddSmoothUpTo r T).card * Nat.totient (Q r)) ≤
      (multiples (band r T) (2 * T * Q r * base r)).card := by
  classical
  let S := oddSmoothUpTo r T
  let R := (range (Q r)).filter (fun u => (Q r).Coprime u)
  let V := range (base r)
  have hex (d : ℕ) (hd : d ∈ S) :
      ∃ e : ℕ, T < 2 ^ e * d ∧ 2 ^ e * d ≤ 2 * T := by
    have hdI := (mem_filter.mp hd).1
    exact dyadic_crossing (by have := (mem_Icc.mp hdI).1; omega)
      (mem_Icc.mp hdI).2
  let exp (d : ℕ) : ℕ := if hd : d ∈ S then Classical.choose (hex d hd) else 0
  have exp_spec (d : ℕ) (hd : d ∈ S) :
      T < 2 ^ exp d * d ∧ 2 ^ exp d * d ≤ 2 * T := by
    simp only [exp, dif_pos hd]
    exact Classical.choose_spec (hex d hd)
  let f : (ℕ × ℕ) × ℕ → ℕ := fun z =>
    (2 ^ exp z.1.1 * z.1.1) * (z.1.2 + Q r * z.2)
  have hf : Set.MapsTo f (↑((S ×ˢ R) ×ˢ V) : Set ((ℕ × ℕ) × ℕ))
      (multiples (band r T) (2 * T * Q r * base r)) := by
    intro z hz
    obtain ⟨hdu, hv⟩ := mem_product.mp hz
    obtain ⟨hd, hu⟩ := mem_product.mp hdu
    obtain ⟨hult, huQ⟩ := mem_filter.mp hu
    have hult' : z.1.2 < Q r := mem_range.mp hult
    have hvlt : z.2 < base r := mem_range.mp hv
    have hupos : 0 < z.1.2 := by
      by_contra h
      have heq : z.1.2 = 0 := by omega
      rw [heq] at huQ
      simp only [Nat.coprime_zero_right] at huQ
      have := Q_gt_one hr
      omega
    have hmulpos : 0 < z.1.2 + Q r * z.2 := by omega
    have hmullt : z.1.2 + Q r * z.2 < Q r * base r := by
      have hQ := Q_gt_one hr
      nlinarith
    obtain ⟨hcgt, hcle⟩ := exp_spec z.1.1 hd
    have hcpos : 0 < 2 ^ exp z.1.1 * z.1.1 := by omega
    have hcband : 2 ^ exp z.1.1 * z.1.1 ∈ band r T := by
      apply mem_filter.mpr
      constructor
      · exact mem_Ioc.mpr ⟨hcgt, (hcle.trans (by
          have hb : 2 ≤ base r := by
            have hb4 : 4 ≤ base r := by
              simpa [base] using (Nat.pow_le_pow_right (n := 2) (by omega) hr)
            omega
          nlinarith))⟩
      · rw [← insert_two_oddPrimes (by omega)]
        exact Nat.pow_mul_mem_factoredNumbers Nat.prime_two _ (mem_filter.mp hd).2
    apply mem_filter.mpr
    constructor
    · apply mem_Icc.mpr
      dsimp [f]
      constructor
      · exact Nat.mul_pos hcpos hmulpos
      · exact (Nat.mul_le_mul hcle (Nat.le_of_lt hmullt)).trans_eq (by ring)
    · exact ⟨2 ^ exp z.1.1 * z.1.1, hcband, dvd_mul_right _ _⟩
  have hinj : Set.InjOn f (↑((S ×ˢ R) ×ˢ V) : Set ((ℕ × ℕ) × ℕ)) := by
    intro z hz z' hz' heq
    obtain ⟨hdu, hv⟩ := mem_product.mp hz
    obtain ⟨hd, hu⟩ := mem_product.mp hdu
    obtain ⟨hdu', hv'⟩ := mem_product.mp hz'
    obtain ⟨hd', hu'⟩ := mem_product.mp hdu'
    obtain ⟨hult, huQ⟩ := mem_filter.mp hu
    obtain ⟨hult', huQ'⟩ := mem_filter.mp hu'
    dsimp [f] at heq
    have hcop : (Q r).Coprime (z.1.2 + Q r * z.2) := by
      simpa [Nat.Coprime, Nat.gcd_add_mul_left_left] using huQ
    have hcop' : (Q r).Coprime (z'.1.2 + Q r * z'.2) := by
      simpa [Nat.Coprime, Nat.gcd_add_mul_left_left] using huQ'
    have hdeq : z.1.1 = z'.1.1 :=
      far_pair_injective (mem_filter.mp hd).2 (mem_filter.mp hd').2 hcop hcop' heq
    have hcpos : 0 < 2 ^ exp z.1.1 * z.1.1 := by
      have := (exp_spec z.1.1 hd).1
      omega
    have hmuleq : z.1.2 + Q r * z.2 = z'.1.2 + Q r * z'.2 := by
      rw [← hdeq] at heq
      exact Nat.eq_of_mul_eq_mul_left hcpos heq
    obtain ⟨hueq, hveq⟩ := combined_multiplier_injective (by have := Q_gt_one hr; omega)
      (mem_range.mp hult) (mem_range.mp hult') hmuleq
    exact Prod.ext (Prod.ext hdeq hueq) hveq
  have hc := Finset.card_le_card_of_injOn f hf hinj
  simpa only [card_product, S, R, V, card_range, ← Nat.totient_eq_card_coprime,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc

lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    have hp : p.Prime := hS p (mem_insert_self p S)
    have hs : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hq)).mp hdvd
      exact hpS (heq ▸ hq)
    rw [Finset.prod_insert hpS, Nat.totient_mul hcop, Nat.totient_prime hp,
      ih hs, Finset.prod_insert hpS]

lemma totient_Q (r : ℕ) : Nat.totient (Q r) = phiOdd r := by
  exact totient_prod_primes (oddPrimes r) (fun p hp => mem_oddPrimes_prime hp)

lemma exists_amplifying_r (C : ℕ) :
    ∃ r : ℕ, 2 ≤ r ∧ 4 * C * r * Q r < base r * phiOdd r := by
  obtain ⟨r, hr, hgap⟩ := exists_two_pow_gt_const_mul_pow 2 ((4 * C) ^ 2)
  have hcoef : (4 * C * r) ^ 2 < base r := by
    change (4 * C * r) ^ 2 < 2 ^ r
    convert hgap using 1 <;> ring
  have hQpos : 0 < Q r := by
    dsimp [Q]
    exact prod_pos fun p hp => (mem_oddPrimes_prime hp).pos
  have hphipos : 0 < phiOdd r := by
    dsimp [phiOdd]
    exact prod_pos fun p hp => by have := (mem_oddPrimes_prime hp).two_le; omega
  have hwall := base_mul_phiOdd_sq_ge_Q_sq hr
  have hsq : (4 * C * r * Q r) ^ 2 < (base r * phiOdd r) ^ 2 := by
    calc
      (4 * C * r * Q r) ^ 2 = (4 * C * r) ^ 2 * (Q r) ^ 2 := by ring
      _ < base r * (Q r) ^ 2 := Nat.mul_lt_mul_of_pos_right hcoef (by positivity)
      _ ≤ base r * (base r * (phiOdd r) ^ 2) := Nat.mul_le_mul_left _ hwall
      _ = (base r * phiOdd r) ^ 2 := by ring
  refine ⟨r, hr, ?_⟩
  exact (sq_lt_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp hsq

theorem finite_counterexample_unbounded (C : ℕ) :
    ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      ∃ n m : ℕ, 0 < n ∧ (∀ a ∈ A, a ≤ n) ∧ n < m ∧
        C * m * (multiples A n).card < n * (multiples A m).card := by
  obtain ⟨r, hr, hamp⟩ := exists_amplifying_r C
  obtain ⟨k, hslow⟩ := exists_slow_H r
  let T := (base r) ^ k
  have hT : 0 < T := pow_pos (base_pos r) _
  have hH : 0 < (oddSmoothUpTo r T).card := by
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, ?_⟩, ?_⟩⟩
    · exact hT
    · simp [Nat.mem_factoredNumbers]
  have hnear := near_bound (show 1 ≤ r by omega) T
  have hfar := far_bound hr hT
  have hslow' : (oddSmoothUpTo r (base r * T)).card ≤
      2 * (oddSmoothUpTo r T).card := by
    simpa [H, T, pow_succ, Nat.mul_comm] using hslow
  have hnear' : (multiples (band r T) (base r * T)).card ≤
      2 * r * (oddSmoothUpTo r T).card := by
    calc
      _ ≤ r * (oddSmoothUpTo r (base r * T)).card := hnear
      _ ≤ r * (2 * (oddSmoothUpTo r T).card) := Nat.mul_le_mul_left r hslow'
      _ = 2 * r * (oddSmoothUpTo r T).card := by ring
  refine ⟨band r T, band_nonempty_pow (show 1 ≤ r by omega) k,
    band_zero_not_mem r T, base r * T, 2 * T * Q r * base r,
    Nat.mul_pos (base_pos r) hT, (fun a ha => band_le ha), ?_, ?_⟩
  · have hQ := Q_gt_one hr
    have hnpos : 0 < base r * T := Nat.mul_pos (base_pos r) hT
    have hfactor : 1 < 2 * Q r := by omega
    calc
      base r * T < (base r * T) * (2 * Q r) := lt_mul_of_one_lt_right hnpos hfactor
      _ = 2 * T * Q r * base r := by ring
  · calc
      C * (2 * T * Q r * base r) * (multiples (band r T) (base r * T)).card
          ≤ C * (2 * T * Q r * base r) *
              (2 * r * (oddSmoothUpTo r T).card) :=
            Nat.mul_le_mul_left _ hnear'
      _ = (T * base r * (oddSmoothUpTo r T).card) * (4 * C * r * Q r) := by ring
      _ < (T * base r * (oddSmoothUpTo r T).card) * (base r * phiOdd r) :=
        Nat.mul_lt_mul_of_pos_left hamp
          (Nat.mul_pos (Nat.mul_pos hT (base_pos r)) hH)
      _ = (base r * T) *
          (base r * (oddSmoothUpTo r T).card * Nat.totient (Q r)) := by
        rw [totient_Q]
        ring
      _ ≤ (base r * T) *
          (multiples (band r T) (2 * T * Q r * base r)).card :=
        Nat.mul_le_mul_left _ hfar

/-- Finite-scale densities of sets of multiples admit no universal amplification bound. -/
theorem proof :
    ∀ C : ℕ, ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      ∃ n m : ℕ, 0 < n ∧ (∀ a ∈ A, a ≤ n) ∧ n < m ∧
        C * m * ((Icc 1 n).filter (fun j => ∃ a ∈ A, a ∣ j)).card <
          n * ((Icc 1 m).filter (fun j => ∃ a ∈ A, a ∣ j)).card :=
  finite_counterexample_unbounded

#print axioms proof

end Submissions.E488Unbounded.Cole

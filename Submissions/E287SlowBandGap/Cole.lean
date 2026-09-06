import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.SmoothNumbers

/- The smooth-band definitions, exponent encoding, cardinal bound and slow-step
existence proof are adapted from Jig #398 statement43, artifact
0bd20596-fdbd-4fdf-ac0a-3ed0ad6afc23 (Cole Benefield), building on Declan Gessel's
statement40. The disjoint-pair count and internal-hole consequence are added here.
This theorem concerns only the unmodified slow-growth bands, not all E287 sets. -/
namespace Submissions.E287SlowBandGap.Cole
open Filter Finset

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


def base (r : ℕ) : ℕ := 2 ^ r

def primes (r : ℕ) : Finset ℕ := Nat.primesBelow (base r + 1)

def oddPrimes (r : ℕ) : Finset ℕ := (primes r).erase 2

def oddSmoothUpTo (r T : ℕ) : Finset ℕ :=
  (Icc 1 T).filter (fun d => d ∈ Nat.factoredNumbers (oddPrimes r))


def H (r k : ℕ) : ℕ := (oddSmoothUpTo r ((base r) ^ k)).card


def band (r T : ℕ) : Finset ℕ :=
  (Ioc T (base r * T)).filter (fun a => a ∈ Nat.factoredNumbers (primes r))


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


lemma band_le {r T a : ℕ} (ha : a ∈ band r T) : a ≤ base r * T :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).2


lemma band_mem_factored {r T a : ℕ} (ha : a ∈ band r T) :
    a ∈ Nat.factoredNumbers (primes r) := (Finset.mem_filter.mp ha).2


lemma small_mem_factored {r a : ℕ} (ha : 0 < a) (ha' : a < base r + 1) :
    a ∈ Nat.factoredNumbers (primes r) := by
  rw [Nat.mem_factoredNumbers_iff_forall_le]
  refine ⟨by omega, ?_⟩
  intro p hp hprime hdvd
  exact Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt (Nat.le_of_dvd ha hdvd) ha', hprime⟩


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


lemma pair_count (A : Finset ℕ) (u L : ℕ)
    (h : ∀ i < L, u + 2*i ∈ A ∨ u + 2*i + 1 ∈ A) :
    L ≤ A.card := by
  classical
  have hex (i : Fin L) : ∃ a : A, u + 2*i.val ≤ a.val ∧ a.val ≤ u + 2*i.val+1 := by
    rcases h i.val i.isLt with hi | hi
    · exact ⟨⟨_, hi⟩, le_rfl, by dsimp; omega⟩
    · exact ⟨⟨_, hi⟩, by dsimp; omega, le_rfl⟩
  let f : Fin L → A := fun i => Classical.choose (hex i)
  have hf : Function.Injective f := by
    intro i j heq
    have hi := Classical.choose_spec (hex i)
    have hj := Classical.choose_spec (hex j)
    have hv : (f i).val = (f j).val := congrArg Subtype.val heq
    change (Classical.choose (hex i)).val = (Classical.choose (hex j)).val at hv
    apply Fin.ext
    omega
  simpa using Fintype.card_le_of_injective f hf


lemma exponential_width (r : ℕ) (hr : 5 ≤ r) : 4*r+4 ≤ base r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num [base]
  | succ n hn ih =>
    simp only [base, pow_succ] at *
    nlinarith

/-- The slow-growth smooth bands used for unbounded amplification have
two consecutive internal holes once r >= 5; prime support may vary with r. -/

theorem slow_band_has_internal_holes (r k : ℕ) (hr : 5 ≤ r)
    (hslow : H r (k+1) ≤ 2 * H r k) :
    ∃ x : ℕ, 2 * base r ^ k ≤ x ∧ x+1 < base r * base r ^ k ∧
      x ∉ band r (base r ^ k) ∧ x+1 ∉ band r (base r ^ k) := by
  let T := base r ^ k
  have hT : 0 < T := pow_pos (base_pos r) _
  have hH : H r k ≤ T := by
    have hs : oddSmoothUpTo r T ⊆ Icc 1 T := filter_subset _ _
    have hc := card_le_card hs
    simpa [H, T, Nat.card_Icc] using hc
  have hc : (band r T).card ≤ 2*r*T := by
    have hb := band_card_le (r := r) (T := T) (by omega)
    have he : base r*T = base r^(k+1) := by simp [T, pow_succ, mul_comm]
    rw [he] at hb
    change (band r T).card ≤ r * H r (k+1) at hb
    calc
      _ ≤ r * H r (k+1) := hb
      _ ≤ r * (2 * H r k) := Nat.mul_le_mul_left r hslow
      _ ≤ r * (2 * T) := Nat.mul_le_mul_left r (Nat.mul_le_mul_left 2 hH)
      _ = 2*r*T := by ring
  have hwidth := exponential_width r hr
  have hex : ∃ i < 2*r*T+1,
      2*T+2*i ∉ band r T ∧ 2*T+2*i+1 ∉ band r T := by
    by_contra hn
    push_neg at hn
    have hp : ∀ i < 2*r*T+1,
        2*T+2*i ∈ band r T ∨ 2*T+2*i+1 ∈ band r T := by
      intro i hi
      by_cases hx : 2*T+2*i ∈ band r T
      · exact Or.inl hx
      · exact Or.inr (hn i hi hx)
    have := pair_count (band r T) (2*T) (2*r*T+1) hp
    omega
  obtain ⟨i, hi, hx, hx'⟩ := hex
  refine ⟨2*T+2*i, by omega, ?_, hx, hx'⟩
  change 2*T+2*i+1 < base r*T
  have hm := Nat.mul_le_mul_right T hwidth
  nlinarith




lemma upper_endpoint_mem (r k : ℕ) (hr : 1 ≤ r) :
    base r * base r ^ k ∈ band r (base r ^ k) := by
  have hT : 0 < base r ^ k := pow_pos (base_pos r) _
  have hb : 1 < base r := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hr
    simp only [pow_one] at this
    exact lt_of_lt_of_le (by omega) this
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_Ioc.mpr ⟨by nlinarith, le_rfl⟩
  · rw [Nat.mem_factoredNumbers']
    intro p hp hpd
    rw [← pow_succ'] at hpd
    have hd := hp.dvd_of_dvd_pow hpd
    exact Nat.mem_primesBelow.mpr
      ⟨lt_of_le_of_lt (Nat.le_of_dvd (base_pos r) hd) (by omega), hp⟩



theorem proof :
    ∀ r : ℕ, 5 ≤ r →
      (∃ k : ℕ, H r (k+1) ≤ 2*H r k) ∧
      ∀ k : ℕ, H r (k+1) ≤ 2*H r k →
        ∃ a ∈ band r (base r ^ k), ∃ b ∈ band r (base r ^ k),
          ∃ x : ℕ, a ≤ x ∧ x+1 < b ∧
            x ∉ band r (base r ^ k) ∧ x+1 ∉ band r (base r ^ k) := by
  intro r hr
  refine ⟨exists_slow_H r, ?_⟩
  intro k hk
  obtain ⟨x, hlo, hhi, hx, hx'⟩ := slow_band_has_internal_holes r k hr hk
  exact ⟨2 * base r ^ k, two_mul_pow_mem_band (by omega) k,
    base r * base r ^ k, upper_endpoint_mem r k (by omega), x, hlo, hhi, hx, hx'⟩

#print axioms proof
end Submissions.E287SlowBandGap.Cole

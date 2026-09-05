import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.ByContra
import Mathlib.Data.Nat.GCD.BigOperators


namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample
open Finset

def primes : Finset ℕ := Nat.primesBelow 257
def oddPrimes : Finset ℕ := primes.erase 2
def Q : ℕ := ∏ p ∈ oddPrimes, p
def phiOdd : ℕ := ∏ p ∈ oddPrimes, (p - 1)

def oddSmoothUpTo (T : ℕ) : Finset ℕ :=
  (Icc 1 T).filter (fun d => d ∈ Nat.factoredNumbers oddPrimes)

def H (k : ℕ) : ℕ := (oddSmoothUpTo (256 ^ k)).card

def band (T : ℕ) : Finset ℕ :=
  (Ioc T (256 * T)).filter (fun a => a ∈ Nat.factoredNumbers primes)

def multiples (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun j => ∃ a ∈ A, a ∣ j)

lemma primes_two : 2 ∈ primes := by decide
lemma oddPrimes_no_two : 2 ∉ oddPrimes := by simp [oddPrimes]
lemma insert_two_oddPrimes : insert 2 oddPrimes = primes := by
  exact Finset.insert_erase primes_two

lemma mem_primes_prime {p : ℕ} (hp : p ∈ primes) : p.Prime :=
  (Nat.mem_primesBelow.mp hp).2

lemma mem_oddPrimes_prime {p : ℕ} (hp : p ∈ oddPrimes) : p.Prime :=
  mem_primes_prime (Finset.mem_of_mem_erase hp)

lemma mem_oddPrimes_ne_two {p : ℕ} (hp : p ∈ oddPrimes) : p ≠ 2 :=
  (Finset.mem_erase.mp hp).1

set_option maxRecDepth 10000 in
lemma oddPrimes_card : oddPrimes.card = 53 := by decide

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample


namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample.PolynomialCount
open Finset

/-- Crude but fully finite exponent-vector count for integers with prime factors in s. -/
theorem primeFactors_card_le (s : Finset ℕ) (b : ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
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

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample.PolynomialCount

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample.FiniteGrowth

/-- A sequence bounded at one endpoint cannot grow by a factor greater than 3/2
at every preceding step if the corresponding geometric lower bound is too large. -/
theorem slow_step (h : ℕ → ℕ) (N B : ℕ) (hzero : 1 ≤ h 0)
    (hbound : h N ≤ B) (hgap : 2 ^ N * B < 3 ^ N) :
    ∃ k < N, 2 * h (k + 1) ≤ 3 * h k := by
  by_contra hnone
  have hfast : ∀ k < N, 3 * h k ≤ 2 * h (k + 1) := by
    intro k hk
    have : ¬ 2 * h (k + 1) ≤ 3 * h k := by
      intro hh
      exact hnone ⟨k, hk, hh⟩
    omega
  have hgrowth : ∀ k ≤ N, 3 ^ k ≤ 2 ^ k * h k := by
    intro k
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hf := hfast k (by omega)
      calc
        3 ^ (k + 1) = 3 * 3 ^ k := by simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ 3 * (2 ^ k * h k) := Nat.mul_le_mul_left 3 hp
        _ = 2 ^ k * (3 * h k) := by simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ 2 ^ k * (2 * h (k + 1)) := Nat.mul_le_mul_left _ hf
        _ = 2 ^ (k + 1) * h (k + 1) := by simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hn := hgrowth N le_rfl
  have hu := Nat.mul_le_mul_left (2 ^ N) hbound
  omega

/-- Explicit exact endpoint comparison for 53 odd prime coordinates and base 256. -/
theorem endpoint_gap : 2 ^ 4096 * (8 * 4096 + 1) ^ 53 < 3 ^ 4096 := by
  decide

/-- The finite pigeonhole result needed by the smooth-window counterexample. -/
theorem slow_step_4096 (h : ℕ → ℕ) (hzero : 1 ≤ h 0)
    (hbound : h 4096 ≤ (8 * 4096 + 1) ^ 53) :
    ∃ k < 4096, 2 * h (k + 1) ≤ 3 * h k :=
  slow_step h 4096 ((8 * 4096 + 1) ^ 53) hzero hbound endpoint_gap

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample.FiniteGrowth

namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample
open Finset

/-- Finite polynomial bound on the odd-smooth counting sequence. -/
theorem H_polynomial_bound (k : ℕ) : H k ≤ (8 * k + 1) ^ 53 := by
  have hb := Submissions.ErdosMultiplesSmoothRefuted.Counterexample.PolynomialCount.primeFactors_card_le oddPrimes (8 * k)
    (fun p hp => (mem_oddPrimes_prime hp).two_le)
  have he : 2 ^ (8 * k) = 256 ^ k := by rw [pow_mul]; norm_num
  simpa only [he, oddPrimes_card, H, oddSmoothUpTo,
    Nat.mem_factoredNumbers_iff_primeFactors_subset] using hb

lemma H_zero_pos : 1 ≤ H 0 := by
  have hone : 1 ∈ oddSmoothUpTo (256 ^ 0) := by
    simp [oddSmoothUpTo, Nat.mem_factoredNumbers]
  exact Finset.one_le_card.mpr ⟨1, hone⟩

/-- A specific finite range contains a multiplicative window with slow odd-smooth growth. -/
theorem exists_slow_H : ∃ k < 4096, 2 * H (k + 1) ≤ 3 * H k :=
  Submissions.ErdosMultiplesSmoothRefuted.Counterexample.FiniteGrowth.slow_step_4096 H H_zero_pos (H_polynomial_bound 4096)

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample


namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample
open Finset

lemma power_residue_unique {T d e f : ℕ}
    (he : T < 2 ^ e * d) (he' : 2 ^ e * d ≤ 256 * T)
    (hf : T < 2 ^ f * d) (hf' : 2 ^ f * d ≤ 256 * T)
    (hmod : e % 8 = f % 8) : e = f := by
  have exclude (a b : ℕ) (ha : T < 2 ^ a * d)
      (hb : 2 ^ b * d ≤ 256 * T) (hab : a + 8 ≤ b) : False := by
    have hp : (2 : ℕ) ^ (a + 8) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hab
    have hm := Nat.mul_le_mul_right d hp
    rw [pow_add] at hm
    norm_num at hm
    nlinarith
  by_contra hne
  have ha : e + 8 ≤ f ∨ f + 8 ≤ e := by omega
  rcases ha with ha | ha
  · exact exclude e f he hf' ha
  · exact exclude f e hf he' ha

lemma band_zero_not_mem (T : ℕ) : 0 ∉ band T := by
  simp [band]

lemma band_le {T a : ℕ} (ha : a ∈ band T) : a ≤ 256 * T :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).2

lemma band_pos {T a : ℕ} (ha : a ∈ band T) : 0 < a := by
  have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).1
  omega

lemma band_mem_factored {T a : ℕ} (ha : a ∈ band T) :
    a ∈ Nat.factoredNumbers primes := (Finset.mem_filter.mp ha).2

lemma small_mem_factored {a : ℕ} (ha : 0 < a) (ha' : a < 257) :
    a ∈ Nat.factoredNumbers primes := by
  rw [Nat.mem_factoredNumbers_iff_forall_le]
  refine ⟨by omega, ?_⟩
  intro p hp hprime hdvd
  exact Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩

lemma multiples_band_eq (T : ℕ) : multiples (band T) (256 * T) = band T := by
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
    have hclt : c < 257 := by nlinarith
    have hcs := small_mem_factored hcpos hclt
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, hjle⟩,
      Nat.mul_mem_factoredNumbers has hcs⟩
    have : a ≤ a * c := Nat.le_mul_of_pos_right a hcpos
    omega
  · intro hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨band_pos hj, band_le hj⟩,
      j, hj, dvd_refl _⟩

noncomputable def bandSplit {T : ℕ} (j : band T) :
    ℕ × Nat.factoredNumbers oddPrimes :=
  (Nat.equivProdNatFactoredNumbers Nat.prime_two oddPrimes_no_two).symm
    ⟨j, by simpa [insert_two_oddPrimes] using band_mem_factored j.2⟩

lemma bandSplit_eq {T : ℕ} (j : band T) :
    2 ^ (bandSplit j).1 * (bandSplit j).2.val = j.val := by
  have h := (Nat.equivProdNatFactoredNumbers Nat.prime_two oddPrimes_no_two).apply_symm_apply
    ⟨j.val, by simpa [insert_two_oddPrimes] using band_mem_factored j.2⟩
  exact congrArg Subtype.val h

lemma bandSplit_mem {T : ℕ} (j : band T) :
    (bandSplit j).2.val ∈ oddSmoothUpTo (256 * T) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, (bandSplit j).2.property⟩
  · exact Nat.pos_of_ne_zero (bandSplit j).2.property.1
  · have hp : 0 < (2 : ℕ) ^ (bandSplit j).1 := pow_pos (by omega) _
    have hd := Nat.le_mul_of_pos_left (bandSplit j).2.val hp
    rw [bandSplit_eq] at hd
    exact hd.trans (band_le j.2)

noncomputable def bandEncode {T : ℕ} (j : band T) :
    oddSmoothUpTo (256 * T) × Fin 8 :=
  (⟨(bandSplit j).2.val, bandSplit_mem j⟩,
    ⟨(bandSplit j).1 % 8, Nat.mod_lt _ (by omega)⟩)

lemma bandEncode_injective (T : ℕ) : Function.Injective (@bandEncode T) := by
  intro j k heq
  have hd : (bandSplit j).2.val = (bandSplit k).2.val :=
    congrArg (fun z => z.1.val) heq
  have hmod : (bandSplit j).1 % 8 = (bandSplit k).1 % 8 :=
    congrArg (fun z => z.2.val) heq
  have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp j.2).1
  have hk := Finset.mem_Ioc.mp (Finset.mem_filter.mp k.2).1
  have hje := bandSplit_eq j
  have hke := bandSplit_eq k
  rw [← hd] at hke
  have he : (bandSplit j).1 = (bandSplit k).1 :=
    power_residue_unique (hje ▸ hj.1) (hje ▸ hj.2)
      (hke ▸ hk.1) (hke ▸ hk.2) hmod
  apply Subtype.ext
  rw [← hje, ← hke, he]

lemma band_card_le (T : ℕ) : (band T).card ≤ 8 * (oddSmoothUpTo (256 * T)).card := by
  have h := Fintype.card_le_of_injective (@bandEncode T) (bandEncode_injective T)
  simpa [Fintype.card_prod, Nat.mul_comm] using h

lemma near_bound (T : ℕ) :
    (multiples (band T) (256 * T)).card ≤ 8 * (oddSmoothUpTo (256 * T)).card := by
  rw [multiples_band_eq]
  exact band_card_le T

lemma two_mul_pow_mem_band (k : ℕ) : 2 * 256 ^ k ∈ band (256 ^ k) := by
  have ht : 0 < (256 : ℕ) ^ k := pow_pos (by omega) _
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  apply Nat.mul_mem_factoredNumbers
  · exact small_mem_factored (by omega) (by omega)
  · rw [Nat.mem_factoredNumbers']
    intro p hp hpd
    have hpd' := hp.dvd_of_dvd_pow hpd
    exact Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpd') (by omega), hp⟩

lemma band_nonempty_pow (k : ℕ) : (band (256 ^ k)).Nonempty :=
  ⟨2 * 256 ^ k, two_mul_pow_mem_band k⟩

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample


namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample
open Finset

lemma oddSmooth_coprime_residue {d r : ℕ}
    (hd : d ∈ Nat.factoredNumbers oddPrimes) (hr : Q.Coprime r) :
    d.Coprime r := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpr
  have hpP : p ∈ oddPrimes := Nat.mem_factoredNumbers'.mp hd p hp hpd
  have hpQ : p ∣ Q := by
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hpP
  have hcop : p.Coprime r := hr.of_dvd_left hpQ
  exact (hp.coprime_iff_not_dvd.mp hcop) hpr

lemma oddSmooth_coprime_two {d : ℕ} (hd : d ∈ Nat.factoredNumbers oddPrimes) :
    d.Coprime 2 :=
  (Nat.prime_two.factoredNumbers_coprime oddPrimes_no_two hd).symm

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

lemma far_pair_injective {d d' r r' e e' : ℕ}
    (hd : d ∈ Nat.factoredNumbers oddPrimes)
    (hd' : d' ∈ Nat.factoredNumbers oddPrimes)
    (hr : Q.Coprime r) (hr' : Q.Coprime r')
    (heq : (2 ^ e * d) * r = (2 ^ e' * d') * r') : d = d' := by
  have hdiv : d ∣ d' := by
    have h : d ∣ (2 ^ e' * d') * r' := by
      rw [← heq]
      exact dvd_mul_of_dvd_left (dvd_mul_left d (2 ^ e)) r
    have h' : d ∣ 2 ^ e' * d' :=
      (oddSmooth_coprime_residue hd hr').dvd_of_dvd_mul_right h
    exact ((oddSmooth_coprime_two hd).pow_right e').dvd_of_dvd_mul_left h'
  have hdiv' : d' ∣ d := by
    have h : d' ∣ (2 ^ e * d) * r := by
      rw [heq]
      exact dvd_mul_of_dvd_left (dvd_mul_left d' (2 ^ e')) r'
    have h' : d' ∣ 2 ^ e * d :=
      (oddSmooth_coprime_residue hd' hr).dvd_of_dvd_mul_right h
    exact ((oddSmooth_coprime_two hd').pow_right e).dvd_of_dvd_mul_left h'
  exact Nat.dvd_antisymm hdiv hdiv'

lemma far_bound (T : ℕ) (hT : 0 < T) (hQ : 1 < Q) :
    (oddSmoothUpTo T).card * Nat.totient Q ≤
      (multiples (band T) (2 * T * Q)).card := by
  classical
  let S := oddSmoothUpTo T
  let R := (range Q).filter (fun r => Q.Coprime r)
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
  let f : ℕ × ℕ → ℕ := fun dr => (2 ^ exp dr.1 * dr.1) * dr.2
  have hf : Set.MapsTo f (↑(S ×ˢ R) : Set (ℕ × ℕ))
      (multiples (band T) (2 * T * Q)) := by
    intro dr hdr
    obtain ⟨hd, hr⟩ := mem_product.mp hdr
    obtain ⟨hrlt, hrQ⟩ := mem_filter.mp hr
    have hrlt' : dr.2 < Q := mem_range.mp hrlt
    have hrpos : 0 < dr.2 := by
      by_contra h
      have heq : dr.2 = 0 := by omega
      rw [heq] at hrQ
      simp only [Nat.coprime_zero_right] at hrQ
      omega
    obtain ⟨hcgt, hcle⟩ := exp_spec dr.1 hd
    have hcpos : 0 < 2 ^ exp dr.1 * dr.1 := by omega
    have hcband : 2 ^ exp dr.1 * dr.1 ∈ band T := by
      apply mem_filter.mpr
      constructor
      · exact mem_Ioc.mpr ⟨hcgt, by omega⟩
      · rw [← insert_two_oddPrimes]
        exact Nat.pow_mul_mem_factoredNumbers Nat.prime_two _ (mem_filter.mp hd).2
    apply mem_filter.mpr
    constructor
    · apply mem_Icc.mpr
      dsimp [f]
      constructor
      · exact Nat.mul_pos hcpos hrpos
      · exact Nat.mul_le_mul hcle (by omega)
    · exact ⟨2 ^ exp dr.1 * dr.1, hcband, dvd_mul_right _ _⟩
  have hinj : Set.InjOn f (↑(S ×ˢ R) : Set (ℕ × ℕ)) := by
    intro dr hdr ds hds heq
    obtain ⟨hd, hr⟩ := mem_product.mp hdr
    obtain ⟨hd', hr'⟩ := mem_product.mp hds
    have hdeq : dr.1 = ds.1 :=
      far_pair_injective (mem_filter.mp hd).2 (mem_filter.mp hd').2
        (mem_filter.mp hr).2 (mem_filter.mp hr').2 heq
    have hpos : 0 < 2 ^ exp dr.1 * dr.1 := by
      have := (exp_spec dr.1 hd).1
      omega
    have hreq : dr.2 = ds.2 := by
      dsimp [f] at heq
      rw [← hdeq] at heq
      exact Nat.eq_of_mul_eq_mul_left hpos heq
    exact Prod.ext hdeq hreq
  have hc := Finset.card_le_card_of_injOn f hf hinj
  simpa only [card_product, S, R, ← Nat.totient_eq_card_coprime] using hc

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample


namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample
open Finset

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

lemma totient_Q : Nat.totient Q = phiOdd := by
  exact totient_prod_primes oddPrimes (fun p hp => mem_oddPrimes_prime hp)

set_option maxRecDepth 10000 in
lemma Q_large : 128 < Q := by decide

set_option maxRecDepth 10000 in
lemma constant_ratio : 3 * Q < 16 * phiOdd := by decide

lemma totient_ratio : 3 * Q < 16 * Nat.totient Q := by
  rw [totient_Q]
  exact constant_ratio

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample


namespace Submissions.ErdosMultiplesSmoothRefuted.Counterexample
open Finset

theorem finite_counterexample :
    ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      ∃ n m : ℕ, (∀ a ∈ A, a ≤ n) ∧ n < m ∧
        2 * m * (multiples A n).card < n * (multiples A m).card := by
  obtain ⟨k, hk, hslow⟩ := exists_slow_H
  let T := 256 ^ k
  have hT : 0 < T := pow_pos (by decide) _
  have hH : 0 < (oddSmoothUpTo T).card := by
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, hT⟩, ?_⟩⟩
    simp [Nat.mem_factoredNumbers]
  have hnear := near_bound T
  have hfar := far_bound T hT (by have := Q_large; omega)
  have hslow' : 2 * (oddSmoothUpTo (256 * T)).card ≤ 3 * (oddSmoothUpTo T).card := by
    simpa [H, T, pow_succ, Nat.mul_comm] using hslow
  have hnear' : (multiples (band T) (256 * T)).card ≤ 12 * (oddSmoothUpTo T).card := by
    omega
  refine ⟨band T, band_nonempty_pow k, band_zero_not_mem T, 256 * T, 2 * T * Q,
    (fun a ha => band_le ha), ?_, ?_⟩
  · have hq := Nat.mul_lt_mul_of_pos_left Q_large hT
    nlinarith
  · calc
      2 * (2 * T * Q) * (multiples (band T) (256 * T)).card
          ≤ 2 * (2 * T * Q) * (12 * (oddSmoothUpTo T).card) :=
        Nat.mul_le_mul_left _ hnear'
      _ = (16 * (T * (oddSmoothUpTo T).card)) * (3 * Q) := by ring
      _ < (16 * (T * (oddSmoothUpTo T).card)) * (16 * Nat.totient Q) :=
        Nat.mul_lt_mul_of_pos_left totient_ratio (by positivity)
      _ = (256 * T) * ((oddSmoothUpTo T).card * Nat.totient Q) := by ring
      _ ≤ (256 * T) * (multiples (band T) (2 * T * Q)).card :=
        Nat.mul_le_mul_left _ hfar

/-- Negation of the unrestricted root, with its literal finite-count statement. -/
theorem proof : ¬ (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A → ∀ n m : ℕ,
    (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun j => ∃ a ∈ A, a ∣ j)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun j => ∃ a ∈ A, a ∣ j)).card) := by
  intro h
  obtain ⟨A, hA, hzero, n, m, hmax, hnm, hbad⟩ := finite_counterexample
  have hgood := h A hA hzero n m hmax hnm
  change n * (multiples A m).card < 2 * m * (multiples A n).card at hgood
  omega

end Submissions.ErdosMultiplesSmoothRefuted.Counterexample

#print axioms Submissions.ErdosMultiplesSmoothRefuted.Counterexample.proof

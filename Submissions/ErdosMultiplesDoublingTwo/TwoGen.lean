import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Two generators `a ≠ b`. If one divides the other the set of multiples is that of the smaller
generator and the singleton argument (`n < a (q+1) ≤ 2 a q`, `q = n / a ≥ 1`) applies.
Otherwise `L = lcm a b ≥ 2 max a b`, so with `p = n / a`, `q = n / b`, `r = n / L`, inclusion–exclusion
gives `M n = p + q - r` with `2 r ≤ min p q`, hence `n / a + n / b < p + q + 2 ≤ 2 M n`,
and the union bound `M m ≤ m / a + m / b` yields `n M m ≤ m (n / a + n / b) < 2 m M n`.
-/

namespace Submissions.ErdosMultiplesDoublingTwo.TwoGen

open Finset

lemma card_mult (a x : ℕ) : ((Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  have : (Icc 1 x) = Ioc 0 x := by
    have h := Icc_add_one_left_eq_Ioc (0 : ℕ) x
    simpa using h
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma filter_pair (a b x : ℕ) :
    (Icc 1 x).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k) =
      (Icc 1 x).filter (fun k => a ∣ k) ∪ (Icc 1 x).filter (fun k => b ∣ k) := by
  ext k
  simp only [mem_filter, mem_union, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hk, c, hc | hc, hck⟩
    · exact Or.inl ⟨hk, hc ▸ hck⟩
    · exact Or.inr ⟨hk, hc ▸ hck⟩
  · rintro (⟨hk, h⟩ | ⟨hk, h⟩)
    · exact ⟨hk, a, Or.inl rfl, h⟩
    · exact ⟨hk, b, Or.inr rfl, h⟩

lemma filter_inter (a b x : ℕ) :
    (Icc 1 x).filter (fun k => a ∣ k) ∩ (Icc 1 x).filter (fun k => b ∣ k) =
      (Icc 1 x).filter (fun k => Nat.lcm a b ∣ k) := by
  ext k
  simp only [mem_inter, mem_filter, Nat.lcm_dvd_iff]
  tauto

/-- Inclusion–exclusion for two generators, in additive form. -/
lemma card_pair_add (a b x : ℕ) :
    ((Icc 1 x).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card + x / Nat.lcm a b =
      x / a + x / b := by
  rw [filter_pair, ← card_mult (Nat.lcm a b) x, ← filter_inter, card_union_add_card_inter,
    card_mult, card_mult]

lemma filter_pair_of_dvd (a b x : ℕ) (hab : a ∣ b) :
    (Icc 1 x).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k) =
      (Icc 1 x).filter (fun k => a ∣ k) := by
  ext k
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hk, c, hc | hc, hck⟩
    · exact ⟨hk, hc ▸ hck⟩
    · exact ⟨hk, dvd_trans hab (hc ▸ hck)⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, a, Or.inl rfl, h⟩

lemma pair_comm (a b : ℕ) : ({a, b} : Finset ℕ) = {b, a} := Finset.pair_comm a b

/-- The singleton doubling inequality `n * (m / a) < 2 * m * (n / a)` for `1 ≤ a ≤ n < m`. -/
lemma singleton_ineq (a n m : ℕ) (ha : 0 < a) (han : a ≤ n) (hnm : n < m) :
    n * (m / a) < 2 * m * (n / a) := by
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have h1 : n < a * (n / a + 1) := by
    have := Nat.lt_div_mul_add (a := n) ha
    rw [Nat.mul_comm] at this
    linarith [Nat.mul_succ a (n / a)]
  have h2 : a * (n / a + 1) ≤ 2 * a * (n / a) := by nlinarith
  have h3 : n < 2 * a * (n / a) := lt_of_lt_of_le h1 h2
  have h4 : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h5 : n * (a * (m / a)) ≤ n * m := Nat.mul_le_mul_left n h4
  have h6 : n * m < 2 * a * (n / a) * m := by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
    exact Nat.mul_lt_mul_of_pos_right h3 hm
  have h7 : a * (n * (m / a)) < a * (2 * m * (n / a)) := by
    calc a * (n * (m / a)) = n * (a * (m / a)) := by ring
      _ ≤ n * m := h5
      _ < 2 * a * (n / a) * m := h6
      _ = a * (2 * m * (n / a)) := by ring
  exact Nat.lt_of_mul_lt_mul_left h7

lemma lcm_ge_two_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : ¬ a ∣ b) :
    2 * b ≤ Nat.lcm a b := by
  obtain ⟨t, ht⟩ : b ∣ Nat.lcm a b := Nat.dvd_lcm_right a b
  have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at ht
    omega
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [Nat.mul_one] at ht
    exact hab (ht ▸ Nat.dvd_lcm_left a b)
  have : 2 ≤ t := by omega
  rw [ht]
  exact Nat.mul_le_mul_left b this |>.trans_eq' (by ring)

/-- `(n : ℚ) / a < n / a + 1` (natural division on the right). -/
lemma ratdiv_lt (n a : ℕ) (ha : 0 < a) : (n : ℚ) / a < ((n / a : ℕ) : ℚ) + 1 := by
  have h : n < (n / a + 1) * a := by
    have := Nat.lt_div_mul_add (a := n) ha
    linarith [Nat.succ_mul (n / a) a]
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  rw [div_lt_iff₀ ha']
  exact_mod_cast h

lemma natdiv_le_ratdiv (x a : ℕ) : ((x / a : ℕ) : ℚ) ≤ (x : ℚ) / a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  · rw [le_div_iff₀ (by exact_mod_cast ha)]
    exact_mod_cast Nat.div_mul_le_self x a

lemma arith (p q r M : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hIE : M + r = p + q)
    (hra : r ≤ p / 2) (hrb : r ≤ q / 2) : p + q + 2 ≤ 2 * M := by
  omega

/-- The coprime-ish case: neither generator divides the other. -/
lemma main_case (a b n m : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : ¬ a ∣ b) (hba : ¬ b ∣ a)
    (han : a ≤ n) (hbn : b ≤ n) (hnm : n < m) :
    n * ((Finset.Icc 1 m).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card := by
  set Mm := ((Finset.Icc 1 m).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card with hMm
  set Mn := ((Finset.Icc 1 n).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card with hMn
  set L := Nat.lcm a b with hL
  have hLb : 2 * b ≤ L := lcm_ge_two_mul a b ha hb hab
  have hLa : 2 * a ≤ L := by
    have := lcm_ge_two_mul b a hb ha hba
    rwa [Nat.lcm_comm] at this
  have hIEn : Mn + n / L = n / a + n / b := card_pair_add a b n
  have hIEm : Mm + m / L = m / a + m / b := card_pair_add a b m
  have hp : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have hq : 1 ≤ n / b := (Nat.one_le_div_iff hb).mpr hbn
  have hrb : n / L ≤ n / b / 2 := by
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left (by linarith) (by positivity)
  have hra : n / L ≤ n / a / 2 := by
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left (by linarith) (by positivity)
  have hkey : n / a + n / b + 2 ≤ 2 * Mn := arith _ _ _ _ hp hq hIEn hra hrb
  -- rational union bound
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) hnm)
  have hMmle : (Mm : ℚ) ≤ (m : ℚ) / a + (m : ℚ) / b := by
    have h1 : Mm ≤ m / a + m / b := hIEm ▸ Nat.le_add_right _ _
    calc (Mm : ℚ) ≤ ((m / a + m / b : ℕ) : ℚ) := by exact_mod_cast h1
      _ = ((m / a : ℕ) : ℚ) + ((m / b : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ (m : ℚ) / a + (m : ℚ) / b := add_le_add (natdiv_le_ratdiv m a) (natdiv_le_ratdiv m b)
  have hsum : (n : ℚ) / a + (n : ℚ) / b < 2 * (Mn : ℚ) := by
    have h1 := ratdiv_lt n a ha
    have h2 := ratdiv_lt n b hb
    have h3 : ((n / a : ℕ) : ℚ) + ((n / b : ℕ) : ℚ) + 2 ≤ 2 * (Mn : ℚ) := by
      exact_mod_cast hkey
    linarith
  have hswap : (n : ℚ) * ((m : ℚ) / a + (m : ℚ) / b) = m * ((n : ℚ) / a + (n : ℚ) / b) := by
    ring
  have h5 : (n : ℚ) * Mm < 2 * m * Mn := by
    calc (n : ℚ) * Mm ≤ n * ((m : ℚ) / a + (m : ℚ) / b) :=
          mul_le_mul_of_nonneg_left hMmle (by positivity)
      _ = m * ((n : ℚ) / a + (n : ℚ) / b) := hswap
      _ < m * (2 * Mn) := mul_lt_mul_of_pos_left hsum hm0
      _ = 2 * m * Mn := by ring
  exact_mod_cast h5

theorem proof : ∀ a b : ℕ, 0 < a → 0 < b → a ≠ b → ∀ n m : ℕ, a ≤ n → b ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card := by
  intro a b ha hb hab n m han hbn hnm
  by_cases hd : a ∣ b
  · rw [filter_pair_of_dvd a b m hd, filter_pair_of_dvd a b n hd, card_mult, card_mult]
    exact singleton_ineq a n m ha han hnm
  by_cases hd' : b ∣ a
  · rw [pair_comm, filter_pair_of_dvd b a m hd', filter_pair_of_dvd b a n hd', card_mult,
      card_mult]
    exact singleton_ineq b n m hb hbn hnm
  exact main_case a b n m ha hb hd hd' han hbn hnm

end Submissions.ErdosMultiplesDoublingTwo.TwoGen

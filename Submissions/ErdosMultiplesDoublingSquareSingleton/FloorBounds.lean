import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The Square Bound for `A = {a}`: `(n − ⌊n/a⌋)² m ≤ (m − ⌊m/a⌋) n²` for `1 ≤ a ≤ n < m`.

`U(x) = x − ⌊x/a⌋`. From `(2a − 1)⌊n/a⌋ ≥ n` (write `n = qa + r`, `r < a ≤ qa`) we get
`(2a − 1) U(n) ≤ (2a − 2) n`; from `a⌊m/a⌋ ≤ m` we get `a U(m) ≥ (a − 1) m`. Then
`(2a−1)² a · U(n)² m ≤ 4(a−1)² a · n² m ≤ (a−1)(2a−1)² · n² m ≤ (2a−1)² a · U(m) n²`
using `4a(a−1) ≤ (2a−1)²`.
-/

namespace Submissions.ErdosMultiplesDoublingSquareSingleton.FloorBounds

open Finset

lemma card_nonmult (a x : ℕ) :
    ((Icc 1 x).filter (fun k => ¬ ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card = x - x / a := by
  have hM : ((Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card = x / a := by
    have h : ((Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)) =
        (Ioc 0 x).filter (fun k => a ∣ k) := by
      rw [← Finset.Icc_add_one_left_eq_Ioc]
      ext k
      simp
    rw [h, Nat.Ioc_filter_dvd_card_eq_div]
  have hsum := Finset.card_filter_add_card_filter_not (s := Icc 1 x)
    (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)
  rw [Nat.card_Icc, hM] at hsum
  omega

lemma floor_lower (a n : ℕ) (ha : 0 < a) (han : a ≤ n) : n ≤ (2 * a - 1) * (n / a) := by
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have h1 := Nat.div_add_mod n a
  have h2 := Nat.mod_lt n ha
  have h3 : n % a ≤ (a - 1) * (n / a) := by
    calc n % a ≤ a - 1 := by omega
      _ = (a - 1) * 1 := by ring
      _ ≤ (a - 1) * (n / a) := Nat.mul_le_mul_left _ hq
  have h4 : (2 * a - 1) * (n / a) = a * (n / a) + (a - 1) * (n / a) := by
    have : 2 * a - 1 = a + (a - 1) := by omega
    rw [this, add_mul]
  linarith

theorem proof : ∀ a : ℕ, 0 < a → ∀ n m : ℕ, a ≤ n → n < m →
    ((Finset.Icc 1 n).filter (fun k => ¬ ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card ^ 2 * m ≤
      ((Finset.Icc 1 m).filter (fun k => ¬ ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card * n ^ 2 := by
  intro a ha n m han hnm
  rw [card_nonmult, card_nonmult]
  have hqn := Nat.div_mul_le_self n a
  have hqm := Nat.div_mul_le_self m a
  have hl := floor_lower a n ha han
  set q := n / a with hq
  set p := m / a with hp
  -- Un = n - q, Um = m - p
  have hUn : (2 * a - 1) * (n - q) ≤ (2 * a - 2) * n := by
    have : q ≤ n := Nat.div_le_self n a
    zify [this, (by omega : 1 ≤ 2 * a), (by omega : 2 ≤ 2 * a)] at hl ⊢
    nlinarith
  have hUm : (a - 1) * m ≤ a * (m - p) := by
    have : p ≤ m := Nat.div_le_self m a
    zify [this, (by omega : 1 ≤ a)] at hqm ⊢
    nlinarith
  -- multiply through by (2a-1)^2 * a > 0
  have hpos : 0 < (2 * a - 1) ^ 2 * a := by
    have : 1 ≤ 2 * a - 1 := by omega
    positivity
  apply Nat.le_of_mul_le_mul_left _ hpos
  have hqn' : q ≤ n := Nat.div_le_self n a
  have hpm' : p ≤ m := Nat.div_le_self m a
  zify [hqn', hpm', (by omega : 1 ≤ 2 * a), (by omega : 2 ≤ 2 * a), (by omega : 1 ≤ a)] at hUn hUm ⊢
  -- LHS = (2a-1)^2 a (n-q)^2 m ≤ a m ((2a-2) n)^2 = 4 a (a-1)^2 n^2 m
  -- RHS = (2a-1)^2 a (m-p) n^2 ≥ (2a-1)^2 (a-1) m n^2
  have hUn2 : ((2 * (a:ℤ) - 1) * ((n:ℤ) - q)) ^ 2 ≤ ((2 * (a:ℤ) - 2) * n) ^ 2 := by
    apply pow_le_pow_left₀ _ hUn
    have : (q:ℤ) ≤ n := by exact_mod_cast hqn'
    nlinarith
  have hm0 : (0:ℤ) ≤ m := by positivity
  have hn0 : (0:ℤ) ≤ n := by positivity
  have ha1 : (0:ℤ) ≤ a - 1 := by
    have : (1:ℤ) ≤ a := by exact_mod_cast ha
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hUn2 hm0, mul_le_mul_of_nonneg_right hUm (mul_nonneg hn0 hn0),
    mul_nonneg (mul_nonneg ha1 hm0) (mul_nonneg hn0 hn0)]

end Submissions.ErdosMultiplesDoublingSquareSingleton.FloorBounds

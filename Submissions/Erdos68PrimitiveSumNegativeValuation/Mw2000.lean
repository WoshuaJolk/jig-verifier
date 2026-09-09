import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos68PrimitiveSumNegativeValuation.Mw2000

private theorem unique_min_sum
    {ι : Type*} [DecidableEq ι] (p : ℕ) [Fact p.Prime]
    (t : Finset ι) (f : ι → ℚ) (k : ι)
    (hk0 : f k ≠ 0)
    (ht0 : ∀ i ∈ t, f i ≠ 0)
    (hmin : ∀ i ∈ t, padicValRat p (f k) < padicValRat p (f i)) :
    (∑ i ∈ t, f i) + f k ≠ 0 ∧
      padicValRat p (∑ i ∈ t, f i + f k) = padicValRat p (f k) := by
  induction t using Finset.induction with
  | empty => simp [hk0]
  | @insert a t ha ih =>
      have hi := ih (fun i hi => ht0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hmin i (Finset.mem_insert_of_mem hi))
      have hsum0 : (∑ i ∈ t, f i) + f k ≠ 0 := hi.1
      have hne :
          padicValRat p ((∑ i ∈ t, f i) + f k) ≠ padicValRat p (f a) := by
        rw [hi.2]
        exact ne_of_lt (hmin a (Finset.mem_insert_self a t))
      have hadd0 : ((∑ i ∈ t, f i) + f k) + f a ≠ 0 := by
        intro hzero
        have heq := eq_neg_of_add_eq_zero_left hzero
        have hv := congrArg (padicValRat p) heq
        rw [padicValRat.neg] at hv
        exact hne hv
      have hadd := padicValRat.add_eq_min hadd0 hsum0
        (ht0 a (Finset.mem_insert_self a t)) hne
      have heq :
          f a + (∑ i ∈ t, f i) + f k =
            ((∑ i ∈ t, f i) + f k) + f a := by ring
      constructor
      · rw [Finset.sum_insert ha, heq]
        exact hadd0
      · rw [Finset.sum_insert ha, heq, hadd, min_eq_left, hi.2]
        rw [hi.2]
        exact (hmin a (Finset.mem_insert_self a t)).le

private lemma factorial_sub_one_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    n.factorial - 1 ≠ 0 := by
  have hfac : 1 < n.factorial := Nat.one_lt_factorial.mpr (by omega)
  omega

private lemma reciprocal_valuation (p n : ℕ) [Fact p.Prime] (hn : 2 ≤ n) :
    padicValRat p ((1 : ℚ) / (n.factorial - 1 : ℕ)) =
      -(padicValNat p (n.factorial - 1) : ℤ) := by
  have hdenNat := factorial_sub_one_ne_zero hn
  have hdenRat : ((n.factorial - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hdenNat
  rw [padicValRat.div one_ne_zero hdenRat, padicValRat.one, ← padicValRat_of_nat]
  omega

theorem proof :
    ∀ N p : ℕ, 2 ≤ N → p.Prime → p ∣ N.factorial - 1 →
      (∀ n : ℕ, 2 ≤ n → n < N → ¬p ∣ n.factorial - 1) →
      padicValRat p
          (∑ n ∈ Finset.Icc 2 N,
            (1 : ℚ) / (n.factorial - 1 : ℕ)) < 0 := by
  intro N p hN hp hpN hprim
  letI : Fact p.Prime := ⟨hp⟩
  let s := Finset.Icc 2 N
  let q : ℕ → ℚ := fun n => (1 : ℚ) / (n.factorial - 1 : ℕ)
  have hNs : N ∈ s := Finset.mem_Icc.mpr ⟨hN, le_rfl⟩
  have hdenN := factorial_sub_one_ne_zero hN
  have hpos : 1 ≤ padicValNat p (N.factorial - 1) :=
    one_le_padicValNat_of_dvd hdenN hpN
  have hmax :
      ∀ n ∈ s, n ≠ N →
        padicValNat p (n.factorial - 1) <
          padicValNat p (N.factorial - 1) := by
    intro n hn hnN
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnle : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hnlt : n < N := lt_of_le_of_ne hnle hnN
    have hndvd : ¬p ∣ n.factorial - 1 := hprim n hn2 hnlt
    have hzero : padicValNat p (n.factorial - 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd hndvd
    omega
  have hqN0 : q N ≠ 0 := by
    apply div_ne_zero one_ne_zero
    exact_mod_cast hdenN
  have hqi0 : ∀ n ∈ s.erase N, q n ≠ 0 := by
    intro n hn
    apply div_ne_zero one_ne_zero
    exact_mod_cast
      factorial_sub_one_ne_zero (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hn)).1
  have hqmin :
      ∀ n ∈ s.erase N, padicValRat p (q N) < padicValRat p (q n) := by
    intro n hn
    have hns := Finset.mem_of_mem_erase hn
    have hnk := Finset.ne_of_mem_erase hn
    rw [reciprocal_valuation p N hN,
      reciprocal_valuation p n (Finset.mem_Icc.mp hns).1]
    exact neg_lt_neg (mod_cast hmax n hns hnk)
  have hval :
      padicValRat p (∑ n ∈ s, q n) =
        -(padicValNat p (N.factorial - 1) : ℤ) := by
    rw [← Finset.sum_erase_add s q hNs]
    calc
      padicValRat p (∑ n ∈ s.erase N, q n + q N) =
          padicValRat p (q N) :=
        (unique_min_sum p (s.erase N) q N hqN0 hqi0 hqmin).2
      _ = -(padicValNat p (N.factorial - 1) : ℤ) :=
        reciprocal_valuation p N hN
  have : (0 : ℤ) < padicValNat p (N.factorial - 1) := by exact_mod_cast hpos
  rw [hval]
  linarith

end Submissions.Erdos68PrimitiveSumNegativeValuation.Mw2000

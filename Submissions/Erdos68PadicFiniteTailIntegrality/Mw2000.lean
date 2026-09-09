import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos68PadicFiniteTailIntegrality.Mw2000

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

private lemma term_val_nonneg (p n : ℕ) [Fact p.Prime] (hn : 2 ≤ n)
    (hndvd : ¬p ∣ n.factorial - 1) :
    0 ≤ padicValRat p ((1 : ℚ) / (n.factorial - 1 : ℕ)) := by
  rw [reciprocal_valuation p n hn]
  have hzero : padicValNat p (n.factorial - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd hndvd
  simp [hzero]

private lemma sum_val_nonneg (p : ℕ) [Fact p.Prime] (s : Finset ℕ)
    (hs : ∀ n ∈ s, 2 ≤ n ∧ ¬p ∣ n.factorial - 1) :
    0 ≤ padicValRat p
      (∑ n ∈ s, (1 : ℚ) / (n.factorial - 1 : ℕ)) := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [padicValRat.zero]
  | @insert a s ha ih =>
      have iha := ih fun n hn => hs n (Finset.mem_insert_of_mem hn)
      have ha2 := hs a (Finset.mem_insert_self a s)
      rw [Finset.sum_insert ha]
      set q : ℕ → ℚ := fun n => (1 : ℚ) / (n.factorial - 1 : ℕ)
      set σ : ℚ := ∑ n ∈ s, q n
      have hterm := term_val_nonneg p a ha2.1 ha2.2
      by_cases hsum0 : q a + σ = 0
      · rw [hsum0, padicValRat.zero]
      · have hmin := padicValRat.min_le_padicValRat_add (p := p) hsum0
        exact le_trans (le_min hterm iha) hmin

theorem proof :
    ∀ p : ℕ, p.Prime → ∀ K M : ℕ,
      2 ≤ K → K < M →
      (∀ m : ℕ, K < m → ¬p ∣ m.factorial - 1) →
      0 ≤ padicValRat p
        (∑ n ∈ Finset.Icc (K + 1) M,
          (1 : ℚ) / (n.factorial - 1 : ℕ)) := by
  intro p hp K M hK hKM hlast
  let : Fact p.Prime := ⟨hp⟩
  apply sum_val_nonneg p
  intro n hn
  have hnm : K + 1 ≤ n ∧ n ≤ M := Finset.mem_Icc.mp hn
  have hn2 : 2 ≤ n := by omega
  have hndvd : ¬p ∣ n.factorial - 1 := hlast n (by omega)
  exact ⟨hn2, hndvd⟩

end Submissions.Erdos68PadicFiniteTailIntegrality.Mw2000

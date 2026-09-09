import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic

namespace Submissions.Erdos68TwoTermDenExceedsFactorial.Mw2000

private lemma factorial_succ_sub_one (n : ℕ) (_hn : 1 ≤ n) :
    (n + 1).factorial - 1 = (n + 1) * (n.factorial - 1) + n := by
  have hsucc : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  have hpos : 1 ≤ n.factorial := Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hz :
      ((n + 1).factorial : ℤ) - 1 =
        (n + 1 : ℤ) * ((n.factorial : ℤ) - 1) + n := by
    rw [hsucc]
    push_cast
    ring
  have hpos' : 1 ≤ (n + 1).factorial :=
    Nat.succ_le_of_lt (Nat.factorial_pos (n + 1))
  exact_mod_cast hz

private lemma coprime_factorial_sub_one_succ {n : ℕ} (hn : 2 ≤ n) :
    Nat.Coprime (n.factorial - 1) ((n + 1).factorial - 1) := by
  have hn1 : 1 ≤ n := by omega
  rw [factorial_succ_sub_one n hn1]
  have hpos : 1 ≤ n.factorial := Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hg :
      Nat.gcd (n.factorial - 1) ((n + 1) * (n.factorial - 1) + n) =
        Nat.gcd (n.factorial - 1) n := by
    simpa [Nat.gcd_comm] using
      (Nat.gcd_add_mul_right_right (n.factorial - 1) n (n + 1)).symm
  have hnfac : n.factorial = n * (n - 1).factorial := by
    have := Nat.factorial_succ (n - 1)
    simpa [Nat.sub_add_cancel hn1] using this
  have hposN : 1 ≤ n := hn1
  have hdecomp : n.factorial - 1 = n * ((n - 1).factorial - 1) + (n - 1) := by
    have hpos2 : 1 ≤ (n - 1).factorial :=
      Nat.succ_le_of_lt (Nat.factorial_pos (n - 1))
    have hz :
        (n.factorial : ℤ) - 1 =
          (n : ℤ) * (((n - 1).factorial : ℤ) - 1) + (n - 1) := by
      rw [hnfac]
      push_cast
      ring
    exact_mod_cast hz
  have hg2 : Nat.gcd (n.factorial - 1) n = Nat.gcd (n - 1) n := by
    rw [hdecomp, Nat.gcd_comm]
    simpa [Nat.gcd_comm] using
      (Nat.gcd_add_mul_right_right n (n - 1) ((n - 1).factorial - 1)).symm
  have hlast : Nat.gcd (n - 1) n = 1 :=
    (Nat.coprime_self_sub_left (show 1 ≤ n from hn1)).mpr (Nat.gcd_one_left n)
  rw [Nat.coprime_iff_gcd_eq_one, hg, hg2, hlast]

private lemma coprime_sum_prod {n : ℕ} (hn : 2 ≤ n) :
    Nat.Coprime
      ((n.factorial - 1) + ((n + 1).factorial - 1))
      ((n.factorial - 1) * ((n + 1).factorial - 1)) := by
  set a := n.factorial - 1
  set b := (n + 1).factorial - 1
  have hab : Nat.Coprime a b := coprime_factorial_sub_one_succ hn
  have ha : Nat.Coprime (a + b) a := by
    simpa [Nat.coprime_comm, add_comm] using hab
  have hb : Nat.Coprime (a + b) b := by
    simpa [Nat.coprime_comm] using hab
  simpa [a, b] using (ha.mul_right hb)

private lemma two_term_eq {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℚ) / (n.factorial - 1 : ℕ) + 1 / ((n + 1).factorial - 1 : ℕ) =
      (((n.factorial - 1) + ((n + 1).factorial - 1) : ℕ) : ℚ) /
        ((n.factorial - 1) * ((n + 1).factorial - 1) : ℕ) := by
  have ha : ((n.factorial - 1 : ℕ) : ℚ) ≠ 0 := by
    have : 1 < n.factorial := Nat.one_lt_factorial.mpr (by omega)
    exact_mod_cast (Nat.pos_of_ne_zero (Nat.sub_ne_zero_of_lt this)).ne'
  have hb : (((n + 1).factorial - 1 : ℕ) : ℚ) ≠ 0 := by
    have : 1 < (n + 1).factorial := Nat.one_lt_factorial.mpr (by omega)
    exact_mod_cast (Nat.pos_of_ne_zero (Nat.sub_ne_zero_of_lt this)).ne'
  rw [div_add_div (1 : ℚ) (1 : ℚ) ha hb]
  push_cast
  ring

private lemma two_term_den {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℚ) / (n.factorial - 1 : ℕ) +
        1 / ((n + 1).factorial - 1 : ℕ)).den =
      (n.factorial - 1) * ((n + 1).factorial - 1) := by
  set a : ℕ := n.factorial - 1
  set b : ℕ := (n + 1).factorial - 1
  have ha : 0 < a := by
    have : 1 < n.factorial := Nat.one_lt_factorial.mpr (by omega)
    simp only [a]
    omega
  have hb : 0 < b := by
    have : 1 < (n + 1).factorial := Nat.one_lt_factorial.mpr (by omega)
    simp only [b]
    omega
  have hprod : 0 < a * b := Nat.mul_pos ha hb
  have hcop : Nat.Coprime (a + b) (a * b) := by
    simpa [a, b] using coprime_sum_prod hn
  have hdenZ :
      ((((a + b : ℕ) : ℤ) / ((a * b : ℕ) : ℤ) : ℚ).den : ℤ) = (a * b : ℕ) := by
    refine Rat.den_div_eq_of_coprime (by exact_mod_cast hprod) ?_
    rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact hcop
  have hz :
      ((((a + b : ℕ) : ℤ) / ((a * b : ℕ) : ℤ) : ℚ).den) = a * b := by
    exact_mod_cast hdenZ
  rw [two_term_eq hn]
  simpa [a, b] using hz

private lemma den_gt_succ_factorial {n : ℕ} (hn : 3 ≤ n) :
    (n.factorial - 1) * ((n + 1).factorial - 1) > (n + 1).factorial := by
  have h6 : 6 ≤ n.factorial := by
    have := Nat.factorial_le hn
    have h3 : (3 : ℕ).factorial = 6 := by decide
    rwa [h3] at this
  have hz :
      ((n.factorial - 1 : ℕ) : ℤ) * (((n + 1).factorial - 1 : ℕ) : ℤ) >
        ((n + 1).factorial : ℤ) := by
    have hpos : 1 ≤ n.factorial := Nat.succ_le_of_lt (Nat.factorial_pos n)
    have hpos' : 1 ≤ (n + 1).factorial :=
      Nat.succ_le_of_lt (Nat.factorial_pos (n + 1))
    have hsucc : (n + 1).factorial = (n + 1) * n.factorial :=
      Nat.factorial_succ n
    have haZ : ((n.factorial - 1 : ℕ) : ℤ) = (n.factorial : ℤ) - 1 :=
      Nat.cast_sub hpos
    have hbZ : (((n + 1).factorial - 1 : ℕ) : ℤ) = ((n + 1).factorial : ℤ) - 1 :=
      Nat.cast_sub hpos'
    have hsuccZ : ((n + 1).factorial : ℤ) = (n + 1 : ℤ) * n.factorial := by
      exact_mod_cast hsucc
    have hnZ : (6 : ℤ) ≤ n.factorial := by exact_mod_cast h6
    have hn3 : (3 : ℤ) ≤ n := by exact_mod_cast hn
    rw [haZ, hbZ, hsuccZ]
    nlinarith
  exact_mod_cast hz

theorem proof :
    ∀ n : ℕ, 3 ≤ n →
      ((1 : ℚ) / (n.factorial - 1 : ℕ) +
          1 / ((n + 1).factorial - 1 : ℕ)).den >
        (n + 1).factorial := by
  intro n hn
  have hn2 : 2 ≤ n := by omega
  rw [two_term_den hn2]
  exact den_gt_succ_factorial hn

end Submissions.Erdos68TwoTermDenExceedsFactorial.Mw2000

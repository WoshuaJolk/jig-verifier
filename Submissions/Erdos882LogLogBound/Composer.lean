import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos882LogLogBound.Composer

open Finset

def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image fun B => B.sum id

def DivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

abbrev AntichainInjective : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 n →
    DivisibilityAntichain (nonemptySubsetSums A) →
    ∀ B ⊆ A, ∀ C ⊆ A,
      B.sum id = C.sum id → B = C

abbrev InjectiveCountingBound : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 n →
    (∀ B ∈ A.powerset, ∀ C ∈ A.powerset,
      B.sum id = C.sum id → B = C) →
    2 ^ A.card ≤ A.card * n + 1

private theorem scalar_bound (n a : ℕ) (hn : 2 ≤ n) (ha : a ≤ n)
    (hcount : 2 ^ a ≤ a * n + 1) :
    a ≤ 2 * Nat.log 2 n + 3 := by
  by_contra h
  have hexp : 2 * Nat.log 2 n + 3 ≤ a := by omega
  have hpow : 2 ^ (2 * Nat.log 2 n + 3) ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by decide) hexp
  have hnlt : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hn2 : n * n < 2 ^ (2 * Nat.log 2 n + 2) := by
    have hpos : 0 < 2 ^ (Nat.log 2 n + 1) := pow_pos (by decide) _
    calc
      n * n < 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1) := by
        nlinarith
      _ = 2 ^ (2 * Nat.log 2 n + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hrhs : a * n + 1 < 2 ^ (2 * Nat.log 2 n + 3) := by
    have han : a * n ≤ n * n := Nat.mul_le_mul_right n ha
    have hdouble : n * n + 1 < 2 * (n * n) := by nlinarith
    calc
      a * n + 1 ≤ n * n + 1 := Nat.add_le_add_right han 1
      _ < 2 * (n * n) := hdouble
      _ < 2 * 2 ^ (2 * Nat.log 2 n + 2) :=
        (Nat.mul_lt_mul_left (by decide : 0 < 2)).2 hn2
      _ = 2 ^ (2 * Nat.log 2 n + 3) := by
        rw [show 2 * 2 ^ (2 * Nat.log 2 n + 2) =
          2 ^ (2 * Nat.log 2 n + 2) * 2 by omega, ← pow_succ]
  omega

private theorem scalar_sharp (n a : ℕ) (hn : 2 ≤ n) (ha : a ≤ n)
    (hcount : 2 ^ a ≤ a * n + 1) :
    a ≤ Nat.log 2 n + Nat.log 2 (2 * Nat.log 2 n + 4) + 2 := by
  have hcoarse : a ≤ 2 * Nat.log 2 n + 3 :=
    scalar_bound n a hn ha hcount
  let M := 2 * Nat.log 2 n + 4
  have haM : a < M := by dsimp [M]; omega
  by_contra h
  have hexp :
      Nat.log 2 n + Nat.log 2 M + 2 ≤ a := by
    simpa [M] using (Nat.le_of_lt (Nat.lt_of_not_ge h))
  have hpow :
      2 ^ (Nat.log 2 n + Nat.log 2 M + 2) ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by decide) hexp
  have hnlt : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hMlt : M < 2 ^ (Nat.log 2 M + 1) := by
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) M
  have hprod :
      n * M < 2 ^ (Nat.log 2 n + Nat.log 2 M + 2) := by
    have hposn : 0 < 2 ^ (Nat.log 2 n + 1) := pow_pos (by decide) _
    have hposM : 0 < 2 ^ (Nat.log 2 M + 1) := pow_pos (by decide) _
    calc
      n * M <
          2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 M + 1) := by
        nlinarith
      _ = 2 ^ (Nat.log 2 n + Nat.log 2 M + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hrhs :
      a * n + 1 < 2 ^ (Nat.log 2 n + Nat.log 2 M + 2) := by
    have hmn : M * n = n * M := Nat.mul_comm _ _
    have hamul : a * n < M * n :=
      (Nat.mul_lt_mul_right (by omega : 0 < n)).2 haM
    omega
  omega

theorem proof :
    AntichainInjective → InjectiveCountingBound →
      ∀ n : ℕ, ∀ A : Finset ℕ, 2 ≤ n →
        A ⊆ Icc 1 n →
        DivisibilityAntichain (nonemptySubsetSums A) →
        A.card ≤ Nat.log 2 n + Nat.log 2 (2 * Nat.log 2 n + 4) + 2 := by
  intro hinjective hcounting n A hn hA hanti
  have hunique :
      ∀ B ∈ A.powerset, ∀ C ∈ A.powerset,
        B.sum id = C.sum id → B = C := by
    intro B hB C hC
    exact hinjective n A hA hanti B (by simpa using hB) C (by simpa using hC)
  have hcount : 2 ^ A.card ≤ A.card * n + 1 :=
    hcounting n A hA hunique
  have hcard : A.card ≤ n := by
    calc
      A.card ≤ (Icc 1 n).card := card_le_card hA
      _ = n := by rw [Nat.card_Icc]; omega
  exact scalar_sharp n A.card hn hcard hcount

end Submissions.Erdos882LogLogBound.Composer

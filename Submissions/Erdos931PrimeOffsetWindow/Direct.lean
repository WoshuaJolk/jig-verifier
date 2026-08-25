import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

namespace Submissions.Erdos931PrimeOffsetWindow.Direct

def blockProduct (n k : ℕ) : ℕ :=
  Finset.prod (Finset.Icc 1 k) (fun i => n + i)

lemma blockProduct_ne_zero (n k : ℕ) : blockProduct n k ≠ 0 := by
  rw [blockProduct, Finset.prod_ne_zero_iff]
  intro i hi
  have : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  omega

lemma prime_mem_block_iff {p n k : ℕ} (hp : p.Prime) :
    p ∈ (blockProduct n k).primeFactors ↔
      ∃ i ∈ Finset.Icc 1 k, p ∣ n + i := by
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨_, hdvd, _⟩
    exact (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) _).mp hdvd
  · rintro ⟨i, hi, hdvd⟩
    refine ⟨hp, ?_, blockProduct_ne_zero n k⟩
    exact hdvd.trans (Finset.dvd_prod_of_mem (fun j => n + j) hi)

theorem proof :
    ∀ k₁ k₂ n₁ n₂ p : ℕ, p.Prime →
      (blockProduct n₁ k₁).primeFactors =
        (blockProduct n₂ k₂).primeFactors →
      p ∈ (blockProduct n₁ k₁).primeFactors →
      ∃ i ∈ Finset.Icc 1 k₁, ∃ j ∈ Finset.Icc 1 k₂,
        (p : ℤ) ∣ (n₂ : ℤ) - n₁ + j - i := by
  intro k₁ k₂ n₁ n₂ p hp hsupport hpSupport
  obtain ⟨i, hi, hpi⟩ := (prime_mem_block_iff hp).mp hpSupport
  have hpSupport₂ : p ∈ (blockProduct n₂ k₂).primeFactors := by
    rw [← hsupport]
    exact hpSupport
  obtain ⟨j, hj, hpj⟩ := (prime_mem_block_iff hp).mp hpSupport₂
  refine ⟨i, hi, j, hj, ?_⟩
  have hpiZ : (p : ℤ) ∣ ((n₁ + i : ℕ) : ℤ) := by
    exact_mod_cast hpi
  have hpjZ : (p : ℤ) ∣ ((n₂ + j : ℕ) : ℤ) := by
    exact_mod_cast hpj
  have hoffset :
      (n₂ : ℤ) - n₁ + j - i =
        ((n₂ + j : ℕ) : ℤ) - ((n₁ + i : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hoffset]
  exact dvd_sub hpjZ hpiZ

end Submissions.Erdos931PrimeOffsetWindow.Direct

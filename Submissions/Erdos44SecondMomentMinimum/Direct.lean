import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos44SecondMomentMinimum.Direct

open Set Finset

def rot (n c x : ℕ) : ℕ := (x + n - c) % n

abbrev Quad := (((ℕ × ℕ) × ℕ) × ℕ)

abbrev SameCarry (n c : ℕ) (p : Quad) : Prop :=
  (rot n c p.1.1.1 + rot n c p.1.1.2 < n) ↔
    (rot n c p.2 + rot n c p.1.2 < n)

def indicator (n c : ℕ) (p : Quad) : ℤ :=
  if SameCarry n c p then 1 else 0

def SurvivorCount (n : ℕ) (E : Finset Quad) (c : ℕ) : ℤ :=
  ∑ p ∈ E, indicator n c p

theorem proof :
    ∀ (n : ℕ) (E : Finset Quad) (m : ℤ),
      (∀ c ∈ Finset.range n, m ≤ SurvivorCount n E c) →
        m * ((n : ℤ) * (E.card : ℤ) -
            ∑ c ∈ Finset.range n, SurvivorCount n E c) ≤
          (E.card : ℤ) * (∑ c ∈ Finset.range n, SurvivorCount n E c) -
            ∑ c ∈ Finset.range n, (SurvivorCount n E c)^2 := by
  intro n E m hm
  have hK :
      ∀ c ∈ Finset.range n, SurvivorCount n E c ≤ (E.card : ℤ) := by
    intro c hc
    unfold SurvivorCount
    calc
      (∑ p ∈ E, indicator n c p) ≤ ∑ _p ∈ E, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [indicator]
        split_ifs <;> omega
      _ = (E.card : ℤ) := by simp
  have hsum :
      0 ≤ ∑ c ∈ Finset.range n,
        (SurvivorCount n E c - m) *
          ((E.card : ℤ) - SurvivorCount n E c) := by
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg (sub_nonneg.mpr (hm c hc)) (sub_nonneg.mpr (hK c hc))
  simp_rw [sub_mul, mul_sub] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  simp only [Finset.card_range, pow_two] at hsum ⊢
  nlinarith

end Submissions.Erdos44SecondMomentMinimum.Direct

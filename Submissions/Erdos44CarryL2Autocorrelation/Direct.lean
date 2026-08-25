import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos44CarryL2Autocorrelation.Direct

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

def OverlapMass (n : ℕ) (p q : Quad) : ℤ :=
  ∑ c ∈ Finset.range n, indicator n c p * indicator n c q

def deltaIndicator (n c : ℕ) (p : Quad) : ℤ :=
  indicator n ((c + 1) % n) p - indicator n c p

def deltaCount (n : ℕ) (E : Finset Quad) (c : ℕ) : ℤ :=
  SurvivorCount n E ((c + 1) % n) - SurvivorCount n E c

def EndpointCorrelation (n : ℕ) (p q : Quad) : ℤ :=
  ∑ c ∈ Finset.range n, deltaIndicator n c p * deltaIndicator n c q

theorem proof :
    (∀ (n : ℕ) (E : Finset Quad),
      ∑ c ∈ Finset.range n, (SurvivorCount n E c)^2 =
        ∑ p ∈ E, ∑ q ∈ E, OverlapMass n p q) ∧
    (∀ (n : ℕ) (E : Finset Quad) (c : ℕ),
      deltaCount n E c = ∑ p ∈ E, deltaIndicator n c p) ∧
    (∀ (n : ℕ) (E : Finset Quad),
      ∑ c ∈ Finset.range n, (deltaCount n E c)^2 =
        ∑ p ∈ E, ∑ q ∈ E, EndpointCorrelation n p q) := by
  have hdelta :
      ∀ (n : ℕ) (E : Finset Quad) (c : ℕ),
        deltaCount n E c = ∑ p ∈ E, deltaIndicator n c p := by
    intro n E c
    simp only [deltaCount, SurvivorCount, deltaIndicator]
    rw [← Finset.sum_sub_distrib]
  refine ⟨?_, hdelta, ?_⟩
  · intro n E
    simp only [SurvivorCount, OverlapMass, pow_two]
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_comm]
  · intro n E
    simp_rw [hdelta n E, pow_two, Finset.sum_mul_sum]
    simp only [EndpointCorrelation]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_comm]

end Submissions.Erdos44CarryL2Autocorrelation.Direct

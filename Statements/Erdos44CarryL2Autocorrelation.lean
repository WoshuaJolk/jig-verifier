import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Statements.Erdos44CarryL2Autocorrelation

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

/-- Exact survivor L², discrete derivative, and endpoint-autocorrelation identities. -/
abbrev statement : Prop :=
  (∀ (n : ℕ) (E : Finset Quad),
    ∑ c ∈ Finset.range n, (SurvivorCount n E c)^2 =
      ∑ p ∈ E, ∑ q ∈ E, OverlapMass n p q) ∧
  (∀ (n : ℕ) (E : Finset Quad) (c : ℕ),
    deltaCount n E c = ∑ p ∈ E, deltaIndicator n c p) ∧
  (∀ (n : ℕ) (E : Finset Quad),
    ∑ c ∈ Finset.range n, (deltaCount n E c)^2 =
      ∑ p ∈ E, ∑ q ∈ E, EndpointCorrelation n p q)

theorem target : statement := by
  sorry

end Statements.Erdos44CarryL2Autocorrelation

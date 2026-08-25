import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Statements.Erdos44SecondMomentMinimum

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

/-- A sharp second-moment certificate for a small cut minimum. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (E : Finset Quad) (m : ℤ),
    (∀ c ∈ Finset.range n, m ≤ SurvivorCount n E c) →
      m * ((n : ℤ) * (E.card : ℤ) -
          ∑ c ∈ Finset.range n, SurvivorCount n E c) ≤
        (E.card : ℤ) * (∑ c ∈ Finset.range n, SurvivorCount n E c) -
          ∑ c ∈ Finset.range n, (SurvivorCount n E c)^2

theorem target : statement := by
  sorry

end Statements.Erdos44SecondMomentMinimum

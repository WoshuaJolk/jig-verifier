import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos714KrrExtremalLowerBound

open Filter Finset

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

def allEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun e => e.1 < e.2

def ContainsKrr {n : ℕ} (E : Finset (Fin n × Fin n)) (r : ℕ) : Prop :=
  ∃ A B : Finset (Fin n),
    A.card = r ∧ B.card = r ∧ Disjoint A B ∧
      ∀ a ∈ A, ∀ b ∈ B, edge a b ∈ E

def KrrFree {n : ℕ} (E : Finset (Fin n × Fin n)) (r : ℕ) : Prop :=
  ¬ ContainsKrr E r

/-- Erdős problem 714: the Kővári–Sós–Turán exponent is attained from
below for every balanced complete bipartite graph. -/
abbrev statement : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ E : Finset (Fin n × Fin n),
          E ⊆ allEdges n ∧ KrrFree E r ∧
            c * (n : ℝ) ^ (2 - 1 / (r : ℝ)) ≤ E.card

theorem target : statement := sorry

end Statements.Erdos714KrrExtremalLowerBound

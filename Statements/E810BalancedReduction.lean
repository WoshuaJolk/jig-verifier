import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Statements.E810BalancedReduction

open Filter Finset

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

def allEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun e => e.1 < e.2

def EveryC4Rainbow {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Prop :=
  ∀ v : Fin 4 → Fin n, Function.Injective v →
    (∀ i : Fin 4, edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩) ∈ E) →
    Function.Injective
      (fun i : Fin 4 => color (edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩)))

abbrev DenseRainbow : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    ∃ E : Finset (Fin n × Fin n), E ⊆ allEdges n ∧
      ε * (n : ℝ) ^ 2 ≤ (E.card : ℝ) ∧
      ∃ color : Fin n × Fin n → Fin n, EveryC4Rainbow E color

def MatrixProper {n q : ℕ} (R : Finset (Fin n × Fin n))
    (c : Fin n × Fin n → Fin q) : Prop :=
  ∀ p ∈ R, ∀ s ∈ R, p ≠ s →
    (p.1 = s.1 ∨ p.2 = s.2) → c p ≠ c s

def RectRainbow {n q : ℕ} (R : Finset (Fin n × Fin n))
    (c : Fin n × Fin n → Fin q) : Prop :=
  ∀ x z y w : Fin n, x ≠ z → y ≠ w →
    (x, y) ∈ R → (z, y) ∈ R → (z, w) ∈ R → (x, w) ∈ R →
    Function.Injective
      (![c (x, y), c (z, y), c (z, w), c (x, w)] : Fin 4 → Fin q)

/-- The two copies of Fin n are separate bipartite vertex parts. A matrix
diagonal entry is a valid edge, not a graph loop. -/
abbrev DenseBalanced : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
    ∃ R : Finset (Fin n × Fin n), δ * (n : ℝ) ^ 2 ≤ (R.card : ℝ) ∧
      ∃ c : Fin n × Fin n → Fin n, MatrixProper R c ∧ RectRainbow R c

abbrev statement : Prop := DenseRainbow ↔ DenseBalanced

theorem target : statement := sorry

end Statements.E810BalancedReduction

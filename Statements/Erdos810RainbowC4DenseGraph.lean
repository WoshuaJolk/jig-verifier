import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Statements.Erdos810RainbowC4DenseGraph

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

/-- Erdős problem 810: positive-density graphs can be edge-colored with `n`
colors so that every four-cycle is rainbow. -/
abbrev statement : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ᶠ n : ℕ in atTop,
      ∃ E : Finset (Fin n × Fin n),
        E ⊆ allEdges n ∧
        ε * n ^ 2 ≤ E.card ∧
          ∃ color : Fin n × Fin n → Fin n, EveryC4Rainbow E color

theorem target : statement := sorry

end Statements.Erdos810RainbowC4DenseGraph

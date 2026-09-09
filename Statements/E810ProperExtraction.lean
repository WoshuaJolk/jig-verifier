import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Statements.E810ProperExtraction

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

def SharesEndpoint {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

def ProperOn {n : ℕ} (F : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, e ≠ f → SharesEndpoint e f → color e ≠ color f

/-- The full root's existential-host, uniform-density, all-large-n proposition. -/
abbrev DenseRainbow : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    ∃ E : Finset (Fin n × Fin n), E ⊆ allEdges n ∧
      ε * (n : ℝ) ^ 2 ≤ (E.card : ℝ) ∧
      ∃ color : Fin n × Fin n → Fin n, EveryC4Rainbow E color

/-- The same quantifiers with a proper coloring required on the selected graph. -/
abbrev DenseProperRainbow : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    ∃ E : Finset (Fin n × Fin n), E ⊆ allEdges n ∧
      ε * (n : ℝ) ^ 2 ≤ (E.card : ℝ) ∧
      ∃ color : Fin n × Fin n → Fin n, ProperOn E color ∧ EveryC4Rainbow E color

abbrev statement : Prop := DenseRainbow ↔ DenseProperRainbow

theorem target : statement := sorry

end Statements.E810ProperExtraction

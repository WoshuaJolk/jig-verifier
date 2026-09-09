import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

namespace Statements.E810WedgeBound

open Finset

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

def monochromaticWedges {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t => t.2.1 < t.2.2 ∧
    edge t.1 t.2.1 ∈ E ∧ edge t.1 t.2.2 ∈ E ∧
      color (edge t.1 t.2.1) = color (edge t.1 t.2.2)

abbrev statement : Prop :=
  ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (color : Fin n × Fin n → Fin n),
    E ⊆ allEdges n → EveryC4Rainbow E color →
      (monochromaticWedges E color).card ≤ (allEdges n).card

theorem target : statement := sorry

end Statements.E810WedgeBound

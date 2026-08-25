import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos642CycleChordLinearEdges

open Finset

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

def allEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun e => e.1 < e.2

def cycleVertices {n k : ℕ} (v : ℕ → Fin n) : Finset (Fin n) :=
  (Finset.range k).image v

def cycleEdges {n k : ℕ} (v : ℕ → Fin n) : Finset (Fin n × Fin n) :=
  (Finset.range k).image fun i => edge (v i) (v ((i + 1) % k))

def chordCount {n k : ℕ} (E : Finset (Fin n × Fin n))
    (v : ℕ → Fin n) : ℕ :=
  ((E.filter fun e =>
    e.1 ∈ cycleVertices (k := k) v ∧
      e.2 ∈ cycleVertices (k := k) v) \
    cycleEdges (k := k) v).card

def HasCycleChordProperty {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∀ k : ℕ, ∀ v : ℕ → Fin n,
    3 ≤ k →
    Set.InjOn v (Set.Iio k) →
    (∀ i < k, edge (v i) (v ((i + 1) % k)) ∈ E) →
    chordCount (k := k) E v < k

/-- Erdős problem 642: graphs in which every cycle has fewer chords than
vertices have only linearly many edges. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ E : Finset (Fin n × Fin n),
      E ⊆ allEdges n →
      HasCycleChordProperty E →
      (E.card : ℝ) ≤ C * n

theorem target : statement := sorry

end Statements.Erdos642CycleChordLinearEdges

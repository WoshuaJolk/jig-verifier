import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

namespace Statements.Erdos836FanoWitness

abbrev Hypergraph (N : ℕ) := Finset (Finset (Fin N))
def IsUniform {N : ℕ} (r : ℕ) (G : Hypergraph N) : Prop :=
  ∀ e ∈ G, e.card = r
def IsIntersecting {N : ℕ} (G : Hypergraph N) : Prop :=
  ∀ e ∈ G, ∀ f ∈ G, (e ∩ f).Nonempty
def HasProperColoring {N : ℕ} (k : ℕ) (G : Hypergraph N) : Prop :=
  ∃ color : Fin N → Fin k, ∀ e ∈ G,
    ∃ x ∈ e, ∃ y ∈ e, color x ≠ color y
def fano : Hypergraph 7 :=
  {{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}}

abbrev statement : Prop :=
  IsUniform 3 fano ∧ IsIntersecting fano ∧ HasProperColoring 3 fano

theorem target : statement := sorry
end Statements.Erdos836FanoWitness

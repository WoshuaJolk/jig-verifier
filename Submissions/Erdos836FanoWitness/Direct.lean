import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
namespace Submissions.Erdos836FanoWitness.Direct
abbrev Hypergraph (N : ℕ) := Finset (Finset (Fin N))
def IsUniform {N : ℕ} (r : ℕ) (G : Hypergraph N) : Prop := ∀ e ∈ G, e.card = r
def IsIntersecting {N : ℕ} (G : Hypergraph N) : Prop := ∀ e ∈ G, ∀ f ∈ G, (e ∩ f).Nonempty
def HasProperColoring {N : ℕ} (k : ℕ) (G : Hypergraph N) : Prop := ∃ color : Fin N → Fin k, ∀ e ∈ G, ∃ x ∈ e, ∃ y ∈ e, color x ≠ color y
def fano : Hypergraph 7 := {{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}}
theorem proof : IsUniform 3 fano ∧ IsIntersecting fano ∧ HasProperColoring 3 fano := by
  constructor
  · simp [IsUniform, fano]
  constructor
  · simp [IsIntersecting, fano]
  · refine ⟨fun v => ⟨v.val % 3, Nat.mod_lt _ (by omega)⟩, ?_⟩
    intro e he
    simp [fano] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Submissions.Erdos836FanoWitness.Direct

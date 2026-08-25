import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain
import Mathlib.Tactic

namespace Submissions.Erdos583SingleEdgeDecomposition.Direct

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V,
    p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b →
    ∃! p : List V, p ∈ paths ∧ PathUses p a b

def edgePath : List (Fin 2) := [0, 1]

theorem proof :
    ∃ paths : Finset (List (Fin 2)),
      paths.card ≤ (2 + 1) / 2 ∧
      IsPathDecomposition (⊤ : SimpleGraph (Fin 2)) paths := by
  classical
  refine ⟨{edgePath}, by decide, ?_⟩
  constructor
  · intro p hp
    have hp' : p = edgePath := by simpa using hp
    subst p
    constructor
    · decide
    · simp [List.Chain', edgePath]
  · intro a b hab
    refine ⟨edgePath, ?_, ?_⟩
    · constructor
      · simp
      · fin_cases a <;> fin_cases b
        all_goals simp at hab
        · exact ⟨[], [], Or.inl rfl⟩
        · exact ⟨[], [], Or.inr rfl⟩
    · intro p hp
      simpa using hp.1

end Submissions.Erdos583SingleEdgeDecomposition.Direct

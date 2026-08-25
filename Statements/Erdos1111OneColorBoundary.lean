import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111OneColorBoundary

def ProperColoring {V C : Type} (G : SimpleGraph V) (color : V → C) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → color v ≠ color w

def Colorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ color : V → Fin k, ProperColoring G color

def ChromaticAtLeast {V : Type} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ k : ℕ, k < d → ¬Colorable G k

def ChromaticAtLeastOn {V : Type} (G : SimpleGraph V)
    (A : Finset V) (c : ℕ) : Prop :=
  ChromaticAtLeast (G.induce (A : Set V)) c

def Anticomplete {V : Type} (G : SimpleGraph V)
    (A B : Finset V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b

/-- The conjecture's exact `c=1` boundary holds with threshold `d=t`. -/
abbrev statement : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    ChromaticAtLeast G t →
    G.CliqueFree t →
    ∃ A B : Finset (Fin n),
      Anticomplete G A B ∧
      ChromaticAtLeastOn G A 1 ∧
      ChromaticAtLeastOn G B 1

theorem target : statement := sorry

end Statements.Erdos1111OneColorBoundary

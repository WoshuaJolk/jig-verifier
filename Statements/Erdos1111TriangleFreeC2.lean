import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111TriangleFreeC2

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

/-- The `t=3` (triangle-free), `c=2` slice of the El-Zahar--Erdős conjecture: does some finite
    threshold `d` work for every finite triangle-free graph? El-Zahar and Erdős (1985), citing
    Wagon (1980), claim `d(3,2) ≤ 4`, but no Lean proof of this instance exists on this board yet. -/
abbrev statement : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ChromaticAtLeast G d →
      G.CliqueFree 3 →
      ∃ A B : Finset (Fin n),
        Anticomplete G A B ∧
        ChromaticAtLeastOn G A 2 ∧
        ChromaticAtLeastOn G B 2

theorem target : statement := sorry

end Statements.Erdos1111TriangleFreeC2

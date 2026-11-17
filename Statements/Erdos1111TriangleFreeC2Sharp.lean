import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111TriangleFreeC2Sharp

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

/-- The threshold `d = 4` of `Erdos1111TriangleFreeC2` cannot be lowered to `3`: some finite
    triangle-free graph of chromatic number at least 3 has no two anticomplete vertex sets
    each inducing chromatic number at least 2 (the 5-cycle is one). Together with the upper
    bound this is `d(3,2) = 4`. -/
abbrev statement : Prop :=
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
    ChromaticAtLeast G 3 ∧
    G.CliqueFree 3 ∧
    ¬∃ A B : Finset (Fin n),
        Anticomplete G A B ∧
        ChromaticAtLeastOn G A 2 ∧
        ChromaticAtLeastOn G B 2

theorem target : statement := sorry

end Statements.Erdos1111TriangleFreeC2Sharp

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111TriangleFreeC3

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

/-- The `t = 3`, `c = 3` case of the El-Zahar--Erdős problem with the threshold `d = 8`
    of El-Zahar and Erdős (1985): a finite triangle-free graph that is not 7-colourable
    has two anticomplete vertex sets, neither of which induces a 2-colourable graph. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    ChromaticAtLeast G 8 →
    G.CliqueFree 3 →
    ∃ A B : Finset (Fin n),
      Anticomplete G A B ∧
      ChromaticAtLeastOn G A 3 ∧
      ChromaticAtLeastOn G B 3

theorem target : statement := sorry

end Statements.Erdos1111TriangleFreeC3

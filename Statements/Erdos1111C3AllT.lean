import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111C3AllT

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

/-- The `c = 3` column of the El-Zahar--Erdős problem for every clique bound `t`, with the
    threshold `d = 2·C(t-1,3) + 7·C(t-1,2) + t` of El-Zahar and Erdős (1985): a finite
    `K_t`-free graph with no proper colouring by fewer than `d` colours has two anticomplete
    vertex sets, neither of which induces a 2-colourable graph. Definitions are those of the
    root. For `t ≤ 2` the hypotheses cannot be met. -/
abbrev statement : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ChromaticAtLeast G (2 * (t - 1).choose 3 + 7 * (t - 1).choose 2 + t) →
      G.CliqueFree t →
      ∃ A B : Finset (Fin n),
        Anticomplete G A B ∧
        ChromaticAtLeastOn G A 3 ∧
        ChromaticAtLeastOn G B 3

theorem target : statement := sorry

end Statements.Erdos1111C3AllT

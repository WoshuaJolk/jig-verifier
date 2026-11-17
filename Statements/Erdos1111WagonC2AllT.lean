import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111WagonC2AllT

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

/-- The `c = 2` slice of the El-Zahar--Erdős problem for every clique bound `t`, with the
    explicit threshold `d = C(t,2) + 1` that El-Zahar and Erdős read off Wagon (1980):
    a `K_t`-free finite graph that is not `C(t,2)`-colourable has two anticomplete vertex
    sets, each inducing chromatic number at least 2. Definitions are those of the root,
    `Erdos1111AnticompleteChromatic`. For `t ≤ 2` the hypotheses cannot be met. -/
abbrev statement : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ChromaticAtLeast G (t.choose 2 + 1) →
      G.CliqueFree t →
      ∃ A B : Finset (Fin n),
        Anticomplete G A B ∧
        ChromaticAtLeastOn G A 2 ∧
        ChromaticAtLeastOn G B 2

theorem target : statement := sorry

end Statements.Erdos1111WagonC2AllT

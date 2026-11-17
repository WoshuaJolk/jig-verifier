import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111DiagonalSuffices

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

/-- The El-Zahar--Erdős reduction to the diagonal. For each `c ≥ 2`, if some threshold works
    for `K_c`-free graphs (the case `t = c`), then some threshold works for `K_t`-free graphs
    for every `t`. Since a `K_t`-free graph with `t ≤ c` is `K_c`-free, the root
    `Erdos1111AnticompleteChromatic` is therefore equivalent to its diagonal cases `t = c`.
    Definitions are those of the root. -/
abbrev statement : Prop :=
  ∀ c : ℕ, 2 ≤ c →
    (∃ d : ℕ, 1 ≤ d ∧
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
        ChromaticAtLeast G d →
        G.CliqueFree c →
        ∃ A B : Finset (Fin n),
          Anticomplete G A B ∧
          ChromaticAtLeastOn G A c ∧
          ChromaticAtLeastOn G B c) →
    ∀ t : ℕ, 1 ≤ t →
      ∃ d : ℕ, 1 ≤ d ∧
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          ChromaticAtLeast G d →
          G.CliqueFree t →
          ∃ A B : Finset (Fin n),
            Anticomplete G A B ∧
            ChromaticAtLeastOn G A c ∧
            ChromaticAtLeastOn G B c

theorem target : statement := sorry

end Statements.Erdos1111DiagonalSuffices

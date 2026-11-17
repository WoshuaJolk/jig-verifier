import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Statements.Erdos1111OddCycleVsHighChromatic

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

/-- The asymmetric theorem of El-Zahar and Erdős (1985): for all `t, c` there is `d` such
    that every finite `K_t`-free graph of chromatic number at least `d` has two anticomplete
    vertex sets `A, B`, with `A` not 2-colourable and `B` of chromatic number at least `c`.
    This is the root with the demand on `A` lowered from `c` to `3`. -/
abbrev statement : Prop :=
  ∀ t c : ℕ, 1 ≤ t → 1 ≤ c →
    ∃ d : ℕ, 1 ≤ d ∧
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
        ChromaticAtLeast G d →
        G.CliqueFree t →
        ∃ A B : Finset (Fin n),
          Anticomplete G A B ∧
          ChromaticAtLeastOn G A 3 ∧
          ChromaticAtLeastOn G B c

theorem target : statement := sorry

end Statements.Erdos1111OddCycleVsHighChromatic

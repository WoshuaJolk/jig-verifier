import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Statements.Erdos738InducedTreesInfiniteChromatic

universe u

def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a → False

def InfiniteChromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ∀ color : V → Fin k,
    ∃ u v : V, G.Adj u v ∧ color u = color v

def IsInducedCopy {V : Type*} {n : ℕ}
    (T : SimpleGraph (Fin n)) (G : SimpleGraph V) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧
    ∀ a b : Fin n, T.Adj a b ↔ G.Adj (f a) (f b)

/-- Erdős problem 738: every finite tree occurs induced in every triangle-free
graph of infinite chromatic number. -/
abbrev statement : Prop :=
  ∀ (V : Type u) [Infinite V], ∀ G : SimpleGraph V,
    TriangleFree G → InfiniteChromatic G →
      ∀ n : ℕ, ∀ T : SimpleGraph (Fin n),
        T.IsTree → IsInducedCopy T G

theorem target : statement := sorry

end Statements.Erdos738InducedTreesInfiniteChromatic

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

namespace Statements.Erdos714EmptyGraphKrrFree

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

def ContainsKrr {n : ℕ} (E : Finset (Fin n × Fin n)) (r : ℕ) : Prop :=
  ∃ A B : Finset (Fin n),
    A.card = r ∧ B.card = r ∧ Disjoint A B ∧
      ∀ a ∈ A, ∀ b ∈ B, edge a b ∈ E

/-- The empty graph contains no positive-order balanced complete bipartite
subgraph. -/
abbrev statement : Prop :=
  ∀ n r : ℕ, 0 < r →
    ¬ ContainsKrr (n := n) ∅ r

theorem target : statement := sorry

end Statements.Erdos714EmptyGraphKrrFree

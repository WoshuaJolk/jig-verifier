import Mathlib.Data.Fin.Basic

namespace Statements.Erdos642CanonicalEdgeSymmetric

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

/-- The canonical representation of an undirected edge is independent of
endpoint order. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ u v : Fin n, edge u v = edge v u

theorem target : statement := sorry

end Statements.Erdos642CanonicalEdgeSymmetric

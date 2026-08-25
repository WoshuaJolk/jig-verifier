import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Submissions.Erdos642CanonicalEdgeSymmetric.Direct

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

theorem proof :
    ∀ n : ℕ, ∀ u v : Fin n, edge u v = edge v u := by
  intro n u v
  unfold edge
  by_cases huv : u < v
  · simp [huv, not_lt.mpr huv.le]
  · have hvu : v < u ∨ v = u := lt_or_eq_of_le (not_lt.mp huv)
    rcases hvu with hvu | rfl
    · simp [huv, hvu]
    · simp

end Submissions.Erdos642CanonicalEdgeSymmetric.Direct

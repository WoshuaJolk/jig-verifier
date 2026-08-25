import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Submissions.Erdos544ZeroCliqueBoundary.Worker04Smoke

def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

theorem proof : ∀ n l : ℕ, IsGraphRamsey n 0 l := by
  intro n l G h
  exact SimpleGraph.not_cliqueFree_zero h.1

end Submissions.Erdos544ZeroCliqueBoundary.Worker04Smoke

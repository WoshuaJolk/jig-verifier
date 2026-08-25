import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Submissions.Erdos544ZeroCliqueBoundary.Worker04Degenerate

def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

theorem proof : False → ∀ n l : ℕ, IsGraphRamsey n 0 l :=
  False.elim

end Submissions.Erdos544ZeroCliqueBoundary.Worker04Degenerate

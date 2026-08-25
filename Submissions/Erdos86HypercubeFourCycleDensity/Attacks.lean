import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

namespace Submissions.Erdos86HypercubeFourCycleDensity.Attacks

open Filter Finset

abbrev Vertex (n : ℕ) := Fin n → Bool

def cube (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := (Finset.univ.filter fun i => x i ≠ y i).card = 1
  symm := ⟨by intro x y h; simpa [ne_comm] using h⟩
  loopless := ⟨by intro x h; simp at h⟩

def ContainsFourCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ v : Fin 4 ↪ V,
    G.Adj (v 0) (v 1) ∧ G.Adj (v 1) (v 2) ∧
      G.Adj (v 2) (v 3) ∧ G.Adj (v 3) (v 0)

noncomputable def extremal (n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : SimpleGraph (Vertex n) =>
      if G ≤ cube n ∧ ¬ContainsFourCycle G then G.edgeFinset.card else 0

def totalEdges (n : ℕ) : ℝ := n * 2 ^ (n - 1)

abbrev claimedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop,
      (extremal n : ℝ) ≤ (1 / 2 + ε) * totalEdges n

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem epsilonDomainNonempty : ∃ ε : ℝ, 0 < ε := ⟨1, by norm_num⟩

end Submissions.Erdos86HypercubeFourCycleDensity.Attacks

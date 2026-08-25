import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos82SingletonLowerBound.Singleton

variable {V : Type*} [Fintype V]

def isRegularInduced {G : SimpleGraph V} (S : Subgraph G) : Prop :=
  open scoped Classical in
  S.IsInduced ∧ ∃ k, S.coe.IsRegularOfDegree k

noncomputable def F (n : ℕ) : ℕ :=
  sSup {k | ∀ (G : SimpleGraph (Fin n)), ∃ S : Subgraph G,
    isRegularInduced S ∧ k ≤ S.verts.ncard}

theorem proof : ∀ n : ℕ, 0 < n → 1 ≤ F n := by
  classical
  intro n hn
  apply le_csSup
  · refine ⟨n, ?_⟩
    intro k hk
    obtain ⟨S, hS, hkS⟩ := hk (⊥ : SimpleGraph (Fin n))
    exact hkS.trans (by simpa using S.verts.ncard_le_card)
  · intro G
    let v : Fin n := ⟨0, hn⟩
    refine ⟨G.singletonSubgraph v, ?_, ?_⟩
    · constructor
      · rw [Subgraph.singletonSubgraph_eq_induce]
        exact (Subgraph.isInduced_iff_exists_eq_induce_top _).2 ⟨{v}, rfl⟩
      · refine ⟨0, ?_⟩
        intro w
        exact SimpleGraph.degree_eq_zero_of_subsingleton w
    · simp

end Submissions.Erdos82SingletonLowerBound.Singleton

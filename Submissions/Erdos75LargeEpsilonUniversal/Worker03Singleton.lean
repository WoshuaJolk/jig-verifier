import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

namespace Submissions.Erdos75LargeEpsilonUniversal.Worker03Singleton

theorem proof :
    ∀ (V : Type) (G : SimpleGraph V) (ε : ℝ), 1 < ε →
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (H : G.Subgraph),
        H.verts.ncard = n →
        ∃ I : Finset V,
          (I : Set V) ⊆ H.verts ∧
          G.IsIndepSet (I : Set V) ∧
          (I.card : ℝ) > (n : ℝ) ^ (1 - ε) := by
  intro V G ε hε
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  intro H hcard
  have hn0 : n ≠ 0 := by omega
  have hverts : H.verts.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by simpa [hcard] using hn0)
  rcases hverts with ⟨v, hv⟩
  refine ⟨{v}, by simpa, by simp, ?_⟩
  simp only [Finset.card_singleton, Nat.cast_one]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hn)
    (by linarith)

end Submissions.Erdos75LargeEpsilonUniversal.Worker03Singleton

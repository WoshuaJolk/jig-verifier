import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-
Known edge-deletion lemma of Markstrom and Carr
(arXiv:2605.22844v1, Corollary 0.1(2)).
Adapted from Andrew Bisch's EGC.IsMinCex.not_adj_of_four_le_degree:
https://github.com/AJBisch/AJBisch.github.io/blob/main/EGC.lean
This adaptation uses Jig's Fin-n minimality and edgeFinset cardinalities.
It proves a conditional restriction, not existence of a counterexample.
-/
namespace Submissions.ErdosGyarfasMinCexHighDegIndep.ColeskiEdgeDeletion
open Finset SimpleGraph

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

/-- A counterexample to the Erdős–Gyárfás conjecture: a nonempty finite simple graph with every
degree at least `3` and no power-of-two cycle. -/
def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

/-- A minimal counterexample: a counterexample that is lexicographically minimal in
(order, size) among all counterexamples on any `Fin m`. If the conjecture is true no such graph
exists, and every statement about `IsMinCex` is a statement about the structure a counterexample
would have to have. -/
def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)


theorem proof (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsMinCex G) (u w : Fin n)
    (hu : 4 ≤ G.degree u) (hw : 4 ≤ G.degree w) : ¬ G.Adj u w := by
  intro hadj
  have huw : u ≠ w := hadj.ne
  set H : SimpleGraph (Fin n) := G.deleteEdges {s(u, w)} with hH
  haveI : DecidableRel H.Adj := fun a b =>
    decidable_of_iff (G.Adj a b ∧ ¬ s(a, b) = s(u, w)) (by
      rw [hH, deleteEdges_adj, Set.mem_singleton_iff])
  -- neighbor sets of the edge-deleted graph
  have hnbu : H.neighborFinset u = (G.neighborFinset u).erase w := by
    ext y
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨hGy, hne⟩
      refine ⟨fun hyw => hne (Or.inl ⟨rfl, hyw⟩), hGy⟩
    · rintro ⟨hyw, hGy⟩
      refine ⟨hGy, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hyw h
      · exact huw h
  have hnbw : H.neighborFinset w = (G.neighborFinset w).erase u := by
    ext y
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨hGy, hne⟩
      refine ⟨fun hyu => hne (Or.inr ⟨rfl, hyu⟩), hGy⟩
    · rintro ⟨hyu, hGy⟩
      refine ⟨hGy, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact huw h.symm
      · exact hyu h
  have hnbo : ∀ x, x ≠ u → x ≠ w → H.neighborFinset x = G.neighborFinset x := by
    intro x hxu hxw
    ext y
    rw [mem_neighborFinset, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hxu h1
      · exact hxw h1
  -- the deleted graph still has minimum degree ≥ 3
  have hdeg : ∀ v, 3 ≤ H.degree v := by
    intro x
    rcases eq_or_ne x u with rfl | hxu
    · rw [← card_neighborFinset_eq_degree, hnbu,
        Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj),
        card_neighborFinset_eq_degree]
      omega
    rcases eq_or_ne x w with rfl | hxw
    · rw [← card_neighborFinset_eq_degree, hnbw,
        Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj.symm),
        card_neighborFinset_eq_degree]
      omega
    · rw [← card_neighborFinset_eq_degree, hnbo x hxu hxw,
        card_neighborFinset_eq_degree]
      exact hG.1.2.1 x
  -- it is a proper subgraph
  have hne : H ≠ G := by
    intro h
    have : H.Adj u w := h ▸ hadj
    rw [hH, deleteEdges_adj] at this
    exact this.2 (Set.mem_singleton _)
  -- Every cycle in the deleted graph is still a cycle of the original.
  have hno : ¬ HasPow2Cycle H := by
    rintro ⟨v, c, k, hc, hk, hlen⟩
    let f : H →g G := .ofLE (deleteEdges_le _)
    have hf : Function.Injective f := fun _ _ h => h
    exact hG.1.2.2 ⟨f v, c.map f, k,
      (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc, hk,
      by simpa only [SimpleGraph.Walk.length_map] using hlen⟩
  have hcex : IsCex H := ⟨hG.1.1, hdeg, hno⟩
  rcases hG.2 n H hcex with hlt | ⟨_, hcard⟩
  · exact Nat.lt_irrefl n hlt
  · have hsub : H.edgeFinset ⊆ G.edgeFinset := by
      intro e he
      have he' : e ∈ H.edgeSet := by simpa using he
      have : e ∈ G.edgeSet := SimpleGraph.edgeSet_mono (deleteEdges_le _) he'
      simpa using this
    have heq : H.edgeFinset = G.edgeFinset := Finset.eq_of_subset_of_card_le hsub hcard
    apply hne
    apply SimpleGraph.edgeSet_injective
    ext e
    simpa using (show e ∈ H.edgeFinset ↔ e ∈ G.edgeFinset by rw [heq])

end Submissions.ErdosGyarfasMinCexHighDegIndep.ColeskiEdgeDeletion

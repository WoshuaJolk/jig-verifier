import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

open SimpleGraph

namespace Submissions.Erdos184SingletonEdgeDecomposition.Worker04

def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

noncomputable def edgeSubgraph {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    G.Subgraph where
  verts := Set.univ
  Adj v w := s(v, w) = e.1
  adj_sub h := by
    rw [← G.mem_edgeSet, h]
    exact e.2
  edge_vert := by simp

theorem edgeSet_edgeSubgraph {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    (edgeSubgraph G e).edgeSet = {e.1} := by
  ext x
  induction x using Sym2.inductionOn with
  | _ v w =>
      simp [Subgraph.mem_edgeSet, edgeSubgraph]

open scoped Classical in
noncomputable def singletonEdgeDecomposition {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Finset G.Subgraph :=
  G.edgeFinset.attach.image fun e =>
    edgeSubgraph G ⟨e.1, SimpleGraph.mem_edgeFinset.mp e.2⟩

open scoped Classical in
theorem proof :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        D.card ≤ G.edgeFinset.card := by
  intro V _ G
  refine ⟨singletonEdgeDecomposition G, ?_, ?_, ?_⟩
  · intro H hH
    simp only [singletonEdgeDecomposition, Finset.mem_image] at hH
    obtain ⟨e, -, rfl⟩ := hH
    right
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    rw [← Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    rw [Subgraph.image_coe_edgeSet_coe, edgeSet_edgeSubgraph]
    simp
  · constructor
    · rintro H hH K hK hne
      simp only [singletonEdgeDecomposition, Finset.mem_coe, Finset.mem_image] at hH hK
      obtain ⟨e, -, rfl⟩ := hH
      obtain ⟨e', -, rfl⟩ := hK
      change Disjoint (edgeSubgraph G ⟨e.1, _⟩).edgeSet (edgeSubgraph G ⟨e'.1, _⟩).edgeSet
      rw [edgeSet_edgeSubgraph, edgeSet_edgeSubgraph]
      simp only [Set.disjoint_singleton]
      intro he
      apply hne
      congr
    · ext e
      simp [singletonEdgeDecomposition, edgeSet_edgeSubgraph]
  · unfold singletonEdgeDecomposition
    exact (Finset.card_image_le).trans_eq Finset.card_attach

end Submissions.Erdos184SingletonEdgeDecomposition.Worker04

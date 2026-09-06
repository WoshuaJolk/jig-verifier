import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
Jig problem 399, statement 5: the known degree-three-neighbour property
of a hypothetical minimum-order counterexample to the Erdős–Gyárfás conjecture.
The proof deletes a vertex and uses only minimum order, not edge minimality.
It neither constructs a counterexample nor settles the parent conjecture.
The result is in Carr, arXiv:2605.22844, and Andrew Bisch's existing Lean
formalization EGC.IsMinCex.exists_cubic_neighbor. This file adapts the known
argument to Jig's Fin-indexed canonical proposition.
-/

namespace Submissions.ErdosGyarfasMinCexCubicNeighbour.VertexDeletion

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

theorem cycle_of_injective_hom {n m : ℕ} {G : SimpleGraph (Fin n)}
    {H : SimpleGraph (Fin m)} (f : H →g G) (hf : Function.Injective f) :
    HasPow2Cycle H → HasPow2Cycle G := by
  rintro ⟨v, c, k, hc, hk, hlen⟩
  exact ⟨f v, c.map f, k, hc.map hf, hk, by simpa using hlen⟩

theorem survivors_card_lt {n : ℕ} (u : Fin n) :
    Fintype.card {v : Fin n // v ≠ u} < n := by
  simpa using (Fintype.card_subtype_lt (p := fun v : Fin n => v ≠ u)
    (x := u) (by simp))

theorem survivors_card_pos {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (hdeg : 3 ≤ G.degree u) :
    0 < Fintype.card {v : Fin n // v ≠ u} := by
  obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u).mp (by omega : 0 < G.degree u)
  exact Fintype.card_pos_iff.mpr ⟨⟨v, hv.ne.symm⟩⟩

section Deletion

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)

theorem degree_delete_eq_erase (v : {x : V // x ≠ u}) :
    (G.induce {x : V | x ≠ u}).degree v = (G.neighborFinset v.val |>.erase u).card := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce (s := {x : V | x ≠ u}) v)
  simp only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] at h
  rw [h]
  congr 1
  ext x
  simp [and_comm]

theorem degree_delete_ge_three
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (hneigh : ∀ v : V, G.Adj u v → 4 ≤ G.degree v)
    (v : {x : V // x ≠ u}) :
    3 ≤ (G.induce {x : V | x ≠ u}).degree v := by
  rw [degree_delete_eq_erase]
  by_cases h : G.Adj u v.val
  · have hu : u ∈ G.neighborFinset v.val := by simpa using h.symm
    rw [Finset.card_erase_of_mem hu, SimpleGraph.card_neighborFinset_eq_degree]
    have := hneigh v.val h
    omega
  · have hu : u ∉ G.neighborFinset v.val := by simpa [SimpleGraph.adj_comm] using h
    rw [Finset.erase_eq_of_notMem hu, SimpleGraph.card_neighborFinset_eq_degree]
    exact hdeg v.val

end Deletion

theorem proof :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    ∀ u : Fin n, ∃ w : Fin n, G.Adj u w ∧ G.degree w = 3 := by
  classical
  intro n G inst hG u
  by_contra hnone
  have high : ∀ v : Fin n, G.Adj u v → 4 ≤ G.degree v := by
    intro v huv
    have hlow := hG.1.2.1 v
    have hne : G.degree v ≠ 3 := fun heq => hnone ⟨v, huv, heq⟩
    omega
  let V := {v : Fin n // v ≠ u}
  let D := G.induce {v : Fin n | v ≠ u}
  let e := (Fintype.equivFin V).symm
  let H : SimpleGraph (Fin (Fintype.card V)) := D.comap e
  let iso : H ≃g D := SimpleGraph.Iso.comap e D
  let inclusion : D →g G := SimpleGraph.Hom.comap Subtype.val G
  let f : H →g G := inclusion.comp iso.toHom
  have hf : Function.Injective f := Subtype.val_injective.comp iso.injective
  have hH : IsCex H := by
    refine ⟨survivors_card_pos G u (hG.1.2.1 u), ?_, ?_⟩
    · intro v
      rw [← iso.degree_eq v]
      exact degree_delete_ge_three G u hG.1.2.1 high (iso v)
    · intro hc
      exact hG.1.2.2 (cycle_of_injective_hom f hf hc)
  have hlt : Fintype.card V < n := survivors_card_lt u
  rcases hG.2 _ H hH with h | ⟨h, _⟩ <;> omega

end Submissions.ErdosGyarfasMinCexCubicNeighbour.VertexDeletion

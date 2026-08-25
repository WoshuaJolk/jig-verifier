import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23LowDegreeRemoval.Direct

open scoped Classical in
lemma add_one_edge_at_isolated
    {V : Type} [Fintype V] (G H : SimpleGraph V) (v w : V)
    (hle : H ≤ G.deleteIncidenceSet v) (hbip : H.IsBipartite)
    (hvw : G.Adj v w) :
    ∃ H' : SimpleGraph V,
      H' ≤ G ∧ H'.IsBipartite ∧ H.edgeFinset.card < H'.edgeFinset.card := by
  classical
  have hvwne : v ≠ w := G.ne_of_adj hvw
  let H' : SimpleGraph V :=
    SimpleGraph.fromRel fun x y => H.Adj x y ∨ (x = v ∧ y = w)
  have hH'le : H' ≤ G := by
    intro x y hxy
    simp only [H', SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with (hxy | hxy) | (hxy | hxy)
    · exact (G.deleteIncidenceSet_le v) (hle hxy)
    · simpa [hxy.1, hxy.2] using hvw
    · exact (G.deleteIncidenceSet_le v) (hle hxy.symm)
    · simpa [hxy.1, hxy.2] using hvw.symm
  have hH'bip : H'.IsBipartite := by
    obtain ⟨c, hc⟩ := hbip
    let c' : V → Fin 2 := fun x =>
      if x = v then (if c w = 0 then 1 else 0) else c x
    refine ⟨c', ?_⟩
    intro x y hxy
    simp only [H', SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with (hxy | hxy) | (hxy | hxy)
    · have hxv : x ≠ v := by
        intro hx
        subst x
        have := hle hxy
        simpa [deleteIncidenceSet_adj] using this
      have hyv : y ≠ v := by
        intro hy
        subst y
        have := hle hxy
        simpa [deleteIncidenceSet_adj] using this
      simpa [c', hxv, hyv] using hc hxy
    · rcases hxy with ⟨hx, hy⟩
      by_cases hcw : c w = 0
      · simp [c', hx, hy, hvwne, hvwne.symm, hcw]
      · have hone : c w = 1 := by
          apply Fin.ext
          omega
        simp [c', hx, hy, hvwne, hvwne.symm, hcw, hone]
    · have hxv : x ≠ v := by
        intro hx
        subst x
        have := hle hxy.symm
        simpa [deleteIncidenceSet_adj] using this
      have hyv : y ≠ v := by
        intro hy
        subst y
        have := hle hxy.symm
        simpa [deleteIncidenceSet_adj] using this
      simpa [c', hxv, hyv] using hc hxy.symm
    · rcases hxy with ⟨hy, hx⟩
      by_cases hcw : c w = 0
      · simp [c', hx, hy, hvwne, hvwne.symm, hcw]
      · have hone : c w = 1 := by
          apply Fin.ext
          omega
        simp [c', hx, hy, hvwne, hvwne.symm, hcw, hone]
  have hHleH' : H ≤ H' := by
    intro x y hxy
    simp only [H', SimpleGraph.fromRel_adj]
    exact ⟨H.ne_of_adj hxy, Or.inl (Or.inl hxy)⟩
  have hnot : ¬ H.Adj v w := by
    intro h
    have := hle h
    simpa [deleteIncidenceSet_adj, hvwne] using this
  have hstrict : H.edgeFinset ⊂ H'.edgeFinset := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨edgeFinset_mono hHleH', ?_⟩
    intro heq
    have hmem' : s(v, w) ∈ H'.edgeFinset := by
      rw [mem_edgeFinset, mem_edgeSet]
      simp [H', SimpleGraph.fromRel_adj, hvwne]
    have hmem : s(v, w) ∈ H.edgeFinset := by
      rw [heq]
      exact hmem'
    exact hnot (by simpa [mem_edgeFinset, mem_edgeSet] using hmem)
  have hcard := Finset.card_lt_card hstrict
  refine ⟨H', hH'le, hH'bip, ?_⟩
  convert hcard using 1
  congr 1
  ext e
  simp only [mem_edgeFinset]

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ),
      G.degree v ≤ 2 →
      (∃ H : SimpleGraph V,
        H ≤ G.deleteIncidenceSet v ∧ H.IsBipartite ∧
          ((G.deleteIncidenceSet v).edgeFinset \ H.edgeFinset).card ≤ k) →
      ∃ H' : SimpleGraph V,
        H' ≤ G ∧ H'.IsBipartite ∧
          (G.edgeFinset \ H'.edgeFinset).card ≤ k + G.degree v / 2 := by
  intro V _ G v k hdeg
  rintro ⟨H, hle, hbip, hcost⟩
  classical
  let D := G.deleteIncidenceSet v
  have hDleG : D ≤ G := G.deleteIncidenceSet_le v
  have hHleD : H ≤ D := hle
  have hHleG : H ≤ G := hHleD.trans hDleG
  have hcost' : D.edgeFinset.card - H.edgeFinset.card ≤ k := by
    rw [← Finset.card_sdiff_of_subset (edgeFinset_mono hHleD)]
    exact hcost
  have hDcard : D.edgeFinset.card = G.edgeFinset.card - G.degree v := by
    simpa [D] using G.card_edgeFinset_deleteIncidenceSet v
  by_cases hz : G.degree v = 0
  · refine ⟨H, hHleG, hbip, ?_⟩
    rw [Finset.card_sdiff_of_subset (edgeFinset_mono hHleG)]
    simp [hz]
    omega
  · have hpos : 0 < G.degree v := Nat.pos_of_ne_zero hz
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hpos
    obtain ⟨H', hH'le, hH'bip, hcard⟩ :=
      add_one_edge_at_isolated G H v w hle hbip hvw
    refine ⟨H', hH'le, hH'bip, ?_⟩
    rw [Finset.card_sdiff_of_subset (edgeFinset_mono hH'le)]
    have hcases : G.degree v = 1 ∨ G.degree v = 2 := by omega
    rcases hcases with hdeg1 | hdeg2
    · simp [hdeg1]
      omega
    · simp [hdeg2]
      omega

end Submissions.Erdos23LowDegreeRemoval.Direct

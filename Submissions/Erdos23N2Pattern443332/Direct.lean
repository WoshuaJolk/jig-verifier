import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23N2Pattern443332.Direct

open scoped Classical in
lemma degree_two_vertices_neighbor_of_four
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hall : ∀ x : V, G.degree x = 2 ∨ G.degree x = 3 ∨ G.degree x = 4)
    (hC : ((Finset.univ : Finset V).filter fun x => G.degree x = 2).card = 2)
    {a : V} (ha : G.degree a = 4)
    (hweight : (∑ x ∈ G.neighborFinset a, G.degree x) ≤ 10) :
    ((Finset.univ : Finset V).filter fun x => G.degree x = 2) ⊆
      G.neighborFinset a := by
  classical
  let C := (Finset.univ : Finset V).filter fun x => G.degree x = 2
  let N := G.neighborFinset a
  let D := N.filter fun x => G.degree x = 2
  intro c hc
  by_contra hcN
  have hcC : c ∈ C := hc
  have hcD : c ∉ D := by simp [D, N, hcN]
  have hDsubC : D ⊆ C := by
    intro x hx
    have hx2 : G.degree x = 2 := (Finset.mem_filter.mp hx).2
    simp [C, hx2]
  have hDproper : D ⊂ C := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hDsubC, ?_⟩
    intro heq
    have : c ∈ D := by rw [heq]; exact hcC
    exact hcD this
  have hDcard : D.card ≤ 1 := by
    have := Finset.card_lt_card hDproper
    simpa [C, hC] using this
  have hNcard : N.card = 4 := by
    simpa [N, card_neighborFinset_eq_degree, ha]
  have hDsubN : D ⊆ N := Finset.filter_subset _ _
  let E := N \ D
  have hEcard : E.card = 4 - D.card := by
    dsimp [E]
    rw [Finset.card_sdiff_of_subset hDsubN, hNcard]
  have hsumD : (∑ x ∈ D, G.degree x) = 2 * D.card := by
    calc
      (∑ x ∈ D, G.degree x) = ∑ _x ∈ D, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ = 2 * D.card := by simp [mul_comm]
  have hsumE : 3 * E.card ≤ ∑ x ∈ E, G.degree x := by
    calc
      3 * E.card = ∑ _x ∈ E, 3 := by simp [mul_comm]
      _ ≤ ∑ x ∈ E, G.degree x := by
        apply Finset.sum_le_sum
        intro x hx
        have hxnot2 : G.degree x ≠ 2 := by
          intro hx2
          have hxN : x ∈ N := (Finset.mem_sdiff.mp hx).1
          have : x ∈ D := Finset.mem_filter.mpr ⟨hxN, hx2⟩
          exact (Finset.mem_sdiff.mp hx).2 this
        rcases hall x with hx2 | hx3 | hx4
        · exact (hxnot2 hx2).elim
        · omega
        · omega
  have hpartition :
      (∑ x ∈ N, G.degree x) =
        (∑ x ∈ D, G.degree x) + ∑ x ∈ E, G.degree x := by
    dsimp [E]
    rw [← Finset.sum_sdiff hDsubN]
    omega
  have : 11 ≤ ∑ x ∈ N, G.degree x := by
    rw [hpartition, hsumD]
    omega
  have hw : (∑ x ∈ N, G.degree x) ≤ 10 := by simpa [N] using hweight
  omega

open scoped Classical in
lemma pattern_has_heavy_independent_set
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 10)
    (htri : G.CliqueFree 3)
    (hall : ∀ x : V, G.degree x = 2 ∨ G.degree x = 3 ∨ G.degree x = 4)
    (hA : ((Finset.univ : Finset V).filter fun x => G.degree x = 4).card = 2)
    (hB : ((Finset.univ : Finset V).filter fun x => G.degree x = 3).card = 6)
    (hC : ((Finset.univ : Finset V).filter fun x => G.degree x = 2).card = 2)
    (hweight : ∀ v : V, (∑ x ∈ G.neighborFinset v, G.degree x) ≤ 10) :
    ∃ S : Finset V,
      G.IsIndepSet (S : Set V) ∧ 11 ≤ ∑ x ∈ S, G.degree x := by
  classical
  let A := (Finset.univ : Finset V).filter fun x => G.degree x = 4
  let B := (Finset.univ : Finset V).filter fun x => G.degree x = 3
  let C := (Finset.univ : Finset V).filter fun x => G.degree x = 2
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.mp (by simpa [A] using hA)
  have haA : a ∈ A := by
    change a ∈ (Finset.univ : Finset V).filter fun x => G.degree x = 4
    rw [hAeq]
    simp
  have hbA : b ∈ A := by
    change b ∈ (Finset.univ : Finset V).filter fun x => G.degree x = 4
    rw [hAeq]
    simp
  have ha4 : G.degree a = 4 := (Finset.mem_filter.mp haA).2
  have hb4 : G.degree b = 4 := (Finset.mem_filter.mp hbA).2
  have hCa : C ⊆ G.neighborFinset a := by
    simpa [C] using
      degree_two_vertices_neighbor_of_four G hall hC ha4 (hweight a)
  have hCb : C ⊆ G.neighborFinset b := by
    simpa [C] using
      degree_two_vertices_neighbor_of_four G hall hC hb4 (hweight b)
  have hCne : C.Nonempty := Finset.card_pos.mp (by simpa [C, hC])
  obtain ⟨p, hpC⟩ := hCne
  have hap : G.Adj a p := by
    simpa [mem_neighborFinset] using hCa hpC
  have hbp : G.Adj b p := by
    simpa [mem_neighborFinset] using hCb hpC
  have hnotab : ¬G.Adj a b := by
    intro hadj
    have hind := SimpleGraph.isIndepSet_neighborSet_of_triangleFree G htri p
    exact hind (by simpa [mem_neighborSet] using hap.symm)
      (by simpa [mem_neighborSet] using hbp.symm) hab hadj
  let Na := G.neighborFinset a
  let Nb := G.neighborFinset b
  let Fa := B ∩ Na
  let Fb := B ∩ Nb
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    have hx3 : G.degree x = 3 := (Finset.mem_filter.mp hxB).2
    have hx2 : G.degree x = 2 := (Finset.mem_filter.mp hxC).2
    omega
  have hFaC : Disjoint Fa C := (Finset.disjoint_of_subset_left
    (Finset.inter_subset_left) hBC)
  have hFbC : Disjoint Fb C := (Finset.disjoint_of_subset_left
    (Finset.inter_subset_left) hBC)
  have hFaCsub : Fa ∪ C ⊆ Na := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact hCa hx
  have hFbCsub : Fb ∪ C ⊆ Nb := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact hCb hx
  have hNacard : Na.card = 4 := by
    simpa [Na, card_neighborFinset_eq_degree, ha4]
  have hNbcard : Nb.card = 4 := by
    simpa [Nb, card_neighborFinset_eq_degree, hb4]
  have hFacard : Fa.card ≤ 2 := by
    have hu := Finset.card_le_card hFaCsub
    rw [Finset.card_union_of_disjoint hFaC, hNacard] at hu
    simpa [C, hC] using hu
  have hFbcard : Fb.card ≤ 2 := by
    have hu := Finset.card_le_card hFbCsub
    rw [Finset.card_union_of_disjoint hFbC, hNbcard] at hu
    simpa [C, hC] using hu
  let F := Fa ∪ Fb
  have hFcard : F.card ≤ 4 := by
    have := Finset.card_union_le Fa Fb
    dsimp [F]
    omega
  have hnsub : ¬B ⊆ F := by
    intro hsub
    have := Finset.card_le_card hsub
    have hBcard : B.card = 6 := by simpa [B] using hB
    omega
  obtain ⟨c, hcB, hcF⟩ := Finset.not_subset.mp hnsub
  have hc3 : G.degree c = 3 := (Finset.mem_filter.mp hcB).2
  have hcFa : c ∉ Fa := by
    intro hc
    exact hcF (Finset.mem_union_left _ hc)
  have hcFb : c ∉ Fb := by
    intro hc
    exact hcF (Finset.mem_union_right _ hc)
  have hnotac : ¬G.Adj a c := by
    intro hac
    apply hcFa
    exact Finset.mem_inter.mpr ⟨hcB, by simpa [Na, mem_neighborFinset] using hac⟩
  have hnotbc : ¬G.Adj b c := by
    intro hbc
    apply hcFb
    exact Finset.mem_inter.mpr ⟨hcB, by simpa [Nb, mem_neighborFinset] using hbc⟩
  have hca : c ≠ a := by
    intro h
    subst c
    omega
  have hcb : c ≠ b := by
    intro h
    subst c
    omega
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  refine ⟨{a, b, c}, ?_, ?_⟩
  · rw [IsIndepSet]
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals simp_all [adj_comm]
  · simp [hab, hac, hbc, ha4, hb4, hc3]

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        G.edgeFinset.card = 15 →
        (∀ x : V, G.degree x = 2 ∨ G.degree x = 3 ∨ G.degree x = 4) →
        ((Finset.univ : Finset V).filter fun x => G.degree x = 4).card = 2 →
        ((Finset.univ : Finset V).filter fun x => G.degree x = 3).card = 6 →
        ((Finset.univ : Finset V).filter fun x => G.degree x = 2).card = 2 →
          ∃ (H : SimpleGraph V),
            H ≤ G ∧ H.IsBipartite ∧
              (G.edgeFinset \ H.edgeFinset).card ≤ 4 := by
  intro V _ hcard G htri hedges hall hA hB hC
  classical
  have hS :
      ∃ S : Finset V,
        G.IsIndepSet (S : Set V) ∧ 11 ≤ ∑ x ∈ S, G.degree x := by
    by_cases hweight :
        ∀ v : V, (∑ x ∈ G.neighborFinset v, G.degree x) ≤ 10
    · exact pattern_has_heavy_independent_set G hcard htri hall hA hB hC hweight
    · push_neg at hweight
      obtain ⟨v, hv⟩ := hweight
      refine ⟨G.neighborFinset v, ?_, by omega⟩
      simpa [coe_neighborFinset] using
        SimpleGraph.isIndepSet_neighborSet_of_triangleFree G htri v
  obtain ⟨S, hind, hsum⟩ := hS
  let H : SimpleGraph V := G.between (↑S : Set V) ↑(Sᶜ)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hle : H ≤ G := G.between_le
  have hd : Disjoint (↑S : Set V) ↑(Sᶜ) := by
    rw [Finset.coe_compl]
    exact disjoint_compl_right
  have hbwith : H.IsBipartiteWith (↑S : Set V) ↑(Sᶜ) := by
    simpa [H] using
      (G.between_isBipartiteWith
        (s := (↑S : Set V)) (t := (↑(Sᶜ) : Set V)) hd)
  have hbip : H.IsBipartite := hbwith.isBipartite
  have hdeg : ∀ x ∈ S, H.degree x = G.degree x := by
    intro x hx
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    congr 1
    ext y
    have hyout : G.Adj x y → y ∉ S := by
      intro hxy hy
      exact hind hx hy (G.ne_of_adj hxy) hxy
    simp [H, SimpleGraph.between_adj, hx]
    exact hyout
  have hedge : H.edgeFinset.card = ∑ x ∈ S, G.degree x := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hbwith]
    exact Finset.sum_congr rfl fun x hx ↦ hdeg x hx
  refine ⟨H, hle, hbip, ?_⟩
  rw [Finset.card_sdiff_of_subset (edgeFinset_mono hle), hedge, hedges]
  omega

end Submissions.Erdos23N2Pattern443332.Direct

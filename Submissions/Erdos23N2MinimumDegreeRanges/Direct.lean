import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23N2MinimumDegreeRanges.Direct

open scoped Classical in
lemma indep_three_of_six
    {V : Type} [Fintype V] (G : SimpleGraph V) (htri : G.CliqueFree 3)
    (U : Finset V) (hU : 6 ≤ U.card) :
    ∃ S : Finset V, S ⊆ U ∧ S.card = 3 ∧
      G.IsIndepSet (S : Set V) := by
  classical
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hvU⟩ := hUne
  let N := (U.erase v).filter fun x => G.Adj v x
  let R := (U.erase v).filter fun x => ¬G.Adj v x
  have hpartition : N.card + R.card = (U.erase v).card := by
    simpa [N, R] using
      Finset.card_filter_add_card_filter_not (s := U.erase v) (fun x => G.Adj v x)
  have herase : (U.erase v).card = U.card - 1 :=
    Finset.card_erase_of_mem hvU
  by_cases hN : 3 ≤ N.card
  · obtain ⟨S, hSN, hScard⟩ := Finset.exists_subset_card_eq hN
    refine ⟨S, ?_, hScard, ?_⟩
    · intro x hx
      have hxN := hSN hx
      exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hxN).1
    · have hneigh :=
        G.isIndepSet_neighborSet_of_triangleFree htri v
      intro x hx y hy hxy hadj
      have hxN := hSN hx
      have hyN := hSN hy
      have hxadj : G.Adj v x := (Finset.mem_filter.mp hxN).2
      have hyadj : G.Adj v y := (Finset.mem_filter.mp hyN).2
      exact hneigh hxadj hyadj hxy hadj
  · have hR : 3 ≤ R.card := by omega
    obtain ⟨T, hTR, hTcard⟩ := Finset.exists_subset_card_eq hR
    have hnclique : ¬G.IsClique (T : Set V) := by
      intro hc
      exact htri T ⟨hc, hTcard⟩
    obtain ⟨x, y, hxy, hnxy⟩ := G.not_isClique_iff.mp hnclique
    let S : Finset V := {v, x.1, y.1}
    have hxR : x.1 ∈ R := hTR x.2
    have hyR : y.1 ∈ R := hTR y.2
    have hxU : x.1 ∈ U := by
      have := (Finset.mem_filter.mp hxR).1
      exact Finset.mem_of_mem_erase this
    have hyU : y.1 ∈ U := by
      have := (Finset.mem_filter.mp hyR).1
      exact Finset.mem_of_mem_erase this
    have hxv : x.1 ≠ v := by
      exact Finset.ne_of_mem_erase (Finset.mem_filter.mp hxR).1
    have hyv : y.1 ≠ v := by
      exact Finset.ne_of_mem_erase (Finset.mem_filter.mp hyR).1
    have hxyv : x.1 ≠ y.1 := by
      exact fun h => hxy (Subtype.ext h)
    have hvx : ¬G.Adj v x.1 := (Finset.mem_filter.mp hxR).2
    have hvy : ¬G.Adj v y.1 := (Finset.mem_filter.mp hyR).2
    have hSsub : S ⊆ U := by
      intro z hz
      simp [S] at hz
      rcases hz with rfl | rfl | rfl
      · exact hvU
      · exact hxU
      · exact hyU
    have hScard : S.card = 3 := by
      simp [S, hxv.symm, hyv.symm, hxyv]
    have hSind : G.IsIndepSet (S : Set V) := by
      rw [← isClique_compl]
      have hc : Gᶜ.IsNClique 3 S := by
        rw [is3Clique_triple_iff]
        simp [compl_adj, hxv.symm, hyv.symm, hxyv, hvx, hvy, hnxy]
      exact hc.isClique
    exact ⟨S, hSsub, hScard, hSind⟩

open scoped Classical in
lemma indep_four_of_ten
    {V : Type} [Fintype V] (G : SimpleGraph V) (htri : G.CliqueFree 3)
    (U : Finset V) (hU : 10 ≤ U.card) :
    ∃ S : Finset V, S ⊆ U ∧ S.card = 4 ∧
      G.IsIndepSet (S : Set V) := by
  classical
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hvU⟩ := hUne
  let N := (U.erase v).filter fun x => G.Adj v x
  let R := (U.erase v).filter fun x => ¬G.Adj v x
  have hpartition : N.card + R.card = (U.erase v).card := by
    simpa [N, R] using
      Finset.card_filter_add_card_filter_not (s := U.erase v) (fun x => G.Adj v x)
  have herase : (U.erase v).card = U.card - 1 :=
    Finset.card_erase_of_mem hvU
  by_cases hN : 4 ≤ N.card
  · obtain ⟨S, hSN, hScard⟩ := Finset.exists_subset_card_eq hN
    refine ⟨S, ?_, hScard, ?_⟩
    · intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hSN hx)).1
    · have hneigh :=
        G.isIndepSet_neighborSet_of_triangleFree htri v
      intro x hx y hy hxy hadj
      have hxadj : G.Adj v x := (Finset.mem_filter.mp (hSN hx)).2
      have hyadj : G.Adj v y := (Finset.mem_filter.mp (hSN hy)).2
      exact hneigh hxadj hyadj hxy hadj
  · have hR : 6 ≤ R.card := by omega
    obtain ⟨T, hTR, hTcard, hTind⟩ :=
      indep_three_of_six G htri R hR
    let S : Finset V := insert v T
    have hvT : v ∉ T := by
      intro hv
      have hvR := hTR hv
      exact Finset.notMem_erase v _ (Finset.mem_filter.mp hvR).1
    have hSsub : S ⊆ U := by
      intro x hx
      simp [S] at hx
      rcases hx with rfl | hx
      · exact hvU
      · exact Finset.mem_of_mem_erase
          (Finset.mem_filter.mp (hTR hx)).1
    have hScard : S.card = 4 := by simp [S, hvT, hTcard]
    have hSind : G.IsIndepSet (S : Set V) := by
      rw [← isClique_compl]
      have hTc : Gᶜ.IsNClique 3 T := by
        have hcT : Gᶜ.IsClique (T : Set V) := by simpa using hTind
        exact ⟨hcT, hTcard⟩
      have hvcompl : ∀ x ∈ T, Gᶜ.Adj v x := by
        intro x hx
        have hxR := hTR hx
        have hnotadj : ¬G.Adj v x := (Finset.mem_filter.mp hxR).2
        have hvx : v ≠ x :=
          (Finset.ne_of_mem_erase (Finset.mem_filter.mp hxR).1).symm
        simp [compl_adj, hnotadj, hvx]
      exact (hTc.insert hvcompl).isClique
    exact ⟨S, hSsub, hScard, hSind⟩

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        (((∀ v : V, 1 ≤ G.degree v) ∧ G.edgeFinset.card ≤ 8) ∨
          ((∀ v : V, 2 ≤ G.degree v) ∧ G.edgeFinset.card ≤ 12) ∨
          ((∀ v : V, 3 ≤ G.degree v) ∧ G.edgeFinset.card ≤ 16)) →
            ∃ (H : SimpleGraph V),
              H ≤ G ∧ H.IsBipartite ∧
                (G.edgeFinset \ H.edgeFinset).card ≤ 4 := by
  intro V _ hcard G htri hrange
  obtain ⟨S, _, hScard, hSind⟩ :=
    indep_four_of_ten G htri Finset.univ (by simp [hcard])
  obtain ⟨k, hmindeg, hedges, hk⟩ :
      ∃ k : ℕ, (∀ v : V, k ≤ G.degree v) ∧
        G.edgeFinset.card ≤ 4 * (k + 1) ∧
          (k = 1 ∨ k = 2 ∨ k = 3) := by
    rcases hrange with h1 | h2 | h3
    · exact ⟨1, h1.1, by omega, Or.inl rfl⟩
    · exact ⟨2, h2.1, by omega, Or.inr (Or.inl rfl)⟩
    · exact ⟨3, h3.1, by omega, Or.inr (Or.inr rfl)⟩
  have hweight : 4 * k ≤ ∑ v ∈ S, G.degree v := by
    calc
      4 * k = ∑ _v ∈ S, k := by simp [hScard]
      _ ≤ _ := Finset.sum_le_sum fun v _ ↦ hmindeg v
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
  have hdeg : ∀ x ∈ S, H.degree x = G.degree x := by
    intro x hx
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    congr 1
    ext y
    have hyout : G.Adj x y → y ∉ S := by
      intro hxy hy
      exact hSind hx hy (G.ne_of_adj hxy) hxy
    simp [H, SimpleGraph.between_adj, hx]
    exact hyout
  have hHcard : H.edgeFinset.card = ∑ x ∈ S, G.degree x := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hbwith]
    exact Finset.sum_congr rfl fun x hx ↦ hdeg x hx
  refine ⟨H, hle, hbwith.isBipartite, ?_⟩
  calc
    (G.edgeFinset \ H.edgeFinset).card =
        G.edgeFinset.card - H.edgeFinset.card :=
      Finset.card_sdiff_of_subset (edgeFinset_mono hle)
    _ = G.edgeFinset.card - ∑ x ∈ S, G.degree x := by rw [hHcard]
    _ ≤ 4 := by omega

end Submissions.Erdos23N2MinimumDegreeRanges.Direct

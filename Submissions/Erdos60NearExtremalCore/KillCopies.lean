import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open SimpleGraph

namespace Submissions.Erdos60NearExtremalCore.KillCopies

set_option maxHeartbeats 1000000 in
theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      extremalNumber n (cycleGraph 4) < G.edgeSet.ncard →
      ∃ H : SimpleGraph (Fin n),
        ∃ _ : DecidableRel H.Adj,
        H ≤ G ∧
        (cycleGraph 4).Free H ∧
        G.edgeSet.ncard -
            {C : G.Subgraph | Nonempty (C.coe ≃g cycleGraph 4)}.ncard ≤
          H.edgeSet.ncard ∧
        H.edgeSet.ncard ≤ extremalNumber n (cycleGraph 4) ∧
        extremalNumber n (cycleGraph 4) - H.edgeSet.ncard <
          {C : G.Subgraph | Nonempty (C.coe ≃g cycleGraph 4)}.ncard ∧
        (∑ v, (G.degree v - H.degree v)) ≤
          2 * {C : G.Subgraph | Nonempty (C.coe ≃g cycleGraph 4)}.ncard := by
  intro n G _ hexcess
  classical
  have hC4 : cycleGraph 4 ≠ ⊥ := by
    intro h
    have hadj : (cycleGraph 4).Adj (0 : Fin 4) (1 : Fin 4) := by
      simp [cycleGraph_adj]
    rw [h] at hadj
    exact hadj
  let A : Set G.Subgraph :=
    {C | Nonempty (cycleGraph 4 ≃g C.coe)}
  let B : Set G.Subgraph :=
    {C | Nonempty (C.coe ≃g cycleGraph 4)}
  have hcount : G.copyCount (cycleGraph 4) = B.ncard := by
    have hab : A.ncard = B.ncard := by
      apply Set.ncard_congr'
      exact
        { toFun := fun x => ⟨x.1, ⟨x.2.some.symm⟩⟩
          invFun := fun x => ⟨x.1, ⟨x.2.some.symm⟩⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun x => Subtype.ext rfl }
    rw [← hab]
    change G.copyCount (cycleGraph 4) =
      {C : G.Subgraph | Nonempty (cycleGraph 4 ≃g C.coe)}.ncard
    rw [SimpleGraph.copyCount, Set.ncard_eq_toFinset_card]
    congr 1
    ext C
    simp
  let H := G.killCopies (cycleGraph 4)
  letI hHDec : DecidableRel H.Adj := Classical.decRel _
  have hfree : (cycleGraph 4).Free H := by
    exact free_killCopies hC4
  have hle : H ≤ G := by
    exact killCopies_le_left
  have hremoved :
      G.edgeSet.ncard - G.copyCount (cycleGraph 4) ≤ H.edgeSet.ncard := by
    have h0 :=
      le_card_edgeFinset_killCopies (G := G) (H := cycleGraph 4)
    have hG :
        G.edgeSet.ncard = G.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card G.edgeSet]
      congr 1
      ext e
      simp
    have hH :
        (@SimpleGraph.edgeFinset (Fin n) H
          SimpleGraph.killCopies.edgeSet.instFintype).card =
            H.edgeSet.ncard := by
      rw [Set.ncard_eq_toFinset_card H.edgeSet]
      congr 1
      ext e
      simp
    rw [hG]
    exact h0.trans_eq hH
  have hext : H.edgeSet.ncard ≤ extremalNumber n (cycleGraph 4) := by
    calc
      _ = (@SimpleGraph.edgeFinset (Fin n) H H.fintypeEdgeSet).card := by
        rw [Set.ncard_eq_toFinset_card H.edgeSet]
        congr 1
        ext e
        simp
      _ ≤ _ := by
        simpa [H] using card_edgeFinset_le_extremalNumber hfree
  have hsumG : ∑ v, G.degree v = 2 * G.edgeSet.ncard := by
    calc
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 2 * G.edgeSet.ncard := by
        congr 1
        rw [Set.ncard_eq_toFinset_card G.edgeSet]
        congr 1
        ext e
        simp
  have hsumH : ∑ v, H.degree v = 2 * H.edgeSet.ncard := by
    calc
      _ = 2 * (@SimpleGraph.edgeFinset (Fin n) H H.fintypeEdgeSet).card :=
        H.sum_degrees_eq_twice_card_edges
      _ = 2 * H.edgeSet.ncard := by
        congr 1
        rw [Set.ncard_eq_toFinset_card H.edgeSet]
        congr 1
        ext e
        simp
  have hdegree (v : Fin n) : H.degree v ≤ G.degree v :=
    H.degree_le_of_le hle
  have hsumdiff :
      (∑ v, (G.degree v - H.degree v)) =
        (∑ v, G.degree v) - ∑ v, H.degree v := by
    simpa using
      (Finset.sum_tsub_distrib Finset.univ
        (fun v _ => hdegree v))
  have hdegreeLoss :
      (∑ v, (G.degree v - H.degree v)) ≤
        2 * G.copyCount (cycleGraph 4) := by
    have hHG : H.edgeSet.ncard ≤ G.edgeSet.ncard :=
      Set.ncard_le_ncard (edgeSet_mono hle)
    omega
  refine ⟨H, hHDec, hle, hfree, ?_, hext, ?_, ?_⟩
  · simpa [B, hcount] using hremoved
  · rw [← hcount]
    omega
  · simpa [B, hcount] using hdegreeLoss

end Submissions.Erdos60NearExtremalCore.KillCopies

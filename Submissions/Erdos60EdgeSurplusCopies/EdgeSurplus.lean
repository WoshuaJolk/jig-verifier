import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open SimpleGraph

namespace Submissions.Erdos60EdgeSurplusCopies.EdgeSurplus

set_option maxHeartbeats 1000000 in
theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card - extremalNumber n (cycleGraph 4) ≤
        {H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4)}.ncard := by
  intro n G _
  classical
  have hC4 : cycleGraph 4 ≠ ⊥ := by
    intro h
    have hadj : (cycleGraph 4).Adj (0 : Fin 4) (1 : Fin 4) := by
      simp [cycleGraph_adj]
    rw [h] at hadj
    exact hadj
  have hfree : (cycleGraph 4).Free (G.killCopies (cycleGraph 4)) :=
    free_killCopies hC4
  have hkill :
      G.edgeFinset.card - G.copyCount (cycleGraph 4) ≤
        (G.killCopies (cycleGraph 4)).edgeSet.ncard := by
    refine (le_card_edgeFinset_killCopies (G := G) (H := cycleGraph 4)).trans_eq ?_
    rw [Set.ncard_eq_toFinset_card
      ((G.killCopies (cycleGraph 4)).edgeSet)]
    congr 1
    ext e
    simp
  have hext :
      (G.killCopies (cycleGraph 4)).edgeSet.ncard ≤
        extremalNumber n (cycleGraph 4) := by
    calc
      _ = (@SimpleGraph.edgeFinset (Fin n) (G.killCopies (cycleGraph 4))
          (G.killCopies (cycleGraph 4)).fintypeEdgeSet).card := by
        rw [Set.ncard_eq_toFinset_card
          ((G.killCopies (cycleGraph 4)).edgeSet)]
        congr 1
        ext e
        simp
      _ ≤ _ := by simpa using card_edgeFinset_le_extremalNumber hfree
  have hsurplus :
      G.edgeFinset.card - extremalNumber n (cycleGraph 4) ≤
        G.copyCount (cycleGraph 4) := by
    omega
  let A : Set G.Subgraph :=
    {H' | Nonempty (cycleGraph 4 ≃g H'.coe)}
  let B : Set G.Subgraph :=
    {H' | Nonempty (H'.coe ≃g cycleGraph 4)}
  have hcount : A.ncard = B.ncard := by
    apply Set.ncard_congr'
    exact
      { toFun := fun x => ⟨x.1, ⟨x.2.some.symm⟩⟩
        invFun := fun x => ⟨x.1, ⟨x.2.some.symm⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  have hcopy : G.copyCount (cycleGraph 4) = A.ncard := by
    change G.copyCount (cycleGraph 4) =
      {H' : G.Subgraph | Nonempty (cycleGraph 4 ≃g H'.coe)}.ncard
    rw [SimpleGraph.copyCount, Set.ncard_eq_toFinset_card]
    congr 1
    ext H'
    simp
  change G.edgeFinset.card - extremalNumber n (cycleGraph 4) ≤ B.ncard
  rw [← hcount, ← hcopy]
  exact hsurplus

end Submissions.Erdos60EdgeSurplusCopies.EdgeSurplus

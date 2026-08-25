import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Submissions.Erdos743OrderTwo.Identity

def identityPackingMap :
    (i : Fin (2 - 1)) → Fin (i.val + 2) ↪ Fin 2 :=
  fun i =>
    { toFun := fun v => ⟨v.val, by omega⟩
      inj' := by
        intro a b h
        apply Fin.ext
        simpa using congrArg Fin.val h }

theorem graph_on_two_eq_top_of_isTree
    (G : SimpleGraph (Fin 2)) (hG : G.IsTree) :
    G = ⊤ := by
  apply top_unique
  intro u v huv
  simp only [SimpleGraph.top_adj] at huv
  by_contra hnot
  have h01 : ¬G.Adj 0 1 := by
    fin_cases u <;> fin_cases v <;>
      simp_all [SimpleGraph.adj_comm]
  have hbot : G = ⊥ := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp_all [SimpleGraph.adj_comm]
  rw [hbot] at hG
  exact SimpleGraph.not_connected_bot hG.connected

theorem proof :
    ∀ T : (i : Fin (2 - 1)) → SimpleGraph (Fin (i.val + 2)),
      (∀ i, (T i).IsTree) →
      ∃ f : (i : Fin (2 - 1)) → Fin (i.val + 2) ↪ Fin 2,
        ∀ u v : Fin 2, u ≠ v →
          ∃! i : Fin (2 - 1),
            ∃ a b : Fin (i.val + 2), (T i).Adj a b ∧
              ((f i a = u ∧ f i b = v) ∨
               (f i a = v ∧ f i b = u)) := by
  intro T hT
  refine ⟨identityPackingMap, ?_⟩
  intro u v huv
  refine ⟨(0 : Fin (2 - 1)), ?_, ?_⟩
  · refine ⟨u, v, ?_, ?_⟩
    · rw [graph_on_two_eq_top_of_isTree (T 0) (hT 0)]
      simpa using huv
    · left
      constructor <;> apply Fin.ext <;> rfl
  · intro j hj
    apply Fin.ext
    omega

end Submissions.Erdos743OrderTwo.Identity

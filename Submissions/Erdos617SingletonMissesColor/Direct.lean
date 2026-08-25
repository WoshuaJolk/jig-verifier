import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

namespace Submissions.Erdos617SingletonMissesColor.Direct

theorem proof :
    ∀ (V : Type) [Fintype V] [DecidableEq V], Nonempty V →
      ∀ coloring : Sym2 V → Fin 2,
        ∃ (S : Finset V) (k : Fin 2),
          S.card = 1 ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  intro V _ _ hV coloring
  let a : V := Classical.choice hV
  refine ⟨{a}, 0, by simp, ?_⟩
  intro u hu v hv huv
  simp only [Finset.mem_singleton] at hu hv
  exact (huv (hu.trans hv.symm)).elim

end Submissions.Erdos617SingletonMissesColor.Direct

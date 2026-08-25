import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

namespace Submissions.Erdos644SingletonTransversal.Direct

abbrev SetFamily (N : ℕ) := Finset (Finset (Fin N))

def Hits {N : ℕ} (T : Finset (Fin N)) (F : SetFamily N) : Prop :=
  ∀ A ∈ F, (T ∩ A).Nonempty

def singletonFamily : SetFamily 2 := {{0}}

theorem proof :
    ∃ T : Finset (Fin 2), T.card ≤ 1 ∧ Hits T singletonFamily := by
  refine ⟨{0}, by simp, ?_⟩
  simp [Hits, singletonFamily]

end Submissions.Erdos644SingletonTransversal.Direct

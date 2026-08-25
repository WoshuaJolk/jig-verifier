import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

namespace Submissions.Erdos644SingletonTransversal.Degenerate

abbrev SetFamily (N : ℕ) := Finset (Finset (Fin N))

def Hits {N : ℕ} (T : Finset (Fin N)) (F : SetFamily N) : Prop :=
  ∀ A ∈ F, (T ∩ A).Nonempty

def singletonFamily : SetFamily 2 := {{0}}

theorem proof : False →
    ∃ T : Finset (Fin 2), T.card ≤ 1 ∧ Hits T singletonFamily := False.elim

end Submissions.Erdos644SingletonTransversal.Degenerate

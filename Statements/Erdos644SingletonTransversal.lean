import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

namespace Statements.Erdos644SingletonTransversal

abbrev SetFamily (N : ℕ) := Finset (Finset (Fin N))

def Hits {N : ℕ} (T : Finset (Fin N)) (F : SetFamily N) : Prop :=
  ∀ A ∈ F, (T ∩ A).Nonempty

def singletonFamily : SetFamily 2 := {{0}}

abbrev statement : Prop :=
  ∃ T : Finset (Fin 2), T.card ≤ 1 ∧ Hits T singletonFamily

theorem target : statement := sorry

end Statements.Erdos644SingletonTransversal

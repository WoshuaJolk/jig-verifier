import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset

namespace Statements.Erdos572CompleteSixCycle

abbrev FiniteGraph (N : ℕ) := Finset (Finset (Fin N))

def completeGraph (N : ℕ) : FiniteGraph N :=
  Finset.univ.filter fun e => e.card = 2

def ContainsCycle {N : ℕ} (ℓ : ℕ) (E : FiniteGraph N) : Prop :=
  ∃ hℓ : 0 < ℓ, ∃ v : Fin ℓ → Fin N, Function.Injective v ∧
    ∀ i : Fin ℓ,
      ({v i, v ⟨(i.val + 1) % ℓ, Nat.mod_lt _ hℓ⟩} :
        Finset (Fin N)) ∈ E

abbrev statement : Prop := ContainsCycle 6 (completeGraph 6)

theorem target : statement := sorry

end Statements.Erdos572CompleteSixCycle

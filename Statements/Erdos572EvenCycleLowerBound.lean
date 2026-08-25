import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos572EvenCycleLowerBound

open Filter

abbrev FiniteGraph (N : ℕ) := Finset (Finset (Fin N))

def IsSimpleGraph {N : ℕ} (E : FiniteGraph N) : Prop :=
  ∀ e ∈ E, e.card = 2

def ContainsCycle {N : ℕ} (ℓ : ℕ) (E : FiniteGraph N) : Prop :=
  ∃ hℓ : 0 < ℓ, ∃ v : Fin ℓ → Fin N, Function.Injective v ∧
    ∀ i : Fin ℓ,
      ({v i, v ⟨(i.val + 1) % ℓ, Nat.mod_lt _ hℓ⟩} :
        Finset (Fin N)) ∈ E

noncomputable def evenCycleTuran (N k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ E : FiniteGraph N,
    IsSimpleGraph E ∧ ¬ ContainsCycle (2 * k) E ∧ E.card = m}

/-- Erdős problem 572: the conjectured lower order for every even cycle. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c * (N : ℝ) ^ (1 + (1 : ℝ) / k) ≤ evenCycleTuran N k

theorem target : statement := sorry

end Statements.Erdos572EvenCycleLowerBound

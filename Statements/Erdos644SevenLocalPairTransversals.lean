import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace Statements.Erdos644SevenLocalPairTransversals

open Filter

abbrev SetFamily (N : ℕ) := Finset (Finset (Fin N))

def IsUniform {N : ℕ} (k : ℕ) (F : SetFamily N) : Prop :=
  ∀ A ∈ F, A.card = k

def Hits {N : ℕ} (T : Finset (Fin N)) (F : SetFamily N) : Prop :=
  ∀ A ∈ F, (T ∩ A).Nonempty

def HasLocalPairTransversals {N : ℕ} (r : ℕ) (F : SetFamily N) : Prop :=
  ∀ S : SetFamily N, S ⊆ F → S.card = r →
    ∃ T : Finset (Fin N), T.card ≤ 2 ∧ Hits T S

def IsUniversalBound (m k r : ℕ) : Prop :=
  ∀ N : ℕ, ∀ F : SetFamily N,
    IsUniform k F → HasLocalPairTransversals r F →
      ∃ T : Finset (Fin N), T.card ≤ m ∧ Hits T F

noncomputable def transversalBound (k r : ℕ) : ℕ :=
  sInf {m : ℕ | IsUniversalBound m k r}

/-- Erdős problem 644: the seven-local pair-transversal conjecture. -/
abbrev statement : Prop :=
  Tendsto
    (fun k => (transversalBound k 7 : ℝ) / k)
    atTop (nhds (3 / 4 : ℝ))

theorem target : statement := sorry

end Statements.Erdos644SevenLocalPairTransversals

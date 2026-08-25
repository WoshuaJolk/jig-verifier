import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

open Filter Real
open scoped Asymptotics

namespace Statements.Erdos562HypergraphRamseyTower

/-- The two-colour diagonal `r`-uniform hypergraph Ramsey number. -/
noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf {m | ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin m),
        e ⊆ S → e.card = r → c e = color}

/-- Erdős Problem 562: after `r-1` iterated logarithms, the diagonal `r`-uniform hypergraph Ramsey number has linear order for every `r ≥ 3`. -/
abbrev statement : Prop :=
  ∀ r ≥ 3,
    (fun n ↦ log^[r - 1] (hypergraphRamsey r n)) =Θ[atTop]
      (fun n ↦ (n : ℝ))

theorem target : statement := sorry

end Statements.Erdos562HypergraphRamseyTower

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Nat

/-!
# Erdős problem 564

Does the two-colour three-uniform diagonal Ramsey number have a doubly
exponential lower bound?
-/

open Filter

namespace Statements.Erdos564HypergraphRamseyDoubleExp

noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf {m | ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin m),
        e ⊆ S → e.card = r → c e = color}

abbrev statement : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ ((2 : ℝ) ^ (c * n)) ≤ hypergraphRamsey 3 n

theorem target : statement := sorry

end Statements.Erdos564HypergraphRamseyDoubleExp

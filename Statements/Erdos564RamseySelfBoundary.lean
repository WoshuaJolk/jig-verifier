import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat

/-!
# Boundary semantics for Erdős problem 564

The three-uniform Ramsey number of a three-vertex set is exactly three.
-/

namespace Statements.Erdos564RamseySelfBoundary

noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf {m | ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin m),
        e ⊆ S → e.card = r → c e = color}

abbrev statement : Prop := hypergraphRamsey 3 3 = 3

theorem target : statement := sorry

end Statements.Erdos564RamseySelfBoundary

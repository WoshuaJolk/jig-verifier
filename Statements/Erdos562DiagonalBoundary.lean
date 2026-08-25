import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos562DiagonalBoundary

noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf {m | ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin m),
        e ⊆ S → e.card = r → c e = color}

/-- The diagonal `r`-uniform Ramsey number equals `r` when the target monochromatic set also has size `r`. -/
abbrev statement : Prop :=
  ∀ r : ℕ, hypergraphRamsey r r = r

theorem target : statement := sorry

end Statements.Erdos562DiagonalBoundary

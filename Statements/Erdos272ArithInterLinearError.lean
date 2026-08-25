import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.Asymptotics.Defs

namespace Statements.Erdos272ArithInterLinearError

open Filter Asymptotics Finset

def IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

def IsArithInterSet (N : ℕ) (A : Finset (Finset ℕ)) : Prop :=
  A ⊆ (Finset.Icc 1 N).powerset ∧
    (SetLike.coe A).Pairwise fun S T =>
      ∃ l > 0, IsAPOfLength (SetLike.coe (S ∩ T)) l

noncomputable def maxArithInterCard (N : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ A : Finset (Finset ℕ), IsArithInterSet N A ∧ t = A.card}

/-- Szabó's open linear-error strengthening for Erdős problem 272. -/
abbrev statement : Prop :=
  (fun N => (maxArithInterCard N - N ^ 2 / 2 : ℝ)) =O[atTop]
    fun N : ℕ => (N : ℝ)

theorem target : statement := sorry

end Statements.Erdos272ArithInterLinearError

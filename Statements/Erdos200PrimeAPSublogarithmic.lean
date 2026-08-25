import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Statements.Erdos200PrimeAPSublogarithmic

open Filter Real

def IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

noncomputable def longestPrimeArithmeticProgressions (n : ℕ) : ℕ :=
  sSup {(k : ℕ) | ∃ s ⊆ Set.Icc 1 n,
    IsAPOfLength s k ∧ ∀ m ∈ s, m.Prime}

/-- Erdős problem 200. -/
abbrev statement : Prop :=
  (fun n => (longestPrimeArithmeticProgressions n : ℝ)) =o[atTop]
    (fun n => log n)

theorem target : statement := sorry

end Statements.Erdos200PrimeAPSublogarithmic

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Statements.J4P280SidonIntervalDegree
namespace SidonBlockEnergy
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

end SidonBlockEnergy
namespace LabelIntervalDegree
open Finset
def lowerNeighbors (S : Finset ℕ) (a start L : ℕ) : Finset ℕ :=
  S.filter (fun b => b < a ∧ start ≤ a-b ∧ a-b < start+L)

def upperNeighbors (S : Finset ℕ) (a start L : ℕ) : Finset ℕ :=
  S.filter (fun b => a < b ∧ start ≤ b-a ∧ b-a < start+L)

end LabelIntervalDegree

open Finset SidonBlockEnergy LabelIntervalDegree

abbrev statement : Prop :=
  ∀ (S : Finset Nat), IsSidon (S : Set Nat) → ∀ a start L : Nat, 1 ≤ L →
    ((lowerNeighbors S a start L).card + (upperNeighbors S a start L).card) ^ 2 ≤ 16 * L

end Statements.J4P280SidonIntervalDegree

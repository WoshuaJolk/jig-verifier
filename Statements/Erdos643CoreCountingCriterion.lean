import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith

namespace Statements.Erdos643CoreCountingCriterion

open scoped BigOperators

def Uniform3 {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ E ∈ F, E.card = 3

def allPairs (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard 2 Finset.univ

def extensionSet {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => x ∉ p ∧ insert x p ∈ F

def codegree {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : Finset (Fin n)) : ℕ :=
  (extensionSet F p).card

def commonLinkCount {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : Finset (Fin n)) : ℕ :=
  ((allPairs n).filter fun w => p ⊆ extensionSet F w).card

abbrev statement : Prop :=
  ∀ {n : ℕ} (F : Finset (Finset (Fin n))), Uniform3 F →
    ∀ (C : Finset (Finset (Fin n))), C ⊆ allPairs n →
      (∑ p ∈ C, commonLinkCount F p) ≤ (∑ p ∈ C, codegree F p) →
      (∀ p ∈ allPairs n, p ∉ C → commonLinkCount F p ≤ 3) →
      F.card ≤ Nat.choose n 2

theorem target : statement := sorry

end Statements.Erdos643CoreCountingCriterion

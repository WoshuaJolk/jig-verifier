import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Statements.Erdos1158KtrHypergraphLowerBound

open Filter Finset

def Uniform {n : ℕ} (E : Finset (Finset (Fin n))) (t : ℕ) : Prop :=
  ∀ e ∈ E, e.card = t

def ContainsKt {n : ℕ} (E : Finset (Finset (Fin n)))
    (t r : ℕ) : Prop :=
  ∃ parts : Fin t → Finset (Fin n),
    (∀ i, (parts i).card = r) ∧
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
    ∀ choice : Fin t → Fin n,
      (∀ i, choice i ∈ parts i) →
      (Finset.univ.image choice : Finset (Fin n)) ∈ E

/-- Erdős problem 1158: the complete balanced multipartite hypergraph has
the conjectured extremal exponent from below. -/
abbrev statement : Prop :=
  ∀ t r : ℕ, 2 ≤ t → 2 ≤ r →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∃ E : Finset (Finset (Fin n)),
          Uniform E t ∧ ¬ ContainsKt E t r ∧
            (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)) - ε) ≤ E.card

theorem target : statement := sorry

end Statements.Erdos1158KtrHypergraphLowerBound

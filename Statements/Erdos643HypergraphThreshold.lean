import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Statements.Erdos643HypergraphThreshold

def Uniform {V : Type} [DecidableEq V]
    (t : ℕ) (F : Finset (Finset V)) : Prop :=
  ∀ A ∈ F, A.card = t

def HasDisjointEqualUnion {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, ∃ D ∈ F,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    A ∪ B = C ∪ D ∧ Disjoint A B ∧ Disjoint C D

def IsThreshold (n t m : ℕ) : Prop :=
  (∀ F : Finset (Finset (Fin n)),
      Uniform t F → m ≤ F.card → HasDisjointEqualUnion F) ∧
  ∀ q : ℕ, q < m →
    ∃ F : Finset (Finset (Fin n)),
      Uniform t F ∧ q ≤ F.card ∧ ¬HasDisjointEqualUnion F

/-- Erdős Problem 643: for each fixed t≥3, the threshold for a
disjoint equal-union quadruple is asymptotic to choose(n,t-1). -/
abbrev statement : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∀ f : ℕ → ℕ,
    (∀ n, IsThreshold n t (f n)) →
      Filter.Tendsto
        (fun n : ℕ => (f n : ℝ) / (Nat.choose n (t - 1) : ℝ))
        Filter.atTop (nhds 1)

theorem target : statement := sorry

end Statements.Erdos643HypergraphThreshold

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Statements.Erdos643ThresholdLowerBound

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

abbrev statement : Prop :=
  (∀ n t : ℕ, ∃! m, IsThreshold n t m) ∧
  (∀ n t m : ℕ, 1 ≤ n → 1 ≤ t → IsThreshold n t m →
    Nat.choose (n - 1) (t - 1) + 1 ≤ m) ∧
  (∀ t : ℕ, 1 ≤ t → ∀ f : ℕ → ℕ, (∀ n, IsThreshold n t (f n)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      1 - ε ≤ (f n : ℝ) / (Nat.choose n (t - 1) : ℝ))

theorem target : statement := sorry

end Statements.Erdos643ThresholdLowerBound

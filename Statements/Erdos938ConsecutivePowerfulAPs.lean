import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card

namespace Statements.Erdos938ConsecutivePowerfulAPs

def Nat.Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

instance (k n : ℕ) : Decidable (Nat.Full k n) := by
  unfold Nat.Full
  infer_instance

abbrev Nat.Powerful : ℕ → Prop := Nat.Full 2

def IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (length : ℕ∞) (a d : α) : Prop :=
  ENat.card s = length ∧
    s = {a + n • d | (n : ℕ) (_ : n < length)}

def IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (length : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s length a d

/-- Erdős Problem 938: only finitely many triples of consecutive powerful
numbers form three-term arithmetic progressions. -/
abbrev statement : Prop :=
  {P : Finset ℕ |
      IsAPOfLength (P : Set ℕ) 3 ∧
        ∃ k, P =
          {Nat.nth Nat.Powerful k, Nat.nth Nat.Powerful (k + 1),
            Nat.nth Nat.Powerful (k + 2)}}.Finite

theorem target : statement := sorry

end Statements.Erdos938ConsecutivePowerfulAPs

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Submissions.Erdos1059Witness101.Worker03VacuousControl

def IsFactorial (d : ℕ) : Prop := d ∈ Set.range Nat.factorial
def factorialsBelow (n : ℕ) : Set ℕ := {d | d < n ∧ IsFactorial d}
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime
def AvoidsPrimeFactorialDifferences (n : ℕ) : Prop :=
  ∀ d ∈ factorialsBelow n, IsComposite (n - d)

theorem proof (h : False) :
    Nat.Prime 101 ∧ AvoidsPrimeFactorialDifferences 101 := h.elim

end Submissions.Erdos1059Witness101.Worker03VacuousControl

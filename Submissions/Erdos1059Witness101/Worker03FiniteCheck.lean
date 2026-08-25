import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos1059Witness101.Worker03FiniteCheck

def IsFactorial (d : ℕ) : Prop := d ∈ Set.range Nat.factorial
def factorialsBelow (n : ℕ) : Set ℕ := {d | d < n ∧ IsFactorial d}
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime
def AvoidsPrimeFactorialDifferences (n : ℕ) : Prop :=
  ∀ d ∈ factorialsBelow n, IsComposite (n - d)

abbrev DecidableIsFactorial (d : ℕ) : Prop :=
  ((Finset.Icc 0 d).filter (fun k => Nat.factorial k = d)).Nonempty

def decidableFactorialsBelow (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter DecidableIsFactorial

def DecidableAvoids (n : ℕ) : Prop :=
  ∀ d ∈ decidableFactorialsBelow n, IsComposite (n - d)

lemma isFactorial_equivalent (d : ℕ) :
    IsFactorial d ↔ DecidableIsFactorial d := by
  unfold IsFactorial DecidableIsFactorial
  simp
  constructor
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter]
    constructor
    · have hk' : k ≤ d := by
        rw [← hk]
        apply Nat.self_le_factorial
      rw [Finset.mem_Icc]
      exact ⟨Nat.zero_le k, hk'⟩
    · exact hk
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter] at hk
    exact hk.2

lemma factorialsBelow_equivalent (n : ℕ) :
    factorialsBelow n = ↑(decidableFactorialsBelow n) := by
  ext d
  simp only [factorialsBelow, decidableFactorialsBelow, Set.mem_setOf_eq,
    Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
  rw [isFactorial_equivalent]

lemma avoids_equivalent (n : ℕ) :
    DecidableAvoids n ↔ AvoidsPrimeFactorialDifferences n := by
  unfold DecidableAvoids AvoidsPrimeFactorialDifferences
  rw [factorialsBelow_equivalent n]
  simp

set_option maxRecDepth 10000 in
theorem proof :
    Nat.Prime 101 ∧ AvoidsPrimeFactorialDifferences 101 := by
  constructor
  · decide
  · apply (avoids_equivalent 101).mp
    norm_num [DecidableAvoids, decidableFactorialsBelow,
      DecidableIsFactorial, IsComposite]
    decide

end Submissions.Erdos1059Witness101.Worker03FiniteCheck

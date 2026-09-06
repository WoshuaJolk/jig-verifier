import Mathlib.NumberTheory.SmoothNumbers
namespace Statements.E287SlowBandGap
open Finset
def base (r : ℕ) : ℕ := 2 ^ r

def primes (r : ℕ) : Finset ℕ := Nat.primesBelow (base r + 1)

def oddPrimes (r : ℕ) : Finset ℕ := (primes r).erase 2

def oddSmoothUpTo (r T : ℕ) : Finset ℕ :=
  (Icc 1 T).filter (fun d => d ∈ Nat.factoredNumbers (oddPrimes r))


def H (r k : ℕ) : ℕ := (oddSmoothUpTo r ((base r) ^ k)).card


def band (r T : ℕ) : Finset ℕ :=
  (Ioc T (base r * T)).filter (fun a => a ∈ Nat.factoredNumbers (primes r))



abbrev statement : Prop :=
∀ r : ℕ, 5 ≤ r →
      (∃ k : ℕ, H r (k+1) ≤ 2*H r k) ∧
      ∀ k : ℕ, H r (k+1) ≤ 2*H r k →
        ∃ a ∈ band r (base r ^ k), ∃ b ∈ band r (base r ^ k),
          ∃ x : ℕ, a ≤ x ∧ x+1 < b ∧
            x ∉ band r (base r ^ k) ∧ x+1 ∉ band r (base r ^ k)
end Statements.E287SlowBandGap

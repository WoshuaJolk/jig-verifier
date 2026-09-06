import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.ErdosMultiplesSmoothExplicit48

/-- The primes below 257. -/
def primes : Finset ℕ := Nat.primesBelow 257

/-- Q: the product of the odd primes below 257 (≈ 3.2 × 10^100). -/
def Q : ℕ := ∏ p ∈ primes.erase 2, p

/-- T = 256^48 = 2^384. -/
def T : ℕ := 256 ^ 48

/-- A: every 257-smooth integer in the band (T, 256T]. -/
def A : Finset ℕ := (Finset.Ioc T (256 * T)).filter (fun a => a ∈ Nat.factoredNumbers primes)

/-- M(x): the number of integers in [1, x] divisible by some element of A. -/
def M (x : ℕ) : ℕ := ((Finset.Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card

/-- Explicit witness for the smooth-band refutation of Erdős #488 with k = 48:
with n = 256T = 2^392 = max A and m = 2TQ > n, one has n·M(m) > 2m·M(n). -/
abbrev statement : Prop := 2 * (2 * T * Q) * M (256 * T) < 256 * T * M (2 * T * Q)

theorem target : statement := sorry

end Statements.ErdosMultiplesSmoothExplicit48

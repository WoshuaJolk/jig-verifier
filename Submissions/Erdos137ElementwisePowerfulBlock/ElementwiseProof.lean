import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős 137: element-wise powerful blocks have powerful products

If every element of a block of consecutive integers is powerful, so is the
product of the block: a prime dividing the product divides some element, the
element's square divisibility pulls back, and the element divides the product.
No coprimality between elements is required, so this is a one-way (sufficient)
condition: it says a block of powerful numbers refutes the root conjecture, not
that a powerful product forces element-wise powerfulness (which is false in
general, since small primes can pool their valuations across different elements).
-/

namespace Submissions.Erdos137ElementwisePowerfulBlock.ElementwiseProof

open Finset
open scoped BigOperators

def Powerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

def consecutiveProduct (start length : ℕ) : ℕ :=
  ∏ x ∈ Finset.Ioc start (start + length), x

-- a prime dividing a finite product divides some element
theorem prime_dvd_prod_extract {p : ℕ} (hp : p.Prime) {s : Finset ℕ} {f : ℕ → ℕ}
    (h : p ∣ ∏ x ∈ s, f x) : ∃ x ∈ s, p ∣ f x := by
  classical
  induction s using Finset.induction with
  | empty => simp at h; exact absurd h hp.ne_one
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha] at h
      rcases hp.dvd_mul.mp h with hd | hd
      · exact ⟨a, Finset.mem_insert_self _ _, hd⟩
      · obtain ⟨x, hx, hfx⟩ := ih hd
        exact ⟨x, Finset.mem_insert_of_mem hx, hfx⟩

theorem proof : ∀ start length : ℕ,
    (∀ x ∈ Finset.Ioc start (start + length), Powerful x) →
      Powerful (consecutiveProduct start length) := by
  intro start length hall p hprime hdvd
  obtain ⟨x, hx, hpx⟩ := prime_dvd_prod_extract hprime hdvd
  have hp2x : p ^ 2 ∣ x := hall x hx p hprime hpx
  exact hp2x.trans (Finset.dvd_prod_of_mem (fun _ => _) hx)

end Submissions.Erdos137ElementwisePowerfulBlock.ElementwiseProof

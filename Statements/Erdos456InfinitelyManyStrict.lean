import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# An infinite strict-inequality family for Erdős problem 456

There are infinitely many `n` for which the least totient preimage is strictly
smaller than the least prime congruent to one modulo `n`.
-/

open Nat

namespace Statements.Erdos456InfinitelyManyStrict

noncomputable def p (n : ℕ) : ℕ :=
  sInf {q | q.Prime ∧ q ≡ 1 [MOD n]}

noncomputable def m (n : ℕ) : ℕ :=
  sInf {q | 0 < q ∧ n ∣ totient q}

abbrev statement : Prop := {n | m n < p n}.Infinite

theorem target : statement := sorry

end Statements.Erdos456InfinitelyManyStrict

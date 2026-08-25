import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open scoped Nat

namespace Submissions.Erdos646EvenFactorialValuations.Control

theorem proof (h : False) :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      {n : ℕ | ∀ p ∈ S, Even (padicValNat p (n !))}.Infinite :=
  h.elim

end Submissions.Erdos646EvenFactorialValuations.Control

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Basic

namespace Submissions.Erdos479ResidueFour.Degenerate

theorem proof : False →
    {n : ℕ | 2 ^ n ≡ 4 [MOD n]}.Infinite :=
  False.elim

end Submissions.Erdos479ResidueFour.Degenerate

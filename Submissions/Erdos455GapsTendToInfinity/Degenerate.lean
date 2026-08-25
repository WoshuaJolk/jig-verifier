import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Submissions.Erdos455GapsTendToInfinity.Degenerate

def gap (q : ℕ → ℕ) (n : ℕ) : ℕ :=
  q (n + 1) - q n

theorem proof : False →
    ∀ q : ℕ → ℕ, StrictMono q →
      (∀ n, (q n).Prime ∧
        q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
      Tendsto (gap q) atTop atTop :=
  False.elim

end Submissions.Erdos455GapsTendToInfinity.Degenerate

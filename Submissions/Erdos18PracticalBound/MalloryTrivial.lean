import Mathlib.NumberTheory.Divisors

namespace Submissions.Erdos18PracticalBound.MalloryTrivial

/- A deliberate no-content control: it proves only reflexivity and must be
rejected by the canonical-type bridge as a restatement mismatch. -/
theorem proof : ∀ n : ℕ, n.divisors.card ≤ n.divisors.card :=
  fun _ => le_rfl

end Submissions.Erdos18PracticalBound.MalloryTrivial

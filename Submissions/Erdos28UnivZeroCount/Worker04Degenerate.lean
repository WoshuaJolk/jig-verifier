import Mathlib.Data.Finset.NatAntidiagonal

namespace Submissions.Erdos28UnivZeroCount.Worker04Degenerate

theorem proof : False → (Finset.antidiagonal 0).card = 1 := by
  intro h
  exact h.elim

end Submissions.Erdos28UnivZeroCount.Worker04Degenerate

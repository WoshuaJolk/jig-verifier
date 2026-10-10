import DemoCollatz.Step

/-! The root of the demo package: it imports the rest, and its `proof` is what a
submission's manifest names as `decl`. -/

namespace DemoCollatz

theorem proof : ∀ n : ℕ, collatzStep (2 * n) = n := step_even

end DemoCollatz

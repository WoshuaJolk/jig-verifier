import Mathlib.Algebra.Group.Nat.Even

/-! A two-module package used to exercise the pinned-package path end to end.
It lives here so a CI test can name a public commit; nothing builds it except
a submission that pins it. -/

namespace DemoCollatz

def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

theorem step_even (n : ℕ) : collatzStep (2 * n) = n := by
  have h : Even (2 * n) := ⟨n, Nat.two_mul n⟩
  simp [collatzStep, h]

end DemoCollatz

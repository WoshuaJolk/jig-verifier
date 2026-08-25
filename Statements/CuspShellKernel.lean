import Mathlib

/-!
# CuspShellKernel

The sparse coefficient flattening arising at the Tate cusp can be eliminated
shell by shell.  Nonvanishing of its two-by-two shell minors forces a trivial
kernel on all columns retained by the rank-k flattening.
-/

namespace Statements.CuspShellKernel

def delta (r : ℕ) (A B : ℕ → ℂ) (j : ℕ) : ℂ :=
  A 0 * A r * B j * B (r - j) - A j * A (r - j) * B 0 * B r

abbrev statement : Prop :=
  ∀ (r : ℕ) (A B x : ℕ → ℂ), 1 ≤ r →
    A 0 * B 0 ≠ 0 → A 0 * B r ≠ 0 →
    (∀ j, 1 ≤ j → j < r → delta r A B j ≠ 0) →
    (A 0 * B 0) * x r = 0 →
    (∀ j, 1 ≤ j → j < r →
      (A j * B 0) * x (r - j) + (A 0 * B j) * x (r + j) = 0) →
    (∀ j, 1 ≤ j → j < r →
      (A r * B (r - j)) * x (r - j) +
        (A (r - j) * B r) * x (r + j) = 0) →
    (A 0 * B r) * x (2 * r) = 0 →
    ∀ m, 1 ≤ m → m ≤ 2 * r → x m = 0

theorem target : statement := sorry

end Statements.CuspShellKernel

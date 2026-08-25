import Mathlib

namespace Submissions.CuspShellKernel.Elimination

def delta (r : ℕ) (A B : ℕ → ℂ) (j : ℕ) : ℂ :=
  A 0 * A r * B j * B (r - j) - A j * A (r - j) * B 0 * B r

theorem proof :
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
    ∀ m, 1 ≤ m → m ≤ 2 * r → x m = 0 := by
  intro r A B x hr hA00 hA0r hdelta hcenter hlow hhigh htop
  have hxcenter : x r = 0 :=
    (mul_eq_zero.mp hcenter).resolve_left hA00
  have hxtop : x (2 * r) = 0 :=
    (mul_eq_zero.mp htop).resolve_left hA0r
  have hshell (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
      x (r - j) = 0 ∧ x (r + j) = 0 := by
    have hd := hdelta j hj1 hjr
    have he1 := hlow j hj1 hjr
    have he2 := hhigh j hj1 hjr
    have hleft : delta r A B j * x (r - j) = 0 := by
      unfold delta
      linear_combination
        -(A (r - j) * B r) * he1 + (A 0 * B j) * he2
    have hright : delta r A B j * x (r + j) = 0 := by
      unfold delta
      linear_combination
        (A r * B (r - j)) * he1 - (A j * B 0) * he2
    exact ⟨(mul_eq_zero.mp hleft).resolve_left hd,
      (mul_eq_zero.mp hright).resolve_left hd⟩
  intro m hm1 hmle
  rcases lt_trichotomy m r with hmr | hmr | hrm
  · have hj1 : 1 ≤ r - m := Nat.sub_pos_iff_lt.mpr hmr
    have hjr : r - m < r := Nat.sub_lt (by omega) hm1
    have hz := (hshell (r - m) hj1 hjr).1
    rwa [Nat.sub_sub_self (Nat.le_of_lt hmr)] at hz
  · simpa [hmr] using hxcenter
  · by_cases hm : m = 2 * r
    · simpa [hm] using hxtop
    · have hm_lt : m < 2 * r := lt_of_le_of_ne hmle hm
      have hj1 : 1 ≤ m - r := Nat.sub_pos_iff_lt.mpr hrm
      have hjr : m - r < r := by omega
      have hz := (hshell (m - r) hj1 hjr).2
      rwa [Nat.add_sub_of_le (Nat.le_of_lt hrm)] at hz

end Submissions.CuspShellKernel.Elimination

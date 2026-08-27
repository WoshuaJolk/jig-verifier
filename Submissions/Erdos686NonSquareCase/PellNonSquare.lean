import Mathlib.NumberTheory.Pell
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Erdős problem 686 holds for every non-square N

Erdős asked whether every integer `N ≥ 2` is a ratio
`∏_{i≤k}(m+i) / ∏_{i≤k}(n+i)` of two *disjoint* (`m ≥ n+k`) equal-length products
of consecutive integers.  For every `N` that is not a perfect square this is a
Pell equation, and `k = 2` always suffices.

**The reduction.**  With `k = 2` and `X = 2m+3`, `Y = 2n+3`,
`(m+1)(m+2) = (X²-1)/4`, so the requirement is `X² - N Y² = 1 - N` with `X, Y`
odd and `X ≥ Y+4`.

**The construction.**  Let `(a,b)` solve `a² - N b² = 1` nontrivially — such a
solution exists exactly because `N` is not a square (`Pell.exists_of_not_isSquare`).
Doubling twice, `(a,b) ↦ (a²+Nb², 2ab)`, gives a solution `(a₂,b₂)` with
`b₂ ≥ 4` even; then `a₂² = 1 + N b₂²` forces `a₂` odd.  Writing `a₂ = 2u+1`,
`b₂ = 2c`, the Pell relation becomes

  `u(u+1) = N c²`,

and then `m = u + Nc - 1`, `n = u + c - 1` satisfy
`(m+1)(m+2) = N (n+1)(n+2)` — because
`(u+Nc)(u+Nc+1) - N(u+c)(u+c+1) = (N-1)(Nc² - u(u+1)) = 0`.
Disjointness is `m - n = (N-1)c ≥ 2`.

**Example.** `N = 2`: `u(u+1) = 2c²` with `c = 98`, `u = 138` gives
`n = 235`… the concrete witness produced by this construction is
`696·697 / (492·493) = 2`.

What is left of Erdős 686 is exactly the perfect squares, where no Pell solution
exists and `k = 2` provably cannot work.
-/

namespace Submissions.Erdos686NonSquareCase.PellNonSquare


/-- one Pell doubling step -/
private lemma dbl {d a b : ℤ} (h : a ^ 2 - d * b ^ 2 = 1) :
    (a ^ 2 + d * b ^ 2) ^ 2 - d * (2 * a * b) ^ 2 = 1 := by
  have : (a ^ 2 + d * b ^ 2) ^ 2 - d * (2 * a * b) ^ 2 = (a ^ 2 - d * b ^ 2) ^ 2 := by ring
  rw [this, h]; norm_num

theorem key (N : ℕ) (hN : 2 ≤ N) (hsq : ¬ IsSquare N) :
    ∃ m n : ℕ, n + 2 ≤ m ∧ ((m + 1) * (m + 2) : ℤ) = (N:ℤ) * ((n + 1) * (n + 2)) := by
  have hd0 : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hN
  have hdsq : ¬ IsSquare ((N : ℤ)) := by
    rw [Int.isSquare_natCast_iff]; exact hsq
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hd0 hdsq
  -- normalise to a, b ≥ 1
  set a0 : ℤ := |x| with ha0
  set b0 : ℤ := |y| with hb0
  have h0 : a0 ^ 2 - (N : ℤ) * b0 ^ 2 = 1 := by
    rw [ha0, hb0, sq_abs, sq_abs]; exact hxy
  have hb0pos : 1 ≤ b0 := by
    have : b0 ≠ 0 := by simpa [hb0, abs_eq_zero] using hy
    have : 0 ≤ b0 := abs_nonneg y
    omega
  have ha0pos : 1 ≤ a0 := by
    nlinarith [h0, hb0pos, abs_nonneg x, sq_nonneg a0, sq_nonneg b0]
  -- two doublings
  set a1 : ℤ := a0 ^ 2 + (N : ℤ) * b0 ^ 2 with ha1
  set b1 : ℤ := 2 * a0 * b0 with hb1
  have h1 : a1 ^ 2 - (N : ℤ) * b1 ^ 2 = 1 := dbl h0
  have hb1ge : 2 ≤ b1 := by rw [hb1]; nlinarith
  have ha1ge : 1 ≤ a1 := by rw [ha1]; nlinarith
  set a2 : ℤ := a1 ^ 2 + (N : ℤ) * b1 ^ 2 with ha2
  set b2 : ℤ := 2 * a1 * b1 with hb2
  have h2 : a2 ^ 2 - (N : ℤ) * b2 ^ 2 = 1 := dbl h1
  have hb2ge : 4 ≤ b2 := by rw [hb2]; nlinarith
  have ha2ge : 1 ≤ a2 := by rw [ha2]; nlinarith
  -- b2 is even, hence a2 is odd
  have hb2even : ∃ c : ℤ, b2 = 2 * c := ⟨a1 * b1, by rw [hb2]; ring⟩
  obtain ⟨c, hc⟩ := hb2even
  have ha2odd : Odd a2 := by
    rcases Int.even_or_odd a2 with he | ho
    · exfalso
      obtain ⟨t, ht⟩ := he
      have hE : 4 * (t ^ 2 - (N : ℤ) * c ^ 2) = 1 := by
        have h := h2
        rw [ht, hc] at h
        linear_combination h
      generalize (t ^ 2 - (N : ℤ) * c ^ 2) = X at hE
      omega
    · exact ho
  obtain ⟨u, hu⟩ := ha2odd          -- a2 = 2*u + 1
  have hcge : 2 ≤ c := by omega
  have huge : 0 ≤ u := by omega
  -- the Pell relation becomes  u*(u+1) = N*c^2
  have hkey : u * (u + 1) = (N : ℤ) * c ^ 2 := by
    have h4 : 4 * (u * (u + 1)) = 4 * ((N : ℤ) * c ^ 2) := by
      have h := h2
      rw [hu, hc] at h
      linear_combination h
    linarith
  -- move to ℕ
  obtain ⟨un, rfl⟩ : ∃ un : ℕ, u = (un : ℤ) := ⟨u.toNat, (Int.toNat_of_nonneg huge).symm⟩
  obtain ⟨cn, rfl⟩ : ∃ cn : ℕ, c = (cn : ℤ) := ⟨c.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hcn : 2 ≤ cn := by exact_mod_cast hcge
  have hkeyN : (un : ℤ) * (un + 1) = (N : ℤ) * (cn : ℤ) ^ 2 := hkey
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, N = P + 2 := ⟨N - 2, by omega⟩
  obtain ⟨Q, rfl⟩ : ∃ Q : ℕ, cn = Q + 2 := ⟨cn - 2, by omega⟩
  refine ⟨un + P*Q + 2*P + 2*Q + 3, un + Q + 1, by omega, ?_⟩
  push_cast at hkeyN ⊢
  linear_combination (-((P:ℤ) + 1)) * hkeyN



lemma prodIcc2 (t : ℕ) : (∏ i ∈ Finset.Icc 1 2, (t + i)) = (t + 1) * (t + 2) := by
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl]
  rw [Finset.prod_pair (by norm_num)]

theorem proof : ∀ N ≥ (2 : ℕ), ¬ IsSquare N →
    ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  intro N hN hsq
  obtain ⟨m, n, hmn, hid⟩ := key N hN hsq
  refine ⟨2, le_refl 2, n, m, hmn, ?_⟩
  rw [prodIcc2, prodIcc2]
  have hne : (((n + 1) * (n + 2) : ℕ) : ℚ) ≠ 0 := by
    have h : (0:ℕ) < (n + 1) * (n + 2) := by positivity
    have : ((n + 1) * (n + 2) : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  rw [eq_div_iff hne]
  have : ((m + 1) * (m + 2) : ℕ) = N * ((n + 1) * (n + 2)) := by exact_mod_cast hid
  push_cast [this]
  ring


end Submissions.Erdos686NonSquareCase.PellNonSquare

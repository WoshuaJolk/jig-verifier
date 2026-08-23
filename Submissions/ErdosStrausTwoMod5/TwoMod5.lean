import Mathlib

/-! Every n >= 2 with n = 2 mod 5 admits an Erdos-Straus representation.

Three cases. `n ≡ 2 (mod 3)`: the classical identity with x = (n+1)/3. `3 ∣ n`: scale
4/3 = 1/1 + 1/4 + 1/12 by n/3. Otherwise `n ≡ 7 (mod 15)`: writing n = 15t+7, note
2n+1 = 15(2t+1), and 4/n = 1/(2(2t+1)) + 1/(4n) + 1/(4n(2t+1)), an instance of the
family e·n = 4uv - u - v, e ∣ uv (here u = 4, v = 4(2t+1), e = 8). -/

namespace Submissions.ErdosStrausTwoMod5.TwoMod5

abbrev ES (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

theorem key {n x y z : ℕ} (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) :
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h' : (4 : ℚ) * ((x : ℚ) * y * z) = (n : ℚ) * ((y : ℚ) * z + (x : ℚ) * z + (x : ℚ) * y) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) h
  field_simp
  linear_combination h'

/-- `n ≡ 2 (mod 3)`: `4/(3k+2) = 1/(k+1) + 1/(3k+2) + 1/((3k+2)(k+1))`. -/
theorem es_mod3 (k : ℕ) : ES (3 * k + 2) :=
  ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega,
    Nat.mul_pos (by omega) (by omega),
    key (by omega) (by omega) (by omega) (Nat.mul_pos (by omega) (by omega)) (by ring)⟩

/-- `3 ∣ n`: scale `4/3 = 1/1 + 1/4 + 1/12` by `m = n/3`. -/
theorem es_threeDvd (m : ℕ) (hm : 0 < m) : ES (3 * m) :=
  ⟨m, 4 * m, 12 * m, hm, by omega, by omega,
    key (by omega) hm (by omega) (by omega) (by ring)⟩

/-- `n ≡ 7 (mod 15)`: `4/n = 1/(2(2t+1)) + 1/(4n) + 1/(4n(2t+1))` for `n = 15t+7`. -/
theorem es_mod15 (t : ℕ) : ES (15 * t + 7) :=
  ⟨2 * (2 * t + 1), 4 * (15 * t + 7), 4 * ((15 * t + 7) * (2 * t + 1)),
    by omega, by omega,
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    key (by omega) (by omega) (by omega)
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) (by ring)⟩

theorem twoModFive : ∀ n : ℕ, 2 ≤ n → n % 5 = 2 → ES n := by
  intro n hn h5
  by_cases h3 : n % 3 = 2
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    exact es_mod3 k
  by_cases h3' : n % 3 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    exact es_threeDvd m (by omega)
  · obtain ⟨t, rfl⟩ : ∃ t, n = 15 * t + 7 := ⟨n / 15, by omega⟩
    exact es_mod15 t

theorem proof : ∀ n : ℕ, 2 ≤ n → n % 5 = 2 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := twoModFive

end Submissions.ErdosStrausTwoMod5.TwoMod5

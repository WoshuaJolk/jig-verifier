import Mathlib

/-! Every n >= 2 with n mod 7 a quadratic nonresidue (3, 5, or 6) admits an Erdos-Straus
representation.

All three classes come from one identity family: if e * n = 4*u*v - u - v with e ∣ u*v,
then 4/n = 1/(uv/e) + 1/(nu) + 1/(nv). With u = 2 and e = 1, 2, 4 this covers
n ≡ 5, 6, 3 (mod 7) respectively:

* n = 7t+5: 4/n = 1/(2(t+1)) + 1/(2n) + 1/(n(t+1))
* n = 7t+6: 4/n = 1/(2(t+1)) + 1/(2n) + 1/(2n(t+1))
* n = 7t+3: 4/n = 1/(2t+1)   + 1/(2n) + 1/(n(4t+2)) -/

namespace Submissions.ErdosStrausNonresidueMod7.NonresidueMod7

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

/-- `n ≡ 3 (mod 7)`: `4/n = 1/(2t+1) + 1/(2n) + 1/(n(4t+2))` for `n = 7t+3`. -/
theorem es_mod7_3 (t : ℕ) : ES (7 * t + 3) :=
  ⟨2 * t + 1, 2 * (7 * t + 3), (7 * t + 3) * (4 * t + 2),
    by omega, by omega, Nat.mul_pos (by omega) (by omega),
    key (by omega) (by omega) (by omega) (Nat.mul_pos (by omega) (by omega)) (by ring)⟩

/-- `n ≡ 5 (mod 7)`: `4/n = 1/(2(t+1)) + 1/(2n) + 1/(n(t+1))` for `n = 7t+5`. -/
theorem es_mod7_5 (t : ℕ) : ES (7 * t + 5) :=
  ⟨2 * (t + 1), 2 * (7 * t + 5), (7 * t + 5) * (t + 1),
    by omega, by omega, Nat.mul_pos (by omega) (by omega),
    key (by omega) (by omega) (by omega) (Nat.mul_pos (by omega) (by omega)) (by ring)⟩

/-- `n ≡ 6 (mod 7)`: `4/n = 1/(2(t+1)) + 1/(2n) + 1/(2n(t+1))` for `n = 7t+6`. -/
theorem es_mod7_6 (t : ℕ) : ES (7 * t + 6) :=
  ⟨2 * (t + 1), 2 * (7 * t + 6), 2 * ((7 * t + 6) * (t + 1)),
    by omega, by omega,
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    key (by omega) (by omega) (by omega)
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) (by ring)⟩

theorem nonresidueMod7 : ∀ n : ℕ, 2 ≤ n → (n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) → ES n := by
  intro n _ h7
  rcases h7 with h | h | h
  · obtain ⟨t, rfl⟩ : ∃ t, n = 7 * t + 3 := ⟨n / 7, by omega⟩
    exact es_mod7_3 t
  · obtain ⟨t, rfl⟩ : ∃ t, n = 7 * t + 5 := ⟨n / 7, by omega⟩
    exact es_mod7_5 t
  · obtain ⟨t, rfl⟩ : ∃ t, n = 7 * t + 6 := ⟨n / 7, by omega⟩
    exact es_mod7_6 t

theorem proof : ∀ n : ℕ, 2 ≤ n → (n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := nonresidueMod7

end Submissions.ErdosStrausNonresidueMod7.NonresidueMod7

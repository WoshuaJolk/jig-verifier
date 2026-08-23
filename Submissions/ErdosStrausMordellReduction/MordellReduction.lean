import Mathlib

/-! The Erdos-Straus conjecture is equivalent to its restriction to primes p with
p mod 840 the square of a unit: p = 1 mod 24, p a QR mod 5, p a QR mod 7.

Backward is specialisation. Forward: every n >= 2 has a prime factor p, a representation
of 4/p scales to 4/n, and every prime outside the restricted set falls to a congruence
identity: the classical coverage for p not 1 mod 24 (identities mod 2, 3, 4, 8 and the
40t+33 case), the identity family e*n = 4uv - u - v with e | uv for the nonresidue
classes 2 mod 5 (via 15t+7) and 3, 5, 6 mod 7, and the mod-40 identity for 3 mod 5.
The coverage lemmas below follow the ErdosStrausThreeMod5 submission (ThreeMod5.lean,
this repo); the mod-5 and mod-7 nonresidue identities are new here. -/

namespace Submissions.ErdosStrausMordellReduction.MordellReduction

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

theorem es_even (m : ℕ) (hm : 0 < m) : ES (2 * m) :=
  ⟨m, m + 1, m * (m + 1), hm, Nat.succ_pos m, Nat.mul_pos hm (Nat.succ_pos m),
    key (by omega) hm (Nat.succ_pos m) (Nat.mul_pos hm (Nat.succ_pos m)) (by ring)⟩

theorem es_mod3 (k : ℕ) : ES (3 * k + 2) :=
  ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega,
    Nat.mul_pos (by omega) (by omega),
    key (by omega) (by omega) (by omega) (Nat.mul_pos (by omega) (by omega)) (by ring)⟩

theorem es_mod4 (k : ℕ) : ES (4 * k + 3) :=
  ⟨k + 1, (4 * k + 3) * (k + 1) + 1,
    ((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1),
    by omega, by omega,
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega),
    key (by omega) (by omega) (by omega)
      (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by ring)⟩

theorem es_mod8 (m : ℕ) : ES (8 * m + 5) :=
  ⟨2 * (m + 1), (8 * m + 5) * (m + 1), 2 * ((8 * m + 5) * (m + 1)),
    by omega, Nat.mul_pos (by omega) (by omega),
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    key (by omega) (by omega) (Nat.mul_pos (by omega) (by omega))
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) (by ring)⟩

/-- `n ≡ 33 (mod 40)`: `4/n = 1/(10T) + 1/(5nT) + 1/(2nT)` with `T = (n+7)/40`. -/
theorem es_mod40 (t : ℕ) : ES (40 * t + 33) :=
  ⟨10 * (t + 1), 5 * ((40 * t + 33) * (t + 1)), 2 * ((40 * t + 33) * (t + 1)),
    by omega,
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    key (by omega) (by omega)
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) (by ring)⟩

/-- `n ≡ 7 (mod 15)`: `4/n = 1/(2(2t+1)) + 1/(4n) + 1/(4n(2t+1))` for `n = 15t+7`. -/
theorem es_mod15 (t : ℕ) : ES (15 * t + 7) :=
  ⟨2 * (2 * t + 1), 4 * (15 * t + 7), 4 * ((15 * t + 7) * (2 * t + 1)),
    by omega, by omega,
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)),
    key (by omega) (by omega) (by omega)
      (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) (by ring)⟩

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

theorem es_three : ES 3 :=
  ⟨1, 4, 12, by norm_num, by norm_num, by norm_num,
    key (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

theorem es_mul {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) (h : ES d) : ES n := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := h
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  refine ⟨k * x, k * y, k * z, Nat.mul_pos hk0 hx, Nat.mul_pos hk0 hy, Nat.mul_pos hk0 hz, ?_⟩
  push_cast
  rw [← div_div, hxyz]
  field_simp

/-- Everything outside `n ≡ 1 (mod 24)` is covered by the classical identities. -/
theorem coverage : ∀ n : ℕ, 2 ≤ n → n % 24 ≠ 1 → ES n := by
  intro n hn h24
  by_cases h2 : n % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    exact es_even m (by omega)
  by_cases h3 : n % 3 = 2
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    exact es_mod3 k
  by_cases h3' : n % 3 = 0
  · exact es_mul (by omega) (Nat.dvd_of_mod_eq_zero h3') es_three
  by_cases h4 : n % 4 = 3
  · obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    exact es_mod4 k
  by_cases h8 : n % 8 = 5
  · obtain ⟨m, rfl⟩ : ∃ m, n = 8 * m + 5 := ⟨n / 8, by omega⟩
    exact es_mod8 m
  · exact absurd (by omega : n % 24 = 1) h24

theorem twoModFive : ∀ n : ℕ, 2 ≤ n → n % 5 = 2 → ES n := by
  intro n hn h5
  by_cases h3 : n % 3 = 2
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    exact es_mod3 k
  by_cases h3' : n % 3 = 0
  · exact es_mul (by omega) (Nat.dvd_of_mod_eq_zero h3') es_three
  · obtain ⟨t, rfl⟩ : ∃ t, n = 15 * t + 7 := ⟨n / 15, by omega⟩
    exact es_mod15 t

theorem threeModFive : ∀ n : ℕ, 2 ≤ n → n % 5 = 3 → ES n := by
  intro n hn h5
  by_cases h24 : n % 24 = 1
  · obtain ⟨t, rfl⟩ : ∃ t, n = 40 * t + 33 := ⟨n / 40, by omega⟩
    exact es_mod40 t
  · exact coverage n hn h24

theorem nonresidueMod7 : ∀ n : ℕ, 2 ≤ n → (n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) → ES n := by
  intro n _ h7
  rcases h7 with h | h | h
  · obtain ⟨t, rfl⟩ : ∃ t, n = 7 * t + 3 := ⟨n / 7, by omega⟩
    exact es_mod7_3 t
  · obtain ⟨t, rfl⟩ : ∃ t, n = 7 * t + 5 := ⟨n / 7, by omega⟩
    exact es_mod7_5 t
  · obtain ⟨t, rfl⟩ : ∃ t, n = 7 * t + 6 := ⟨n / 7, by omega⟩
    exact es_mod7_6 t

/-- Every prime outside the restricted set is settled by a congruence identity. -/
theorem prime_outside {p : ℕ} (hp : p.Prime)
    (h : ¬(p % 24 = 1 ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4))) :
    ES p := by
  by_cases hp24 : p % 24 = 1
  · by_cases hp5 : p % 5 = 2
    · exact twoModFive p hp.two_le hp5
    by_cases hp5' : p % 5 = 3
    · exact threeModFive p hp.two_le hp5'
    by_cases hp50 : p % 5 = 0
    · rcases hp.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero hp50) with h5 | h5 <;> omega
    by_cases hp7 : p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6
    · exact nonresidueMod7 p hp.two_le hp7
    by_cases hp70 : p % 7 = 0
    · rcases hp.eq_one_or_self_of_dvd 7 (Nat.dvd_of_mod_eq_zero hp70) with h7 | h7 <;> omega
    · exact absurd ⟨hp24, by omega, by omega⟩ h
  · exact coverage p hp.two_le hp24

theorem equiv :
    (∀ p : ℕ, p.Prime → p % 24 = 1 → (p % 5 = 1 ∨ p % 5 = 4) →
        (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) → ES p) ↔
      (∀ n : ℕ, 2 ≤ n → ES n) := by
  constructor
  · intro H n hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    refine es_mul (by omega) hpn ?_
    by_cases h : p % 24 = 1 ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4)
    · exact H p hp h.1 h.2.1 h.2.2
    · exact prime_outside hp h
  · intro H p hp _ _ _
    exact H p hp.two_le

theorem proof :
    (∀ p : ℕ, p.Prime → p % 24 = 1 → (p % 5 = 1 ∨ p % 5 = 4) →
        (p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) →
        ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
          (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) ↔
      (∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
          (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) := equiv

end Submissions.ErdosStrausMordellReduction.MordellReduction

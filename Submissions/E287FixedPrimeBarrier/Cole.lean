import Mathlib.Tactic

namespace Submissions.E287FixedPrimeBarrier.Cole

theorem coprime_cancelled_denominator (L t : ℕ) (h : 1 ≤ L*t) :
    Nat.Coprime L (L*t-1) := by
  have hc : Nat.Coprime (L*t) (L*t-1) :=
    (Nat.coprime_self_sub_right h).mpr (Nat.coprime_one_right _)
  exact hc.of_dvd_left (dvd_mul_right L t)

theorem symmetric_pair (a t : ℚ) (ha : a ≠ 0)
    (hm : a^2*t-a ≠ 0) (hp : a^2*t+a ≠ 0)
    (hd : a^2*t^2-1 ≠ 0) :
    1/(a^2*t-a) + 1/(a^2*t+a) = 2*t/(a^2*t^2-1) := by
  have hm' : a*t-1 ≠ 0 := by
    intro h
    apply hm
    calc a^2*t-a = a*(a*t-1) := by ring
         _ = 0 := by rw [h, mul_zero]
  have hp' : a*t+1 ≠ 0 := by
    intro h
    apply hp
    calc a^2*t+a = a*(a*t+1) := by ring
         _ = 0 := by rw [h, mul_zero]
  field_simp [ha, hm', hp', hd]
  <;> ring

theorem sum_den_coprime {ι : Type*} (s : Finset ι) (f : ι → ℚ) (L : ℕ)
    (h : ∀ i ∈ s, Nat.Coprime L (f i).den) :
    Nat.Coprime L (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply ((h a (Finset.mem_insert_self _ _)).mul_right
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))).of_dvd_right
    exact Rat.add_den_dvd _ _

theorem fraction_den_coprime (u d L : ℕ) (h : Nat.Coprime L d) :
    Nat.Coprime L ((u : ℚ) / d).den := by
  apply h.of_dvd_right
  have hh := Rat.den_dvd (u : ℤ) (d : ℤ)
  simpa only [Rat.divInt_eq_div, Int.cast_natCast, Int.natCast_dvd_natCast] using hh

theorem natural_pair_coprime (L a : ℕ) (ha : 0 < a) (hL : a < L)
    (hdvd : a^2 ∣ L) :
    Nat.Coprime L (1 / ((L-a : ℕ) : ℚ) + 1 / ((L+a : ℕ) : ℚ)).den := by
  obtain ⟨t, ht⟩ := hdvd
  have htpos : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    simp [this] at ht
    omega
  have hprod : 1 < L*t := by nlinarith
  have heq : 1 / ((L-a : ℕ) : ℚ) + 1 / ((L+a : ℕ) : ℚ) =
      ((2*t : ℕ) : ℚ) / ((L*t-1 : ℕ) : ℚ) := by
    have hqa : (a : ℚ) ≠ 0 := by positivity
    have hqm : (L : ℚ) - a ≠ 0 := by exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hL))
    have hqp : (L : ℚ) + a ≠ 0 := by positivity
    have hqd : (L : ℚ)*t-1 ≠ 0 := by
      have : (1 : ℚ) < (L : ℚ)*t := by exact_mod_cast hprod
      linarith
    have hqt : (L : ℚ) = (a : ℚ)^2*t := by exact_mod_cast ht
    push_cast [Nat.cast_sub (Nat.le_of_lt hL), Nat.cast_sub (by omega : 1 ≤ L*t)]
    rw [hqt] at hqm hqp hqd ⊢
    convert symmetric_pair (a : ℚ) (t : ℚ) hqa hqm hqp
      (by simpa only [pow_two, mul_assoc] using hqd) using 1 <;> ring
  rw [heq]
  exact fraction_den_coprime _ _ _ (coprime_cancelled_denominator L t (by omega))

theorem symmetric_block_coprime (L m : ℕ) (hLm : m < L)
    (hdiv : ∀ a, 1 ≤ a → a ≤ m → a^2 ∣ L) :
    Nat.Coprime L
      (∑ a ∈ Finset.Icc 1 m,
        (1 / ((L-a : ℕ) : ℚ) + 1 / ((L+a : ℕ) : ℚ))).den := by
  apply sum_den_coprime
  intro a ha
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp ha
  exact natural_pair_coprime L a (by omega) (by omega) (hdiv a hlo hhi)

def center (m : ℕ) : ℕ := (m+2).factorial^2

theorem center_large (m : ℕ) : m+1 < center m := by
  have h := Nat.self_le_factorial (m+2)
  unfold center
  nlinarith

theorem square_dvd_center (m a : ℕ) (ha : 1 ≤ a) (ham : a ≤ m) :
    a^2 ∣ center m := by
  apply pow_dvd_pow_of_dvd
  exact Nat.dvd_factorial (by omega) (by omega)

theorem explicit_block_coprime (m : ℕ) :
    Nat.Coprime (center m)
      (∑ a ∈ Finset.Icc 1 m,
        (1 / ((center m-a : ℕ) : ℚ) + 1 / ((center m+a : ℕ) : ℚ))).den := by
  exact symmetric_block_coprime _ m (by have := center_large m; omega)
    (square_dvd_center m)

def sequence (L m i : ℕ) : ℕ := L-m+i + if i < m then 0 else 1

theorem sequence_strict (L m : ℕ) : StrictMono (sequence L m) := by
  intro i j hij
  unfold sequence
  split_ifs <;> omega

theorem sequence_step (L m i : ℕ) : sequence L m (i+1) - sequence L m i ≤ 2 := by
  unfold sequence
  split_ifs <;> omega

theorem sequence_first (m : ℕ) : 1 < sequence (center m) m 0 := by
  have := center_large m
  unfold sequence
  split_ifs <;> omega

theorem sequence_sum (L m : ℕ) (hLm : m ≤ L) :
    (∑ i ∈ Finset.range (2*m), 1 / (sequence L m i : ℚ)) =
      ∑ a ∈ Finset.Icc 1 m,
        (1 / ((L-a : ℕ) : ℚ) + 1 / ((L+a : ℕ) : ℚ)) := by
  rw [two_mul, Finset.sum_range_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_bij (fun i _ => m-i)
    · intro i hi
      simp only [Finset.mem_range] at hi
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi j hj heq
      simp only [Finset.mem_range] at hi hj
      omega
    · intro a ha
      obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
      exact ⟨m-a, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      have : sequence L m i = L-(m-i) := by
        unfold sequence
        rw [if_pos hi']
        omega
      rw [this]
  · apply Finset.sum_bij (fun i _ => i+1)
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi j hj heq
      omega
    · intro a ha
      obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
      exact ⟨a-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i hi
      have : sequence L m (m+i) = L+(i+1) := by
        unfold sequence
        rw [if_neg (by omega)]
        omega
      rw [this]

theorem fixed_prime_cutoff (m : ℕ) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ 1 < s 0 ∧
      (∀ i, s (i+1)-s i ≤ 2) ∧
      (∀ p, p.Prime → p ≤ m →
        ¬p ∣ (∑ i ∈ Finset.range (2*m), 1/(s i : ℚ)).den) := by
  refine ⟨sequence (center m) m, sequence_strict _ _, sequence_first m,
    sequence_step _ _, ?_⟩
  intro p hp hpm
  have hc := explicit_block_coprime m
  rw [← sequence_sum (center m) m (by have := center_large m; omega)] at hc
  have hd : p ∣ center m := by
    exact (dvd_pow_self p (by decide : 2 ≠ 0)).trans
      (square_dvd_center m p (by have := hp.two_le; omega) hpm)
  exact hp.coprime_iff_not_dvd.mp (hc.of_dvd_left hd)

theorem center_mass_bound (m : ℕ) : 3*m < center m := by
  have h := Nat.self_le_factorial (m+2)
  unfold center
  nlinarith

theorem constructed_sum_lt_one (m : ℕ) :
    (∑ i ∈ Finset.range (2*m), 1/(sequence (center m) m i : ℚ)) < 1 := by
  by_cases hm : m = 0
  · subst m
    norm_num
  have hmass := center_mass_bound m
  have hfirst : 2*m < sequence (center m) m 0 := by
    unfold sequence
    rw [if_pos (by omega)]
    omega
  have hbound : ∀ i ∈ Finset.range (2*m),
      1/(sequence (center m) m i : ℚ) < 1/(2*m : ℚ) := by
    intro i hi
    have hmono := (sequence_strict (center m) m).monotone (Nat.zero_le i)
    have hden : (2*m : ℚ) < (sequence (center m) m i : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le hfirst hmono)
    exact one_div_lt_one_div_of_lt (by positivity) hden
  have hs := Finset.sum_lt_sum_of_nonempty
    (Finset.nonempty_range_iff.mpr (by omega : 2*m ≠ 0)) hbound
  have hsum : (∑ _i ∈ Finset.range (2*m), (1/(2*m : ℚ))) = 1 := by
    simp
    field_simp
  linarith

theorem central_gap_exact (L m : ℕ) (hm : 1 ≤ m) :
    sequence L m m - sequence L m (m-1) = 2 := by
  unfold sequence
  rw [if_neg (by omega : ¬m < m), if_pos (by omega : m-1 < m)]
  omega

theorem proof : ∀ m : ℕ, 1 ≤ m → ∃ s : ℕ → ℕ,
  StrictMono s ∧ 1 < s 0 ∧
  (∀ i, s (i+1)-s i ≤ 2) ∧
  s m - s (m-1) = 2 ∧
  (∑ i ∈ Finset.range (2*m), 1/(s i : ℚ)) < 1 ∧
  (∀ p : ℕ, p.Prime → p ≤ m →
    ¬p ∣ (∑ i ∈ Finset.range (2*m), 1/(s i : ℚ)).den) := by
  intro m hm
  refine ⟨sequence (center m) m, sequence_strict _ _, sequence_first m,
    sequence_step _ _, central_gap_exact _ _ hm, constructed_sum_lt_one m, ?_⟩
  intro p hp hpm
  have hc := explicit_block_coprime m
  rw [← sequence_sum (center m) m (by have := center_large m; omega)] at hc
  have hd : p ∣ center m :=
    (dvd_pow_self p (by decide : 2 ≠ 0)).trans
      (square_dvd_center m p (by have := hp.two_le; omega) hpm)
  exact hp.coprime_iff_not_dvd.mp (hc.of_dvd_left hd)
end Submissions.E287FixedPrimeBarrier.Cole

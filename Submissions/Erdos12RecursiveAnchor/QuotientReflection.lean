import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos12RecursiveAnchor.QuotientReflection

private theorem anchor_dvd_pair
    (L r q u v : ℕ)
    (hsum : u + v = (r + L * q) / Nat.gcd L r) :
    r + L * q ∣ (r + L * (q + u)) + (r + L * (q + v)) := by
  let g := Nat.gcd L r
  let x := r + L * q
  have hgL : g ∣ L := Nat.gcd_dvd_left L r
  have hgr : g ∣ r := Nat.gcd_dvd_right L r
  have hgx : g ∣ x := by
    exact dvd_add hgr (dvd_mul_of_dvd_left hgL q)
  obtain ⟨ell, hL⟩ := hgL
  have hxrestore : x / g * g = x := Nat.div_mul_cancel hgx
  refine ⟨2 + ell, ?_⟩
  calc
    (r + L * (q + u)) + (r + L * (q + v))
        = 2 * x + L * (u + v) := by simp [x]; ring
    _ = 2 * x + L * (x / g) := by rw [hsum]
    _ = 2 * x + (g * ell) * (x / g) := by rw [hL]
    _ = 2 * x + ell * (x / g * g) := by ring
    _ = 2 * x + ell * x := by rw [hxrestore]
    _ = x * (2 + ell) := by ring

/-- Inside one residue progression `r + L*q`, a fresh element at quotient `q`
becomes a reflection anchor of modulus `(r + L*q) / gcd(L,r)` on later
quotients.  Consequently at most half that many quotient indices fit in its
first quotient window. -/
theorem proof :
    ∀ (A : Set ℕ) (L r q : ℕ) (Q : Finset ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      0 < L →
      r + L * q ∈ A →
      (∀ s ∈ Q,
        r + L * s ∈ A ∧ q < s ∧
          s < q + (r + L * q) / Nat.gcd L r) →
      Q.card ≤ ((r + L * q) / Nat.gcd L r) / 2 := by
  intro A L r q Q hP hL hx hQ
  let m := (r + L * q) / Nat.gcd L r
  let f : ℕ → ℕ := fun s ↦ min (s - q) (m - (s - q))
  have hf_maps : Q.image f ⊆ Finset.Ioc 0 (m / 2) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨_, hqs, hsm⟩ := hQ s hs
    have hu_pos : 0 < s - q := by omega
    have hu_lt : s - q < m := by simpa [m] using (show s - q <
        (r + L * q) / Nat.gcd L r by omega)
    have href_pos : 0 < m - (s - q) := by omega
    have hupper : min (s - q) (m - (s - q)) ≤ m / 2 := by
      rcases le_total (s - q) (m - (s - q)) with h | h
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right h]
        omega
    exact Finset.mem_Ioc.mpr ⟨lt_min hu_pos href_pos, hupper⟩
  have hf_inj : Set.InjOn f Q := by
    intro s hs t ht hst
    obtain ⟨hsA, hqs, hsm⟩ := hQ s hs
    obtain ⟨htA, hqt, htm⟩ := hQ t ht
    dsimp [f] at hst
    by_cases hsside : s - q ≤ m - (s - q)
    · rw [min_eq_left hsside] at hst
      by_cases htside : t - q ≤ m - (t - q)
      · rw [min_eq_left htside] at hst
        omega
      · rw [min_eq_right (Nat.le_of_not_ge htside)] at hst
        have huv : (s - q) + (t - q) = m := by omega
        have hdvd :
            r + L * q ∣ (r + L * s) + (r + L * t) := by
          have hsrepr : q + (s - q) = s := by omega
          have htrepr : q + (t - q) = t := by omega
          rw [← hsrepr, ← htrepr]
          exact anchor_dvd_pair L r q (s - q) (t - q) (by simpa [m] using huv)
        have hxs : r + L * q < r + L * s := by
          exact Nat.add_lt_add_left ((Nat.mul_lt_mul_left hL).2 hqs) r
        have hxt : r + L * q < r + L * t := by
          exact Nat.add_lt_add_left ((Nat.mul_lt_mul_left hL).2 hqt) r
        have heq := hP (r + L * q) hx (r + L * s) hsA
          (r + L * t) htA hdvd hxs hxt
        have hmul : L * s = L * t := Nat.add_left_cancel heq
        exact Nat.eq_of_mul_eq_mul_left hL hmul
    · rw [min_eq_right (Nat.le_of_not_ge hsside)] at hst
      by_cases htside : t - q ≤ m - (t - q)
      · rw [min_eq_left htside] at hst
        have huv : (s - q) + (t - q) = m := by omega
        have hdvd :
            r + L * q ∣ (r + L * s) + (r + L * t) := by
          have hsrepr : q + (s - q) = s := by omega
          have htrepr : q + (t - q) = t := by omega
          rw [← hsrepr, ← htrepr]
          exact anchor_dvd_pair L r q (s - q) (t - q) (by simpa [m] using huv)
        have hxs : r + L * q < r + L * s := by
          exact Nat.add_lt_add_left ((Nat.mul_lt_mul_left hL).2 hqs) r
        have hxt : r + L * q < r + L * t := by
          exact Nat.add_lt_add_left ((Nat.mul_lt_mul_left hL).2 hqt) r
        have heq := hP (r + L * q) hx (r + L * s) hsA
          (r + L * t) htA hdvd hxs hxt
        have hmul : L * s = L * t := Nat.add_left_cancel heq
        exact Nat.eq_of_mul_eq_mul_left hL hmul
      · rw [min_eq_right (Nat.le_of_not_ge htside)] at hst
        omega
  calc
    Q.card = (Q.image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (Finset.Ioc 0 (m / 2)).card := Finset.card_le_card hf_maps
    _ = m / 2 := by simp
    _ = ((r + L * q) / Nat.gcd L r) / 2 := rfl

end Submissions.Erdos12RecursiveAnchor.QuotientReflection

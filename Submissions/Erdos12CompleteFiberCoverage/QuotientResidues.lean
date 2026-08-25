import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic

namespace Submissions.Erdos12CompleteFiberCoverage.QuotientResidues

private theorem anchor_dvd_pair
    (L r q u v : ℕ)
    (hm : (r + L * q) / Nat.gcd L r ∣ u + v) :
    r + L * q ∣ (r + L * (q + u)) + (r + L * (q + v)) := by
  let g := Nat.gcd L r
  let x := r + L * q
  have hgL : g ∣ L := Nat.gcd_dvd_left L r
  have hgr : g ∣ r := Nat.gcd_dvd_right L r
  have hgx : g ∣ x := dvd_add hgr (dvd_mul_of_dvd_left hgL q)
  obtain ⟨ell, hL⟩ := hgL
  obtain ⟨k, huv⟩ := hm
  have hxrestore : x / g * g = x := Nat.div_mul_cancel hgx
  refine ⟨2 + ell * k, ?_⟩
  calc
    (r + L * (q + u)) + (r + L * (q + v))
        = 2 * x + L * (u + v) := by simp [x]; ring
    _ = 2 * x + L * ((x / g) * k) := by rw [huv]
    _ = 2 * x + (g * ell) * ((x / g) * k) := by rw [hL]
    _ = 2 * x + (x / g * g) * (ell * k) := by ring
    _ = 2 * x + x * (ell * k) := by rw [hxrestore]
    _ = x * (2 + ell * k) := by ring

/-- The recursive-anchor condition is a complete-fiber exclusion: for a fresh
anchor at quotient `q`, any two later quotient differences whose sum is
divisible by `m = (r+Lq)/gcd(L,r)` must come from the same progression point.
The other residue coordinates are irrelevant. -/
theorem proof :
    ∀ (A : Set ℕ) (L r q s t : ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      0 < L →
      r + L * q ∈ A →
      r + L * s ∈ A →
      r + L * t ∈ A →
      q < s →
      q < t →
      (r + L * q) / Nat.gcd L r ∣ (s - q) + (t - q) →
      s = t := by
  intro A L r q s t hP hL hq hs ht hqs hqt hdvd
  have hsrepr : q + (s - q) = s := by omega
  have htrepr : q + (t - q) = t := by omega
  have hanchor :
      r + L * q ∣ (r + L * s) + (r + L * t) := by
    rw [← hsrepr, ← htrepr]
    exact anchor_dvd_pair L r q (s - q) (t - q) hdvd
  have hxs : r + L * q < r + L * s := by
    exact Nat.add_lt_add_left ((Nat.mul_lt_mul_left hL).2 hqs) r
  have hxt : r + L * q < r + L * t := by
    exact Nat.add_lt_add_left ((Nat.mul_lt_mul_left hL).2 hqt) r
  have heq := hP (r + L * q) hq (r + L * s) hs
    (r + L * t) ht hanchor hxs hxt
  have hmul : L * s = L * t := Nat.add_left_cancel heq
  exact Nat.eq_of_mul_eq_mul_left hL hmul

end Submissions.Erdos12CompleteFiberCoverage.QuotientResidues

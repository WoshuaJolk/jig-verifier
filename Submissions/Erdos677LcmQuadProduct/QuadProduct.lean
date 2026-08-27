import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
/-!
# Closed form for the least common multiple of four consecutive integers

`2 * gcd(n+1,3) * lcm(n+1,n+2,n+3,n+4) = (n+1)(n+2)(n+3)(n+4)`.

The correction factor is `2 * gcd(a,3)`: the prime 2 always contributes exactly
one, because of the two even members one is `2 mod 4`; the prime 3 contributes
one exactly when `3 | a`, because then `a` and `a+3` are both multiples of 3 and
one of them is exactly divisible by 3.  Formally: split the block into the pairs
`(a, a+2)` and `(a+1, a+3)`, use `gcd * lcm = product` on each, and compute
`gcd(lcm(a,a+2), lcm(a+1,a+3)) = gcd(a,3)` through
`gcd(a(a+2), (a+1)(a+3)) = gcd(3, 2a+5) = gcd(a,3)`.
-/

namespace Submissions.Erdos677LcmQuadProduct.QuadProduct
def lcmInterval (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

lemma gcd_two_eq (x : ℕ) : Nat.gcd x 2 = if x % 2 = 0 then 2 else 1 := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

lemma ioc4 (n : ℕ) : Finset.Ioc n (n+4) = {n+1, n+2, n+3, n+4} := by
  ext x; simp [Finset.mem_Ioc]; omega

lemma split (n : ℕ) :
    lcmInterval n 4 = Nat.lcm (Nat.lcm (n+1) (n+3)) (Nat.lcm (n+2) (n+4)) := by
  unfold lcmInterval
  rw [ioc4]
  simp only [Finset.lcm_insert, Finset.lcm_singleton, id_eq, normalize_eq]
  show Nat.lcm (n+1) (Nat.lcm (n+2) (Nat.lcm (n+3) (n+4)))
      = Nat.lcm (Nat.lcm (n+1) (n+3)) (Nat.lcm (n+2) (n+4))
  rw [Nat.lcm_assoc]
  congr 1
  rw [← Nat.lcm_assoc, ← Nat.lcm_assoc, Nat.lcm_comm (n+2) (n+3)]

lemma prodX (n : ℕ) :
    Nat.gcd ((n+1)*(n+3)) ((n+2)*(n+4)) = Nat.gcd (n+1) 3 := by
  have h : (n+2)*(n+4) = (2*n+5) + 1*((n+1)*(n+3)) := by ring
  rw [h, Nat.gcd_add_mul_right_right]
  set X := (n+1)*(n+3) with hX
  set g := Nat.gcd X (2*n+5) with hg
  have h4 : 4 * X + 3 = (2*n+3) * (2*n+5) := by rw [hX]; ring
  have hA : g ∣ 4 * X := Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 4
  have hB : g ∣ 4 * X + 3 := by rw [h4]; exact Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
  have g3 : g ∣ 3 := (Nat.dvd_add_right hA).mp hB
  have g25 : g ∣ 2*n+5 := Nat.gcd_dvd_right _ _
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd ?_ g3
    rcases (Nat.dvd_prime Nat.prime_three).1 g3 with h1 | h1
    · rw [h1]; exact one_dvd _
    · -- g = 3, and 3 ∣ 2n+5 forces 3 ∣ n+1
      rw [h1] at g25 ⊢
      obtain ⟨c, hc⟩ := g25
      exact ⟨(n+1)/3, by omega⟩
  · have d1 : Nat.gcd (n+1) 3 ∣ X := by rw [hX]; exact (Nat.gcd_dvd_left _ _).mul_right _
    have d2 : Nat.gcd (n+1) 3 ∣ 2*n+5 := by
      have e1 : Nat.gcd (n+1) 3 ∣ 2*(n+1) := (Nat.gcd_dvd_left _ _).mul_left 2
      have e2 : Nat.gcd (n+1) 3 ∣ 3 := Nat.gcd_dvd_right _ _
      have : 2*n+5 = 2*(n+1) + 3 := by ring
      rw [this]; exact Nat.dvd_add e1 e2
    exact Nat.dvd_gcd d1 d2

lemma gcdAC (n : ℕ) : Nat.gcd (n+1) (n+3) = Nat.gcd (n+1) 2 := by
  rw [show n+3 = 2 + 1*(n+1) by ring, Nat.gcd_add_mul_right_right]

lemma gcdBD (n : ℕ) : Nat.gcd (n+2) (n+4) = Nat.gcd (n+2) 2 := by
  rw [show n+4 = 2 + 1*(n+2) by ring, Nat.gcd_add_mul_right_right]

theorem proof :
    ∀ n : ℕ,
      2 * Nat.gcd (n+1) 3 * lcmInterval n 4 = (n+1)*(n+2)*(n+3)*(n+4) := by
  intro n
  have hP : Nat.gcd (n+1) 2 * Nat.lcm (n+1) (n+3) = (n+1)*(n+3) := by
    rw [← gcdAC]; exact Nat.gcd_mul_lcm _ _
  have hQ : Nat.gcd (n+2) 2 * Nat.lcm (n+2) (n+4) = (n+2)*(n+4) := by
    rw [← gcdBD]; exact Nat.gcd_mul_lcm _ _
  have hg2 : Nat.gcd (n+1) 2 * Nat.gcd (n+2) 2 = 2 := by
    rw [gcd_two_eq, gcd_two_eq]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [Nat.add_mod, h]
  have hPQ : Nat.gcd (Nat.lcm (n+1) (n+3)) (Nat.lcm (n+2) (n+4)) = Nat.gcd (n+1) 3 := by
    apply Nat.dvd_antisymm
    · have dP : Nat.lcm (n+1) (n+3) ∣ (n+1)*(n+3) :=
        Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
      have dQ : Nat.lcm (n+2) (n+4) ∣ (n+2)*(n+4) :=
        Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
      rw [← prodX n]
      exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans dP) ((Nat.gcd_dvd_right _ _).trans dQ)
    · refine Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.dvd_lcm_left _ _)) ?_
      rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_right (n+1) 3) with h1 | h1
      · rw [h1]; exact one_dvd _
      · rw [h1]
        have h3 : (3:ℕ) ∣ n+1 := h1 ▸ Nat.gcd_dvd_left (n+1) 3
        obtain ⟨c, hc⟩ := h3
        exact dvd_trans ⟨c+1, by omega⟩ (Nat.dvd_lcm_right (n+2) (n+4))
  have hmain := Nat.gcd_mul_lcm (Nat.lcm (n+1) (n+3)) (Nat.lcm (n+2) (n+4))
  rw [hPQ] at hmain
  rw [split, mul_assoc, hmain]
  calc 2 * (Nat.lcm (n+1) (n+3) * Nat.lcm (n+2) (n+4))
      = (Nat.gcd (n+1) 2 * Nat.gcd (n+2) 2) * (Nat.lcm (n+1) (n+3) * Nat.lcm (n+2) (n+4)) := by
        rw [hg2]
    _ = (Nat.gcd (n+1) 2 * Nat.lcm (n+1) (n+3)) * (Nat.gcd (n+2) 2 * Nat.lcm (n+2) (n+4)) := by
        ring
    _ = ((n+1)*(n+3)) * ((n+2)*(n+4)) := by rw [hP, hQ]
    _ = (n+1)*(n+2)*(n+3)*(n+4) := by ring



end Submissions.Erdos677LcmQuadProduct.QuadProduct

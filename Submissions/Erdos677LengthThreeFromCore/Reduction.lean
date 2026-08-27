import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# The length-three case of Erdős 677 reduces to a single cubic equation

Write `M(n,k) = lcm(n+1, ..., n+k)`.  Since
`gcd(a,2) * lcm(a, a+1, a+2) = a(a+1)(a+2)`, an equality `M(m,3) = M(n,3)` with
`n + 3 ≤ m` forces

  `gcd(m+1,2) * (n+1)(n+2)(n+3) = gcd(n+1,2) * (m+1)(m+2)(m+3)`.

Each gcd is `1` or `2`.  Three of the four sign patterns contradict the strict
monotonicity of `x ↦ (x+1)(x+2)(x+3)`.  The surviving one — `n+1` odd, `m+1`
even — says `(m+1)(m+2)(m+3) = 2(n+1)(n+2)(n+3)`, i.e. with `u = n+2`, `v = m+2`

  `v³ - v = 2(u³ - u)`,   `v ≥ u + 3`.
-/

namespace Submissions.Erdos677LengthThreeFromCore.Reduction

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

private lemma ioc3 (n : ℕ) : Finset.Ioc n (n + 3) = {n + 1, n + 2, n + 3} := by
  ext x; simp [Finset.mem_Ioc]; omega

private lemma cop (a : ℕ) : Nat.Coprime a (a + 1) := by simp [Nat.Coprime]

private lemma li3 (n : ℕ) :
    lcmInterval n 3 = Nat.lcm (n + 1) ((n + 2) * (n + 3)) := by
  unfold lcmInterval
  rw [ioc3]
  simp only [Finset.lcm_insert, Finset.lcm_singleton, id_eq, normalize_eq]
  have h : Nat.lcm (n + 2) (n + 3) = (n + 2) * (n + 3) :=
    Nat.Coprime.lcm_eq_mul (cop (n + 2))
  show Nat.lcm (n + 1) (Nat.lcm (n + 2) (n + 3)) = Nat.lcm (n + 1) ((n + 2) * (n + 3))
  rw [h]

private lemma gcd3 (n : ℕ) :
    Nat.gcd (n + 1) ((n + 2) * (n + 3)) = Nat.gcd (n + 1) 2 := by
  have h1 : Nat.Coprime (n + 2) (n + 1) := (cop (n + 1)).symm
  calc Nat.gcd (n + 1) ((n + 2) * (n + 3))
      = Nat.gcd ((n + 2) * (n + 3)) (n + 1) := Nat.gcd_comm _ _
    _ = Nat.gcd (n + 3) (n + 1) := Nat.Coprime.gcd_mul_left_cancel (n + 3) h1
    _ = Nat.gcd (n + 1) (n + 3) := Nat.gcd_comm _ _
    _ = Nat.gcd (n + 1) 2 := by
          rw [show n + 3 = 2 + 1 * (n + 1) by ring, Nat.gcd_add_mul_right_right]

private lemma lcm_triple (n : ℕ) :
    Nat.gcd (n + 1) 2 * lcmInterval n 3 = (n + 1) * (n + 2) * (n + 3) := by
  rw [li3, ← gcd3, Nat.gcd_mul_lcm]; ring

private lemma gcd_two (k : ℕ) : Nat.gcd (k + 1) 2 = 1 ∨ Nat.gcd (k + 1) 2 = 2 :=
  (Nat.dvd_prime Nat.prime_two).1 (Nat.gcd_dvd_right _ _)

private lemma prod_lt {n m : ℕ} (h : n < m) :
    (n + 1) * (n + 2) * (n + 3) < (m + 1) * (m + 2) * (m + 3) :=
  Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (by omega) (by omega)) (by omega)

theorem proof :
    (∀ u v : ℕ, u + 3 ≤ v → v ^ 3 + 2 * u ≠ 2 * u ^ 3 + v) →
      ∀ m n : ℕ, n + 3 ≤ m → lcmInterval m 3 ≠ lcmInterval n 3 := by
  intro H m n hmn heq
  have hn := lcm_triple n
  have hm := lcm_triple m
  rw [heq] at hm
  have key : Nat.gcd (m + 1) 2 * ((n + 1) * (n + 2) * (n + 3))
      = Nat.gcd (n + 1) 2 * ((m + 1) * (m + 2) * (m + 3)) := by
    rw [← hn, ← hm]; ring
  have hA : (n + 1) * (n + 2) * (n + 3) + (n + 2) = (n + 2) ^ 3 := by ring
  have hB : (m + 1) * (m + 2) * (m + 3) + (m + 2) = (m + 2) ^ 3 := by ring
  rcases gcd_two n with gn | gn <;> rcases gcd_two m with gm | gm <;>
    rw [gn, gm] at key
  · have := prod_lt (n := n) (m := m) (by omega); omega
  · exact H (n + 2) (m + 2) (by omega) (by linarith [key, hA, hB])
  · have := prod_lt (n := n) (m := m) (by omega); omega
  · have := prod_lt (n := n) (m := m) (by omega); omega

end Submissions.Erdos677LengthThreeFromCore.Reduction

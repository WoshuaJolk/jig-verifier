import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Closed form for the least common multiple of three consecutive integers

`gcd(n+1, 2) * lcm(n+1, n+2, n+3) = (n+1)(n+2)(n+3)`.

Equivalently `lcm(a, a+1, a+2) = a(a+1)(a+2) / gcd(a,2)`.  The proof is the
gcd-lcm identity together with `gcd(a, (a+1)(a+2)) = gcd(a, 2)`, which holds
because `a` is coprime to `a+1` and `a + 2 = 2 + 1 * a`.
-/

namespace Submissions.Erdos677LcmTripleProduct.TripleProduct

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

theorem proof :
    ∀ n : ℕ, Nat.gcd (n + 1) 2 * lcmInterval n 3 = (n + 1) * (n + 2) * (n + 3) := by
  intro n
  rw [li3, ← gcd3, Nat.gcd_mul_lcm]; ring

end Submissions.Erdos677LcmTripleProduct.TripleProduct

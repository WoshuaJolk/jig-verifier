import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Submissions.Erdos18FiniteShiftCRTBarrier.Direct

theorem proof :
    ∀ k h : ℕ, ∃ A : ℕ, h ≤ A ∧
      ∀ i : ℕ, i < h →
        ∃ p : ℕ,
          p.Prime ∧
          k < p ∧
          p ∣ A - i ∧
          ¬(A - i ∣ k.factorial) := by
  intro k h
  let primeAt : ℕ → ℕ := fun i => Nat.nth Nat.Prime (k + i)
  have hpprime (i : ℕ) : (primeAt i).Prime := by
    exact Nat.prime_nth_prime (k + i)
  have hpgt (i : ℕ) : k < primeAt i := by
    have := Nat.add_two_le_nth_prime (k + i)
    dsimp [primeAt]
    omega
  have hcop :
      (List.range h).Pairwise
        (fun a b => Nat.Coprime (primeAt a) (primeAt b)) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_range] at hi hj
    simp only [List.getElem_range]
    rw [Nat.coprime_primes (hpprime i) (hpprime j)]
    exact ne_of_lt
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (by omega))
  let C : ℕ :=
    Nat.chineseRemainderOfList id primeAt (List.range h) hcop
  let P : ℕ := ((List.range h).map primeAt).prod
  let A : ℕ := C + P * h
  have hPne : P ≠ 0 := by
    dsimp [P]
    apply List.prod_ne_zero
    intro hz
    simp only [List.mem_map] at hz
    obtain ⟨i, hi, heq⟩ := hz
    exact (hpprime i).ne_zero heq
  have hPpos : 0 < P := Nat.pos_of_ne_zero hPne
  have hhA : h ≤ A := by
    dsimp [A]
    have : h ≤ P * h := Nat.le_mul_of_pos_left h hPpos
    omega
  refine ⟨A, hhA, ?_⟩
  intro i hi
  let p := primeAt i
  have hip : i ∈ List.range h := List.mem_range.mpr hi
  have hCmod : C ≡ i [MOD p] := by
    exact (Nat.chineseRemainderOfList id primeAt (List.range h) hcop).prop i hip
  have hpP : p ∣ P := by
    dsimp [p, P]
    apply List.dvd_prod
    exact List.mem_map.mpr ⟨i, hip, rfl⟩
  have hPmod : P ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hpP
  have hAmod : A ≡ i [MOD p] := by
    have := hCmod.add (hPmod.mul_right h)
    simpa [A] using this
  have hiA : i ≤ A := hi.le.trans hhA
  have hpdiff : p ∣ A - i :=
    (Nat.modEq_iff_dvd' hiA).mp hAmod.symm
  refine ⟨p, hpprime i, hpgt i, hpdiff, ?_⟩
  intro hdvd
  have hpfact : p ∣ k.factorial := hpdiff.trans hdvd
  have hple : p ≤ k := (hpprime i).dvd_factorial.mp hpfact
  exact (not_le_of_gt (hpgt i)) hple

end Submissions.Erdos18FiniteShiftCRTBarrier.Direct

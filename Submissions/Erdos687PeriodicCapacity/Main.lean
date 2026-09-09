import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
A finite ingredient for the critical-survivor approach to Erdős 687.
The injection is the elementary coprime-moduli counting argument; the final
inequality is a union bound. No asymptotic survivor lower bound is assumed proved.
-/

namespace Submissions.Erdos687PeriodicCapacity.Main

open scoped BigOperators

theorem class_capacity (L M p a : ℕ) (A S : Finset ℕ)
    (hS : ∀ m ∈ S, m ≤ L ∧ m % M ∈ A) (hcop : M.Coprime p) :
    (S.filter (fun m => m % p = a % p)).card ≤
      A.card * (L / (M * p) + 1) := by
  let T := S.filter (fun m => m % p = a % p)
  have hcard : T.card ≤ (A ×ˢ Finset.range (L / (M * p) + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun m : ℕ => (m % M, m / (M * p)))
    · intro m hm
      have hmS : m ∈ S := (Finset.mem_filter.mp hm).1
      apply Finset.mem_product.mpr
      exact ⟨(hS m hmS).2, Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.div_le_div_right (hS m hmS).1))⟩
    · intro m hm n hn heq
      have hmS := Finset.mem_filter.mp hm
      have hnS := Finset.mem_filter.mp hn
      have hM : m % M = n % M := congrArg Prod.fst heq
      have hdiv : m / (M * p) = n / (M * p) := congrArg Prod.snd heq
      have hp : m % p = n % p := hmS.2.trans hnS.2.symm
      have hmod : m % (M * p) = n % (M * p) :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hM, hp⟩
      calc
        m = m % (M * p) + M * p * (m / (M * p)) :=
          (Nat.mod_add_div m (M * p)).symm
        _ = n % (M * p) + M * p * (n / (M * p)) := by rw [hmod, hdiv]
        _ = n := Nat.mod_add_div n (M * p)
  simpa [T, Finset.card_product] using hcard

theorem proof (L M : ℕ) (A S P : Finset ℕ) (residue : ℕ → ℕ)
    (hS : ∀ m ∈ S, m ≤ L ∧ m % M ∈ A)
    (hcop : ∀ p ∈ P, M.Coprime p)
    (hcover : ∀ m ∈ S, ∃ p ∈ P, m % p = residue p % p) :
    S.card ≤ A.card * ∑ p ∈ P, (L / (M * p) + 1) := by
  have hsub : S ⊆ P.biUnion (fun p => S.filter (fun m => m % p = residue p % p)) := by
    intro m hm
    obtain ⟨p, hp, hmp⟩ := hcover m hm
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hm, hmp⟩⟩
  calc
    S.card ≤ (P.biUnion (fun p => S.filter (fun m => m % p = residue p % p))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (S.filter (fun m => m % p = residue p % p)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P, A.card * (L / (M * p) + 1) :=
      Finset.sum_le_sum (fun p hp => class_capacity L M p (residue p) A S hS (hcop p hp))
    _ = A.card * ∑ p ∈ P, (L / (M * p) + 1) := (Finset.mul_sum P _ _).symm

noncomputable def survivors (L z : ℕ) (residue : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (L + 1)).filter (fun m => 0 < m ∧
    ∀ p ∈ (Finset.range (z + 1)).filter Nat.Prime, m % p ≠ residue p % p)

theorem mem_survivors {L z m : ℕ} {residue : ℕ → ℕ} :
    m ∈ survivors L z residue ↔ m ∈ Finset.range (L + 1) ∧ 0 < m ∧
      ∀ p ∈ (Finset.range (z + 1)).filter Nat.Prime, m % p ≠ residue p % p := by
  simp only [survivors, Finset.mem_filter]

def tailPrimes (X z : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun p => p.Prime ∧ z < p)

/-- Apply the finite estimate to the root's exact one-class-per-prime cover. -/
theorem covering_capacity (X L z M : ℕ) (A : Finset ℕ) (residue : ℕ → ℕ)
    (hcover : ∀ m : ℕ, 1 ≤ m → m ≤ L →
      ∃ p : ℕ, p.Prime ∧ p ≤ X ∧ m % p = residue p % p)
    (hcop : ∀ p ∈ tailPrimes X z, M.Coprime p)
    (hA : ∀ m ∈ survivors L z residue, m % M ∈ A) :
    (survivors L z residue).card ≤
      A.card * ∑ p ∈ tailPrimes X z, (L / (M * p) + 1) := by
  apply proof L M A (survivors L z residue) (tailPrimes X z) residue
  · intro m hm
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp (mem_survivors.mp hm).1), hA m hm⟩
  · exact hcop
  · intro m hm
    have hm' := mem_survivors.mp hm
    have hmL : m ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hm'.1)
    obtain ⟨p, hp, hpX, hmp⟩ := hcover m hm'.2.1 hmL
    have hzp : z < p := Nat.lt_of_not_ge (fun hpz =>
      hm'.2.2 p (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpz), hp⟩) hmp)
    exact ⟨p, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpX), hp, hzp⟩, hmp⟩

/-- Uniform loss from adding the remaining prime classes, without a cover assumption. -/
theorem survivor_loss (X L z M : ℕ) (A : Finset ℕ) (residue : ℕ → ℕ)
    (hcop : ∀ p ∈ tailPrimes X z, M.Coprime p)
    (hA : ∀ m ∈ survivors L z residue, m % M ∈ A) :
    (survivors L z residue).card ≤ (survivors L X residue).card +
      A.card * ∑ p ∈ tailPrimes X z, (L / (M * p) + 1) := by
  classical
  let T := (survivors L z residue).filter
    (fun m => ∃ p ∈ tailPrimes X z, m % p = residue p % p)
  have hT : T.card ≤ A.card * ∑ p ∈ tailPrimes X z, (L / (M * p) + 1) := by
    apply proof L M A T (tailPrimes X z) residue
    · intro m hm
      have hmS := (Finset.mem_filter.mp hm).1
      exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp (mem_survivors.mp hmS).1),
        hA m hmS⟩
    · exact hcop
    · intro m hm
      exact (Finset.mem_filter.mp hm).2
  have hsub : survivors L z residue ⊆ survivors L X residue ∪ T := by
    intro m hm
    by_cases hmT : m ∈ T
    · exact Finset.mem_union.mpr (Or.inr hmT)
    · apply Finset.mem_union.mpr
      left
      have hm' := mem_survivors.mp hm
      apply mem_survivors.mpr
      refine ⟨hm'.1, hm'.2.1, ?_⟩
      intro p hp hmp
      have hp' := Finset.mem_filter.mp hp
      by_cases hpz : p ≤ z
      · exact hm'.2.2 p (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpz), hp'.2⟩) hmp
      · apply hmT
        exact Finset.mem_filter.mpr ⟨hm, p,
          Finset.mem_filter.mpr ⟨hp'.1, hp'.2, Nat.lt_of_not_ge hpz⟩, hmp⟩
  calc
    (survivors L z residue).card ≤ (survivors L X residue ∪ T).card :=
      Finset.card_le_card hsub
    _ ≤ (survivors L X residue).card + T.card := Finset.card_union_le _ _
    _ ≤ (survivors L X residue).card +
        A.card * ∑ p ∈ tailPrimes X z, (L / (M * p) + 1) := Nat.add_le_add_left hT _

#print axioms proof
#print axioms covering_capacity
#print axioms survivor_loss

-- Sharp coprime case: the odd numbers congruent to 1 modulo 3 up to 10.
example : ({1, 7} : Finset ℕ).card ≤
    ({1} : Finset ℕ).card * (10 / (2 * 3) + 1) := by
  have h := class_capacity 10 2 3 1 {1} {1, 7} (by decide) (by decide)
  simpa using h

-- Coprimality is essential; the same estimate fails for M = p = 2.
example : (∀ m ∈ ({2, 4, 6} : Finset ℕ), m ≤ 6 ∧ m % 2 ∈ ({0} : Finset ℕ)) ∧
    (∀ m ∈ ({2, 4, 6} : Finset ℕ), m % 2 = 0 % 2) ∧
    ¬ Nat.Coprime 2 2 ∧
    ¬ (({2, 4, 6} : Finset ℕ).card ≤
      ({0} : Finset ℕ).card * (6 / (2 * 2) + 1)) := by decide

end Submissions.Erdos687PeriodicCapacity.Main

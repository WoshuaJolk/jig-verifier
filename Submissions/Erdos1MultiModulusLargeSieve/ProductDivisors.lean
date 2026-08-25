import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos1MultiModulusLargeSieve.ProductDivisors

private theorem card_diag {α : Type*} [DecidableEq α] (B : Finset α) :
    ((B.product B).filter fun p => p.1 = p.2).card = B.card := by
  rw [show ((B.product B).filter fun p => p.1 = p.2) =
      B.image (fun x => (x, x)) by
    ext p
    constructor
    · intro hp
      obtain ⟨hpB, hpEq⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp₁, _⟩ := Finset.mem_product.mp hpB
      exact Finset.mem_image.mpr ⟨p.1, hp₁, by
        ext
        · rfl
        · exact hpEq⟩
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩]
  rw [Finset.card_image_of_injective]
  intro x y h
  exact congrArg Prod.fst h

private theorem card_offdiag {α : Type*} [DecidableEq α] (B : Finset α) :
    ((B.product B).filter fun p => p.1 ≠ p.2).card =
      B.card * (B.card - 1) := by
  rw [show ((B.product B).filter fun p => p.1 ≠ p.2) =
      (B.product B) \ ((B.product B).filter fun p => p.1 = p.2) by
    ext p
    by_cases h₁ : p.1 ∈ B <;> by_cases h₂ : p.2 ∈ B <;> simp [h₁, h₂]]
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  have hcardprod : (B.product B).card = B.card * B.card := by
    simpa using Finset.card_product B B
  rw [hcardprod, card_diag]
  calc
    B.card * B.card - B.card =
        B.card * B.card - B.card * 1 := by simp
    _ = B.card * (B.card - 1) := (Nat.mul_sub_left_distrib _ _ _).symm

private theorem mod_eq_iff_dvd_dist (q a b : ℕ) :
    a % q = b % q ↔ q ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact Nat.modEq_iff_dvd' hab
  · rw [Nat.dist_eq_sub_of_le_right hba, eq_comm]
    exact Nat.modEq_iff_dvd' hba

private theorem collision_sum_bound
    {α : Type*} [DecidableEq α] (B : Finset α) (f : α → ℕ)
    (P : Finset ℕ) (L : ℕ)
    (hdiv : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      (P.filter fun q => q ∣ Nat.dist (f x) (f y)).card ≤ L) :
    ∑ q ∈ P,
        ((B.product B).filter fun p => f p.1 % q = f p.2 % q).card ≤
      P.card * B.card + L * (B.card * (B.card - 1)) := by
  classical
  let D := (B.product B).filter fun p => p.1 = p.2
  let O := (B.product B).filter fun p => p.1 ≠ p.2
  have hdiag : D.card = B.card := card_diag B
  have hoff : O.card = B.card * (B.card - 1) := card_offdiag B
  have hsplit (q : ℕ) :
      ((B.product B).filter fun p => f p.1 % q = f p.2 % q).card =
        D.card + (O.filter fun p => f p.1 % q = f p.2 % q).card := by
    let C := (B.product B).filter fun p => f p.1 % q = f p.2 % q
    let E := O.filter fun p => f p.1 % q = f p.2 % q
    have hCE : C = D ∪ E := by
      ext p
      by_cases hpB : p ∈ B.product B
      · by_cases hp : p.1 = p.2
        · simp [C, D, E, O, hp]
        · simp [C, D, E, O, hp]
      · have hpB' : ¬(p.1 ∈ B ∧ p.2 ∈ B) := by
          intro hp
          exact hpB (Finset.mem_product.mpr hp)
        simp [C, D, E, O, hpB']
    have hDE : Disjoint D E := by
      rw [Finset.disjoint_left]
      intro p hpD hpE
      have heq : p.1 = p.2 := (Finset.mem_filter.mp hpD).2
      have hne : p.1 ≠ p.2 :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hpE).1).2
      exact hne heq
    change C.card = D.card + E.card
    rw [hCE, Finset.card_union_of_disjoint hDE]
  calc
    _ = ∑ q ∈ P,
          (B.card + (O.filter fun p => f p.1 % q = f p.2 % q).card) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [hsplit, hdiag]
    _ = P.card * B.card +
          ∑ q ∈ P, (O.filter fun p => f p.1 % q = f p.2 % q).card := by
        rw [Finset.sum_add_distrib]
        simp [Nat.mul_comm]
    _ ≤ P.card * B.card + L * O.card := by
        apply Nat.add_le_add_left
        calc
          ∑ q ∈ P, (O.filter fun p => f p.1 % q = f p.2 % q).card =
              ∑ q ∈ P, ∑ p ∈ O,
                if f p.1 % q = f p.2 % q then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro q _
                  simp
          _ = ∑ p ∈ O, ∑ q ∈ P,
                if f p.1 % q = f p.2 % q then 1 else 0 := by
                  rw [Finset.sum_comm]
          _ ≤ ∑ p ∈ O, L := by
                  apply Finset.sum_le_sum
                  intro p hp
                  obtain ⟨hpB, hpne⟩ := Finset.mem_filter.mp hp
                  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpB
                  simpa [mod_eq_iff_dvd_dist] using
                    hdiv p.1 hp₁ p.2 hp₂ hpne
          _ = L * O.card := by simp [Nat.mul_comm]
    _ = _ := by rw [hoff]

private theorem prod_dvd_of_pairwise_coprime (P : Finset ℕ) (d : ℕ)
    (hpair : (P : Set ℕ).Pairwise Nat.Coprime)
    (hdvd : ∀ q ∈ P, q ∣ d) :
    P.prod id ∣ d := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
      rw [Finset.prod_insert ha]
      have hpairP : (P : Set ℕ).Pairwise Nat.Coprime := by
        intro x hx y hy hxy
        exact hpair (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy
      have hacop : Nat.Coprime a (P.prod id) := by
        apply Nat.Coprime.prod_right
        intro x hx
        exact hpair (Finset.mem_insert_self a P) (Finset.mem_insert_of_mem hx) (by
          intro hax
          have hax' : a = x := by simpa using hax
          exact ha (by simpa [hax'] using hx))
      exact hacop.mul_dvd_of_dvd_of_dvd
        (hdvd a (Finset.mem_insert_self a P))
        (ih hpairP (fun q hq => hdvd q (Finset.mem_insert_of_mem hq)))

private theorem coprime_divisor_count (P : Finset ℕ) (Q L R d : ℕ)
    (hpair : (P : Set ℕ).Pairwise Nat.Coprime)
    (hQ : ∀ q ∈ P, Q ≤ q)
    (hQpos : 0 < Q)
    (hdpos : 0 < d)
    (hdR : d ≤ R)
    (hpow : R < Q ^ (L + 1)) :
    (P.filter fun q => q ∣ d).card ≤ L := by
  classical
  let D := P.filter fun q => q ∣ d
  have hDP : D ⊆ P := Finset.filter_subset _ _
  have hpairD : (D : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hxy
    exact hpair (hDP hx) (hDP hy) hxy
  have hprod_dvd : D.prod id ∣ d := by
    apply prod_dvd_of_pairwise_coprime D d hpairD
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hprod_le : D.prod id ≤ R :=
    (Nat.le_of_dvd hdpos hprod_dvd).trans hdR
  have hQprod : Q ^ D.card ≤ D.prod id := by
    apply Finset.pow_card_le_prod
    intro q hq
    exact hQ q (hDP hq)
  by_contra hnot
  change ¬ D.card ≤ L at hnot
  have hL : L + 1 ≤ D.card := by omega
  have hpows : Q ^ (L + 1) ≤ Q ^ D.card :=
    Nat.pow_le_pow_right hQpos hL
  exact (not_lt_of_ge (hpows.trans (hQprod.trans hprod_le))) hpow

private theorem multi_modulus_large_sieve
    {α : Type*} [DecidableEq α] (B : Finset α) (f : α → ℕ)
    (P : Finset ℕ) (Q L R : ℕ)
    (hinj : Set.InjOn f B)
    (hfR : ∀ x ∈ B, f x ≤ R)
    (hpair : (P : Set ℕ).Pairwise Nat.Coprime)
    (hQ : ∀ q ∈ P, Q ≤ q)
    (hQpos : 0 < Q)
    (hpow : R < Q ^ (L + 1)) :
    ∑ q ∈ P,
        ((B.product B).filter fun p => f p.1 % q = f p.2 % q).card ≤
      P.card * B.card + L * (B.card * (B.card - 1)) := by
  apply collision_sum_bound B f P L
  intro x hx y hy hxy
  have hfne : f x ≠ f y := by
    intro h
    exact hxy (hinj hx hy h)
  have hdpos : 0 < Nat.dist (f x) (f y) :=
    Nat.dist_pos_of_ne hfne
  have hdR : Nat.dist (f x) (f y) ≤ R := by
    unfold Nat.dist
    have hxR := hfR x hx
    have hyR := hfR y hy
    omega
  exact coprime_divisor_count P Q L R (Nat.dist (f x) (f y))
    hpair hQ hQpos hdpos hdR hpow

theorem proof :
    ∀ (P : Finset ℕ) (Q L R : ℕ),
      (P : Set ℕ).Pairwise Nat.Coprime →
      (∀ q ∈ P, Q ≤ q) →
      0 < Q →
      R < Q ^ (L + 1) →
      (∀ d : ℕ, 0 < d → d ≤ R →
        ((P.filter fun q => q ∣ d).prod id ∣ d) ∧
        (P.filter fun q => q ∣ d).card ≤ L) ∧
      ∀ (α : Type) [DecidableEq α] (B : Finset α) (f : α → ℕ),
        Set.InjOn f B →
        (∀ x ∈ B, f x ≤ R) →
        ∑ q ∈ P,
            ((B.product B).filter fun p => f p.1 % q = f p.2 % q).card ≤
          P.card * B.card + L * (B.card * (B.card - 1)) := by
  intro P Q L R hpair hQ hQpos hpow
  constructor
  · intro d hdpos hdR
    let D := P.filter fun q => q ∣ d
    have hDP : D ⊆ P := Finset.filter_subset _ _
    have hpairD : (D : Set ℕ).Pairwise Nat.Coprime := by
      intro x hx y hy hxy
      exact hpair (hDP hx) (hDP hy) hxy
    have hprod : D.prod id ∣ d := by
      apply prod_dvd_of_pairwise_coprime D d hpairD
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    exact ⟨hprod, coprime_divisor_count P Q L R d
      hpair hQ hQpos hdpos hdR hpow⟩
  · intro α _ B f hinj hfR
    exact multi_modulus_large_sieve B f P Q L R
      hinj hfR hpair hQ hQpos hpow

end Submissions.Erdos1MultiModulusLargeSieve.ProductDivisors

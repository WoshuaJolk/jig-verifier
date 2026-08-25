import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.PrimeFin

namespace Submissions.Erdos52GcdNormalizationDichotomy.P29

theorem proof :
    ∀ (U : Finset ℕ) (k R : ℕ),
      (∀ u ∈ U, 1 < u) →
      (∀ u ∈ U, u.primeFactors.card ≤ R) →
      U = ∅ ∨
        ∃ P : Finset ℕ, P ⊆ U ∧ (P : Set ℕ).Pairwise Nat.Coprime ∧
          (k ≤ P.card ∨
            ∃ q : ℕ, ∃ V : Finset ℕ,
              q.Prime ∧
              (∃ p ∈ P, q ∣ p) ∧
              V = (U.filter fun u => q ∣ u).image (fun u => u / q) ∧
              U.card ≤ k * R * V.card) := by
  classical
  intro U k R hgt hfac
  by_cases hU : U = ∅
  · exact Or.inl hU
  right
  let C : Finset (Finset ℕ) :=
    U.powerset.filter fun P => (P : Set ℕ).Pairwise Nat.Coprime
  have hC : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C]
  obtain ⟨P, hPC, hmax⟩ := Finset.exists_max_image C Finset.card hC
  have hP : P ⊆ U ∧ (P : Set ℕ).Pairwise Nat.Coprime := by
    simpa [C] using hPC
  refine ⟨P, hP.1, hP.2, ?_⟩
  by_cases hk : k ≤ P.card
  · exact Or.inl hk
  right
  have hcover : ∀ u ∈ U, ∃ p ∈ P, ¬Nat.Coprime p u := by
    intro u hu
    by_cases huP : u ∈ P
    · refine ⟨u, huP, ?_⟩
      intro hc
      have hu1 : u = 1 := by
        simpa [Nat.Coprime] using hc
      have := hgt u hu
      omega
    · by_contra hn
      push Not at hn
      have hpair : ((insert u P : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
        rw [Finset.coe_insert, Set.pairwise_insert]
        refine ⟨hP.2, ?_⟩
        intro p hp hne
        exact ⟨(hn p hp).symm, hn p hp⟩
      have hins : insert u P ∈ C := by
        simp only [C, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, hpair⟩
        intro x hx
        simp only [Finset.mem_insert] at hx
        exact hx.elim (fun h => h ▸ hu) (fun hxP => hP.1 hxP)
      have hcard := hmax (insert u P) hins
      simp [huP] at hcard
  let Q : Finset ℕ := P.biUnion Nat.primeFactors
  have hQ : Q.Nonempty := by
    obtain ⟨u, hu⟩ := U.nonempty_iff_ne_empty.mpr hU
    obtain ⟨p, hpP, hnpu⟩ := hcover u hu
    obtain ⟨q, hqprime, hqdp, -⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hnpu
    refine ⟨q, ?_⟩
    simp only [Q, Finset.mem_biUnion]
    exact ⟨p, hpP, hqprime.mem_primeFactors hqdp (by
      have := hgt p (hP.1 hpP)
      omega)⟩
  let F : ℕ → Finset ℕ := fun q => U.filter fun u => q ∣ u
  obtain ⟨q, hqQ, hqmax⟩ :=
    Finset.exists_max_image Q (fun q => (F q).card) hQ
  have hqprime : q.Prime := by
    simp only [Q, Finset.mem_biUnion] at hqQ
    obtain ⟨p, hpP, hqpf⟩ := hqQ
    exact Nat.prime_of_mem_primeFactors hqpf
  have hqsource : ∃ p ∈ P, q ∣ p := by
    simp only [Q, Finset.mem_biUnion] at hqQ
    obtain ⟨p, hpP, hqpf⟩ := hqQ
    exact ⟨p, hpP, Nat.dvd_of_mem_primeFactors hqpf⟩
  have hUQ : U ⊆ Q.biUnion F := by
    intro u hu
    obtain ⟨p, hpP, hnpu⟩ := hcover u hu
    obtain ⟨r, hrprime, hrdp, hrdu⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hnpu
    simp only [Finset.mem_biUnion]
    refine ⟨r, ?_, ?_⟩
    · simp only [Q, Finset.mem_biUnion]
      exact ⟨p, hpP, hrprime.mem_primeFactors hrdp (by
        have := hgt p (hP.1 hpP)
        omega)⟩
    · simp [F, hu, hrdu]
  have hQcard : Q.card ≤ P.card * R := by
    apply Finset.card_biUnion_le_card_mul
    intro p hpP
    exact hfac p (hP.1 hpP)
  have hUF : U.card ≤ Q.card * (F q).card := by
    calc
      U.card ≤ (Q.biUnion F).card := Finset.card_le_card hUQ
      _ ≤ Q.card * (F q).card :=
        Finset.card_biUnion_le_card_mul Q F (F q).card hqmax
  let V : Finset ℕ := (F q).image fun u => u / q
  have hinj : Set.InjOn (fun u => u / q) (F q) := by
    intro a ha b hb hab
    have hqda : q ∣ a := (by simpa [F] using ha : a ∈ U ∧ q ∣ a).2
    have hqdb : q ∣ b := (by simpa [F] using hb : b ∈ U ∧ q ∣ b).2
    change a / q = b / q at hab
    calc
      a = q * (a / q) := (Nat.mul_div_cancel' hqda).symm
      _ = q * (b / q) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hqdb
  have hVcard : V.card = (F q).card := by
    dsimp only [V]
    exact Finset.card_image_of_injOn hinj
  refine ⟨q, V, hqprime, hqsource, ?_, ?_⟩
  · rfl
  · rw [hVcard]
    calc
      U.card ≤ Q.card * (F q).card := hUF
      _ ≤ (k * R) * (F q).card := by
        apply Nat.mul_le_mul_right
        calc
          Q.card ≤ P.card * R := hQcard
          _ ≤ k * R :=
            Nat.mul_le_mul_right R (Nat.le_of_lt (Nat.lt_of_not_ge hk))
      _ = k * R * (F q).card := rfl

end Submissions.Erdos52GcdNormalizationDichotomy.P29

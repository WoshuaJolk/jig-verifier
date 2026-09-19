import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace Submissions.J5P122RichCircleFoundations.Proof

noncomputable def richCenters (P : Finset ℂ) : Set ℂ :=
  {c : ℂ | 3 ≤ (P.filter fun p => dist p c = 1).card}

noncomputable def maxRichUnitCircles (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset ℂ,
    P.card = n ∧ (richCenters P).ncard = k}

theorem center_unique {a b d c e : ℂ} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (hac : dist a c = 1) (hbc : dist b c = 1)
    (hdc : dist d c = 1) (hae : dist a e = 1) (hbe : dist b e = 1)
    (hde : dist d e = 1) : c = e := by
  by_contra hce
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (V := ℂ) Complex.finrank_real_complex hce hab hac hbc hdc hae hbe hde with h | h
  · exact had h.symm
  · exact hbd h.symm

theorem rich_witness (P : Finset ℂ) (c : richCenters P) :
    ∃ t : P × P × P,
      t.1.val ≠ t.2.1.val ∧ t.1.val ≠ t.2.2.val ∧ t.2.1.val ≠ t.2.2.val ∧
      dist t.1.val c.val = 1 ∧ dist t.2.1.val c.val = 1 ∧ dist t.2.2.val c.val = 1 := by
  classical
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ :=
    Finset.two_lt_card_iff.mp c.property
  exact ⟨(⟨a, (Finset.mem_filter.mp ha).1⟩,
      ⟨b, (Finset.mem_filter.mp hb).1⟩, ⟨d, (Finset.mem_filter.mp hd).1⟩),
    hab, had, hbd, (Finset.mem_filter.mp ha).2,
    (Finset.mem_filter.mp hb).2, (Finset.mem_filter.mp hd).2⟩

noncomputable def witness (P : Finset ℂ) (c : richCenters P) : P × P × P :=
  Classical.choose (rich_witness P c)

theorem witness_spec (P : Finset ℂ) (c : richCenters P) :
    (witness P c).1.val ≠ (witness P c).2.1.val ∧
    (witness P c).1.val ≠ (witness P c).2.2.val ∧
    (witness P c).2.1.val ≠ (witness P c).2.2.val ∧
    dist (witness P c).1.val c.val = 1 ∧
    dist (witness P c).2.1.val c.val = 1 ∧
    dist (witness P c).2.2.val c.val = 1 :=
  Classical.choose_spec (rich_witness P c)

theorem witness_injective (P : Finset ℂ) : Function.Injective (witness P) := by
  intro c e h
  have hc := witness_spec P c
  have he := witness_spec P e
  rw [← h] at he
  apply Subtype.ext
  exact center_unique hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2 he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2

theorem richCenters_finite (P : Finset ℂ) : (richCenters P).Finite := by
  exact Finite.of_injective (witness P) (witness_injective P)

theorem richCenters_ncard_le (P : Finset ℂ) : (richCenters P).ncard ≤ P.card ^ 3 := by
  have h := Nat.card_le_card_of_injective (witness P) (witness_injective P)
  simpa [Set.ncard, Nat.card_eq_fintype_card, pow_succ, mul_assoc] using h

theorem counts_bddAbove (n : ℕ) :
    BddAbove {k : ℕ | ∃ P : Finset ℂ, P.card = n ∧ (richCenters P).ncard = k} := by
  refine ⟨n ^ 3, ?_⟩
  rintro k ⟨P, rfl, rfl⟩
  exact richCenters_ncard_le P

theorem maximum_attained (n : ℕ) : ∃ P : Finset ℂ,
    P.card = n ∧ (richCenters P).ncard = maxRichUnitCircles n := by
  apply Nat.sSup_mem ?_ (counts_bddAbove n)
  obtain ⟨P, hP⟩ := Finset.exists_card_eq (α := ℂ) n
  exact ⟨(richCenters P).ncard, P, hP, rfl⟩

theorem count_le_maximum (P : Finset ℂ) :
    (richCenters P).ncard ≤ maxRichUnitCircles P.card := by
  exact le_csSup (counts_bddAbove P.card) ⟨P, rfl, rfl⟩

theorem maximum_le (n : ℕ) : maxRichUnitCircles n ≤ n ^ 3 := by
  obtain ⟨P, hP, h⟩ := maximum_attained n
  rw [← h, ← hP]
  exact richCenters_ncard_le P

theorem maximum_le_iff (n b : ℕ) : maxRichUnitCircles n ≤ b ↔
    ∀ P : Finset ℂ, P.card = n → (richCenters P).ncard ≤ b := by
  constructor
  · intro h P hP
    have hp := count_le_maximum P
    rw [hP] at hp
    exact hp.trans h
  · intro h
    obtain ⟨P, hP, hmax⟩ := maximum_attained n
    rw [← hmax]
    exact h P hP


/-- Export the conjunction of existing locally checked foundational lemmas. -/
theorem proof :
  (∀ P : Finset ℂ, (richCenters P).Finite) ∧
  (∀ P : Finset ℂ, (richCenters P).ncard ≤ P.card ^ 3) ∧
  (∀ n : ℕ, ∃ P : Finset ℂ,
    P.card = n ∧ (richCenters P).ncard = maxRichUnitCircles n) ∧
  (∀ P : Finset ℂ, (richCenters P).ncard ≤ maxRichUnitCircles P.card) ∧
  (∀ n : ℕ, maxRichUnitCircles n ≤ n ^ 3) ∧
  (∀ n b : ℕ, maxRichUnitCircles n ≤ b ↔
    ∀ P : Finset ℂ, P.card = n → (richCenters P).ncard ≤ b) := by
  exact ⟨richCenters_finite, richCenters_ncard_le, maximum_attained,
    count_le_maximum, maximum_le, maximum_le_iff⟩

end Submissions.J5P122RichCircleFoundations.Proof

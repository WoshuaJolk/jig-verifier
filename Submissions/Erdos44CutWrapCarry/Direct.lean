import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Submissions.Erdos44CutWrapCarry.Direct

open Set Finset

def rot (n c x : ℕ) : ℕ := (x + n - c) % n

abbrev Quad := (((ℕ × ℕ) × ℕ) × ℕ)

abbrev ModCollision (n c : ℕ) (p : Quad) : Prop :=
  (rot n c p.1.1.1 + rot n c p.1.1.2) % n =
    (rot n c p.2 + rot n c p.1.2) % n

abbrev IntegerCollision (n c : ℕ) (p : Quad) : Prop :=
  rot n c p.1.1.1 + rot n c p.1.1.2 =
    rot n c p.2 + rot n c p.1.2

abbrev SameCarry (n c : ℕ) (p : Quad) : Prop :=
  (rot n c p.1.1.1 + rot n c p.1.1.2 < n) ↔
    (rot n c p.2 + rot n c p.1.2 < n)

private theorem mod_eq_iff_same_carry
    (n A B : ℕ) (hn : 0 < n) (hA : A < 2 * n) (hB : B < 2 * n)
    (hmod : A % n = B % n) :
    A = B ↔ ((A < n) ↔ (B < n)) := by
  constructor
  · intro h
    simp [h]
  · intro hcarry
    by_cases hAn : A < n <;> by_cases hBn : B < n
    · rw [Nat.mod_eq_of_lt hAn, Nat.mod_eq_of_lt hBn] at hmod
      exact hmod
    · exact (hBn (hcarry.mp hAn)).elim
    · exact (hAn (hcarry.mpr hBn)).elim
    · have hnA : n ≤ A := by omega
      have hnB : n ≤ B := by omega
      have hAsub : A - n < n := by omega
      have hBsub : B - n < n := by omega
      rw [Nat.mod_eq_sub_mod hnA, Nat.mod_eq_of_lt hAsub,
        Nat.mod_eq_sub_mod hnB, Nat.mod_eq_of_lt hBsub] at hmod
      omega

theorem proof :
    ∀ (n c : ℕ), 0 < n → ∀ E : Finset Quad,
      (∀ p ∈ E, ModCollision n c p) →
        E.filter (IntegerCollision n c) = E.filter (SameCarry n c) := by
  classical
  intro n c hn E hmod
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hint⟩
    refine ⟨hp, ?_⟩
    unfold IntegerCollision at hint
    unfold SameCarry
    simp [hint]
  · rintro ⟨hp, hcarry⟩
    refine ⟨hp, ?_⟩
    have hmc := hmod p hp
    unfold ModCollision at hmc
    unfold IntegerCollision
    unfold SameCarry at hcarry
    have hx := Nat.mod_lt (p.1.1.1 + n - c) hn
    have hy := Nat.mod_lt (p.1.1.2 + n - c) hn
    have hz := Nat.mod_lt (p.1.2 + n - c) hn
    have hd := Nat.mod_lt (p.2 + n - c) hn
    apply (mod_eq_iff_same_carry n
      (rot n c p.1.1.1 + rot n c p.1.1.2)
      (rot n c p.2 + rot n c p.1.2) hn (by dsimp [rot]; omega)
      (by dsimp [rot]; omega) hmc).mpr
    exact hcarry

end Submissions.Erdos44CutWrapCarry.Direct

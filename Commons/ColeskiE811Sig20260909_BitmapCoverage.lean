import Mathlib

/- BEGIN bundled local module BitmapCoverage -/

namespace ColeskiBitmapCoverage

def bitmap : List Nat → Nat
  | [] => 0
  | a :: rest => (1 <<< a) ||| bitmap rest

theorem bitmap_member (xs : List Nat) (a : Nat) :
    (bitmap xs).testBit a = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp [bitmap]
  | cons x xs ih =>
    by_cases h : a = x
    · subst x
      simp [bitmap, Nat.testBit_two_pow, Nat.testBit_one_eq_true_iff_self_eq_zero]
    · simp [bitmap, Nat.testBit_two_pow, Nat.testBit_one_eq_true_iff_self_eq_zero,
        h, ih] <;> omega

theorem from_bitmap {P : Nat → Prop} (xs : List Nat) (bits : Nat)
    (hb : bitmap xs = bits) (hp : ∀ x ∈ xs, P x) (a : Nat)
    (ha : bits.testBit a = true) : P a := by
  apply hp a
  apply (bitmap_member xs a).mp
  simpa only [hb] using ha
end ColeskiBitmapCoverage
#print axioms ColeskiBitmapCoverage.from_bitmap

/- END bundled local module BitmapCoverage -/

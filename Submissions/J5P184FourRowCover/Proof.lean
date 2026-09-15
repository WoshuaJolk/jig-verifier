import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.NormNum

/- Saved local savcab/campaign finite-cover proof. Original declaration bodies are
retained below. This standalone adaptation makes no novelty, full-root, prize,
or independent-kernel-replay claim. See source-preservation.json and CREDIT.md. -/

namespace Submissions.J5P184FourRowCover.Proof

namespace P184Transfer

private def bit (b : Bool) : ℤ := if b then 1 else 0

private def coverPotential : Bool → Bool → Bool → Bool → ℤ
  | false, false, false, false => 4
  | true,  false, false, false => 2
  | false, true,  false, false => 3
  | true,  true,  false, false => 0
  | false, false, true,  false => 4
  | true,  false, true,  false => 1
  | false, true,  true,  false => 1
  | true,  true,  true,  false => 0
  | false, false, false, true  => 3
  | true,  false, false, true  => 2
  | false, true,  false, true  => 2
  | true,  true,  false, true  => 0
  | false, false, true,  true  => 2
  | true,  false, true,  true  => 0
  | false, true,  true,  true  => 1
  | true,  true,  true,  true  => 0

private theorem cover_step (a b c d e : Bool) :
    2 * bit (a || b || c || e) ≤
      1 + 3 * bit a + coverPotential a b c d - coverPotential b c d e := by
  revert a b c d e
  decide

/-- Union of four iterates, with the third iterate deliberately omitted. -/
def fourCover {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv α α) (C : Finset α) : Finset α :=
  Finset.univ.filter fun x =>
    x ∈ C ∨ e x ∈ C ∨ e (e x) ∈ C ∨ e (e (e (e x))) ∈ C

/-- Exact covering obstruction for any permutation, including short cycles.
For translation by -d this is 2|C+{0,d,2d,4d}| ≤ |G|+3|C|. -/
theorem four_cover_card_bound {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv α α) (C : Finset α) :
    2 * (fourCover e C).card ≤ Fintype.card α + 3 * C.card := by
  let b : α → Bool := fun x => decide (x ∈ C)
  let P : α → ℤ := fun x => coverPotential (b x) (b (e x)) (b (e (e x)))
    (b (e (e (e x))))
  have hp : (∑ x, P (e x)) = ∑ x, P x := Equiv.sum_comp e P
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    cover_step (b x) (b (e x)) (b (e (e x)))
      (b (e (e (e x)))) (b (e (e (e (e x))))))
  change (∑ x, 2 * bit (b x || b (e x) || b (e (e x)) || b (e (e (e (e x)))))) ≤
    ∑ x, (1 + 3 * bit (b x) + P x - P (e x)) at hs
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hp, add_sub_cancel_right] at hs
  have hc : (∑ x, bit (b x)) = (C.card : ℤ) := by
    simp [b, bit]
  have hu : (∑ x, bit (b x || b (e x) || b (e (e x)) || b (e (e (e (e x)))))) =
      ((fourCover e C).card : ℤ) := by
    simp [b, bit, fourCover, Bool.or_eq_true, or_assoc]
  rw [hc, hu] at hs
  norm_num at hs
  exact_mod_cast hs

/-- Membership in the four translates, with no disjointness or order assumption. -/
theorem four_translate_card_bound {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (C : Finset G) (d : G) :
    2 * (Finset.univ.filter fun x => x ∈ C ∨ x - d ∈ C ∨
      x - (d + d) ∈ C ∨ x - (d + d + d + d) ∈ C).card ≤
      Fintype.card G + 3 * C.card := by
  simpa only [fourCover, Equiv.subRight_apply, sub_sub] using
    four_cover_card_bound (Equiv.subRight d) C

end P184Transfer

/-- The exact finite-permutation statement, with membership expanded inline. -/
theorem proof :
    ∀ (α : Type) [Fintype α] [DecidableEq α]
    (e : Equiv α α) (C : Finset α),
    2 * (Finset.univ.filter fun x =>
      x ∈ C ∨ e x ∈ C ∨ e (e x) ∈ C ∨ e (e (e (e x))) ∈ C).card ≤
      Fintype.card α + 3 * C.card := by
  intro α instFintype instDecidableEq e C
  simpa only [P184Transfer.fourCover] using
    (P184Transfer.four_cover_card_bound e C)

end Submissions.J5P184FourRowCover.Proof

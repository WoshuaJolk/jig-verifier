import Init

namespace Submissions.J5P26CornerTransfer.Proof

theorem four_values_three_slots (x d a b c : Int)
    (h0 : x=a ∨ x=b ∨ x=c)
    (h1 : x+d=a ∨ x+d=b ∨ x+d=c)
    (h2 : x+2*d=a ∨ x+2*d=b ∨ x+2*d=c)
    (h3 : x+3*d=a ∨ x+3*d=b ∨ x+3*d=c) : d=0 := by
  rcases h0 with h0 | h0 | h0 <;>
    rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> omega

theorem affine_zero_corner (a b c x y d : Int) (hd : d ≠ 0)
    (h0 : a*x+b*y+c=0)
    (h1 : a*(x+d)+b*y+c=0)
    (h2 : a*x+b*(y+d)+c=0) : a=0 ∧ b=0 := by
  rw [Int.mul_add] at h1 h2
  have ha : a*d=0 := by omega
  have hb : b*d=0 := by omega
  constructor
  · rcases Int.mul_eq_zero.mp ha with h | h
    · exact h
    · exact False.elim (hd h)
  · rcases Int.mul_eq_zero.mp hb with h | h
    · exact h
    · exact False.elim (hd h)

theorem negative_principal_vector (a b : Int)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1)
    (hz : a=0 ∨ b=0) : a+b-2 < 0 := by
  omega

abbrev member31 (n : Nat) : Bool :=
  n%31 == 4 || n%31 == 5 || n%31 == 8 || n%31 == 9 || n%31 == 10

abbrev lift31 (x y : Nat) : Bool :=
  member31 (x+y) && member31 (x+2*y)

abbrev midpoint31 (x y : Nat) : Nat :=
  if member31 (21*(2*x+y)) && member31 (21*(x+2*y)) then 1 else 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem exact_counterexample31 :
    (∀ a d : Fin 31, d.val ≠ 0 →
      ¬(member31 a.val=true ∧ member31 (a.val+d.val)=true ∧
        member31 (a.val+2*d.val)=true ∧ member31 (a.val+3*d.val)=true)) ∧
    lift31 0 4=true ∧ lift31 1 4=true ∧ lift31 0 5=true ∧
    ((List.range 31).flatMap (fun x => (List.range 31).filter (fun y => lift31 x y))).length=25 ∧
    midpoint31 3 3=0 ∧ midpoint31 6 6=0 ∧
    midpoint31 3 6=1 ∧ midpoint31 6 3=1 := by
  decide

theorem solves :
  (∀ (x d a b c : Int)
    (h0 : x=a ∨ x=b ∨ x=c)
    (h1 : x+d=a ∨ x+d=b ∨ x+d=c)
    (h2 : x+2*d=a ∨ x+2*d=b ∨ x+2*d=c)
    (h3 : x+3*d=a ∨ x+3*d=b ∨ x+3*d=c), d=0) ∧
  (∀ (a b c x y d : Int) (hd : d ≠ 0)
    (h0 : a*x+b*y+c=0)
    (h1 : a*(x+d)+b*y+c=0)
    (h2 : a*x+b*(y+d)+c=0), a=0 ∧ b=0) ∧
  (∀ (a b : Int)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1)
    (hz : a=0 ∨ b=0), a+b-2 < 0) ∧
  ((∀ a d : Fin 31, d.val ≠ 0 →
      ¬(member31 a.val=true ∧ member31 (a.val+d.val)=true ∧
        member31 (a.val+2*d.val)=true ∧ member31 (a.val+3*d.val)=true)) ∧
    lift31 0 4=true ∧ lift31 1 4=true ∧ lift31 0 5=true ∧
    ((List.range 31).flatMap (fun x => (List.range 31).filter (fun y => lift31 x y))).length=25 ∧
    midpoint31 3 3=0 ∧ midpoint31 6 6=0 ∧
    midpoint31 3 6=1 ∧ midpoint31 6 3=1) := by
  exact ⟨@four_values_three_slots, @affine_zero_corner, @negative_principal_vector, @exact_counterexample31⟩

end Submissions.J5P26CornerTransfer.Proof

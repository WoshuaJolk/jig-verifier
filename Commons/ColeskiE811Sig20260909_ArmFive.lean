import Commons.ColeskiE811Sig20260909_K5SemanticsOnly

/- BEGIN bundled local module ArmFive -/

namespace ColeskiArmFive
open ColeskiK4Coverage
def encodeArm (a : Fin 5 → Fin 6) : Nat := 1*(a 0).val + 6*(a 1).val + 36*(a 2).val + 216*(a 3).val + 1296*(a 4).val

theorem encodeArm_lt (a : Fin 5 → Fin 6) : encodeArm a < 7776 := by
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  have h4 := (a 4).isLt
  unfold encodeArm
  omega

theorem digit_encodeArm (a : Fin 5 → Fin 6) (i : Fin 5) : digit (encodeArm a) i.val = (a i).val := by
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  have h4 := (a 4).isLt
  fin_cases i
  · change (1*(a 0).val + 6*(a 1).val + 36*(a 2).val + 216*(a 3).val + 1296*(a 4).val)/1%6 = (a 0).val
    omega
  · change (1*(a 0).val + 6*(a 1).val + 36*(a 2).val + 216*(a 3).val + 1296*(a 4).val)/6%6 = (a 1).val
    omega
  · change (1*(a 0).val + 6*(a 1).val + 36*(a 2).val + 216*(a 3).val + 1296*(a 4).val)/36%6 = (a 2).val
    omega
  · change (1*(a 0).val + 6*(a 1).val + 36*(a 2).val + 216*(a 3).val + 1296*(a 4).val)/216%6 = (a 3).val
    omega
  · change (1*(a 0).val + 6*(a 1).val + 36*(a 2).val + 216*(a 3).val + 1296*(a 4).val)/1296%6 = (a 4).val
    omega
theorem digit_encodeArm_nat (a : Fin 5 → Fin 6) (i : Nat) (hi : i < 5) :
    digit (encodeArm a) i = (a ⟨i,hi⟩).val := digit_encodeArm a ⟨i,hi⟩
end ColeskiArmFive
#print axioms ColeskiArmFive.digit_encodeArm

/- END bundled local module ArmFive -/

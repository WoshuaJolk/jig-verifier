import Commons.ColeskiE811Sig20260909_K5SemanticsOnly

/- BEGIN bundled local module ArmCode -/

namespace ColeskiArmCode
open ColeskiK4Coverage ColeskiK5Coverage

def encodeArm (a : Fin 4 → Fin 6) : Nat :=
  (a 0).val+6*(a 1).val+36*(a 2).val+216*(a 3).val

theorem encodeArm_lt (a : Fin 4 → Fin 6) : encodeArm a < 1296 := by
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  unfold encodeArm
  omega

theorem digit_encodeArm (a : Fin 4 → Fin 6) (i : Fin 4) : digit (encodeArm a) i.val = (a i).val := by
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  fin_cases i
  · change ((a 0).val+6*(a 1).val+36*(a 2).val+216*(a 3).val)/1%6 = (a 0).val; omega
  · change ((a 0).val+6*(a 1).val+36*(a 2).val+216*(a 3).val)/6%6 = (a 1).val; omega
  · change ((a 0).val+6*(a 1).val+36*(a 2).val+216*(a 3).val)/36%6 = (a 2).val; omega
  · change ((a 0).val+6*(a 1).val+36*(a 2).val+216*(a 3).val)/216%6 = (a 3).val; omega

theorem digit_encodeArm_nat (a : Fin 4 → Fin 6) (i : Nat) (hi : i < 4) :
    digit (encodeArm a) i = (a ⟨i,hi⟩).val := digit_encodeArm a ⟨i,hi⟩

theorem extension_digits_nat (r a i : Nat) (hi : i < 10) :
    digit (extendCode r a) i = extensionDigit r a i := extension_digits r a ⟨i,hi⟩
end ColeskiArmCode
#print axioms ColeskiArmCode.digit_encodeArm

/- END bundled local module ArmCode -/

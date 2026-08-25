import Mathlib.NumberTheory.FermatPsp
import Mathlib.Tactic

namespace Submissions.Erdos1057TwoIsNotCarmichael.Worker01

def IsCarmichael (n : ℕ) : Prop :=
  ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

theorem proof : ¬IsCarmichael 2 := by
  intro h
  have hpsp := h 1 (by omega) (Nat.coprime_one_right 2)
  exact hpsp.2.1 (by norm_num)

end Submissions.Erdos1057TwoIsNotCarmichael.Worker01

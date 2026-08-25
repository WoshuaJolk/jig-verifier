import Mathlib.NumberTheory.FermatPsp

namespace Statements.Erdos1057TwoIsNotCarmichael

def IsCarmichael (n : ℕ) : Prop :=
  ∀ b ≥ 1, n.Coprime b → n.FermatPsp b

abbrev statement : Prop := ¬IsCarmichael 2

theorem target : statement := sorry

end Statements.Erdos1057TwoIsNotCarmichael

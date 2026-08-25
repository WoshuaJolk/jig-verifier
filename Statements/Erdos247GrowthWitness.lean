import Mathlib.Topology.Instances.EReal.Lemmas

open Filter

namespace Statements.Erdos247GrowthWitness

/-- The growth hypotheses in Erdős Problem 247 are jointly satisfiable. -/
abbrev statement : Prop :=
  ∃ n : ℕ → ℕ, StrictMono n ∧
    atTop.limsup (fun k => (n k / k.succ : EReal)) = ⊤

 theorem target : statement := sorry

end Statements.Erdos247GrowthWitness

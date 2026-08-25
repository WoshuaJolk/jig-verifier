import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.RingTheory.Algebraic.Defs

open Filter

namespace Statements.Erdos247SparseBinaryTranscendence

/-- Erdős Problem 247: sparse binary series under an unbounded limsup
growth ratio should be transcendental. -/
abbrev statement : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n →
    atTop.limsup (fun k => (n k / k.succ : EReal)) = ⊤ →
    Transcendental ℚ (∑' k, (1 : ℝ) / 2 ^ n k)

/-- Open target; submissions prove `statement` in their own module. -/
theorem target : statement := sorry

end Statements.Erdos247SparseBinaryTranscendence

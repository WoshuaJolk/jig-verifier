import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos247GrowthWitness.Direct

private def witness (k : ℕ) : ℕ := k * k.succ

private theorem witness_strictMono : StrictMono witness := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [witness]
  nlinarith

private theorem witness_ratio (k : ℕ) :
    (witness k / k.succ : EReal) = k := by
  rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_coe_eq_natCast,
    ← EReal.coe_coe_eq_natCast, ← EReal.coe_div]
  norm_cast
  simp only [witness, Nat.cast_mul, Nat.cast_succ]
  field_simp

private theorem witness_limsup :
    atTop.limsup (fun k => (witness k / k.succ : EReal)) = ⊤ := by
  have hnat : Tendsto (fun k : ℕ => (k : EReal)) atTop (nhds ⊤) := by
    refine (EReal.tendsto_coe_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).congr' ?_
    exact .of_forall fun k => by
      simpa only [Function.comp_apply] using EReal.coe_coe_eq_natCast k
  exact hnat.congr (fun k => (witness_ratio k).symm) |>.limsup_eq

theorem proof :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      atTop.limsup (fun k => (n k / k.succ : EReal)) = ⊤ :=
  ⟨witness, witness_strictMono, witness_limsup⟩

end Submissions.Erdos247GrowthWitness.Direct

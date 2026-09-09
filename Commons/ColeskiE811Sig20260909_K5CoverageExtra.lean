import Commons.ColeskiE811Sig20260909_K5Coverage
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks001
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks015
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks029
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks043
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks057
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks071
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks085
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks099
import Commons.ColeskiE811Sig20260909_K5CoverageBlocks113

/- BEGIN bundled local module K5CoverageExtra -/


namespace ColeskiK5Coverage

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block0_pointwise (k : Nat) (hk : k < 256) : check5 k = true := by
  apply List.all_eq_true.mp block0
  simpa only [List.mem_range] using hk

theorem groups_pointwise (g : Fin 9) (i : Fin 14) (k : Nat)
    (hk : k < if 1 + 14 * g.val + i.val = 126 then 144 else 256) :
    check5 ((1 + 14 * g.val + i.val) * 256 + k) = true := by
  fin_cases g
  · exact group001_pointwise i k (by omega)
  · exact group015_pointwise i k (by omega)
  · exact group029_pointwise i k (by omega)
  · exact group043_pointwise i k (by omega)
  · exact group057_pointwise i k (by omega)
  · exact group071_pointwise i k (by omega)
  · exact group085_pointwise i k (by omega)
  · exact group099_pointwise i k (by omega)
  · exact group113_pointwise i k (by omega)

theorem coverage5 (k : Nat) (hk : k < 32400) : check5 k = true := by
  let b : Fin 127 := ⟨k / 256, by omega⟩
  by_cases hzero : b.val = 0
  · apply block0_pointwise
    dsimp [b] at hzero
    omega
  · let g : Fin 9 := ⟨(b.val - 1) / 14, by omega⟩
    let i : Fin 14 := ⟨(b.val - 1) % 14, Nat.mod_lt _ (by omega)⟩
    have hidx : 1 + 14 * g.val + i.val = b.val := by
      dsimp [g, i]
      omega
    have hrem : k % 256 < if b.val = 126 then 144 else 256 := by
      dsimp [b]
      split <;> omega
    have hrem' :
        k % 256 < if 1 + 14 * g.val + i.val = 126 then 144 else 256 := by
      simpa only [hidx] using hrem
    have hcheck := groups_pointwise g i (k % 256) hrem'
    have heq : (1 + 14 * g.val + i.val) * 256 + k % 256 = k := by
      rw [hidx]
      dsimp [b]
      omega
    simpa only [heq] using hcheck

end ColeskiK5Coverage

#print axioms ColeskiK5Coverage.coverage5

/- END bundled local module K5CoverageExtra -/

import Commons.ColeskiE811Sig20260909_OrbitChecks

/- BEGIN bundled local module OrbitDataSemantics -/

namespace ColeskiOrbitDataSemantics
open ColeskiOrbitChecks ColeskiK4Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem minimum_witness_bound : ∀ r : Fin 551, minimumWitnesses[r.val]! < 7200 := by decide

theorem inverse_colors_correct : ∀ p : Fin 60, ∀ c : Fin 6,
    digit colorPermutations[p.val]! (digit inverseColors[p.val]! c.val) = c.val ∧
    digit inverseColors[p.val]! (digit colorPermutations[p.val]! c.val) = c.val := by
  intro p
  fin_cases p <;> decide

theorem minimum_codes_injective :
    Function.Injective (fun r : Fin 551 => minimumCodes[r.val]!) := by
  intro i j h
  have hi : i.val < minimumCodes.size := by change i.val < 551; exact i.isLt
  have hj : j.val < minimumCodes.size := by change j.val < 551; exact j.isLt
  have hil : i.val < minimumCodes.toList.length := by simpa using hi
  have hjl : j.val < minimumCodes.toList.length := by simpa using hj
  have he : minimumCodes.toList[i.val]'hil = minimumCodes.toList[j.val]'hjl := by
    simpa only [Array.getElem_toList, getElem!_pos minimumCodes i.val hi,
      getElem!_pos minimumCodes j.val hj] using h
  exact Fin.ext (minima_distinct.getElem_inj_iff.mp he)
end ColeskiOrbitDataSemantics
#print axioms ColeskiOrbitDataSemantics.minimum_codes_injective
#print axioms ColeskiOrbitDataSemantics.inverse_colors_correct

/- END bundled local module OrbitDataSemantics -/

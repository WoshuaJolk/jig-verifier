import Commons.ColeskiE811Sig20260909_PaletteAction
import Commons.ColeskiE811Sig20260909_OrbitDataSemantics
import Commons.ColeskiE811Sig20260909_OrbitMinima

/- BEGIN bundled local module OrbitSeparation -/

namespace ColeskiOrbitSeparation
set_option maxRecDepth 8000
set_option maxHeartbeats 0
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiPatternScalar
open ColeskiPaletteAction ColeskiOrbitChecks ColeskiOrbitDataSemantics ColeskiOrbitMinima

noncomputable def representative (r : Fin 551) := fromCode representatives5[r.val]!

noncomputable def attainer (r : Fin 551) : G :=
  tableAction ⟨minimumWitnesses[r.val]!/60, by have h := minimum_witness_bound r; omega⟩
    ⟨minimumWitnesses[r.val]!%60, Nat.mod_lt _ (by decide)⟩

theorem attained (r : Fin 551) :
    patternCode (attainer r • representative r) = minimumCodes[r.val]! := by
  let v : Fin 120 := ⟨minimumWitnesses[r.val]!/60, by have h := minimum_witness_bound r; omega⟩
  let c : Fin 60 := ⟨minimumWitnesses[r.val]!%60, Nat.mod_lt _ (by decide)⟩
  change patternCode (tableAction v c • fromCode representatives5[r.val]!) = _
  rw [tableAction_code, ← transformed_components r v c]
  have hi : 1+c.val+60*v.val+7200*r.val = 1+minimumWitnesses[r.val]!+7200*r.val := by
    dsimp [v,c]
    omega
  rw [hi]
  exact minima_attained r

theorem lower_from_checks
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r : Fin 551) (g : G) : minimumCodes[r.val]! ≤ patternCode (g • representative r) := by
  obtain ⟨v,c,rfl⟩ := action_table_surjective g
  let k : Fin 7200 := ⟨c.val+60*v.val, by omega⟩
  have h := checks r k
  change (decide (minimumCodes[r.val]! ≤ transformed5 (1+k.val+7200*r.val)) && _) = true at h
  have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  change minimumCodes[r.val]! ≤ patternCode (tableAction v c • fromCode representatives5[r.val]!)
  rw [tableAction_code, ← transformed_components r v c]
  simpa only [k, Nat.add_assoc] using hl

theorem separated_from_checks
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true) :
    ∀ i j (g : G), g • representative i = representative j → i = j := by
  exact separate_of_minima representative patternCode (fun r => minimumCodes[r.val]!)
    attainer attained (lower_from_checks checks) minimum_codes_injective
end ColeskiOrbitSeparation
#print axioms ColeskiOrbitSeparation.separated_from_checks

/- END bundled local module OrbitSeparation -/

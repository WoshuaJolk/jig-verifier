import Commons.ColeskiE811Sig20260909_OrbitSeparation
import Commons.ColeskiE811Sig20260909_PaletteFlags

/- BEGIN bundled local module OrbitStabilizers -/

namespace ColeskiOrbitStabilizers
set_option maxRecDepth 8000
set_option maxHeartbeats 0
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiPatternScalar
open ColeskiPaletteAction ColeskiPaletteFlags ColeskiOrbitChecks ColeskiOrbitSeparation

theorem inverse_weight_from_checks
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r : Fin 551) (v : Fin 120) (c : Fin 60)
    (hfix : tableAction v c • representative r = representative r)
    (f : Fin 5 × Fin 6) :
    weight r.val f.1.val f.2.val =
      weight r.val ((tableAction v c)⁻¹ • f).1.val ((tableAction v c)⁻¹ • f).2.val := by
  let k : Fin 7200 := ⟨c.val+60*v.val, by omega⟩
  have hk : k.val/60 = v.val := by dsimp [k]; omega
  have hc : k.val%60 = c.val := by dsimp [k]; omega
  have hcode : transformed5 (1+k.val+7200*r.val) = representatives5[r.val]! := by
    have ht := congrArg patternCode hfix
    change patternCode (tableAction v c • fromCode representatives5[r.val]!) =
      patternCode (fromCode representatives5[r.val]!) at ht
    rw [tableAction_code, code_fromCode _ (representative_bounds r),
      ← transformed_components r v c] at ht
    simpa only [k, Nat.add_assoc] using ht
  have hs := (Bool.and_eq_true_iff.mp (checks r k)).2
  have hst : stabilizerCheck r.val k.val = true := by simpa [hcode] using hs
  have hmem : 6*f.1.val+f.2.val ∈ List.range 30 := List.mem_range.mpr (by omega)
  have hw := List.all_eq_true.mp hst (6*f.1.val+f.2.val) hmem
  have hf1 : (6*f.1.val+f.2.val)/6 = f.1.val := by omega
  have hf2 : (6*f.1.val+f.2.val)%6 = f.2.val := by omega
  rw [(inverse_flag_values v c f).1, (inverse_flag_values v c f).2]
  simpa only [hk,hc,hf1,hf2,beq_iff_eq] using hw

noncomputable def coefficient (r : Fin 551) (f : Fin 5 × Fin 6) : ℝ :=
  (weight r.val f.1.val f.2.val : ℝ) - 170

theorem stabilizers_from_checks
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r : Fin 551) (g : G) (hfix : g • representative r = representative r)
    (f : Fin 5 × Fin 6) : coefficient r (g • f) = coefficient r f := by
  obtain ⟨v,c,rfl⟩ := action_table_surjective g
  have h := inverse_weight_from_checks checks r v c hfix (tableAction v c • f)
  simp only [inv_smul_smul] at h
  unfold coefficient
  rw [h]
end ColeskiOrbitStabilizers
#print axioms ColeskiOrbitStabilizers.stabilizers_from_checks

/- END bundled local module OrbitStabilizers -/

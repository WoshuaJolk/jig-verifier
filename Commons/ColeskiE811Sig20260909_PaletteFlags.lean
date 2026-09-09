import Commons.ColeskiE811Sig20260909_PaletteGroup
import Commons.ColeskiE811Sig20260909_OrbitDataSemantics

/- BEGIN bundled local module PaletteFlags -/

namespace ColeskiPaletteFlags
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPaletteAction
open ColeskiTablePermutations ColeskiOrbitChecks ColeskiOrbitDataSemantics

theorem inverse_color_value (c : Fin 60) (a : Fin 6) :
    ((colorPerm c)⁻¹ a).val = digit inverseColors[c.val]! a.val := by
  let b : Fin 6 := ⟨digit inverseColors[c.val]! a.val, Nat.mod_lt _ (by decide)⟩
  have hb : colorPerm c b = a := Fin.ext (inverse_colors_correct c a).1
  have hi : (colorPerm c)⁻¹ a = b := by rw [← hb]; simp
  rw [hi]

theorem inverse_flag (v : Fin 120) (c : Fin 60) (f : Fin 5 × Fin 6) :
    (tableAction v c)⁻¹ • f = (vertexPerm v f.1, (colorPerm c)⁻¹ f.2) := by
  change (((vertexPerm v)⁻¹)⁻¹ f.1, (colorPerm c)⁻¹ f.2) = _
  rw [inv_inv]

theorem inverse_flag_values (v : Fin 120) (c : Fin 60) (f : Fin 5 × Fin 6) :
    ((tableAction v c)⁻¹ • f).1.val = digit vertexPermutations5[v.val]! f.1.val ∧
    ((tableAction v c)⁻¹ • f).2.val = digit inverseColors[c.val]! f.2.val := by
  rw [inverse_flag]
  exact ⟨vertexPerm_apply v f.1, inverse_color_value c f.2⟩
end ColeskiPaletteFlags
#print axioms ColeskiPaletteFlags.inverse_flag_values

/- END bundled local module PaletteFlags -/

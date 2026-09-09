import Commons.ColeskiE811Sig20260909_ColorCompleteness
import Commons.ColeskiE811Sig20260909_VertexStructural
import Commons.ColeskiE811Sig20260909_PatternAction

/- BEGIN bundled local module PaletteGroup -/

namespace ColeskiPaletteAction
open ColeskiK4Coverage ColeskiPatternAction
open ColeskiTablePermutations ColeskiColorRigidity ColeskiVertexStructural
def colorGroup : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {p | ∀ a b c : Fin 6, good (p a) (p b) (p c) = good a b c}
  one_mem' := by intro a b c; rfl
  mul_mem' := by
    intro p q hp hq a b c
    exact (hp (q a) (q b) (q c)).trans (hq a b c)
  inv_mem' := by
    intro p hp a b c
    have h := hp (p⁻¹ a) (p⁻¹ b) (p⁻¹ c)
    simpa using h.symm

abbrev G := Symmetry (V := Fin 5) colorGroup

noncomputable def tableAction (v : Fin 120) (c : Fin 60) : G :=
  ((vertexPerm v)⁻¹, ⟨colorPerm c, colorPerm_preserves c⟩)

theorem action_table_surjective (g : G) :
    ∃ v : Fin 120, ∃ c : Fin 60, g = tableAction v c := by
  obtain ⟨v,hv⟩ := vertex_table_surjective g.1⁻¹
  obtain ⟨c,hc⟩ := color_table_surjective g.2.val g.2.property
  refine ⟨v,c,?_⟩
  apply Prod.ext
  · change g.1 = (vertexPerm v)⁻¹
    rw [← hv, inv_inv]
  · exact Subtype.ext hc

end ColeskiPaletteAction
#print axioms ColeskiPaletteAction.action_table_surjective

/- END bundled local module PaletteGroup -/

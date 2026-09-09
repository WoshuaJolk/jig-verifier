import Commons.ColeskiE811Sig20260909_PaletteGroup
import Commons.ColeskiE811Sig20260909_PatternTransformAlgebra

/- BEGIN bundled local module PaletteAction -/

namespace ColeskiPaletteAction
open ColeskiK4Coverage ColeskiPatternAction ColeskiPatternCode ColeskiPatternScalar
open ColeskiTablePermutations ColeskiPatternTransform
theorem tableAction_pattern (r : Nat) (v : Fin 120) (c : Fin 60) :
    (tableAction v c) • fromCode r = transformPattern r v c := by
  change transport colorGroup (tableAction v c) (fromCode r) = _
  funext u w
  simp [transport, tableAction, transformPattern]

theorem tableAction_code (r : Nat) (v : Fin 120) (c : Fin 60) :
    patternCode ((tableAction v c) • fromCode r) =
      transformCode r ColeskiK5Coverage.edgeMaps5[v.val]! colorPermutations[c.val]! := by
  rw [tableAction_pattern, transformPattern_code]
end ColeskiPaletteAction
#print axioms ColeskiPaletteAction.action_table_surjective
#print axioms ColeskiPaletteAction.tableAction_code

/- END bundled local module PaletteAction -/

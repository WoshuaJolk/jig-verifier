import Commons.ColeskiE811Sig20260909_FlagSignatureVertexInvariance
import Commons.ColeskiE811Sig20260909_FlagSignatureColorInvariance

/- BEGIN bundled local module FlagSignatureInvariance -/


namespace ColeskiFlagSignature

open ColeskiPatternAction ColeskiPaletteAction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem transport_eq_relabel_recolor (g : G) (x : FivePattern) :
    g • x = relabel g.1 (recolor g.2 x) := by
  rfl

theorem signature_transport (g : G) (x : FivePattern) (flag : FiveFlag) :
    signature (g • x) (g • flag) = signature x flag := by
  rw [transport_eq_relabel_recolor]
  exact (signature_relabel g.1 (recolor g.2 x) (flag.1, g.2.val flag.2)).trans
    (signature_recolor g.2 x flag)

end ColeskiFlagSignature

#print axioms ColeskiFlagSignature.signature_transport

/- END bundled local module FlagSignatureInvariance -/

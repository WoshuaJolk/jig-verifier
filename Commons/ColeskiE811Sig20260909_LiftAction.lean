import Commons.ColeskiE811Sig20260909_FourPermutation
import Commons.ColeskiE811Sig20260909_PatternAction

/- BEGIN bundled local module LiftAction -/

namespace ColeskiLiftAction
open ColeskiFourPermutation ColeskiPatternAction

theorem liftInitial_inverse_apply {n : Nat} (p : Equiv.Perm (Fin n)) (u : Fin n) :
    (liftInitial p)⁻¹ u.castSucc = (p⁻¹ u).castSucc := by
  apply (liftInitial p).injective
  simp [liftInitial_apply]

noncomputable def liftSymmetry {n : Nat} {C : Type*} {H : Subgroup (Equiv.Perm C)}
    (g : Symmetry (V := Fin n) H) : Symmetry (V := Fin (n+1)) H :=
  (liftInitial g.1,g.2)

theorem restrict_lift {n : Nat} {C : Type*} (H : Subgroup (Equiv.Perm C))
    (g : Symmetry (V := Fin n) H) (x : Pattern (Fin (n+1)) C) :
    (fun u v : Fin n => (liftSymmetry g • x) u.castSucc v.castSucc) =
      g • (fun u v : Fin n => x u.castSucc v.castSucc) := by
  funext u v
  change transport H (liftSymmetry g) x u.castSucc v.castSucc =
    transport H g (fun u v : Fin n => x u.castSucc v.castSucc) u v
  simp [transport,liftSymmetry,liftInitial_inverse_apply]
end ColeskiLiftAction
#print axioms ColeskiLiftAction.restrict_lift

/- END bundled local module LiftAction -/

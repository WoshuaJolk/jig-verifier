import Mathlib

/- BEGIN bundled local module PatternAction -/

namespace ColeskiPatternAction

abbrev Pattern (V C : Type*) := V → V → Option C
abbrev Symmetry {V C : Type*} (H : Subgroup (Equiv.Perm C)) := Equiv.Perm V × H

def transport {V C : Type*} (H : Subgroup (Equiv.Perm C))
    (g : Symmetry (V := V) H) (x : Pattern V C) : Pattern V C :=
  fun u v => (x (g.1⁻¹ u) (g.1⁻¹ v)).map (fun c => (g.2 : Equiv.Perm C) c)

instance patternAction {V C : Type*} (H : Subgroup (Equiv.Perm C)) :
    MulAction (Symmetry (V := V) H) (Pattern V C) where
  smul := transport H
  one_smul := by
    intro x
    funext u v
    change transport H (1 : Symmetry H) x u v = x u v
    simp [transport]
  mul_smul := by
    intro g h x
    funext u v
    change transport H (g * h) x u v = transport H g (transport H h x) u v
    simp [transport, mul_inv_rev, Equiv.Perm.mul_apply, Option.map_map,
      Function.comp_def]

instance flagAction {V C : Type*} (H : Subgroup (Equiv.Perm C)) :
    MulAction (Symmetry (V := V) H) (V × C) where
  smul g f := (g.1 f.1, (g.2 : Equiv.Perm C) f.2)
  one_smul := by intro f; rfl
  mul_smul := by intro g h f; rfl

theorem transport_symmetric {V C : Type*} (H : Subgroup (Equiv.Perm C))
    (g : Symmetry (V := V) H) (x : Pattern V C)
    (h : ∀ u v, x u v = x v u) :
    ∀ u v, transport H g x u v = transport H g x v u := by
  intro u v
  simp only [transport, h]

theorem transport_no_loops {V C : Type*} (H : Subgroup (Equiv.Perm C))
    (g : Symmetry (V := V) H) (x : Pattern V C)
    (h : ∀ u, x u u = none) :
    ∀ u, transport H g x u u = none := by
  intro u
  simp [transport, h]
end ColeskiPatternAction
#print axioms ColeskiPatternAction.transport_symmetric
#print axioms ColeskiPatternAction.transport_no_loops

/- END bundled local module PatternAction -/

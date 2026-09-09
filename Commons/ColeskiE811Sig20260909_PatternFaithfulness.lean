import Commons.ColeskiE811Sig20260909_PatternCode

/- BEGIN bundled local module PatternFaithfulness -/

namespace ColeskiPatternFaithfulness
open ColeskiPatternAction ColeskiPatternCode

theorem code_injective (x y : Pattern (Fin 5) (Fin 6))
    (xs : ∀ u v, x u v = x v u) (xd : ∀ u, x u u = none)
    (xf : ∀ u v, u ≠ v → x u v ≠ none)
    (ys : ∀ u v, y u v = y v u) (yd : ∀ u, y u u = none)
    (yf : ∀ u v, u ≠ v → y u v ≠ none)
    (h : patternCode x = patternCode y) : x = y := by
  rw [← reconstruct x xs xd xf, ← reconstruct y ys yd yf, h]

theorem transport_full {V C : Type*} (H : Subgroup (Equiv.Perm C))
    (g : Symmetry (V := V) H) (x : Pattern V C)
    (hf : ∀ u v, u ≠ v → x u v ≠ none) :
    ∀ u v, u ≠ v → transport H g x u v ≠ none := by
  intro u v h
  have hi : g.1⁻¹ u ≠ g.1⁻¹ v := (g.1⁻¹).injective.ne h
  have hx := hf _ _ hi
  change (x (g.1⁻¹ u) (g.1⁻¹ v)).map _ ≠ none
  cases he : x (g.1⁻¹ u) (g.1⁻¹ v) with
  | none => exact False.elim (hx he)
  | some c => simp

theorem reconstruct_transport (H : Subgroup (Equiv.Perm (Fin 6)))
    (g : Symmetry (V := Fin 5) H) (n : Nat) :
    fromCode (patternCode (transport H g (fromCode n))) = transport H g (fromCode n) := by
  exact reconstruct _
    (transport_symmetric H g _ (fromCode_symmetric n))
    (transport_no_loops H g _ (fromCode_no_loops n))
    (transport_full H g _ (fromCode_full n))
end ColeskiPatternFaithfulness
#print axioms ColeskiPatternFaithfulness.code_injective
#print axioms ColeskiPatternFaithfulness.reconstruct_transport

/- END bundled local module PatternFaithfulness -/

import Commons.ColeskiE811Sig20260909_PaletteGroup
import Commons.ColeskiE811Sig20260909_PatternFaithfulness

/- BEGIN bundled local module PatternValidity -/

namespace ColeskiPatternValidity
open ColeskiPatternAction ColeskiPaletteAction ColeskiPatternFaithfulness ColeskiK4Coverage

def Valid {V : Type*} (x : Pattern V (Fin 6)) : Prop :=
  (∀ u v, x u v = x v u) ∧ (∀ u, x u u = none) ∧
  (∀ u v, u ≠ v → x u v ≠ none) ∧
  (∀ u v w, u ≠ v → u ≠ w → v ≠ w →
    good ((x u v).getD 0) ((x u w).getD 0) ((x v w).getD 0) = true)

theorem getD_map (p : Equiv.Perm (Fin 6)) (o : Option (Fin 6)) (h : o ≠ none) :
    (o.map p).getD 0 = p (o.getD 0) := by
  cases o <;> simp_all

theorem valid_transport {V : Type*} (g : Symmetry (V := V) colorGroup)
    (x : Pattern V (Fin 6)) (h : Valid x) : Valid (g • x) := by
  refine ⟨transport_symmetric colorGroup g x h.1,
    transport_no_loops colorGroup g x h.2.1,
    transport_full colorGroup g x h.2.2.1,?_⟩
  intro u v w huv huw hvw
  have hiuv := (g.1⁻¹).injective.ne huv
  have hiuw := (g.1⁻¹).injective.ne huw
  have hivw := (g.1⁻¹).injective.ne hvw
  change good (((x (g.1⁻¹ u) (g.1⁻¹ v)).map g.2.val).getD 0)
    (((x (g.1⁻¹ u) (g.1⁻¹ w)).map g.2.val).getD 0)
    (((x (g.1⁻¹ v) (g.1⁻¹ w)).map g.2.val).getD 0) = true
  rw [getD_map _ _ (h.2.2.1 _ _ hiuv),getD_map _ _ (h.2.2.1 _ _ hiuw),
    getD_map _ _ (h.2.2.1 _ _ hivw),g.2.property]
  exact h.2.2.2 _ _ _ hiuv hiuw hivw

theorem valid_restrict {V W : Type*} (i : W ↪ V)
    (x : Pattern V (Fin 6)) (h : Valid x) : Valid (fun u v => x (i u) (i v)) := by
  refine ⟨fun u v => h.1 _ _,fun u => h.2.1 _,?_,?_⟩
  · intro u v huv
    exact h.2.2.1 _ _ (i.injective.ne huv)
  · intro u v w huv huw hvw
    exact h.2.2.2 _ _ _ (i.injective.ne huv) (i.injective.ne huw) (i.injective.ne hvw)
end ColeskiPatternValidity
#print axioms ColeskiPatternValidity.valid_transport
#print axioms ColeskiPatternValidity.valid_restrict

/- END bundled local module PatternValidity -/

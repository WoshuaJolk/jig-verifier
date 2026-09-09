import Commons.ColeskiE811Sig20260909_SixEdgePattern

/- BEGIN bundled local module DeletedEdgeSplit -/


namespace ColeskiDeletedEdgeSplit
open ColeskiSixVertexLaw
abbrev BaseEdge := {p : Fin 5 × Fin 5 // p.1 < p.2}

def base (z : Fin 6) (e : BaseEdge) : Edge :=
  ⟨(z.succAbove e.val.1,z.succAbove e.val.2),by
    have h := e.property
    exact (Fin.succAboveOrderEmb z).strictMono h⟩

def star (z : Fin 6) (m : Fin 5) : Edge :=
  ⟨(min z (z.succAbove m),max z (z.succAbove m)),by
    have h := Fin.ne_succAbove z m
    exact min_lt_max.mpr h⟩

def splitMap (z : Fin 6) : BaseEdge ⊕ Fin 5 → Edge := Sum.elim (base z) (star z)

theorem split_bijective : ∀ z : Fin 6, Function.Bijective (splitMap z) := by decide

noncomputable def edgeEquiv (z : Fin 6) : BaseEdge ⊕ Fin 5 ≃ Edge :=
  Equiv.ofBijective (splitMap z) (split_bijective z)

theorem base_apply (z : Fin 6) (e : BaseEdge) : edgeEquiv z (.inl e) = base z e := rfl
theorem star_apply (z : Fin 6) (m : Fin 5) : edgeEquiv z (.inr m) = star z m := rfl

end ColeskiDeletedEdgeSplit
#print axioms ColeskiDeletedEdgeSplit.split_bijective

/- END bundled local module DeletedEdgeSplit -/

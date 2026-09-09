import Commons.ColeskiE811Sig20260909_DeletionAction

/- BEGIN bundled local module SeparatorInvariance -/

namespace ColeskiSeparatorInvariance
open ColeskiPatternAction ColeskiPaletteAction ColeskiPatternValidity
open ColeskiDeletionAction ColeskiDeletionPermutation ColeskiOrbitCoefficient ColeskiOrbitChecks

noncomputable def term (x : Pattern (Fin 6) (Fin 6)) (z : Fin 6) (m : Fin 5) (c : Fin 6) : ℝ :=
  coefficientFor (deletePattern x z) (m,c) *
    ((if (x (z.succAbove m) z).getD 0 = c then (6 : ℝ) else 0) - 1)

noncomputable def separator (x : Pattern (Fin 6) (Fin 6)) : ℝ :=
  ∑ z : Fin 6, ∑ m : Fin 5, ∑ c : Fin 6, term x z m c

theorem term_transport
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (g : Symmetry (V := Fin 6) colorGroup) (x : Pattern (Fin 6) (Fin 6))
    (h : Valid x) (z : Fin 6) (m : Fin 5) (c : Fin 6) :
    term (g • x) (g.1 z) (deletionPerm g.1 z m) (g.2.val c) = term x z m c := by
  unfold term
  rw [deletion_coefficient_transport checks g x h z m c,edge_transport g x h z m]
  simp only [g.2.val.injective.eq_iff]

theorem separator_transport
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (g : Symmetry (V := Fin 6) colorGroup) (x : Pattern (Fin 6) (Fin 6))
    (h : Valid x) : separator (g • x) = separator x := by
  unfold separator
  rw [← Equiv.sum_comp g.1 (fun z => ∑ m : Fin 5, ∑ c : Fin 6, term (g • x) z m c)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Equiv.sum_comp (deletionPerm g.1 z)
    (fun m => ∑ c : Fin 6, term (g • x) (g.1 z) m c)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Equiv.sum_comp g.2.val
    (fun c => term (g • x) (g.1 z) (deletionPerm g.1 z m) c)]
  apply Finset.sum_congr rfl
  intro c hc
  exact term_transport checks g x h z m c
end ColeskiSeparatorInvariance
#print axioms ColeskiSeparatorInvariance.separator_transport

/- END bundled local module SeparatorInvariance -/

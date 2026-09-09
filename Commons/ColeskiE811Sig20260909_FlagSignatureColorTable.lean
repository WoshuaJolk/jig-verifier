import Commons.ColeskiE811Sig20260909_FlagSignature
import Commons.ColeskiE811Sig20260909_PaletteGroup

/- BEGIN bundled local module FlagSignatureColorTable -/


namespace ColeskiFlagSignature

open ColeskiK4Coverage ColeskiTablePermutations ColeskiColorRigidity
open ColeskiPaletteAction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem paletteColor_eq_colorPerm (p : Fin 60) (c : Fin 6) :
    paletteColor p c = colorPerm p c := by
  apply Fin.ext
  exact colorPerm_apply p c |>.symm

theorem colorPerm_injective : Function.Injective colorPerm := by
  intro p q h
  have h0 : digit colorPermutations[p.val]! 0 = digit colorPermutations[q.val]! 0 := by
    have hx := congrArg (fun e => (e 0).val) h
    rw [colorPerm_apply, colorPerm_apply] at hx
    exact hx
  have h1 : digit colorPermutations[p.val]! 1 = digit colorPermutations[q.val]! 1 := by
    have hx := congrArg (fun e => (e 1).val) h
    rw [colorPerm_apply, colorPerm_apply] at hx
    exact hx
  have h2 : digit colorPermutations[p.val]! 2 = digit colorPermutations[q.val]! 2 := by
    have hx := congrArg (fun e => (e 2).val) h
    rw [colorPerm_apply, colorPerm_apply] at hx
    exact hx
  have table_unique : ∀ a b : Fin 60,
      digit colorPermutations[a.val]! 0 = digit colorPermutations[b.val]! 0 →
      digit colorPermutations[a.val]! 1 = digit colorPermutations[b.val]! 1 →
      digit colorPermutations[a.val]! 2 = digit colorPermutations[b.val]! 2 → a = b := by
    decide
  exact table_unique p q h0 h1 h2

noncomputable def tableColor (p : Fin 60) : colorGroup :=
  ⟨colorPerm p, colorPerm_preserves p⟩

theorem tableColor_injective : Function.Injective tableColor := by
  intro p q h
  apply colorPerm_injective
  exact congrArg Subtype.val h

theorem tableColor_surjective : Function.Surjective tableColor := by
  intro q
  obtain ⟨p, hp⟩ := color_table_surjective q.val q.property
  refine ⟨p, Subtype.ext ?_⟩
  exact hp.symm

noncomputable def tableColorEquiv : Fin 60 ≃ colorGroup :=
  Equiv.ofBijective tableColor ⟨tableColor_injective, tableColor_surjective⟩

theorem tableColorEquiv_apply (p : Fin 60) : tableColorEquiv p = tableColor p := rfl

noncomputable def composeEquiv (q : colorGroup) : Equiv.Perm (Fin 60) :=
  tableColorEquiv |>.trans ((Equiv.mulRight q).trans tableColorEquiv.symm)

theorem tableColor_composeEquiv (q : colorGroup) (p : Fin 60) :
    tableColor (composeEquiv q p) = tableColor p * q := by
  change tableColorEquiv (tableColorEquiv.symm (tableColorEquiv p * q)) = _
  simp only [Equiv.apply_symm_apply, tableColorEquiv_apply]

theorem paletteColor_composeEquiv (q : colorGroup) (p : Fin 60) (c : Fin 6) :
    paletteColor (composeEquiv q p) c = paletteColor p (q.val c) := by
  rw [paletteColor_eq_colorPerm, paletteColor_eq_colorPerm]
  have h := congrArg Subtype.val (tableColor_composeEquiv q p)
  exact DFunLike.congr_fun h c

end ColeskiFlagSignature

#print axioms ColeskiFlagSignature.paletteColor_composeEquiv

/- END bundled local module FlagSignatureColorTable -/

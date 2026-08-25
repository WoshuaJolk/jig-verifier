import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos60C4Multiplicity.EightFrames

private def fourMap (a b c d : Fin 4) : Fin 4 → Fin 4
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

private theorem cycle4_adj_iff (a b : Fin 4) :
    (cycleGraph 4).Adj a b ↔
      (a = 0 ∧ b = 1) ∨
      (a = 1 ∧ b = 0) ∨
      (a = 1 ∧ b = 2) ∨
      (a = 2 ∧ b = 1) ∨
      (a = 2 ∧ b = 3) ∨
      (a = 3 ∧ b = 2) ∨
      (a = 3 ∧ b = 0) ∨
      (a = 0 ∧ b = 3) := by
  fin_cases a <;> fin_cases b <;> decide

private def dihedralFun : Fin 4 × Bool → Fin 4 → Fin 4
  | ⟨⟨0, _⟩, false⟩ => fourMap 0 1 2 3
  | ⟨⟨1, _⟩, false⟩ => fourMap 1 2 3 0
  | ⟨⟨2, _⟩, false⟩ => fourMap 2 3 0 1
  | ⟨⟨3, _⟩, false⟩ => fourMap 3 0 1 2
  | ⟨⟨0, _⟩, true⟩ => fourMap 0 3 2 1
  | ⟨⟨1, _⟩, true⟩ => fourMap 1 0 3 2
  | ⟨⟨2, _⟩, true⟩ => fourMap 2 1 0 3
  | ⟨⟨3, _⟩, true⟩ => fourMap 3 2 1 0

private def dihedralInv : Fin 4 × Bool → Fin 4 → Fin 4
  | ⟨⟨0, _⟩, false⟩ => dihedralFun (0, false)
  | ⟨⟨1, _⟩, false⟩ => dihedralFun (3, false)
  | ⟨⟨2, _⟩, false⟩ => dihedralFun (2, false)
  | ⟨⟨3, _⟩, false⟩ => dihedralFun (1, false)
  | ⟨⟨0, _⟩, true⟩ => dihedralFun (0, true)
  | ⟨⟨1, _⟩, true⟩ => dihedralFun (1, true)
  | ⟨⟨2, _⟩, true⟩ => dihedralFun (2, true)
  | ⟨⟨3, _⟩, true⟩ => dihedralFun (3, true)

private def dihedralPerm (p : Fin 4 × Bool) : Fin 4 ≃ Fin 4 where
  toFun := dihedralFun p
  invFun := dihedralInv p
  left_inv i := by
    rcases p with ⟨a, flip⟩
    fin_cases a <;> cases flip <;> fin_cases i <;> rfl
  right_inv i := by
    rcases p with ⟨a, flip⟩
    fin_cases a <;> cases flip <;> fin_cases i <;> rfl

private def dihedralAut (p : Fin 4 × Bool) :
    cycleGraph 4 ≃g cycleGraph 4 where
  toEquiv := dihedralPerm p
  map_rel_iff' := by
    intro i j
    rcases p with ⟨a, flip⟩
    fin_cases a <;> cases flip <;> fin_cases i <;> fin_cases j <;> decide

private theorem dihedralAut_injective : Function.Injective dihedralAut := by
  rintro ⟨a, flip⟩ ⟨b, turn⟩ h
  have h0 := congrArg
    (fun e : cycleGraph 4 ≃g cycleGraph 4 => e (0 : Fin 4)) h
  have h1 := congrArg
    (fun e : cycleGraph 4 ≃g cycleGraph 4 => e (1 : Fin 4)) h
  fin_cases a <;> fin_cases b <;> cases flip <;> cases turn <;>
    simp [dihedralAut, dihedralPerm, dihedralFun, fourMap] at h0 h1 ⊢

set_option maxHeartbeats 1000000 in
private theorem dihedralAut_surjective : Function.Surjective dihedralAut := by
  intro e
  have h01 : (cycleGraph 4).Adj (e 0) (e 1) :=
    e.map_rel_iff.mpr (by decide)
  have h12 : (cycleGraph 4).Adj (e 1) (e 2) :=
    e.map_rel_iff.mpr (by decide)
  have h23 : (cycleGraph 4).Adj (e 2) (e 3) :=
    e.map_rel_iff.mpr (by decide)
  have h30 : (cycleGraph 4).Adj (e 3) (e 0) :=
    e.map_rel_iff.mpr (by decide)
  have h02 : e (0 : Fin 4) ≠ e 2 :=
    fun h => (by decide : (0 : Fin 4) ≠ 2) (e.injective h)
  have h13 : e (1 : Fin 4) ≠ e 3 :=
    fun h => (by decide : (1 : Fin 4) ≠ 3) (e.injective h)
  have hall :
      (cycleGraph 4).Adj (e 0) (e 1) ∧
      (cycleGraph 4).Adj (e 1) (e 2) ∧
      (cycleGraph 4).Adj (e 2) (e 3) ∧
      (cycleGraph 4).Adj (e 3) (e 0) :=
    ⟨h01, h12, h23, h30⟩
  generalize h0 : e 0 = a at *
  generalize h1 : e 1 = b at *
  generalize h2 : e 2 = c at *
  generalize h3 : e 3 = d at *
  let p : Fin 4 × Bool :=
    if b = dihedralFun (a, false) 1 then (a, false) else (a, true)
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cycle4_adj_iff] at hall <;>
    refine ⟨p, ?_⟩ <;>
    apply RelIso.ext <;>
    intro i <;>
    fin_cases i <;>
    simp_all [p, dihedralAut, dihedralPerm, dihedralFun, fourMap]

private noncomputable def dihedralEquiv :
    (Fin 4 × Bool) ≃ (cycleGraph 4 ≃g cycleGraph 4) :=
  Equiv.ofBijective dihedralAut
    ⟨dihedralAut_injective, dihedralAut_surjective⟩

private theorem aut_card :
    Nat.card (cycleGraph 4 ≃g cycleGraph 4) = 8 := by
  rw [Nat.card_congr dihedralEquiv.symm]
  simp

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

private abbrev CopyFiber (H' : G.Subgraph) :=
  {f : (cycleGraph 4).Copy G // f.toSubgraph = H'}

private theorem transportedIso_val
    (f : (cycleGraph 4).Copy G) (H' : G.Subgraph)
    (h : f.toSubgraph = H') (i : Fin 4) :
    (((h ▸ f.isoToSubgraph) i : H'.verts) : V) = f i := by
  subst H'
  rfl

private noncomputable def fiberCopy {H' : G.Subgraph}
    (e : H'.coe ≃g cycleGraph 4)
    (a : cycleGraph 4 ≃g cycleGraph 4) :
    (cycleGraph 4).Copy G :=
  ⟨H'.hom.comp (e.symm.comp a).toHom,
    Subgraph.hom_injective.comp (e.symm.comp a).injective⟩

private theorem fiberCopy_toSubgraph {H' : G.Subgraph}
    (e : H'.coe ≃g cycleGraph 4)
    (a : cycleGraph 4 ≃g cycleGraph 4) :
    (fiberCopy G e a).toSubgraph = H' := by
  simp [fiberCopy, SimpleGraph.Copy.toSubgraph, Subgraph.map_comp]

private noncomputable def copyFiberSigmaEquiv :
    (cycleGraph 4).Copy G ≃
      Σ H' : G.Subgraph, CopyFiber G H' where
  toFun f := ⟨f.toSubgraph, ⟨f, rfl⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨H', ⟨f, hf⟩⟩
    dsimp
    cases hf
    rfl

private noncomputable def fiberAutEquiv {H' : G.Subgraph}
    (e : H'.coe ≃g cycleGraph 4) :
    CopyFiber G H' ≃ (cycleGraph 4 ≃g cycleGraph 4) where
  toFun f := e.comp (f.2 ▸ f.1.isoToSubgraph)
  invFun a := ⟨fiberCopy G e a, fiberCopy_toSubgraph G e a⟩
  left_inv f := by
    apply Subtype.ext
    apply SimpleGraph.Copy.ext
    intro i
    change ↑(e.symm (e ((f.2 ▸ f.1.isoToSubgraph) i))) = f.1 i
    rw [e.symm_apply_apply]
    exact transportedIso_val G f.1 H' f.2 i
  right_inv a := by
    let F := fiberCopy G e a
    have hF : F.toSubgraph = H' := fiberCopy_toSubgraph G e a
    have hiso : (hF ▸ F.isoToSubgraph) = e.symm.comp a := by
      apply RelIso.ext
      intro i
      apply Subtype.ext
      exact transportedIso_val G F H' hF i
    apply RelIso.ext
    intro i
    change e ((hF ▸ F.isoToSubgraph) i) = a i
    rw [hiso]
    simp

private theorem fiber_card_eq_eight {H' : G.Subgraph}
    (h : Nonempty (H'.coe ≃g cycleGraph 4)) :
    Nat.card (CopyFiber G H') = 8 := by
  calc
    _ = Nat.card (cycleGraph 4 ≃g cycleGraph 4) :=
      Nat.card_congr (fiberAutEquiv G h.some)
    _ = 8 := aut_card

private theorem multiplicity (G : SimpleGraph V) :
    Nat.card ((cycleGraph 4).Copy G) =
      8 * {H' : G.Subgraph |
        Nonempty (H'.coe ≃g cycleGraph 4)}.ncard := by
  classical
  let B : Set G.Subgraph :=
    {H' | Nonempty (H'.coe ≃g cycleGraph 4)}
  calc
    _ = Nat.card (Σ H' : G.Subgraph, CopyFiber G H') :=
      Nat.card_congr (copyFiberSigmaEquiv G)
    _ = ∑ H' : G.Subgraph, Nat.card (CopyFiber G H') :=
      Nat.card_sigma
    _ = ∑ H' : G.Subgraph, if H' ∈ B then 8 else 0 := by
      apply Finset.sum_congr rfl
      intro H' _
      simp only [B, Set.mem_setOf_eq]
      split_ifs with h
      · exact fiber_card_eq_eight G h
      · haveI : IsEmpty (CopyFiber G H') := ⟨fun f => by
          apply h
          exact ⟨(f.2 ▸ f.1.isoToSubgraph).symm⟩⟩
        simp
    _ = 8 * B.ncard := by
      calc
        (∑ H' : G.Subgraph, if H' ∈ B then 8 else 0) =
            8 * ∑ H' : G.Subgraph, if H' ∈ B then 1 else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro H' _
          by_cases h : H' ∈ B <;> simp [h]
        _ = 8 * B.ncard := by
          congr 1
          rw [Finset.sum_boole]
          rw [Set.ncard_eq_toFinset_card B]
          apply congrArg Finset.card
          ext H'
          simp [B]
    _ = _ := rfl

theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      Nat.card ((cycleGraph 4).Copy G) =
        8 * {H' : G.Subgraph |
          Nonempty (H'.coe ≃g cycleGraph 4)}.ncard := by
  intro n G
  exact multiplicity G

end Submissions.Erdos60C4Multiplicity.EightFrames

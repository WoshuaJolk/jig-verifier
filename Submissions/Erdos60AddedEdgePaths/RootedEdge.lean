import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos60AddedEdgePaths.RootedEdge

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private def fourMap (a b c d : V) : Fin 4 → V
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

private abbrev ThreePaths (u v : V) :=
  {p : V × V //
    G.Adj u p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 v ∧
      p.1 ≠ v ∧ p.2 ≠ u}

private abbrev RootedNewC4 (u v : V) :=
  {f : (cycleGraph 4).Copy (G ⊔ edge u v) //
    f (0 : Fin 4) = u ∧ f (1 : Fin 4) = v}

private def pathCopy {u v : V} (huv : u ≠ v)
    (p : ThreePaths G u v) :
    (cycleGraph 4).Copy (G ⊔ edge u v) := by
  let x := p.1.1
  let y := p.1.2
  have hux : G.Adj u x := p.2.1
  have hxy : G.Adj x y := p.2.2.1
  have hyv : G.Adj y v := p.2.2.2.1
  have hxv : x ≠ v := p.2.2.2.2.1
  have hyu : y ≠ u := p.2.2.2.2.2
  have hux' := hux.ne
  have hxy' := hxy.ne
  have hyv' := hyv.ne
  have hvu : v ≠ u := huv.symm
  refine
    { toHom :=
        { toFun := fourMap u v y x
          map_rel' := by
            intro a b hab
            rw [cycle4_adj_iff] at hab
            rcases hab with h | h | h | h | h | h | h | h
            · obtain ⟨rfl, rfl⟩ := h
              apply (show edge u v ≤ G ⊔ edge u v from le_sup_right)
              rw [edge_adj]
              simp [fourMap, huv, hvu]
            · obtain ⟨rfl, rfl⟩ := h
              apply (show edge u v ≤ G ⊔ edge u v from le_sup_right)
              rw [edge_adj]
              simp [fourMap, huv, hvu]
            · obtain ⟨rfl, rfl⟩ := h
              exact (show G ≤ G ⊔ edge u v from le_sup_left) hyv.symm
            · obtain ⟨rfl, rfl⟩ := h
              exact (show G ≤ G ⊔ edge u v from le_sup_left) hyv
            · obtain ⟨rfl, rfl⟩ := h
              exact (show G ≤ G ⊔ edge u v from le_sup_left) hxy.symm
            · obtain ⟨rfl, rfl⟩ := h
              exact (show G ≤ G ⊔ edge u v from le_sup_left) hxy
            · obtain ⟨rfl, rfl⟩ := h
              exact (show G ≤ G ⊔ edge u v from le_sup_left) hux.symm
            · obtain ⟨rfl, rfl⟩ := h
              exact (show G ≤ G ⊔ edge u v from le_sup_left) hux }
      injective' := by
        intro a b h
        fin_cases a <;> fin_cases b <;>
          simp_all [fourMap] }

@[simp] private theorem pathCopy_zero {u v : V} (huv : u ≠ v)
    (p : ThreePaths G u v) :
    pathCopy G huv p (0 : Fin 4) = u := by
  rcases p with ⟨⟨x, y⟩, h⟩
  rfl

@[simp] private theorem pathCopy_one {u v : V} (huv : u ≠ v)
    (p : ThreePaths G u v) :
    pathCopy G huv p (1 : Fin 4) = v := by
  rcases p with ⟨⟨x, y⟩, h⟩
  rfl

private noncomputable def pathEquiv {u v : V}
    (huv : u ≠ v) :
    ThreePaths G u v ≃ RootedNewC4 G u v where
  toFun p := ⟨pathCopy G huv p, by simp, by simp⟩
  invFun f := by
    have h12 : (cycleGraph 4).Adj (1 : Fin 4) 2 := by decide
    have h23 : (cycleGraph 4).Adj (2 : Fin 4) 3 := by decide
    have h30 : (cycleGraph 4).Adj (3 : Fin 4) 0 := by decide
    have hvyK := f.1.toHom.map_adj h12
    have hyxK := f.1.toHom.map_adj h23
    have hxuK := f.1.toHom.map_adj h30
    have h20 : f.1 (2 : Fin 4) ≠ f.1 0 :=
      fun h => (by decide : (2 : Fin 4) ≠ 0) (f.1.injective h)
    have h21 : f.1 (2 : Fin 4) ≠ f.1 1 :=
      fun h => (by decide : (2 : Fin 4) ≠ 1) (f.1.injective h)
    have h30' : f.1 (3 : Fin 4) ≠ f.1 0 :=
      fun h => (by decide : (3 : Fin 4) ≠ 0) (f.1.injective h)
    have h31 : f.1 (3 : Fin 4) ≠ f.1 1 :=
      fun h => (by decide : (3 : Fin 4) ≠ 1) (f.1.injective h)
    refine ⟨(f.1 3, f.1 2), ?_, ?_, ?_, ?_, ?_⟩
    · rw [sup_adj] at hxuK
      rcases hxuK with h | h
      · simpa [f.2.1] using h.symm
      · rw [edge_adj] at h
        rcases h.1 with h | h
        · exact False.elim (h30' (h.1.trans f.2.1.symm))
        · exact False.elim (h31 (h.1.trans f.2.2.symm))
    · rw [sup_adj] at hyxK
      rcases hyxK with h | h
      · exact h.symm
      · rw [edge_adj] at h
        rcases h.1 with h | h
        · exact False.elim (h20 (h.1.trans f.2.1.symm))
        · exact False.elim (h21 (h.1.trans f.2.2.symm))
    · rw [sup_adj] at hvyK
      rcases hvyK with h | h
      · simpa [f.2.2] using h.symm
      · rw [edge_adj] at h
        rcases h.1 with h | h
        · exact False.elim (huv (h.1.symm.trans f.2.2))
        · exact False.elim (h20 (h.2.trans f.2.1.symm))
    · simpa [f.2.2] using h31
    · simpa [f.2.1] using h20
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv f := by
    apply Subtype.ext
    apply SimpleGraph.Copy.ext
    intro i
    fin_cases i
    · exact f.2.1.symm
    · exact f.2.2.symm
    · rfl
    · rfl

theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (u v : Fin n), u ≠ v → ¬G.Adj u v →
      Nat.card
          {f : (cycleGraph 4).Copy (G ⊔ edge u v) //
            f (0 : Fin 4) = u ∧ f (1 : Fin 4) = v} =
        Nat.card
          {p : Fin n × Fin n //
            G.Adj u p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 v ∧
              p.1 ≠ v ∧ p.2 ≠ u} := by
  intro n G _ u v huv _
  exact Nat.card_congr (pathEquiv G huv).symm

end Submissions.Erdos60AddedEdgePaths.RootedEdge

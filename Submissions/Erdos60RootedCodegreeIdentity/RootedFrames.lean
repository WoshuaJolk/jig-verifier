import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos60RootedCodegreeIdentity.RootedFrames

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private abbrev CN (u v : V) := G.commonNeighbors u v

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

private def frameCopy {u v : V} (huv : u ≠ v)
    (x y : CN G u v) (hxy : x ≠ y) :
    (cycleGraph 4).Copy G := by
  have hux : G.Adj u x.1 := x.2.1
  have hvx : G.Adj v x.1 := x.2.2
  have huy : G.Adj u y.1 := y.2.1
  have hvy : G.Adj v y.1 := y.2.2
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  refine
    { toHom :=
        { toFun := fourMap u x.1 v y.1
          map_rel' := by
            intro a b hab
            rw [cycle4_adj_iff] at hab
            rcases hab with h | h | h | h | h | h | h | h
            · obtain ⟨rfl, rfl⟩ := h
              exact hux
            · obtain ⟨rfl, rfl⟩ := h
              exact hux.symm
            · obtain ⟨rfl, rfl⟩ := h
              exact hvx.symm
            · obtain ⟨rfl, rfl⟩ := h
              exact hvx
            · obtain ⟨rfl, rfl⟩ := h
              exact hvy
            · obtain ⟨rfl, rfl⟩ := h
              exact hvy.symm
            · obtain ⟨rfl, rfl⟩ := h
              exact huy.symm
            · obtain ⟨rfl, rfl⟩ := h
              exact huy }
      injective' := by
        have hux' : u ≠ x.1 := hux.ne
        have hvx' : v ≠ x.1 := hvx.ne
        have huy' : u ≠ y.1 := huy.ne
        have hvy' : v ≠ y.1 := hvy.ne
        intro a b hab
        fin_cases a <;> fin_cases b <;>
          simp_all [fourMap] }

private abbrev OrderedCNPair (u v : V) :=
  ↥((Finset.univ : Finset (CN G u v)).offDiag)

private def frameMap {u v : V} (huv : u ≠ v) :
    OrderedCNPair G u v → (cycleGraph 4).Copy G := fun p =>
  frameCopy G huv p.1.1 p.1.2 (by
    simpa using (Finset.mem_offDiag.mp p.2).2)

@[simp]
private theorem frameMap_zero {u v : V} (huv : u ≠ v)
    (p : OrderedCNPair G u v) :
    frameMap G huv p (0 : Fin 4) = u := by
  rfl

@[simp]
private theorem frameMap_one {u v : V} (huv : u ≠ v)
    (p : OrderedCNPair G u v) :
    frameMap G huv p (1 : Fin 4) = p.1.1 := by
  rfl

@[simp]
private theorem frameMap_two {u v : V} (huv : u ≠ v)
    (p : OrderedCNPair G u v) :
    frameMap G huv p (2 : Fin 4) = v := by
  rfl

@[simp]
private theorem frameMap_three {u v : V} (huv : u ≠ v)
    (p : OrderedCNPair G u v) :
    frameMap G huv p (3 : Fin 4) = p.1.2 := by
  rfl

private abbrev RootedC4Copy (u v : V) :=
  {f : (cycleGraph 4).Copy G //
    f (0 : Fin 4) = u ∧ f (2 : Fin 4) = v}

private noncomputable def rootedFrameEquiv {u v : V} (huv : u ≠ v) :
    OrderedCNPair G u v ≃ RootedC4Copy G u v where
  toFun p := ⟨frameMap G huv p, by simp⟩
  invFun f := by
    have h01 : (cycleGraph 4).Adj (0 : Fin 4) 1 := by decide
    have h21 : (cycleGraph 4).Adj (2 : Fin 4) 1 := by decide
    have h03 : (cycleGraph 4).Adj (0 : Fin 4) 3 := by decide
    have h23 : (cycleGraph 4).Adj (2 : Fin 4) 3 := by decide
    let x : CN G u v :=
      ⟨f.1 1, by
        constructor
        · simpa [f.2.1] using f.1.toHom.map_adj h01
        · simpa [f.2.2] using f.1.toHom.map_adj h21⟩
    let y : CN G u v :=
      ⟨f.1 3, by
        constructor
        · simpa [f.2.1] using f.1.toHom.map_adj h03
        · simpa [f.2.2] using f.1.toHom.map_adj h23⟩
    refine ⟨(x, y), ?_⟩
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    intro h
    have himages : f.1 (1 : Fin 4) = f.1 (3 : Fin 4) := by
      simpa [x, y] using congrArg Subtype.val h
    have h13 : (1 : Fin 4) = 3 := f.1.injective himages
    exact (by decide : (1 : Fin 4) ≠ 3) h13
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv f := by
    apply Subtype.ext
    apply SimpleGraph.Copy.ext
    intro i
    fin_cases i
    · simpa using f.2.1.symm
    · rfl
    · simpa using f.2.2.symm
    · rfl

private theorem card_orderedCNPair (u v : V) :
    Fintype.card (OrderedCNPair G u v) =
      Fintype.card (CN G u v) *
        (Fintype.card (CN G u v) - 1) := by
  calc
    _ = ((Finset.univ : Finset (CN G u v)).offDiag).card :=
      Fintype.card_coe _
    _ = (Finset.univ : Finset (CN G u v)).card ^ 2 -
        (Finset.univ : Finset (CN G u v)).card := by
      rw [Finset.offDiag_card, pow_two]
    _ = _ := by simp [pow_two, Nat.mul_sub_left_distrib]

private theorem rooted_labelled_c4_count_identity
    {u v : V} (huv : u ≠ v) :
    Nat.card (RootedC4Copy G u v) =
      (G.commonNeighbors u v).ncard *
        ((G.commonNeighbors u v).ncard - 1) := by
  classical
  calc
    _ = Nat.card (OrderedCNPair G u v) :=
      Nat.card_congr (rootedFrameEquiv G huv).symm
    _ = Fintype.card (OrderedCNPair G u v) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card (CN G u v) *
        (Fintype.card (CN G u v) - 1) :=
      card_orderedCNPair G u v
    _ = _ := by simp only [Set.fintypeCard_eq_ncard]

theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (u v : Fin n), u ≠ v →
      Nat.card
          {f : (cycleGraph 4).Copy G //
            f (0 : Fin 4) = u ∧ f (2 : Fin 4) = v} =
        (G.commonNeighbors u v).ncard *
          ((G.commonNeighbors u v).ncard - 1) := by
  intro n G _ u v huv
  exact rooted_labelled_c4_count_identity G huv

end Submissions.Erdos60RootedCodegreeIdentity.RootedFrames

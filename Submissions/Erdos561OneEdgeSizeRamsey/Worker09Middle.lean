import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases

namespace Submissions.Erdos561OneEdgeSizeRamsey.Worker09Middle

open SimpleGraph

abbrev StarVertices {s : ℕ} (a : Fin s → ℕ) :=
  Σ i : Fin s, Fin (a i + 1)

def starForest {s : ℕ} (a : Fin s → ℕ) :
    SimpleGraph (StarVertices a) where
  Adj u v :=
    u.1 = v.1 ∧
      ((u.2.val = 0 ∧ v.2.val ≠ 0) ∨
       (v.2.val = 0 ∧ u.2.val ≠ 0))
  symm := ⟨by
    rintro ⟨i, u⟩ ⟨j, v⟩ ⟨hij, h⟩
    exact ⟨hij.symm, h.elim (fun h ↦ Or.inr ⟨h.1, h.2⟩)
      (fun h ↦ Or.inl ⟨h.1, h.2⟩)⟩⟩
  loopless := ⟨by
    rintro ⟨i, u⟩ ⟨_, h⟩
    exact h.elim (fun h ↦ h.2 h.1) (fun h ↦ h.2 h.1)⟩

noncomputable def sizeRamsey {α β : Type*} (G : SimpleGraph α)
    (H : SimpleGraph β) : ℕ :=
  sInf {m : ℕ | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
    F.edgeSet.ncard = m ∧
      ∀ (R : SimpleGraph (Fin n)), R ≤ F →
        G.IsContained R ∨ H.IsContained (F \ R)}

abbrev oneStar := starForest (fun _ : Fin 1 ↦ 1)

theorem oneStar_le_complete :
    oneStar ≤ completeGraph (StarVertices fun _ : Fin 1 ↦ 1) := by
  intro x y hxy
  simpa using hxy.ne

theorem completeFinTwo_contained_of_adj {V : Type*} {G : SimpleGraph V}
    {x y : V} (hxy : G.Adj x y) :
    (completeGraph (Fin 2)).IsContained G := by
  let e : Fin 2 ↪ V :=
    ⟨fun b => if b = 0 then x else y, by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hxy.ne]⟩
  refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  · simp at hab
  · change G.Adj x y
    exact hxy
  · change G.Adj y x
    exact hxy.symm
  · simp at hab

theorem oneStar_contained_completeFinTwo :
    oneStar.IsContained (completeGraph (Fin 2)) := by
  apply (IsContained.of_le oneStar_le_complete).trans
  let e : StarVertices (fun _ : Fin 1 ↦ 1) ≃ Fin 2 :=
    { toFun := fun u => u.2
      invFun := fun j => ⟨0, j⟩
      left_inv := by
        rintro ⟨i, j⟩
        apply Sigma.ext
        · exact Subsingleton.elim _ _
        · simp
      right_inv := by intro j; rfl }
  exact ⟨(Iso.completeGraph e).toCopy⟩

theorem oneStar_contained_of_adj {V : Type*} {G : SimpleGraph V}
    {x y : V} (hxy : G.Adj x y) :
    oneStar.IsContained G :=
  oneStar_contained_completeFinTwo.trans (completeFinTwo_contained_of_adj hxy)

theorem oneStar_notContained_bot {V : Type*} :
    ¬oneStar.IsContained (⊥ : SimpleGraph V) := by
  intro h
  obtain ⟨f⟩ := h
  have hedge : oneStar.Adj ⟨0, 0⟩ ⟨0, 1⟩ := by
    simp [oneStar, starForest]
  exact (f.toHom.map_adj hedge).elim

theorem proof : sizeRamsey oneStar oneStar = 1 := by
  apply le_antisymm
  · apply Nat.sInf_le
    refine ⟨2, edge (0 : Fin 2) 1, ?_, ?_⟩
    · rw [edgeSet_edge_of_ne (by decide)]
      simp
    · intro R hRF
      by_cases h : R.Adj 0 1
      · exact Or.inl (oneStar_contained_of_adj h)
      · right
        apply oneStar_contained_of_adj (x := 0) (y := 1)
        simp [sdiff_adj, edge_adj, h]
  · apply le_csInf
    · refine ⟨1, 2, edge (0 : Fin 2) 1, ?_, ?_⟩
      · rw [edgeSet_edge_of_ne (by decide)]
        simp
      intro R hRF
      by_cases h : R.Adj 0 1
      · exact Or.inl (oneStar_contained_of_adj h)
      · exact Or.inr (oneStar_contained_of_adj (x := 0) (y := 1) (by
          simp [sdiff_adj, edge_adj, h]))
    · intro m hm
      rcases hm with ⟨n, F, hcard, hRamsey⟩
      by_contra hm0
      have hm : m = 0 := Nat.eq_zero_of_not_pos hm0
      have hF : F = ⊥ := by
        rw [← edgeSet_eq_empty, ← Set.ncard_eq_zero]
        simpa [hm] using hcard
      subst F
      rcases hRamsey ⊥ bot_le with hred | hblue
      · exact oneStar_notContained_bot hred
      · exact oneStar_notContained_bot (by simpa using hblue)

end Submissions.Erdos561OneEdgeSizeRamsey.Worker09Middle

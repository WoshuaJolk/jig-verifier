import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos562DiagonalBoundary.ExactSelf

noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf {m | ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin m),
        e ⊆ S → e.card = r → c e = color}

theorem proof :
    ∀ r : ℕ, hypergraphRamsey r r = r := by
  intro r
  have hmem :
      r ∈ {m | ∀ c : Finset (Fin m) → Bool,
        ∃ S : Finset (Fin m), S.card = r ∧
          ∃ color : Bool, ∀ e : Finset (Fin m),
            e ⊆ S → e.card = r → c e = color} := by
    intro c
    refine ⟨Finset.univ, by simp, c Finset.univ, ?_⟩
    intro e _ he
    congr 1
    exact Finset.eq_univ_of_card e
      (he.trans (Fintype.card_fin r).symm)
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨r, hmem⟩
    intro m hm
    obtain ⟨S, hS, -⟩ := hm fun _ ↦ false
    calc
      r = S.card := hS.symm
      _ ≤ Fintype.card (Fin m) := Finset.card_le_univ S
      _ = m := Fintype.card_fin m

end Submissions.Erdos562DiagonalBoundary.ExactSelf

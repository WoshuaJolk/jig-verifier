import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos564RamseySelfBoundary.Direct

noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf {m | ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin m),
        e ⊆ S → e.card = r → c e = color}

private theorem le_hypergraphRamsey (r n : ℕ)
    (hne : {m | ∀ c : Finset (Fin m) → Bool,
      ∃ S : Finset (Fin m), S.card = n ∧
        ∃ color : Bool, ∀ e : Finset (Fin m),
          e ⊆ S → e.card = r → c e = color}.Nonempty) :
    n ≤ hypergraphRamsey r n := by
  apply le_csInf hne
  intro m hm
  have hS : ∃ S : Finset (Fin m), S.card = n ∧ _ := hm (fun _ => false)
  obtain ⟨S, hcard, -⟩ := hS
  calc
    n = S.card := hcard.symm
    _ ≤ Fintype.card (Fin m) := Finset.card_le_univ S
    _ = m := Fintype.card_fin m

theorem proof : hypergraphRamsey 3 3 = 3 := by
  have hmem : 3 ∈ {m | ∀ c : Finset (Fin m) → Bool,
      ∃ S : Finset (Fin m), S.card = 3 ∧
        ∃ color : Bool, ∀ e : Finset (Fin m),
          e ⊆ S → e.card = 3 → c e = color} := by
    intro c
    refine ⟨Finset.univ, by simp, c Finset.univ, ?_⟩
    intro e _ he
    congr 1
    exact Finset.eq_univ_of_card e (he.trans (Fintype.card_fin 3).symm)
  exact le_antisymm (Nat.sInf_le hmem) (le_hypergraphRamsey 3 3 ⟨3, hmem⟩)

end Submissions.Erdos564RamseySelfBoundary.Direct

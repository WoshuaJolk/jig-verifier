import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Sym.Sym2

namespace Submissions.Erdos617TwoCliquePartitionedColors.Main

theorem proof :
    ∀ (r : ℕ), 2 ≤ r →
      ∀ {V : Type} [Fintype V] [DecidableEq V],
        r ^ 2 + 1 ≤ Fintype.card V →
        ∀ coloring : Sym2 V → Fin r,
          ∀ c₁ c₂ : Fin r, c₁ ≠ c₂ →
            ¬ ((∃ P : V → Fin r,
                  ∀ u v : V, u ≠ v → P u = P v → coloring s(u, v) = c₁) ∧
               (∃ P : V → Fin r,
                  ∀ u v : V, u ≠ v → P u = P v → coloring s(u, v) = c₂)) := by
  intro r _hr V _ _ hcard coloring c₁ c₂ hne h
  obtain ⟨⟨P₁, hP₁⟩, ⟨P₂, hP₂⟩⟩ := h
  have hlt : Fintype.card (Fin r × Fin r) < Fintype.card V := by
    have : Fintype.card (Fin r × Fin r) = r ^ 2 := by
      simp [Fintype.card_prod, sq]
    omega
  obtain ⟨u, v, huv, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun v => (P₁ v, P₂ v)) hlt
  have h1 : P₁ u = P₁ v := congrArg Prod.fst heq
  have h2 : P₂ u = P₂ v := congrArg Prod.snd heq
  exact hne ((hP₁ u v huv h1).symm.trans (hP₂ u v huv h2))

end Submissions.Erdos617TwoCliquePartitionedColors.Main

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos595NatGraphTriangleCover.Stars

private def IsCountableUnionOfTriangleFree {V : Type*}
    (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

private theorem subgraph_closed {V : Type*} {G H : SimpleGraph V}
    (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G) :
    IsCountableUnionOfTriangleFree H := by
  obtain ⟨f, hf_free, hf_eq⟩ := hG
  refine ⟨fun i => H ⊓ f i, fun i => (hf_free i).anti inf_le_right, ?_⟩
  ext a b
  simp only [iSup_adj, inf_adj]
  constructor
  · intro hab
    have habG : G.Adj a b := hH hab
    rw [hf_eq, iSup_adj] at habG
    obtain ⟨i, hi⟩ := habG
    exact ⟨i, hab, hi⟩
  · rintro ⟨i, hHab, _⟩
    exact hHab

private theorem complete_nat_is_union :
    IsCountableUnionOfTriangleFree (⊤ : SimpleGraph ℕ) := by
  refine ⟨fun m => SimpleGraph.fromRel (fun (a b : ℕ) => a = m ∨ b = m),
          fun m => ?_, ?_⟩
  · rw [CliqueFree]
    intro s hs
    simp only [isNClique_iff] at hs
    obtain ⟨hs_clique, hs_card⟩ := hs
    rw [isClique_iff] at hs_clique
    obtain ⟨a, b, c, hab, hac, hbc, hs_eq⟩ := Finset.card_eq_three.mp hs_card
    have ha : a ∈ s := hs_eq ▸ Finset.mem_insert_self a _
    have hb : b ∈ s := hs_eq ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self b _))
    have hc : c ∈ s := hs_eq ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self c))))
    have hab_adj := hs_clique ha hb hab
    have hac_adj := hs_clique ha hc hac
    have hbc_adj := hs_clique hb hc hbc
    simp only [fromRel_adj] at hab_adj hac_adj hbc_adj
    have ham_or_bm : a = m ∨ b = m := hab_adj.2.elim id Or.symm
    have ham_or_cm : a = m ∨ c = m := hac_adj.2.elim id Or.symm
    have hbm_or_cm : b = m ∨ c = m := hbc_adj.2.elim id Or.symm
    rcases ham_or_bm with rfl | rfl
    · rcases hbm_or_cm with rfl | rfl
      · exact absurd rfl hab
      · exact absurd rfl hac
    · rcases ham_or_cm with rfl | rfl
      · exact hab.symm rfl
      · exact hbc rfl
  · ext a b
    simp only [iSup_adj, fromRel_adj, top_adj]
    exact ⟨fun hab => ⟨a, hab, Or.inl (Or.inl rfl)⟩,
      fun ⟨_, hne, _⟩ => hne⟩

theorem proof :
    ∀ G : SimpleGraph ℕ, IsCountableUnionOfTriangleFree G :=
  fun G => subgraph_closed le_top complete_nat_is_union

end Submissions.Erdos595NatGraphTriangleCover.Stars

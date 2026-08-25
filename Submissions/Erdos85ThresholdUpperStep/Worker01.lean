import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite
namespace Submissions.Erdos85ThresholdUpperStep.Worker01
open Finset SimpleGraph
open scoped Classical SimpleGraph
private theorem drop {n : ℕ} (G : SimpleGraph (Fin (n+1))) (v : Fin n) : G.degree v.castSucc ≤ (G.comap Fin.castSucc).degree v + 1 := by
 rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
 calc
  #(G.neighborFinset v.castSucc) ≤ #(((G.comap Fin.castSucc).neighborFinset v).map Fin.castSuccEmb ∪ {Fin.last n}) := by
   apply card_le_card
   intro x hx
   by_cases hl : x = Fin.last n
   · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hl)
   · apply Finset.mem_union_left
     apply Finset.mem_map.mpr
     have hxl : x.val < n := by simpa [Fin.lt_def] using Fin.lt_last_iff_ne_last.mpr hl
     let y : Fin n := ⟨x.val,hxl⟩
     refine ⟨y,?_,?_⟩
     · rw [mem_neighborFinset]
       change G.Adj v.castSucc y.castSucc
       rw [mem_neighborFinset] at hx
       simpa [y] using hx
     · apply Fin.ext; rfl
  _ ≤ #(((G.comap Fin.castSucc).neighborFinset v).map Fin.castSuccEmb) + #({Fin.last n} : Finset _) := card_union_le _ _
  _ = (G.comap Fin.castSucc).degree v + 1 := by simp
private theorem transfer : ∀ n k : ℕ, (∀ G : SimpleGraph (Fin n), G.minDegree ≥ k → cycleGraph 4 ⊑ G) → ∀ G : SimpleGraph (Fin (n+1)), G.minDegree ≥ k+1 → cycleGraph 4 ⊑ G := by
 intro n k hf G hm
 cases n with
 | zero =>
  have hz : G.minDegree = 0 := by simp [SimpleGraph.minDegree,degree]
  omega
 | succ n =>
  let H : SimpleGraph (Fin (n+1)) := G.comap Fin.castSucc
  have hh : H.minDegree ≥ k := by
   apply H.le_minDegree_of_forall_le_degree
   intro v
   change k ≤ (G.comap Fin.castSucc).degree v
   have hv : k+1 ≤ G.degree v.castSucc := hm.trans (G.minDegree_le_degree v.castSucc)
   have hd := drop G v
   omega
  have hc : cycleGraph 4 ⊑ H := hf H hh
  apply hc.trans
  rw [isContained_iff_exists_le_comap]
  exact ⟨Fin.castSuccEmb,le_rfl⟩
noncomputable def c4Threshold (n : ℕ) : ℕ := sInf {k : ℕ | ∀ G : SimpleGraph (Fin n), G.minDegree ≥ k → cycleGraph 4 ⊑ G}
private theorem ne (n : ℕ) : {k : ℕ | ∀ G : SimpleGraph (Fin n), G.minDegree ≥ k → cycleGraph 4 ⊑ G}.Nonempty := by
 refine ⟨n+1,?_⟩
 intro G hm
 cases n with
 | zero =>
  have hz : G.minDegree = 0 := by simp [SimpleGraph.minDegree,degree]
  omega
 | succ n =>
  have hl := G.minDegree_lt_card
  simp only [Fintype.card_fin] at hl
  omega
theorem proof : ∀ n : ℕ, c4Threshold (n+1) ≤ c4Threshold n + 1 := by
 intro n
 apply Nat.sInf_le
 apply transfer n (c4Threshold n)
 exact Nat.sInf_mem (ne n)
end Submissions.Erdos85ThresholdUpperStep.Worker01

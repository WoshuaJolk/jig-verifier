import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype

namespace Submissions.Erdos1020MatchingBoundary.PartitionAverage

/-- Average a matching-free uniform family over all relabelings of a fixed
matching. The fixed matching is supplied separately; no factorial is evaluated. -/
theorem bound {n r k : ℕ} (H P : Finset (Finset (Fin n)))
    (hk : 0 < k)
    (hH : ∀ e ∈ H, e.card = r)
    (hP : ∀ e ∈ P, e.card = r)
    (hPk : P.card = k)
    (hPd : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card * k ≤ (k - 1) * n.choose r := by
  classical
  let A := (Finset.univ : Finset (Fin n)).powersetCard r
  let G := (Finset.univ : Finset (Equiv.Perm (Fin n)))
  let R (e : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
    e.map σ.toEmbedding ∈ P
  have hPne : P.Nonempty := Finset.card_pos.mp (by simpa [hPk] using hk)
  obtain ⟨e₀, he₀⟩ := hPne
  let d := (G.bipartiteAbove R e₀).card
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    refine ⟨Equiv.refl _, (Finset.mem_bipartiteAbove R).mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [R] using he₀
  have hdegree (e : Finset (Fin n)) (he : e.card = r) :
      (G.bipartiteAbove R e).card = d := by
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq e₀ e ((hP _ he₀).trans he.symm)
    have hτback : e.map τ.symm.toEmbedding = e₀ := by
      rw [← hτ]
      simp [Finset.map_map]
    change (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      e.map σ.toEmbedding ∈ P)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        e₀.map σ.toEmbedding ∈ P)).card
    refine Finset.card_bij' (fun σ _ => τ.trans σ) (fun σ _ => τ.symm.trans σ)
      ?_ ?_ ?_ ?_
    · intro σ hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.trans_toEmbedding, ← Finset.map_map, hτ] using
        (Finset.mem_filter.mp hσ).2
    · intro σ hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.trans_toEmbedding, ← Finset.map_map, hτback] using
        (Finset.mem_filter.mp hσ).2
    · intro σ _
      simp [← Equiv.trans_assoc]
    · intro σ _
      simp [← Equiv.trans_assoc]
  have hright (σ : Equiv.Perm (Fin n)) : (A.bipartiteBelow R σ).card = k := by
    calc
      (A.bipartiteBelow R σ).card = P.card := by
        apply Finset.card_equiv σ.finsetCongr
        intro e
        simp only [A, R, Finset.mem_bipartiteBelow, Finset.mem_powersetCard_univ,
          Equiv.finsetCongr_apply]
        constructor
        · exact And.right
        · intro he
          exact ⟨by simpa only [Finset.card_map] using hP _ he, he⟩
      _ = k := hPk
  have hrightH (σ : Equiv.Perm (Fin n)) :
      (H.bipartiteBelow R σ).card ≤ k - 1 := by
    apply Nat.le_pred_of_lt
    apply Nat.lt_of_not_ge
    intro hc
    obtain ⟨M, hMH, hMk⟩ := Finset.exists_subset_card_eq hc
    apply hM
    refine ⟨M, fun e he => ((Finset.mem_bipartiteBelow R).mp (hMH he)).1, hMk, ?_⟩
    intro e he f hf hef
    apply (Finset.disjoint_map σ.toEmbedding).mp
    exact hPd _ ((Finset.mem_bipartiteBelow R).mp (hMH he)).2
      _ ((Finset.mem_bipartiteBelow R).mp (hMH hf)).2
      (fun h => hef (Finset.map_injective σ.toEmbedding h))
  have hcount : n.choose r * d = G.card * k := by
    have hc := Finset.card_mul_eq_card_mul (s := A) (t := G) (m := d) (n := k) R
      (fun e he => hdegree e (Finset.mem_powersetCard_univ.mp he))
      (fun σ _ => hright σ)
    simpa [A] using hc
  have hbound : H.card * d ≤ G.card * (k - 1) :=
    Finset.card_mul_le_card_mul (s := H) (t := G) (m := d) (n := k - 1) R
      (fun e he => (hdegree e (hH e he)).ge) (fun σ _ => hrightH σ)
  apply Nat.le_of_mul_le_mul_right (c := d) ?_ hd
  calc
    H.card * k * d = H.card * d * k := by ac_rfl
    _ ≤ G.card * (k - 1) * k := Nat.mul_le_mul_right k hbound
    _ = (G.card * k) * (k - 1) := by ac_rfl
    _ = (n.choose r * d) * (k - 1) := by rw [hcount]
    _ = ((k - 1) * n.choose r) * d := by ac_rfl

end Submissions.Erdos1020MatchingBoundary.PartitionAverage

namespace Submissions.Erdos1020MatchingEndpoint.Main

/-- The exact clique bound at the divisible endpoint n = r*k. -/
theorem endpoint {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (H : Finset (Finset (Fin (r * k))))
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin (r * k))), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ (r * k - 1).choose r := by
  classical
  let block (j : Fin k) : Finset (Fin (r * k)) :=
    ((Finset.univ : Finset (Fin r)) ×ˢ {j}).map finProdFinEquiv.toEmbedding
  have hbcard (j : Fin k) : (block j).card = r := by simp [block]
  have hbdisj (i j : Fin k) (hij : i ≠ j) : Disjoint (block i) (block j) := by
    apply (Finset.disjoint_map finProdFinEquiv.toEmbedding).mpr
    exact Finset.disjoint_product.mpr (Or.inr (Finset.disjoint_singleton.mpr hij))
  have hbinj : Function.Injective block := by
    intro i j heq
    by_contra hij
    have hd := hbdisj i j hij
    rw [heq] at hd
    have hempty := (Finset.disjoint_self_iff_empty (block j)).mp hd
    have hc := hbcard j
    rw [hempty, Finset.card_empty] at hc
    omega
  let P := Finset.univ.image block
  have hPk : P.card = k := by simp [P, Finset.card_image_of_injective _ hbinj]
  have hPU : ∀ e ∈ P, e.card = r := by
    intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    exact hbcard j
  have hPd : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f := by
    intro e he f hf hef
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    exact hbdisj i j (fun hij => hef (congrArg block hij))
  have havg := Submissions.Erdos1020MatchingBoundary.PartitionAverage.bound
    H P hk hH hPU hPk hPd hM
  let C := (r * k).choose r
  let L := (r * k - 1).choose (r - 1)
  let R := (r * k - 1).choose r
  have hchoose : C = k * L := by
    simpa only [C, L, Nat.mul_comm] using
      (Nat.choose_mul_right (m := k) (n := r) (Nat.ne_of_gt hr))
  have hpascal : C = L + R := Nat.choose_eq_choose_pred_add (Nat.mul_pos hr hk) hr
  have hbinom : (k - 1) * C = R * k := by
    have heq : k * L + (k - 1) * C = k * L + R * k := by
      calc
        _ = C + (k - 1) * C := by rw [hchoose]
        _ = (1 + (k - 1)) * C := by rw [Nat.add_mul, Nat.one_mul]
        _ = k * C := by congr 1; omega
        _ = k * (L + R) := by rw [← hpascal]
        _ = k * L + R * k := by rw [Nat.mul_add, Nat.mul_comm k R]
    exact Nat.add_left_cancel heq
  exact Nat.le_of_mul_le_mul_right (havg.trans_eq hbinom) hk

end Submissions.Erdos1020MatchingEndpoint.Main

namespace Submissions.Erdos1020MatchingEndpointProof.Main

/-- The original extremal expression at n=r*k follows from the stronger clique bound. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → n = r * k →
      ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  intro n r k hr hk hn H hH hM
  subst n
  exact (Submissions.Erdos1020MatchingEndpoint.Main.endpoint
    (by omega) (by omega) H hH hM).trans (le_max_left _ _)

end Submissions.Erdos1020MatchingEndpointProof.Main

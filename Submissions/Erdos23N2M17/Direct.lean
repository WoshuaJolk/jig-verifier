import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23N2M17.Direct

open scoped Classical in
lemma sum_neighbor_degrees_eq_sum_sq
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    (∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w) =
      ∑ w : V, (G.degree w) ^ 2 := by
  classical
  calc
    (∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w) =
        ∑ v : V, ∑ w : V, if G.Adj v w then G.degree w else 0 := by
      simp [neighborFinset_eq_filter, Finset.sum_filter]
    _ = ∑ w : V, ∑ v : V, if G.Adj v w then G.degree w else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ w : V, G.degree w * G.degree w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_filter]
      simp [← G.card_neighborFinset_eq_degree, neighborFinset_eq_filter, G.adj_comm]
    _ = ∑ w : V, (G.degree w) ^ 2 := by
      simp [pow_two]

open scoped Classical in
lemma weighted_independent_set
    (V : Type) [Fintype V] (hcard : Fintype.card V = 10)
    (G : SimpleGraph V) (htri : G.CliqueFree 3)
    (hedges : G.edgeFinset.card = 17) :
    ∃ S : Finset V,
      G.IsIndepSet (S : Set V) ∧
        13 ≤ ∑ v ∈ S, G.degree v := by
  classical
  by_contra! hnone
  have hneighbor :
      ∀ v : V, (∑ w ∈ G.neighborFinset v, G.degree w) ≤ 12 := by
    intro v
    have hind :
        G.IsIndepSet (G.neighborFinset v : Set V) := by
      simpa [neighborFinset_def] using
        G.isIndepSet_neighborSet_of_triangleFree htri v
    have := hnone (G.neighborFinset v) hind
    omega
  have hsquares :
      (∑ v : V, (G.degree v) ^ 2) ≤ 120 := by
    rw [← sum_neighbor_degrees_eq_sum_sq G]
    calc
      _ ≤ ∑ _v : V, 12 := Finset.sum_le_sum fun v _ ↦ hneighbor v
      _ = 120 := by simp [hcard]
  have hdegrees : ∑ v : V, G.degree v = 34 := by
    simpa [hedges] using G.sum_degrees_eq_twice_card_edges
  let q : V → ℕ := fun v => (G.degree v) ^ 2 + 12 - 7 * G.degree v
  have hdeg9 : ∀ v : V, G.degree v ≤ 9 := by
    intro v
    have := G.degree_lt_card_verts v
    omega
  have hqadd :
      ∀ v : V, q v + 7 * G.degree v = (G.degree v) ^ 2 + 12 := by
    intro v
    dsimp [q]
    have hd := hdeg9 v
    interval_cases G.degree v <;> norm_num
  have hqidentity :
      (∑ v : V, q v) + 7 * (∑ v : V, G.degree v) =
        (∑ v : V, (G.degree v) ^ 2) + 120 := by
    calc
      (∑ v : V, q v) + 7 * (∑ v : V, G.degree v) =
          ∑ v : V, (q v + 7 * G.degree v) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ v : V, ((G.degree v) ^ 2 + 12) :=
        Finset.sum_congr rfl fun v _ ↦ hqadd v
      _ = (∑ v : V, (G.degree v) ^ 2) + 120 := by
        simp [Finset.sum_add_distrib, hcard]
  have hqsum : (∑ v : V, q v) ≤ 2 := by omega
  have hqpoint : ∀ v : V, q v ≤ 2 := by
    intro v
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)).trans hqsum
  have hdeg_range : ∀ v : V, 2 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v
    have hqv := hqpoint v
    have hd := hdeg9 v
    interval_cases hdv : G.degree v <;> norm_num [q, hdv] at hqv <;> omega
  have hq_other_zero :
      ∀ v : V, q v = 2 → ∀ z : V, z ≠ v → q z = 0 := by
    intro v hqv z hz
    have hzmem : z ∈ (Finset.univ.erase v : Finset V) := by simp [hz]
    have hzle :
        q z ≤ ∑ x ∈ (Finset.univ.erase v : Finset V), q x :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hzmem
    have hsplit :
        (∑ x : V, q x) =
          (∑ x ∈ (Finset.univ.erase v : Finset V), q x) + q v := by
      exact (Finset.sum_erase_add Finset.univ q (Finset.mem_univ v)).symm
    omega
  have hnot_two : ∀ v : V, G.degree v ≠ 2 := by
    intro v hd2
    have hqv : q v = 2 := by simp [q, hd2]
    have hqeq : (∑ x : V, q x) = 2 := by
      have hvle : q v ≤ ∑ x : V, q x :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v)
      omega
    have hsquares_eq : (∑ x : V, (G.degree x) ^ 2) = 120 := by
      omega
    have hneighbor_total :
        (∑ x : V, ∑ z ∈ G.neighborFinset x, G.degree z) = 120 := by
      rw [sum_neighbor_degrees_eq_sum_sq G, hsquares_eq]
    have hvneighbor :
        (∑ z ∈ G.neighborFinset v, G.degree z) = 12 := by
      have hrest :
          (∑ x ∈ (Finset.univ.erase v : Finset V),
            ∑ z ∈ G.neighborFinset x, G.degree z) ≤ 9 * 12 := by
        calc
          _ ≤ ∑ _x ∈ (Finset.univ.erase v : Finset V), 12 :=
            Finset.sum_le_sum fun x _ ↦ hneighbor x
          _ = 9 * 12 := by
            simp [Finset.card_erase_of_mem (Finset.mem_univ v), hcard]
      have hsplit :
          (∑ x : V, ∑ z ∈ G.neighborFinset x, G.degree z) =
            (∑ x ∈ (Finset.univ.erase v : Finset V),
              ∑ z ∈ G.neighborFinset x, G.degree z) +
              (∑ z ∈ G.neighborFinset v, G.degree z) := by
        exact (Finset.sum_erase_add Finset.univ
          (fun x => ∑ z ∈ G.neighborFinset x, G.degree z)
          (Finset.mem_univ v)).symm
      have hvle := hneighbor v
      omega
    have hneighbor_degree_le :
        ∀ z ∈ G.neighborFinset v, G.degree z ≤ 4 := by
      intro z hz
      have hadj : G.Adj v z := by simpa using hz
      have hzneq : z ≠ v := (G.ne_of_adj hadj).symm
      have hqz := hq_other_zero v hqv z hzneq
      have hdlo := (hdeg_range z).1
      have hdhi := (hdeg_range z).2
      interval_cases hdz : G.degree z
      all_goals norm_num [q, hdz] at hqz
      all_goals omega
    have hvcard : (G.neighborFinset v).card = 2 := by
      simpa [hd2] using G.card_neighborFinset_eq_degree v
    have hvupper :
        (∑ z ∈ G.neighborFinset v, G.degree z) ≤ 8 := by
      calc
        _ ≤ ∑ _z ∈ G.neighborFinset v, 4 :=
          Finset.sum_le_sum hneighbor_degree_le
        _ = 8 := by simp [hvcard]
    omega
  have hnot_five : ∀ v : V, G.degree v ≠ 5 := by
    intro v hd5
    have hqv : q v = 2 := by simp [q, hd5]
    have hneighbor_degree_ge :
        ∀ z ∈ G.neighborFinset v, 3 ≤ G.degree z := by
      intro z hz
      have hadj : G.Adj v z := by simpa using hz
      have hzneq : z ≠ v := (G.ne_of_adj hadj).symm
      have hqz := hq_other_zero v hqv z hzneq
      have hdlo := (hdeg_range z).1
      have hdhi := (hdeg_range z).2
      interval_cases hdz : G.degree z
      all_goals norm_num [q, hdz] at hqz
      all_goals omega
    have hvcard : (G.neighborFinset v).card = 5 := by
      simpa [hd5] using G.card_neighborFinset_eq_degree v
    have hvlower :
        15 ≤ ∑ z ∈ G.neighborFinset v, G.degree z := by
      calc
        15 = ∑ _z ∈ G.neighborFinset v, 3 := by simp [hvcard]
        _ ≤ _ := Finset.sum_le_sum hneighbor_degree_ge
    have hvupper := hneighbor v
    omega
  have hdegree_three_or_four :
      ∀ v : V, G.degree v = 3 ∨ G.degree v = 4 := by
    intro v
    have hdr := hdeg_range v
    have h2 := hnot_two v
    have h5 := hnot_five v
    omega
  let S : Finset V := Finset.univ.filter fun v => G.degree v = 4
  have hsum_repr :
      (∑ v : V, G.degree v) = 30 + S.card := by
    calc
      (∑ v : V, G.degree v) =
          ∑ v : V, (3 + if G.degree v = 4 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        rcases hdegree_three_or_four v with h3 | h4
        · simp [h3]
        · simp [h4]
      _ = 30 + S.card := by
        simp [Finset.sum_add_distrib, S, hcard]
  have hScard : S.card = 4 := by omega
  have hSind : G.IsIndepSet (S : Set V) := by
    intro x hx y hy hxy hadj
    have hdx : G.degree x = 4 := by simpa [S] using hx
    have hdy : G.degree y = 4 := by simpa [S] using hy
    have hymem : y ∈ G.neighborFinset x := by simpa using hadj
    have herase_card : ((G.neighborFinset x).erase y).card = 3 := by
      rw [Finset.card_erase_of_mem hymem]
      simpa [hdx] using G.card_neighborFinset_eq_degree x
    have hrest :
        9 ≤ ∑ z ∈ (G.neighborFinset x).erase y, G.degree z := by
      calc
        9 = ∑ _z ∈ (G.neighborFinset x).erase y, 3 := by
          simp [herase_card]
        _ ≤ _ := Finset.sum_le_sum fun z _ ↦ by
          rcases hdegree_three_or_four z with h3 | h4 <;> omega
    have hsplit :
        (∑ z ∈ (G.neighborFinset x).erase y, G.degree z) + G.degree y =
          ∑ z ∈ G.neighborFinset x, G.degree z :=
      Finset.sum_erase_add (G.neighborFinset x) (fun z => G.degree z) hymem
    have hxupper := hneighbor x
    omega
  have hSweight : (∑ v ∈ S, G.degree v) = 16 := by
    calc
      (∑ v ∈ S, G.degree v) = ∑ _v ∈ S, 4 := by
        apply Finset.sum_congr rfl
        intro v hv
        simpa [S] using hv
      _ = 16 := by simp [hScard]
  have := hnone S hSind
  omega

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        G.edgeFinset.card = 17 →
          ∃ (H : SimpleGraph V),
            H ≤ G ∧ H.IsBipartite ∧
              (G.edgeFinset \ H.edgeFinset).card ≤ 4 := by
  intro V _ hcard G htri hedges
  obtain ⟨S, hind, hweight⟩ :=
    weighted_independent_set V hcard G htri hedges
  let H : SimpleGraph V := G.between (↑S : Set V) ↑(Sᶜ)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hle : H ≤ G := G.between_le
  have hd : Disjoint (↑S : Set V) ↑(Sᶜ) := by
    rw [Finset.coe_compl]
    exact disjoint_compl_right
  have hbwith : H.IsBipartiteWith (↑S : Set V) ↑(Sᶜ) := by
    simpa [H] using
      (G.between_isBipartiteWith
        (s := (↑S : Set V)) (t := (↑(Sᶜ) : Set V)) hd)
  have hbip : H.IsBipartite := hbwith.isBipartite
  have hdeg : ∀ x ∈ S, H.degree x = G.degree x := by
    intro x hx
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    congr 1
    ext y
    have hyout : G.Adj x y → y ∉ S := by
      intro hxy hy
      exact hind hx hy (G.ne_of_adj hxy) hxy
    simp [H, SimpleGraph.between_adj, hx]
    exact hyout
  have hedge : H.edgeFinset.card = ∑ x ∈ S, G.degree x := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hbwith]
    exact Finset.sum_congr rfl fun x hx ↦ hdeg x hx
  refine ⟨H, hle, hbip, ?_⟩
  calc
    (G.edgeFinset \ H.edgeFinset).card =
        G.edgeFinset.card - H.edgeFinset.card :=
      Finset.card_sdiff_of_subset (edgeFinset_mono hle)
    _ = 17 - ∑ x ∈ S, G.degree x := by rw [hedges, hedge]
    _ ≤ 4 := by omega

end Submissions.Erdos23N2M17.Direct

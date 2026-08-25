import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23N2M16.Direct

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
    _ = ∑ w : V, (G.degree w) ^ 2 := by simp [pow_two]

open scoped Classical in
lemma weighted_independent_set
    (V : Type) [Fintype V] (hcard : Fintype.card V = 10)
    (G : SimpleGraph V) (htri : G.CliqueFree 3)
    (hedges : G.edgeFinset.card = 16) :
    ∃ S : Finset V,
      G.IsIndepSet (S : Set V) ∧
        12 ≤ ∑ v ∈ S, G.degree v := by
  classical
  by_contra! hnone
  have hneighbor :
      ∀ v : V, (∑ w ∈ G.neighborFinset v, G.degree w) ≤ 11 := by
    intro v
    have hind : G.IsIndepSet (G.neighborFinset v : Set V) := by
      simpa [neighborFinset_def] using
        G.isIndepSet_neighborSet_of_triangleFree htri v
    have := hnone (G.neighborFinset v) hind
    omega
  have hsquares : (∑ v : V, (G.degree v) ^ 2) ≤ 110 := by
    rw [← sum_neighbor_degrees_eq_sum_sq G]
    calc
      _ ≤ ∑ _v : V, 11 := Finset.sum_le_sum fun v _ ↦ hneighbor v
      _ = 110 := by simp [hcard]
  have hdegrees : ∑ v : V, G.degree v = 32 := by
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
    interval_cases hdv : G.degree v <;> norm_num [hdv]
  have hqidentity :
      (∑ v : V, q v) + 7 * (∑ v : V, G.degree v) =
        (∑ v : V, (G.degree v) ^ 2) + 120 := by
    calc
      _ = ∑ v : V, (q v + 7 * G.degree v) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ v : V, ((G.degree v) ^ 2 + 12) :=
        Finset.sum_congr rfl fun v _ ↦ hqadd v
      _ = _ := by simp [Finset.sum_add_distrib, hcard]
  have hqsum : (∑ v : V, q v) ≤ 6 := by omega
  have hqpoint : ∀ v : V, q v ≤ 6 := by
    intro v
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ v)).trans hqsum
  have hdeg_range : ∀ v : V, 1 ≤ G.degree v ∧ G.degree v ≤ 6 := by
    intro v
    have hqv := hqpoint v
    have hd := hdeg9 v
    interval_cases hdv : G.degree v <;> norm_num [q, hdv] at hqv <;> omega
  have hq_outside_le :
      ∀ v : V, ∀ s : Finset V, s ⊆ Finset.univ.erase v →
        (∑ z ∈ s, q z) + q v ≤ 6 := by
    intro v s hs
    have hsub : insert v s ⊆ (Finset.univ : Finset V) := by simp
    have hle :
        (∑ z ∈ insert v s, q z) ≤ ∑ z : V, q z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ ↦ Nat.zero_le _)
    have hvnot : v ∉ s := fun hv => Finset.notMem_erase v _ (hs hv)
    simp [hvnot] at hle
    omega
  have hnot_six : ∀ v : V, G.degree v ≠ 6 := by
    intro v hd6
    have hqv : q v = 6 := by simp [q, hd6]
    have hneighbor_qzero :
        ∀ z ∈ G.neighborFinset v, q z = 0 := by
      intro z hz
      have hzsub : ({z} : Finset V) ⊆ Finset.univ.erase v := by
        intro x hx
        simp at hx
        subst x
        have hadj : G.Adj v z := by simpa using hz
        simp [(G.ne_of_adj hadj).symm]
      have := hq_outside_le v {z} hzsub
      simp [hqv] at this
      omega
    have hneighbor_ge :
        ∀ z ∈ G.neighborFinset v, 3 ≤ G.degree z := by
      intro z hz
      have hqz := hneighbor_qzero z hz
      have hdlo := (hdeg_range z).1
      have hdhi := (hdeg_range z).2
      interval_cases hdz : G.degree z
      all_goals norm_num [q, hdz] at hqz
      all_goals omega
    have hvcard : (G.neighborFinset v).card = 6 := by
      simpa [hd6] using G.card_neighborFinset_eq_degree v
    have : 18 ≤ ∑ z ∈ G.neighborFinset v, G.degree z := by
      calc
        18 = ∑ _z ∈ G.neighborFinset v, 3 := by simp [hvcard]
        _ ≤ _ := Finset.sum_le_sum hneighbor_ge
    have hvupper := hneighbor v
    omega
  have hnot_one : ∀ v : V, G.degree v ≠ 1 := by
    intro v hd1
    have hqv : q v = 6 := by simp [q, hd1]
    have hqeq : (∑ z : V, q z) = 6 := by
      have hvle : q v ≤ ∑ z : V, q z :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ v)
      omega
    have hsquares_eq : (∑ z : V, (G.degree z) ^ 2) = 110 := by omega
    have htotal :
        (∑ x : V, ∑ z ∈ G.neighborFinset x, G.degree z) = 110 := by
      rw [sum_neighbor_degrees_eq_sum_sq G, hsquares_eq]
    have hvsum : (∑ z ∈ G.neighborFinset v, G.degree z) = 11 := by
      have hrest :
          (∑ x ∈ (Finset.univ.erase v : Finset V),
            ∑ z ∈ G.neighborFinset x, G.degree z) ≤ 9 * 11 := by
        calc
          _ ≤ ∑ _x ∈ (Finset.univ.erase v : Finset V), 11 :=
            Finset.sum_le_sum fun x _ ↦ hneighbor x
          _ = 9 * 11 := by
            simp [Finset.card_erase_of_mem (Finset.mem_univ v), hcard]
      have hsplit :=
        (Finset.sum_erase_add Finset.univ
          (fun x => ∑ z ∈ G.neighborFinset x, G.degree z)
          (Finset.mem_univ v)).symm
      have hvle := hneighbor v
      omega
    have hvcard : (G.neighborFinset v).card = 1 := by
      simpa [hd1] using G.card_neighborFinset_eq_degree v
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hvcard
    have hzmem : z ∈ G.neighborFinset v := by rw [hz]; simp
    have hadj : G.Adj v z := by simpa using hzmem
    have hzneq : z ≠ v := (G.ne_of_adj hadj).symm
    have hqz : q z = 0 := by
      have hzle : q v + q z ≤ ∑ x : V, q x := by
        have hzmem : z ∈ (Finset.univ.erase v : Finset V) := by simp [hzneq]
        have hzsingle :
            q z ≤ ∑ x ∈ (Finset.univ.erase v : Finset V), q x :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hzmem
        have hsplit :
            (∑ x : V, q x) =
              (∑ x ∈ (Finset.univ.erase v : Finset V), q x) + q v :=
          (Finset.sum_erase_add Finset.univ q (Finset.mem_univ v)).symm
        omega
      omega
    have hzdeg : G.degree z ≤ 4 := by
      have hdlo := (hdeg_range z).1
      have hdhi := (hdeg_range z).2
      interval_cases hdz : G.degree z
      all_goals norm_num [q, hdz] at hqz
      all_goals omega
    rw [hz] at hvsum
    simp at hvsum
    omega
  have hnot_five : ∀ v : V, G.degree v ≠ 5 := by
    intro v hd5
    have hqv : q v = 2 := by simp [q, hd5]
    have hqneighbors :
        (∑ z ∈ G.neighborFinset v, q z) ≤ 4 := by
      have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
        intro z hz
        have hadj : G.Adj v z := by simpa using hz
        simp [(G.ne_of_adj hadj).symm]
      have := hq_outside_le v (G.neighborFinset v) hsub
      omega
    have hpoint : ∀ z : V, 6 ≤ 2 * G.degree z + q z := by
      intro z
      have hdlo := (hdeg_range z).1
      have hdhi := (hdeg_range z).2
      interval_cases hdz : G.degree z <;> norm_num [q, hdz]
    have hvcard : (G.neighborFinset v).card = 5 := by
      simpa [hd5] using G.card_neighborFinset_eq_degree v
    have hsum :
        30 ≤ 2 * (∑ z ∈ G.neighborFinset v, G.degree z) +
          ∑ z ∈ G.neighborFinset v, q z := by
      calc
        30 = ∑ z ∈ G.neighborFinset v, 6 := by simp [hvcard]
        _ ≤ ∑ z ∈ G.neighborFinset v, (2 * G.degree z + q z) :=
          Finset.sum_le_sum fun z _ ↦ hpoint z
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hvupper := hneighbor v
    omega
  have hdegree_two_to_four :
      ∀ v : V, G.degree v = 2 ∨ G.degree v = 3 ∨ G.degree v = 4 := by
    intro v
    have hdr := hdeg_range v
    have h1 := hnot_one v
    have h5 := hnot_five v
    have h6 := hnot_six v
    omega
  let A : Finset V := Finset.univ.filter fun v => G.degree v = 2
  let C : Finset V := Finset.univ.filter fun v => G.degree v = 4
  have hq_indicator : ∀ v : V, q v = if G.degree v = 2 then 2 else 0 := by
    intro v
    rcases hdegree_two_to_four v with h2 | h3 | h4
    · simp [q, h2]
    · simp [q, h3]
    · simp [q, h4]
  have hq_card : (∑ v : V, q v) = 2 * A.card := by
    calc
      _ = ∑ v : V, if G.degree v = 2 then 2 else 0 :=
        Finset.sum_congr rfl fun v _ ↦ hq_indicator v
      _ = ∑ _v ∈ A, 2 := by
        rw [← Finset.sum_filter]
      _ = A.card * 2 := by simp
      _ = 2 * A.card := by omega
  have hAcard_le : A.card ≤ 3 := by omega
  have neighbor_inter_count (v : V) (T : Finset V) :
      (G.neighborFinset v ∩ T).card =
        ∑ t ∈ T, if G.Adj v t then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr
    ext t
    simp [G.adj_comm, and_comm]
  have hdegree_indicator :
      ∀ v : V,
        G.degree v + (if G.degree v = 2 then 1 else 0) =
          3 + (if G.degree v = 4 then 1 else 0) := by
    intro v
    rcases hdegree_two_to_four v with h2 | h3 | h4 <;> simp [*]
  have hcard_relation : C.card = A.card + 2 := by
    have hsum :
        (∑ v : V, G.degree v) + A.card = 30 + C.card := by
      calc
        (∑ v : V, G.degree v) + A.card =
            ∑ v : V, (G.degree v +
              if G.degree v = 2 then 1 else 0) := by
          simp [Finset.sum_add_distrib, A]
        _ = ∑ v : V, (3 +
              if G.degree v = 4 then 1 else 0) :=
          Finset.sum_congr rfl fun v _ ↦ hdegree_indicator v
        _ = 30 + C.card := by
          simp [Finset.sum_add_distrib, C, hcard]
    omega
  have hC_has_A_neighbor :
      ∀ c ∈ C, ∃ a ∈ A, G.Adj c a := by
    intro c hc
    by_contra! hnoneA
    have hge : ∀ z ∈ G.neighborFinset c, 3 ≤ G.degree z := by
      intro z hz
      rcases hdegree_two_to_four z with h2 | h3 | h4
      · exfalso
        exact hnoneA z (by simp [A, h2]) (by simpa using hz)
      · omega
      · omega
    have hcdeg : G.degree c = 4 := by simpa [C] using hc
    have hccard : (G.neighborFinset c).card = 4 := by
      simpa [hcdeg] using G.card_neighborFinset_eq_degree c
    have : 12 ≤ ∑ z ∈ G.neighborFinset c, G.degree z := by
      calc
        12 = ∑ _z ∈ G.neighborFinset c, 3 := by simp [hccard]
        _ ≤ _ := Finset.sum_le_sum hge
    have := hneighbor c
    omega
  have hAcard_ge : 2 ≤ A.card := by
    by_contra! hsmall
    interval_cases hAc : A.card
    · have hCcard : C.card = 2 := by omega
      have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨c, hc⟩ := hCne
      obtain ⟨a, ha, _⟩ := hC_has_A_neighbor c hc
      have : A.Nonempty := ⟨a, ha⟩
      exact (Finset.card_ne_zero.mpr this) hAc
    · obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp hAc
      have hCsub : C ⊆ G.neighborFinset a := by
        intro c hc
        obtain ⟨a', ha', hadj⟩ := hC_has_A_neighbor c hc
        have : a' = a := by simpa [hAeq] using ha'
        subst a'
        simpa [G.adj_comm] using hadj
      have hCcard : C.card = 3 := by omega
      have hadeg : G.degree a = 2 := by
        have : a ∈ A := by simp [hAeq]
        simpa [A] using this
      have hle := Finset.card_le_card hCsub
      rw [G.card_neighborFinset_eq_degree, hadeg] at hle
      omega
  have hAcases : A.card = 2 ∨ A.card = 3 := by omega
  rcases hAcases with hA2 | hA3
  · have hC4 : C.card = 4 := by omega
    have hCind : G.IsIndepSet (C : Set V) := by
      intro x hx y hy hxy hadj
      have hdx : G.degree x = 4 := by simpa [C] using hx
      have hdy : G.degree y = 4 := by simpa [C] using hy
      have hymem : y ∈ G.neighborFinset x := by simpa using hadj
      have herase_card : ((G.neighborFinset x).erase y).card = 3 := by
        rw [Finset.card_erase_of_mem hymem]
        simpa [hdx] using G.card_neighborFinset_eq_degree x
      have hrest :
          (∑ z ∈ (G.neighborFinset x).erase y, G.degree z) ≤ 7 := by
        have hsplit :=
          Finset.sum_erase_add (G.neighborFinset x)
            (fun z => G.degree z) hymem
        have hxupper := hneighbor x
        omega
      let D := (G.neighborFinset x).erase y
      have hDcard : D.card = 3 := herase_card
      have hDnotA :
          (∑ z ∈ D, if z ∉ A then 1 else 0) = (D \ A).card := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        congr
        ext z
        simp
      have hDlower : 6 + (D \ A).card ≤ ∑ z ∈ D, G.degree z := by
        calc
          6 + (D \ A).card =
              ∑ z ∈ D, (2 + if z ∉ A then 1 else 0) := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [hDcard, hDnotA]
            norm_num
          _ ≤ _ := Finset.sum_le_sum fun z hz ↦ by
            rcases hdegree_two_to_four z with h2 | h3 | h4
            · simp [A, h2]
            · simp [A, h3]
            · simp [A, h4]
      have hnonA : (D \ A).card ≤ 1 := by
        change (((G.neighborFinset x).erase y) \ A).card ≤ 1
        change
          6 + (((G.neighborFinset x).erase y) \ A).card ≤
            ∑ z ∈ (G.neighborFinset x).erase y, G.degree z at hDlower
        omega
      have hAinter : (D ∩ A).card = 2 := by
        have hpart := Finset.card_sdiff_add_card_inter D A
        have hinterle := Finset.card_le_card
          (Finset.inter_subset_right : D ∩ A ⊆ A)
        omega
      have htwoA : ∀ a ∈ A, G.Adj x a := by
        have heq : D ∩ A = A := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          simpa [hA2, hAinter]
        intro a ha
        have haD : a ∈ D := by
          have : a ∈ D ∩ A := heq.symm ▸ ha
          exact (Finset.mem_inter.mp this).1
        exact by simpa [D] using Finset.mem_of_mem_erase haD
      have hcross_lower :
          5 ≤ ∑ c ∈ C, (G.neighborFinset c ∩ A).card := by
        have hxmem : x ∈ C := hx
        have hxcount : (G.neighborFinset x ∩ A).card = 2 := by
          have heq : G.neighborFinset x ∩ A = A := by
            ext a
            constructor
            · exact fun ha => (Finset.mem_inter.mp ha).2
            · intro ha
              exact Finset.mem_inter.mpr ⟨by simpa using htwoA a ha, ha⟩
          rw [heq, hA2]
        have hrest_lower :
            3 ≤ ∑ c ∈ C.erase x, (G.neighborFinset c ∩ A).card := by
          calc
            3 = ∑ _c ∈ C.erase x, 1 := by
              simp [Finset.card_erase_of_mem hxmem, hC4]
            _ ≤ _ := Finset.sum_le_sum fun c hc ↦ by
              obtain ⟨a, ha, hadjca⟩ :=
                hC_has_A_neighbor c (Finset.mem_of_mem_erase hc)
              have hamem : a ∈ G.neighborFinset c ∩ A :=
                Finset.mem_inter.mpr ⟨by simpa using hadjca, ha⟩
              exact Finset.card_pos.mpr ⟨a, hamem⟩
        have hsplit :=
          Finset.sum_erase_add C
            (fun c => (G.neighborFinset c ∩ A).card) hxmem
        omega
      have hcross_upper :
          (∑ c ∈ C, (G.neighborFinset c ∩ A).card) ≤ 4 := by
        calc
          _ = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
            calc
              _ = ∑ c ∈ C, ∑ a ∈ A,
                    if G.Adj c a then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro c hc
                exact neighbor_inter_count c A
              _ = ∑ a ∈ A, ∑ c ∈ C,
                    if G.Adj c a then 1 else 0 := Finset.sum_comm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [neighbor_inter_count]
                apply Finset.sum_congr rfl
                intro c hc
                rw [G.adj_comm]
          _ ≤ ∑ a ∈ A, G.degree a := Finset.sum_le_sum fun a ha ↦ by
            calc
              (G.neighborFinset a ∩ C).card ≤ (G.neighborFinset a).card :=
                Finset.card_le_card Finset.inter_subset_left
              _ = G.degree a := G.card_neighborFinset_eq_degree a
          _ = 4 := by
            calc
              _ = ∑ _a ∈ A, 2 := Finset.sum_congr rfl fun a ha ↦ by
                simpa [A] using ha
              _ = 4 := by simp [hA2]
      omega
    have hweight : (∑ c ∈ C, G.degree c) = 16 := by
      calc
        _ = ∑ _c ∈ C, 4 := Finset.sum_congr rfl fun c hc ↦ by
          simpa [C] using hc
        _ = 16 := by simp [hC4]
    have := hnone C hCind
    omega
  · have hC5 : C.card = 5 := by omega
    have hinternal_le :
        ∀ c ∈ C, (G.neighborFinset c ∩ C).card ≤ 1 := by
      intro c hc
      have hdc : G.degree c = 4 := by simpa [C] using hc
      have hbase :
          8 + 2 * (G.neighborFinset c ∩ C).card ≤
            ∑ z ∈ G.neighborFinset c, G.degree z := by
        have hpoint :
            ∀ z ∈ G.neighborFinset c,
              2 + (if z ∈ C then 2 else 0) ≤ G.degree z := by
          intro z hz
          rcases hdegree_two_to_four z with h2 | h3 | h4
          · simp [C, h2]
          · simp [C, h3]
          · simp [C, h4]
        calc
          8 + 2 * (G.neighborFinset c ∩ C).card =
              ∑ z ∈ G.neighborFinset c,
                (2 + if z ∈ C then 2 else 0) := by
            simp [Finset.sum_add_distrib, hdc,
              ← G.card_neighborFinset_eq_degree, mul_comm]
          _ ≤ _ := Finset.sum_le_sum hpoint
      have hcupper := hneighbor c
      omega
    have hcross_lower :
        15 ≤ ∑ c ∈ C, (G.neighborFinset c \ C).card := by
      calc
        15 = ∑ _c ∈ C, 3 := by simp [hC5]
        _ ≤ _ := Finset.sum_le_sum fun c hc ↦ by
          have hdc : (G.neighborFinset c).card = 4 := by
            rw [G.card_neighborFinset_eq_degree]
            simpa [C] using hc
          have hpart :=
            Finset.card_sdiff_add_card_inter (G.neighborFinset c) C
          have hi := hinternal_le c hc
          omega
    have houtside_sum :
        (∑ z ∈ Cᶜ, G.degree z) = 12 := by
      change (∑ z ∈ (Finset.univ \ C), G.degree z) = 12
      have hCsum : (∑ c ∈ C, G.degree c) = 20 := by
        calc
          _ = ∑ _c ∈ C, 4 := Finset.sum_congr rfl fun c hc ↦ by
            simpa [C] using hc
          _ = 20 := by simp [hC5]
      have hsplit := Finset.sum_sdiff C.subset_univ (f := fun z => G.degree z)
      omega
    have hcross_upper :
        (∑ c ∈ C, (G.neighborFinset c \ C).card) ≤ 12 := by
      calc
        _ = ∑ z ∈ Cᶜ, (G.neighborFinset z ∩ C).card := by
          calc
            _ = ∑ c ∈ C, ∑ z ∈ Cᶜ,
                  if G.Adj c z then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [← neighbor_inter_count c Cᶜ]
              congr 1
              ext z
              simp
            _ = ∑ z ∈ Cᶜ, ∑ c ∈ C,
                  if G.Adj c z then 1 else 0 := Finset.sum_comm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [neighbor_inter_count]
              apply Finset.sum_congr rfl
              intro c hc
              rw [G.adj_comm]
        _ ≤ ∑ z ∈ Cᶜ, G.degree z := Finset.sum_le_sum fun z hz ↦ by
          calc
            (G.neighborFinset z ∩ C).card ≤ (G.neighborFinset z).card :=
              Finset.card_le_card Finset.inter_subset_left
            _ = G.degree z := G.card_neighborFinset_eq_degree z
        _ = 12 := houtside_sum
    omega

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        G.edgeFinset.card = 16 →
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
  refine ⟨H, hle, hbwith.isBipartite, ?_⟩
  calc
    (G.edgeFinset \ H.edgeFinset).card =
        G.edgeFinset.card - H.edgeFinset.card :=
      Finset.card_sdiff_of_subset (edgeFinset_mono hle)
    _ = 16 - ∑ x ∈ S, G.degree x := by rw [hedges, hedge]
    _ ≤ 4 := by omega

end Submissions.Erdos23N2M16.Direct

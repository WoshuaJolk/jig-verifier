import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Submissions.Erdos149DegreeAtMostTwo.Savcab

def strongConflict {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f :=
    e ≠ f ∧
      ((G.lineGraph).Adj e f ∨
        ∃ middle : G.edgeSet,
          (G.lineGraph).Adj e middle ∧ (G.lineGraph).Adj middle f)
  symm := ⟨by
    intro e f h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hef | ⟨middle, hem, hmf⟩
    · exact Or.inl hef.symm
    · exact Or.inr ⟨middle, hmf.symm, hem.symm⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

noncomputable def maximumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  open scoped Classical in G.maxDegree

def StrongColorable {V : Type*} (G : SimpleGraph V) (colors : ℕ) : Prop :=
  (strongConflict G).Colorable colors

open SimpleGraph Finset

/-- The greedy bound: fewer than `k` neighbors at every vertex suffice for `k` colors. -/
theorem colorable_of_degree_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hdeg : ∀ v, G.degree v < k) : G.Colorable k := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    exact Colorable.of_isEmpty k
  · let := hV
    have hk : 0 < k := Nat.zero_lt_of_lt (hdeg (Classical.arbitrary V))
    have hpartial : ∀ s : Finset V, ∃ c : V → Fin k,
        ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → c x ≠ c y := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨fun _ => ⟨0, hk⟩, by simp⟩
      | @insert v s _hv ih =>
        obtain ⟨c, hc⟩ := ih
        have hcard : ((G.neighborFinset v).image c).card < (Finset.univ : Finset (Fin k)).card := by
          simpa only [Finset.card_univ, Fintype.card_fin, G.card_neighborFinset_eq_degree]
            using lt_of_le_of_lt (Finset.card_image_le (s := G.neighborFinset v) (f := c)) (hdeg v)
        obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        refine ⟨Function.update c v a, ?_⟩
        intro x hx y hy hxy
        by_cases hxv : x = v
        · subst x
          have hyv : y ≠ v := hxy.ne'
          have hne : a ≠ c y := fun he => ha
            (Finset.mem_image.mpr ⟨y, (G.mem_neighborFinset v y).mpr hxy, he.symm⟩)
          simpa [Function.update_apply, hyv] using hne
        · by_cases hyv : y = v
          · subst y
            have hne : c x ≠ a := fun he => ha
              (Finset.mem_image.mpr ⟨x, (G.mem_neighborFinset v x).mpr hxy.symm, he⟩)
            simpa [Function.update_apply, hxv] using hne
          · have hx' : x ∈ s := (Finset.mem_insert.mp hx).resolve_left hxv
            have hy' : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hyv
            simpa [Function.update_apply, hxv, hyv] using hc x hx' y hy' hxy
    obtain ⟨c, hc⟩ := hpartial Finset.univ
    exact ⟨Coloring.mk c (fun hxy => hc _ (Finset.mem_univ _) _ (Finset.mem_univ _) hxy)⟩



section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def side (u v : V) : Finset (Sym2 V) :=
  ((G.incidenceFinset u).erase s(u, v)) ∪
    ((G.neighborFinset u).erase v).biUnion
      (fun x => (G.incidenceFinset x).erase s(u, x))

lemma side_card_le (u v : V) (h : G.Adj u v) :
    (side G u v).card ≤ (G.maxDegree - 1) * G.maxDegree := by
  have hu : s(u, v) ∈ G.incidenceFinset u := by
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, h]
  have hv : v ∈ G.neighborFinset u := by simpa using h
  have hinc : ((G.incidenceFinset u).erase s(u,v)).card = G.degree u - 1 := by
    rw [Finset.card_erase_of_mem hu, G.card_incidenceFinset_eq_degree]
  have hnei : ((G.neighborFinset u).erase v).card = G.degree u - 1 := by
    rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree]
  have hsum : ∀ x ∈ (G.neighborFinset u).erase v,
      ((G.incidenceFinset x).erase s(u,x)).card ≤ G.maxDegree - 1 := by
    intro x hx
    have hux : G.Adj u x := by simpa using (Finset.mem_erase.mp hx).2
    have hxmem : s(u,x) ∈ G.incidenceFinset x := by
      simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hux]
    rw [Finset.card_erase_of_mem hxmem, G.card_incidenceFinset_eq_degree]
    exact Nat.sub_le_sub_right (G.degree_le_maxDegree x) 1
  calc
    (side G u v).card ≤
        ((G.incidenceFinset u).erase s(u,v)).card +
          (((G.neighborFinset u).erase v).biUnion
            (fun x => (G.incidenceFinset x).erase s(u,x))).card :=
      Finset.card_union_le _ _
    _ ≤ (G.degree u - 1) +
          ∑ x ∈ (G.neighborFinset u).erase v,
            ((G.incidenceFinset x).erase s(u,x)).card := by
      rw [hinc]
      exact Nat.add_le_add_left (Finset.card_biUnion_le) _
    _ ≤ (G.degree u - 1) +
          ((G.neighborFinset u).erase v).card * (G.maxDegree - 1) := by
      exact Nat.add_le_add_left ((Finset.sum_le_sum hsum).trans_eq (by simp)) _
    _ = (G.degree u - 1) * G.maxDegree := by
      rw [hnei]
      have hp := h.degree_pos_left.trans_le (G.degree_le_maxDegree u)
      calc
        (G.degree u - 1) + (G.degree u - 1) * (G.maxDegree - 1)
            = (G.degree u - 1) * ((G.maxDegree - 1) + 1) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        _ = _ := by rw [Nat.sub_add_cancel hp]
    _ ≤ (G.maxDegree - 1) * G.maxDegree :=
      Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (G.degree_le_maxDegree u) 1)

lemma mem_side (u v : V) (f : G.edgeSet) (hu : u ∈ f.val)
    (hf : f.val ≠ s(u,v)) : f.val ∈ side G u v := by
  apply Finset.mem_union_left
  exact Finset.mem_erase.mpr ⟨hf, by
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet] using
      (show f.val ∈ G.edgeSet ∧ u ∈ f.val from ⟨f.property, hu⟩)⟩

lemma connector_side (u v : V) (m f : G.edgeSet) (hum : u ∈ m.val)
    (hme : m.val ≠ s(u,v)) (hmf : G.lineGraph.Adj m f)
    (hfe : f.val ≠ s(u,v)) : f.val ∈ side G u v := by
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hum
  have hux : G.Adj u x := by simpa [hx] using m.property
  have hxv : x ≠ v := by intro h; subst x; exact hme hx
  obtain ⟨_, y, hym, hyf⟩ := G.lineGraph_adj_iff_exists.mp hmf
  rw [hx, Sym2.mem_iff] at hym
  rcases hym with hy | hy
  · rw [hy] at hyf
    exact mem_side G u v f hyf hfe
  · rw [hy] at hyf
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨x, Finset.mem_erase.mpr ⟨hxv, by simpa using hux⟩, ?_⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro h
      exact hmf.1 (Subtype.ext (hx.trans h.symm))
    · simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet] using
        (show f.val ∈ G.edgeSet ∧ x ∈ f.val from ⟨f.property, hyf⟩)

lemma conflict_mem_union (u v : V) (huv : G.Adj u v) (f : G.edgeSet)
    (h : (strongConflict G).Adj ⟨s(u,v), huv⟩ f) :
    f.val ∈ side G u v ∪ side G v u := by
  have hfe : f.val ≠ s(u,v) := by
    intro he; exact h.1 (Subtype.ext he.symm)
  have hfe' : f.val ≠ s(v,u) := by simpa only [Sym2.eq_swap (a := v)] using hfe
  rcases h.2 with h | ⟨m, hem, hmf⟩
  · obtain ⟨_, x, hxe, hxf⟩ := G.lineGraph_adj_iff_exists.mp h
    rcases Sym2.mem_iff.mp hxe with hx | hx
    · rw [hx] at hxf
      exact Finset.mem_union_left _ (mem_side G u v f hxf hfe)
    · rw [hx] at hxf
      exact Finset.mem_union_right _ (mem_side G v u f hxf hfe')
  · obtain ⟨hne, x, hxe, hxm⟩ := G.lineGraph_adj_iff_exists.mp hem
    have hme : m.val ≠ s(u,v) := by
      intro he; exact hne (Subtype.ext he.symm)
    rcases Sym2.mem_iff.mp hxe with hx | hx
    · rw [hx] at hxm
      exact Finset.mem_union_left _ (connector_side G u v m f hxm hme hmf hfe)
    · rw [hx] at hxm
      have hme' : m.val ≠ s(v,u) := by
        simpa only [Sym2.eq_swap (a := v)] using hme
      exact Finset.mem_union_right _ (connector_side G v u m f hxm hme' hmf hfe')

open scoped Classical in
lemma conflict_degree_le (e : G.edgeSet) :
    (strongConflict G).degree e ≤ 2 * G.maxDegree * (G.maxDegree - 1) := by
  classical
  obtain ⟨⟨u,v⟩, huv⟩ := e
  let S := (strongConflict G).neighborFinset ⟨s(u,v), huv⟩
  have hsub : S.image Subtype.val ⊆ side G u v ∪ side G v u := by
    intro f hf
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hf
    exact conflict_mem_union G u v huv f (by simpa [S] using hf)
  calc
    (strongConflict G).degree ⟨s(u,v), huv⟩ = S.card := rfl
    _ = (S.image Subtype.val).card :=
      (Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)).symm
    _ ≤ (side G u v ∪ side G v u).card := Finset.card_le_card hsub
    _ ≤ (side G u v).card + (side G v u).card := Finset.card_union_le _ _
    _ ≤ (G.maxDegree - 1) * G.maxDegree + (G.maxDegree - 1) * G.maxDegree :=
      Nat.add_le_add (side_card_le G u v huv) (side_card_le G v u huv.symm)
    _ = 2 * G.maxDegree * (G.maxDegree - 1) := by
      rw [← two_mul]
      ac_rfl

end

theorem greedy_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    StrongColorable G (2 * maximumDegree G * (maximumDegree G - 1) + 1) := by
  classical
  apply colorable_of_degree_lt
  intro e
  exact Nat.lt_succ_of_le (conflict_degree_le G e)

theorem degree_at_most_two (n : ℕ) (G : SimpleGraph (Fin n))
    (hd : maximumDegree G ≤ 2) :
    StrongColorable G ((5 * (maximumDegree G)^2) / 4) := by
  classical
  by_cases h0 : maximumDegree G = 0
  · have hG : G = ⊥ := G.maxDegree_eq_zero_iff.mp h0
    subst G
    have : IsEmpty (⊥ : SimpleGraph (Fin n)).edgeSet :=
      ⟨fun e => by simpa using e.property⟩
    exact SimpleGraph.Colorable.of_isEmpty _
  · have h12 : maximumDegree G = 1 ∨ maximumDegree G = 2 := by omega
    rcases h12 with h1 | h2
    · simpa [h1] using greedy_bound n G
    · simpa [h2] using greedy_bound n G

end Submissions.Erdos149DegreeAtMostTwo.Savcab

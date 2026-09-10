import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Submissions.Erdos149FalseTwinDeletion.Savcab

section Part0
-- Source module: BicliqueInterface

namespace StructuralAttack

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


open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- For disjoint edges, canonical conflict is exactly adjacency across endpoints. -/
theorem conflict_iff_cross (e f : G.edgeSet)
    (hdis : ∀ v, v ∈ e.val → v ∈ f.val → False) :
    (strongConflict G).Adj e f ↔
      ∃ x ∈ e.val, ∃ y ∈ f.val, G.Adj x y := by
  constructor
  · rintro ⟨_, h | ⟨m, hem, hmf⟩⟩
    · obtain ⟨_, x, hxe, hxf⟩ := G.lineGraph_adj_iff_exists.mp h
      exact (hdis x hxe hxf).elim
    · obtain ⟨_, x, hxe, hxm⟩ := G.lineGraph_adj_iff_exists.mp hem
      obtain ⟨_, y, hym, hyf⟩ := G.lineGraph_adj_iff_exists.mp hmf
      have hxy : x ≠ y := by
        intro h
        subst y
        exact hdis x hxe hyf
      have hm : m.val = s(x, y) :=
        (Sym2.mem_and_mem_iff hxy).mp ⟨hxm, hym⟩
      refine ⟨x, hxe, y, hyf, ?_⟩
      simpa only [hm, SimpleGraph.mem_edgeSet] using m.property
  · rintro ⟨x, hxe, y, hyf, hxy⟩
    let m : G.edgeSet := ⟨s(x, y), hxy⟩
    have hef : e ≠ f := by
      intro h
      subst f
      exact hdis x hxe hxe
    have hem : e ≠ m := by
      intro h
      have hy : y ∈ e.val := by
        rw [h]
        exact Sym2.mem_mk_right x y
      exact hdis y hy hyf
    have hmf : m ≠ f := by
      intro h
      have hx : x ∈ f.val := by
        rw [← h]
        exact Sym2.mem_mk_left x y
      exact hdis x hxe hx
    refine ⟨hef, Or.inr ⟨m, ?_, ?_⟩⟩
    · exact G.lineGraph_adj_iff_exists.mpr
        ⟨hem, x, hxe, Sym2.mem_mk_left x y⟩
    · exact G.lineGraph_adj_iff_exists.mpr
        ⟨hmf, y, Sym2.mem_mk_right x y, hyf⟩

/-- The rows (or columns) touched from the endpoints of an outside edge. -/
def profile (e : G.edgeSet) (A : Set V) : Set V :=
  {a | a ∈ A ∧ ∃ x ∈ e.val, G.Adj x a}

/-- An external edge sees precisely a union of rows and columns of a biclique.
All adjacency, including the connecting edges, is measured in the full host G. -/
theorem biclique_interface (A B : Set V)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (e : G.edgeSet) (hout : ∀ v ∈ e.val, v ∉ A ∧ v ∉ B)
    (a : V) (ha : a ∈ A) (b : V) (hb : b ∈ B) :
    (strongConflict G).Adj e ⟨s(a, b), hAB a ha b hb⟩ ↔
      a ∈ profile G e A ∨ b ∈ profile G e B := by
  rw [conflict_iff_cross G e _ (by
    intro v hv hvab
    rcases Sym2.mem_iff.mp hvab with rfl | rfl
    · exact (hout _ hv).1 ha
    · exact (hout _ hv).2 hb)]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · exact Or.inl ⟨ha, x, hx, hxy⟩
    · exact Or.inr ⟨hb, x, hx, hxy⟩
  · rintro (⟨_, x, hx, hxa⟩ | ⟨_, x, hx, hxb⟩)
    · exact ⟨x, hx, a, Sym2.mem_mk_left a b, hxa⟩
    · exact ⟨x, hx, b, Sym2.mem_mk_right a b, hxb⟩

theorem biclique_nonconflict_rectangle (A B : Set V)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (e : G.edgeSet) (hout : ∀ v ∈ e.val, v ∉ A ∧ v ∉ B)
    (a : V) (ha : a ∈ A) (b : V) (hb : b ∈ B) :
    ¬ (strongConflict G).Adj e ⟨s(a, b), hAB a ha b hb⟩ ↔
      a ∈ A \ profile G e A ∧ b ∈ B \ profile G e B := by
  rw [biclique_interface G A B hAB e hout a ha b hb]
  simp only [not_or, Set.mem_sdiff, ha, hb, true_and]

/-- Add one leaf to every vertex; false is the original vertex, true its leaf. -/
def pendantHost (K : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj p q :=
    (p.2 = false ∧ q.2 = false ∧ K.Adj p.1 q.1) ∨
    (p.1 = q.1 ∧ p.2 ≠ q.2)
  symm := ⟨by
    rintro p q (⟨hp, hq, h⟩ | ⟨h, hne⟩)
    · exact Or.inl ⟨hq, hp, h.symm⟩
    · exact Or.inr ⟨h.symm, hne.symm⟩⟩
  loopless := ⟨by
    rintro p (⟨_, _, h⟩ | ⟨_, h⟩)
    · exact (K.ne_of_adj h) rfl
    · exact h rfl⟩

def pendantEdge (K : SimpleGraph V) (v : V) : (pendantHost K).edgeSet :=
  ⟨s((v, false), (v, true)), Or.inr ⟨rfl, by change false ≠ true; decide⟩⟩

/-- Every graph occurs exactly on the retained pendant edges of a conflict graph. -/
theorem pendant_conflict_iff (K : SimpleGraph V) (v w : V) :
    (strongConflict (pendantHost K)).Adj (pendantEdge K v) (pendantEdge K w) ↔
      K.Adj v w := by
  by_cases hvw : v = w
  · subst w
    simp
  rw [conflict_iff_cross (pendantHost K) (pendantEdge K v) (pendantEdge K w) (by
    intro z hzv hzw
    have hv : z.1 = v := by
      rcases Sym2.mem_iff.mp hzv with rfl | rfl <;> rfl
    have hw : z.1 = w := by
      rcases Sym2.mem_iff.mp hzw with rfl | rfl <;> rfl
    exact hvw (hv.symm.trans hw))]
  simp [pendantEdge, Sym2.mem_iff, pendantHost, hvw]

def pendantEmbedding (K : SimpleGraph V) : K ↪g strongConflict (pendantHost K) where
  toFun := pendantEdge K
  inj' v w h := by
    have hv : (v, false) ∈ (pendantEdge K w).val := by
      rw [← h]
      exact Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hv with h | h <;> exact congrArg Prod.fst h
  map_rel_iff' := pendant_conflict_iff K _ _


end StructuralAttack
end Part0

section Part1
-- Source module: Submissions.Erdos149GreedyBound.Savcab

namespace Submissions.Erdos149GreedyBound.Savcab

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

end Submissions.Erdos149GreedyBound.Savcab
end Part1

section Part2
-- Source module: TwinInterface

namespace TwinReduction

open SimpleGraph StructuralAttack

variable {V : Type*} (G : SimpleGraph V)

/-- The local interface uses exactly the already verified conflict graph. -/
theorem canonical_conflict :
    strongConflict G = Submissions.Erdos149GreedyBound.Savcab.strongConflict G := rfl

open scoped Classical in
theorem conflict_degree_le_twenty_four [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hdegree : G.maxDegree ≤ 4) (e : G.edgeSet) :
    (strongConflict G).degree e ≤ 24 := by
  classical
  have h := Submissions.Erdos149GreedyBound.Savcab.conflict_degree_le G e
  change (strongConflict G).degree e ≤ 2 * G.maxDegree * (G.maxDegree - 1) at h
  exact h.trans (by
    calc 2 * G.maxDegree * (G.maxDegree - 1)
        ≤ 2 * 4 * (4 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdegree) (Nat.sub_le_sub_right hdegree 1)
      _ = 24 := rfl)

/-- Canonical conflict is endpoint intersection or an edge between endpoints. -/
theorem conflict_iff_endpoints (e f : G.edgeSet) :
    (strongConflict G).Adj e f ↔
      e ≠ f ∧ ∃ x ∈ e.val, ∃ y ∈ f.val, x = y ∨ G.Adj x y := by
  by_cases hdis : ∀ v, v ∈ e.val → v ∈ f.val → False
  · rw [conflict_iff_cross G e f hdis]
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      refine ⟨?_, x, hx, y, hy, Or.inr hxy⟩
      intro hef
      exact hdis x hx (hef ▸ hx)
    · rintro ⟨_, x, hx, y, hy, hxy | hxy⟩
      · subst y
        exact (hdis x hx hy).elim
      · exact ⟨x, hx, y, hy, hxy⟩
  · push Not at hdis
    obtain ⟨x, hxe, hxf, _⟩ := hdis
    constructor
    · intro h
      exact ⟨h.1, x, hxe, x, hxf, Or.inl rfl⟩
    · intro h
      exact ⟨h.1, Or.inl (G.lineGraph_adj_iff_exists.mpr ⟨h.1, x, hxe, hxf⟩)⟩

/-- A retained spoke conflicts with every cell edge of the complete twin cell. -/
theorem spoke_conflicts_cell (p u y : V) (hpu : G.Adj p u) (hpy : G.Adj p y)
    (e : G.edgeSet) (hye : y ∈ e.val) (hpe : p ∉ e.val) :
    (strongConflict G).Adj ⟨s(p,u), hpu⟩ e := by
  rw [conflict_iff_endpoints]
  refine ⟨?_, p, Sym2.mem_mk_left _ _, y, hye, Or.inr hpy⟩
  intro he
  apply hpe
  rw [← he]
  exact Sym2.mem_mk_left _ _

/-- Distinct edges in a complete bipartite cell conflict in the full host. -/
theorem cell_clique (A U : Set V)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, G.Adj a u) :
    (strongConflict G).IsClique
      {e | ∃ a ∈ A, ∃ u ∈ U, e.val = s(a,u)} := by
  rintro e ⟨a, ha, u, hu, he⟩ f ⟨b, hb, v, hv, hf⟩ hne
  rw [conflict_iff_endpoints]
  exact ⟨hne, a, he ▸ Sym2.mem_mk_left _ _, v, hf ▸ Sym2.mem_mk_right _ _,
    Or.inr (hAU a ha v hv)⟩

/-- For a fixed edge avoiding the row set, a twin-cell edge sees only its row.
The neighborhood equation is exact; all connectors are in the original G. -/
theorem fixed_row_conflict (p u : V) (U : Set V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hu : u ∈ U)
    (e : G.edgeSet) (hpe : p ∉ e.val) (hUe : ∀ v ∈ e.val, v ∉ U) :
    (strongConflict G).Adj ⟨s(p,u), (hp u).mpr hu⟩ e ↔
      ∃ x ∈ e.val, G.Adj u x := by
  rw [conflict_iff_endpoints]
  constructor
  · rintro ⟨_, y, hy, x, hx, hyx⟩
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · rcases hyx with rfl | hpx
      · exact (hpe hx).elim
      · exact (hUe x hx ((hp x).mp hpx)).elim
    · rcases hyx with rfl | hux
      · exact (hUe _ hx hu).elim
      · exact ⟨x, hx, hux⟩
  · rintro ⟨x, hx, hux⟩
    refine ⟨?_, u, Sym2.mem_mk_right _ _, x, hx, Or.inr hux⟩
    intro he
    apply hpe
    rw [← he]
    exact Sym2.mem_mk_left _ _

/-- The two cell edges at one row have identical conflicts with fixed edges. -/
theorem twin_row_same_fixed_conflicts (p q u : V) (U : Set V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (e : G.edgeSet)
    (hpe : p ∉ e.val) (hqe : q ∉ e.val) (hUe : ∀ v ∈ e.val, v ∉ U) :
    (strongConflict G).Adj ⟨s(p,u), (hp u).mpr hu⟩ e ↔
      (strongConflict G).Adj ⟨s(q,u), (hq u).mpr hu⟩ e := by
  rw [fixed_row_conflict G p u U hp hu e hpe hUe,
    fixed_row_conflict G q u U hq hu e hqe hUe]


end TwinReduction
end Part2

section Part3
-- Source module: TwinGeometry

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual host edges having no endpoint among the twins or row vertices. -/
def fixedEdges (p q : V) (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => p ∉ e ∧ q ∉ e ∧ ∀ v ∈ e, v ∉ U)

/-- Fixed edges incident with a specified center. -/
def fixedAt (p q : V) (U : Finset V) (x : V) : Finset (Sym2 V) :=
  (fixedEdges G p q U).filter (fun e => x ∈ e)

/-- The row's neighbors other than the two distinguished twins. -/
def rowCenters (p q u : V) : Finset V := G.neighborFinset u \ {p,q}

/-- Fixed edges seen by the row, counted without multiplicity. -/
def rowSeen (p q : V) (U : Finset V) (u : V) : Finset (Sym2 V) :=
  (rowCenters G p q u).biUnion (fixedAt G p q U)

lemma mem_fixedEdges (p q : V) (U : Finset V) (e : Sym2 V) :
    e ∈ fixedEdges G p q U ↔ e ∈ G.edgeSet ∧ p ∉ e ∧ q ∉ e ∧ ∀ v ∈ e, v ∉ U := by
  simp [fixedEdges]

lemma mem_rowCenters (p q u x : V) :
    x ∈ rowCenters G p q u ↔ G.Adj u x ∧ x ≠ p ∧ x ≠ q := by
  simp [rowCenters, not_or]

lemma mem_rowSeen (p q : V) (U : Finset V) (u : V) (e : Sym2 V) :
    e ∈ rowSeen G p q U u ↔ e ∈ fixedEdges G p q U ∧ ∃ x ∈ e, G.Adj u x := by
  constructor
  · intro he
    obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp he
    exact ⟨(Finset.mem_filter.mp he).1, x, (Finset.mem_filter.mp he).2,
      ((mem_rowCenters G p q u x).mp hx).1⟩
  · rintro ⟨he, x, hxe, hux⟩
    have hf := (mem_fixedEdges G p q U e).mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨x, (mem_rowCenters G p q u x).mpr ⟨hux, ?_, ?_⟩, Finset.mem_filter.mpr ⟨he,hxe⟩⟩
    · exact fun h => hf.2.1 (h ▸ hxe)
    · exact fun h => hf.2.2.1 (h ▸ hxe)

/-- The counted row set is exactly the canonical fixed-edge conflict set. -/
theorem rowSeen_iff_conflict (p q : V) (U : Finset V) (u : V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hu : u ∈ U) (e : G.edgeSet)
    (he : e.val ∈ fixedEdges G p q U) :
    e.val ∈ rowSeen G p q U u ↔
      (strongConflict G).Adj ⟨s(p,u), (hp u).mpr hu⟩ e := by
  have hf := (mem_fixedEdges G p q U e.val).mp he
  rw [mem_rowSeen, and_iff_right he]
  exact (fixed_row_conflict G p u (U : Set V) hp hu e hf.2.1 hf.2.2.2).symm

lemma fixedAt_subset_incidence (p q : V) (U : Finset V) (x : V) :
    fixedAt G p q U x ⊆ G.incidenceFinset x := by
  intro e he
  have hf := Finset.mem_filter.mp he
  have hed := ((mem_fixedEdges G p q U e).mp hf.1).1
  simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet] using And.intro hed hf.2

lemma fixedAt_eq_empty_of_row (p q : V) (U : Finset V) {x : V} (hx : x ∈ U) :
    fixedAt G p q U x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hf := Finset.mem_filter.mp he
  exact ((mem_fixedEdges G p q U e).mp hf.1).2.2.2 x hf.2 hx

lemma fixedAt_card_le_three (p q : V) (U : Finset V) {u x : V}
    (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U) (hux : G.Adj u x) :
    (fixedAt G p q U x).card ≤ 3 := by
  have hsub : fixedAt G p q U x ⊆ (G.incidenceFinset x).erase s(u,x) := by
    intro e he
    refine Finset.mem_erase.mpr ⟨?_, fixedAt_subset_incidence G p q U x he⟩
    intro h
    have hf := (mem_fixedEdges G p q U e).mp (Finset.mem_filter.mp he).1
    apply hf.2.2.2 u _ hu
    rw [h]
    exact Sym2.mem_mk_left _ _
  have hmem : s(u,x) ∈ G.incidenceFinset x := by
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hux]
  have hd := (G.degree_le_maxDegree x).trans hdegree
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem, G.card_incidenceFinset_eq_degree] at hcard
  omega

lemma rowCenters_card_le_two (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) : (rowCenters G p q u).card ≤ 2 := by
  have hsub : {p,q} ⊆ G.neighborFinset u := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (G.mem_neighborFinset _ _).mpr ((hp u).mpr hu).symm
    · have := Finset.mem_singleton.mp hv
      subst v
      exact (G.mem_neighborFinset _ _).mpr ((hq u).mpr hu).symm
  have hd := (G.degree_le_maxDegree u).trans hdegree
  rw [rowCenters, Finset.card_sdiff_of_subset hsub, G.card_neighborFinset_eq_degree]
  simp only [Finset.card_pair hpq]
  omega

lemma rowSeen_card_le_three_mul_centers (p q : V) (U : Finset V) (u : V)
    (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U) :
    (rowSeen G p q U u).card ≤ (rowCenters G p q u).card * 3 := by
  calc
    (rowSeen G p q U u).card ≤ ∑ x ∈ rowCenters G p q u, (fixedAt G p q U x).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ rowCenters G p q u, 3 := by
      apply Finset.sum_le_sum
      intro x hx
      exact fixedAt_card_le_three G p q U hdegree hu ((mem_rowCenters G p q u x).mp hx).1
    _ = _ := by simp

/-- Every row sees at most six fixed host edges. -/
theorem rowSeen_card_le_six (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) : (rowSeen G p q U u).card ≤ 6 := by
  have h1 := rowCenters_card_le_two G p q U u hpq hdegree hp hq hu
  have h2 := rowSeen_card_le_three_mul_centers G p q U u hdegree hu
  omega

/-- Seeing at least five fixed edges forces both available outside-neighbor slots to be used. -/
theorem rowCenters_card_eq_two_of_five (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hfive : 5 ≤ (rowSeen G p q U u).card) :
    (rowCenters G p q u).card = 2 := by
  have h1 := rowCenters_card_le_two G p q U u hpq hdegree hp hq hu
  have h2 := rowSeen_card_le_three_mul_centers G p q U u hdegree hu
  omega

/-- In the same regime no center can itself be a row vertex. -/
theorem rowCenters_disjoint_rows_of_five (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hfive : 5 ≤ (rowSeen G p q U u).card) :
    Disjoint (rowCenters G p q u) U := by
  apply Finset.disjoint_left.mpr
  intro x hx hxU
  have hcard := rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu hfive
  have hz := fixedAt_eq_empty_of_row G p q U hxU
  have hsum := Finset.sum_erase_add (rowCenters G p q u)
    (fun y => (fixedAt G p q U y).card) hx
  rw [hz, Finset.card_empty, Nat.add_zero] at hsum
  have hbound : ∑ y ∈ (rowCenters G p q u).erase x, (fixedAt G p q U y).card ≤ 3 := by
    calc
      ∑ y ∈ (rowCenters G p q u).erase x, (fixedAt G p q U y).card
          ≤ ∑ _y ∈ (rowCenters G p q u).erase x, 3 := by
            apply Finset.sum_le_sum
            intro y hy
            exact fixedAt_card_le_three G p q U hdegree hu
              ((mem_rowCenters G p q u y).mp (Finset.mem_of_mem_erase hy)).1
      _ = 3 := by simp [Finset.card_erase_of_mem hx, hcard]
  have hbi : (rowSeen G p q U u).card ≤ ∑ y ∈ rowCenters G p q u, (fixedAt G p q U y).card :=
    Finset.card_biUnion_le
  omega

/-- If every row sees at least five fixed edges, the row set is independent. -/
theorem rows_independent_of_five (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) : G.IsIndepSet U := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p ((hp p).mpr h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q ((hq q).mpr h)
  intro u hu v hv _ huv
  have hcent : v ∈ rowCenters G p q u :=
    (mem_rowCenters G p q u v).mpr ⟨huv, fun h => hpU (h ▸ hv), fun h => hqU (h ▸ hv)⟩
  exact Finset.disjoint_left.mp
    (rowCenters_disjoint_rows_of_five G p q U u hpq hdegree hp hq hu (hfive u hu)) hcent hv

/-- How many row vertices are adjacent to a given center. -/
def rowMultiplicity (U : Finset V) (x : V) : ℕ := (G.neighborFinset x ∩ U).card

/-- Each neighbor in the row set consumes a different incidence slot unavailable to fixed edges. -/
theorem fixedAt_card_add_rowMultiplicity_le_four (p q : V) (U : Finset V) (x : V)
    (hdegree : G.maxDegree ≤ 4) :
    (fixedAt G p q U x).card + rowMultiplicity G U x ≤ 4 := by
  let R := (G.neighborFinset x ∩ U).map (Sym2.mkEmbedding x)
  have hR : R ⊆ G.incidenceFinset x := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp he
    have hxv : G.Adj x v := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hv).1
    change s(x,v) ∈ G.incidenceFinset x
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hxv]
  have hdis : Disjoint (fixedAt G p q U x) R := by
    apply Finset.disjoint_left.mpr
    intro e he hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hr
    have hf := (mem_fixedEdges G p q U _).mp (Finset.mem_filter.mp he).1
    exact hf.2.2.2 v (Sym2.mem_mk_right x v) (Finset.mem_inter.mp hv).2
  have hsub : fixedAt G p q U x ∪ R ⊆ G.incidenceFinset x :=
    Finset.union_subset (fixedAt_subset_incidence G p q U x) hR
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, G.card_incidenceFinset_eq_degree] at hc
  have hr : R.card = rowMultiplicity G U x := by simp [R, rowMultiplicity]
  rw [hr] at hc
  exact hc.trans ((G.degree_le_maxDegree x).trans hdegree)

/-- The two-center bound records all incidences with row vertices, even at other rows. -/
theorem rowSeen_card_add_multiplicities_le_eight (p q : V) (U : Finset V) (u x y : V)
    (hdegree : G.maxDegree ≤ 4) (hcenters : rowCenters G p q u = {x,y}) :
    (rowSeen G p q U u).card + rowMultiplicity G U x + rowMultiplicity G U y ≤ 8 := by
  have hx := fixedAt_card_add_rowMultiplicity_le_four G p q U x hdegree
  have hy := fixedAt_card_add_rowMultiplicity_le_four G p q U y hdegree
  have heq : rowSeen G p q U u = fixedAt G p q U x ∪ fixedAt G p q U y := by
    simp [rowSeen, hcenters]
  have hb := Finset.card_union_le (fixedAt G p q U x) (fixedAt G p q U y)
  rw [← heq] at hb
  omega

/-- An edge joining two outside centers is counted from both centers and must be subtracted. -/
theorem rowSeen_card_add_multiplicities_le_seven_of_adjacent (p q : V) (U : Finset V)
    (u x y : V) (hdegree : G.maxDegree ≤ 4) (hcenters : rowCenters G p q u = {x,y})
    (hxU : x ∉ U) (hyU : y ∉ U) (hxy : G.Adj x y) :
    (rowSeen G p q U u).card + rowMultiplicity G U x + rowMultiplicity G U y ≤ 7 := by
  have hxcent : x ∈ rowCenters G p q u := by simp [hcenters]
  have hycent : y ∈ rowCenters G p q u := by simp [hcenters]
  have hx := (mem_rowCenters G p q u x).mp hxcent
  have hy := (mem_rowCenters G p q u y).mp hycent
  have hedge : s(x,y) ∈ fixedEdges G p q U := by
    rw [mem_fixedEdges]
    refine ⟨hxy, ?_, ?_, ?_⟩
    · simpa using And.intro hx.2.1.symm hy.2.1.symm
    · simpa using And.intro hx.2.2.symm hy.2.2.symm
    · intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hxU
      · exact hyU
  have hinter : s(x,y) ∈ fixedAt G p q U x ∩ fixedAt G p q U y := by
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hedge, Sym2.mem_mk_left _ _⟩,
      Finset.mem_filter.mpr ⟨hedge, Sym2.mem_mk_right _ _⟩⟩
  have hpos := Finset.card_pos.mpr ⟨s(x,y), hinter⟩
  have hc := Finset.card_union_add_card_inter (fixedAt G p q U x) (fixedAt G p q U y)
  have heq : rowSeen G p q U u = fixedAt G p q U x ∪ fixedAt G p q U y := by
    simp [rowSeen, hcenters]
  rw [← heq] at hc
  have hbx := fixedAt_card_add_rowMultiplicity_le_four G p q U x hdegree
  have hby := fixedAt_card_add_rowMultiplicity_le_four G p q U y hdegree
  omega

/-- Six seen fixed edges force two nonadjacent centers with three fixed edges each,
and each center is adjacent to this row alone among all row vertices. -/
theorem row_six_geometry (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hsix : 6 ≤ (rowSeen G p q U u).card) :
    ∃ x y, x ≠ y ∧ rowCenters G p q u = {x,y} ∧ x ∉ U ∧ y ∉ U ∧
      rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 1 ∧
      (fixedAt G p q U x).card = 3 ∧ (fixedAt G p q U y).card = 3 ∧ ¬ G.Adj x y := by
  have hfive : 5 ≤ (rowSeen G p q U u).card := by omega
  obtain ⟨x, y, hxy, hc⟩ := Finset.card_eq_two.mp
    (rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu hfive)
  have hx : x ∈ rowCenters G p q u := by simp [hc]
  have hy : y ∈ rowCenters G p q u := by simp [hc]
  have hdis := rowCenters_disjoint_rows_of_five G p q U u hpq hdegree hp hq hu hfive
  have hxU : x ∉ U := fun h => Finset.disjoint_left.mp hdis hx h
  have hyU : y ∉ U := fun h => Finset.disjoint_left.mp hdis hy h
  have hux := ((mem_rowCenters G p q u x).mp hx).1
  have huy := ((mem_rowCenters G p q u y).mp hy).1
  have hrx : 0 < rowMultiplicity G U x := by
    apply Finset.card_pos.mpr
    exact ⟨u, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hux.symm, hu⟩⟩
  have hry : 0 < rowMultiplicity G U y := by
    apply Finset.card_pos.mpr
    exact ⟨u, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huy.symm, hu⟩⟩
  have hb := rowSeen_card_add_multiplicities_le_eight G p q U u x y hdegree hc
  have hrx1 : rowMultiplicity G U x = 1 := by omega
  have hry1 : rowMultiplicity G U y = 1 := by omega
  have hax := fixedAt_card_le_three G p q U hdegree hu hux
  have hay := fixedAt_card_le_three G p q U hdegree hu huy
  have heq : rowSeen G p q U u = fixedAt G p q U x ∪ fixedAt G p q U y := by
    simp [rowSeen, hc]
  have hunion := Finset.card_union_le (fixedAt G p q U x) (fixedAt G p q U y)
  rw [← heq] at hunion
  refine ⟨x, y, hxy, hc, hxU, hyU, hrx1, hry1, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro hxyAdj
    have := rowSeen_card_add_multiplicities_le_seven_of_adjacent
      G p q U u x y hdegree hc hxU hyU hxyAdj
    omega



end TwinReduction
end Part3

section Part4
-- Source module: TwinColors

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Retained host edges incident with at least one row. -/
def spokeEdges (p q : V) (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => p ∉ e ∧ q ∉ e ∧ ∃ u ∈ U, u ∈ e)

/-- Properness on retained edges, with all conflicts measured in G. -/
def RetainedProper (p q : V) (c : Sym2 V → Fin 20) : Prop :=
  ∀ e f : G.edgeSet, p ∉ e.val → q ∉ e.val → p ∉ f.val → q ∉ f.val →
    (strongConflict G).Adj e f → c e.val ≠ c f.val

/-- A spoke cannot use a color occurring among the fixed exclusions of every row. -/
theorem spoke_colors_disjoint_common (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c) (T : Finset (Fin 20))
    (hT : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    Disjoint ((spokeEdges G p q U).image c) T := by
  rw [Finset.disjoint_left]
  intro a ha haT
  obtain ⟨e, he, rfl⟩ := mem_image.mp ha
  have he' := mem_filter.mp he
  obtain ⟨u, huU, hue⟩ := he'.2.2.2
  obtain ⟨f, hf, hcolor⟩ := mem_image.mp (hT u huU haT)
  have hseen := (mem_rowSeen G p q U u f).mp hf
  have hfixed := (mem_fixedEdges G p q U f).mp hseen.1
  obtain ⟨x, hxf, hux⟩ := hseen.2
  let e' : G.edgeSet := ⟨e, by simpa using he'.1⟩
  let f' : G.edgeSet := ⟨f, hfixed.1⟩
  have hconf : (strongConflict G).Adj e' f' := by
    rw [conflict_iff_endpoints]
    refine ⟨?_, u, hue, x, hxf, Or.inr hux⟩
    intro hef
    have heq : e = f := congrArg Subtype.val hef
    exact hfixed.2.2.2 u (heq ▸ hue) huU
  exact hc e' f' he'.2.1 he'.2.2.1 hfixed.2.1 hfixed.2.2.1 hconf hcolor.symm

/-- Color counts never exceed the already bounded number of fixed edges. -/
theorem row_colors_card_le_six (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (c : Sym2 V → Fin 20) :
    ((rowSeen G p q U u).image c).card ≤ 6 :=
  card_image_le.trans (rowSeen_card_le_six G p q U u hpq hdegree hp hq hu)

/-- Five shared fixed colors activate the tight host-geometry lemmas. -/
theorem shared_colors_force_five_edges (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hfive : 5 ≤ T.card)
    (hT : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card := by
  intro u hu
  exact hfive.trans ((card_le_card (hT u hu)).trans card_image_le)

/-- Six common colors exhaust every row's fixed-color set. -/
theorem row_colors_eq_common_of_six (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hT : T.card = 6) (hsub : T ⊆ (rowSeen G p q U u).image c) :
    (rowSeen G p q U u).image c = T := by
  apply (eq_of_subset_of_card_le hsub ?_).symm
  rw [hT]
  exact row_colors_card_le_six G p q U u hpq hdegree hp hq hu c

/-- A center's fixed colors are among its row's fixed colors. -/
theorem fixedAt_colors_subset_row (p q : V) (U : Finset V) (u x : V)
    (hx : x ∈ rowCenters G p q u) (c : Sym2 V → Fin 20) :
    (fixedAt G p q U x).image c ⊆ (rowSeen G p q U u).image c := by
  apply image_subset_image
  exact subset_biUnion_of_mem (fixedAt G p q U) hx

/-- In the six-color case every fixed edge incident with a center uses a common color. -/
theorem center_fixed_colors_common_of_six (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hT : T.card = 6) (hsub : T ⊆ (rowSeen G p q U u).image c) :
    (fixedAt G p q U x).image c ⊆ T := by
  rw [← row_colors_eq_common_of_six G p q U u hpq hdegree hp hq hu c T hT hsub]
  exact fixedAt_colors_subset_row G p q U u x hx c

/-- With five common colors, a row has at most one additional fixed color. -/
theorem row_extra_colors_le_one (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hT : T.card = 5) (hsub : T ⊆ (rowSeen G p q U u).image c) :
    ((rowSeen G p q U u).image c \ T).card ≤ 1 := by
  rw [card_sdiff_of_subset hsub, hT]
  have h := row_colors_card_le_six G p q U u hpq hdegree hp hq hu c
  omega


end TwinReduction
end Part4

section Part5
-- Source module: TwinSpokes

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma mem_spokeEdges (p q : V) (U : Finset V) (e : Sym2 V) :
    e ∈ spokeEdges G p q U ↔
      e ∈ G.edgeSet ∧ p ∉ e ∧ q ∉ e ∧ ∃ u ∈ U, u ∈ e := by
  simp [spokeEdges]

/-- Every spoke is retained as its actual edge in the original host. -/
def spokeToEdge (p q : V) (U : Finset V) : ↥(spokeEdges G p q U) → G.edgeSet :=
  fun e => ⟨e.val, ((mem_spokeEdges G p q U e.val).mp e.property).1⟩

theorem spokeToEdge_injective (p q : V) (U : Finset V) :
    Function.Injective (spokeToEdge G p q U) := by
  intro e f h
  exact Subtype.ext (congrArg (fun a : G.edgeSet => a.val) h)

/-- The induced spoke conflict graph uses all connectors in the full host G. -/
def spokeGraph (p q : V) (U : Finset V) : SimpleGraph ↥(spokeEdges G p q U) :=
  (strongConflict G).comap (spokeToEdge G p q U)

theorem spokeGraph_adj_iff (p q : V) (U : Finset V)
    (e f : ↥(spokeEdges G p q U)) :
    (spokeGraph G p q U).Adj e f ↔
      (strongConflict G).Adj (spokeToEdge G p q U e) (spokeToEdge G p q U f) := Iff.rfl

def spokeGraph_embedding (p q : V) (U : Finset V) :
    spokeGraph G p q U ↪g strongConflict G where
  toFun := spokeToEdge G p q U
  inj' := spokeToEdge_injective G p q U
  map_rel_iff' := Iff.rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- An actual host edge meets an independent row set in at most one vertex. -/
lemma row_endpoint_unique (U : Finset V) (hU : G.IsIndepSet U)
    (e : G.edgeSet) {u v : V} (hu : u ∈ U) (hv : v ∈ U)
    (hue : u ∈ e.val) (hve : v ∈ e.val) : u = v := by
  by_contra huv
  have heq : e.val = s(u,v) := (Sym2.mem_and_mem_iff huv).mp ⟨hue,hve⟩
  have hadj : G.Adj u v := by simpa only [heq, SimpleGraph.mem_edgeSet] using e.property
  exact hU hu hv huv hadj

theorem spoke_unique_row (p q : V) (U : Finset V) (hU : G.IsIndepSet U)
    (e : ↥(spokeEdges G p q U)) : ∃! u, u ∈ U ∧ u ∈ e.val := by
  obtain ⟨u, hu, hue⟩ := ((mem_spokeEdges G p q U e.val).mp e.property).2.2.2
  refine ⟨u, ⟨hu,hue⟩, ?_⟩
  intro v hv
  exact row_endpoint_unique G U hU (spokeToEdge G p q U e) hv.1 hu hv.2 hue

/-- A spoke can be oriented from a row to one of that row's actual centers. -/
theorem spoke_row_center (p q : V) (U : Finset V) (e : Sym2 V)
    (he : e ∈ spokeEdges G p q U) :
    ∃ u ∈ U, ∃ x ∈ rowCenters G p q u, e = s(u,x) := by
  have hs := (mem_spokeEdges G p q U e).mp he
  obtain ⟨u, hu, hue⟩ := hs.2.2.2
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hue
  refine ⟨u, hu, x, (mem_rowCenters G p q u x).mpr ⟨?_, ?_, ?_⟩, hx⟩
  · simpa only [hx, SimpleGraph.mem_edgeSet] using hs.1
  · intro hxp
    apply hs.2.1
    rw [hx, ← hxp]
    exact Sym2.mem_mk_right _ _
  · intro hxq
    apply hs.2.2.1
    rw [hx, ← hxq]
    exact Sym2.mem_mk_right _ _

theorem row_center_is_spoke (p q : V) (U : Finset V)
    (hpU : p ∉ U) (hqU : q ∉ U) {u x : V} (hu : u ∈ U)
    (hx : x ∈ rowCenters G p q u) : s(u,x) ∈ spokeEdges G p q U := by
  have hc := (mem_rowCenters G p q u x).mp hx
  have hpu : p ≠ u := by intro h; subst u; exact hpU hu
  have hqu : q ≠ u := by intro h; subst u; exact hqU hu
  apply (mem_spokeEdges G p q U _).mpr
  exact ⟨hc.1, by simpa using And.intro hpu hc.2.1.symm,
    by simpa using And.intro hqu hc.2.2.symm, u, hu, Sym2.mem_mk_left _ _⟩

/-- The actual spoke edges from one row, without duplicating shared centers. -/
def rowSpokeEdges (p q u : V) : Finset (Sym2 V) :=
  (rowCenters G p q u).map (Sym2.mkEmbedding u)

theorem spokeEdges_eq_biUnion (p q : V) (U : Finset V)
    (hpU : p ∉ U) (hqU : q ∉ U) :
    spokeEdges G p q U = U.biUnion (rowSpokeEdges G p q) := by
  ext e
  constructor
  · intro he
    obtain ⟨u, hu, x, hx, rfl⟩ := spoke_row_center G p q U e he
    exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_map.mpr ⟨x,hx,rfl⟩⟩
  · intro he
    obtain ⟨u, hu, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp he
    exact row_center_is_spoke G p q U hpU hqU hu hx

theorem rowSpokeEdges_pairwiseDisjoint (p q : V) (U : Finset V)
    (hU : G.IsIndepSet U) : (U : Set V).PairwiseDisjoint (rowSpokeEdges G p q) := by
  intro u hu v hv huv
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨x,hx,hxe⟩ := Finset.mem_map.mp he
  obtain ⟨y,hy,hye⟩ := Finset.mem_map.mp hf
  change s(u,x) = e at hxe
  change s(v,y) = e at hye
  have hux := ((mem_rowCenters G p q u x).mp hx).1
  let edge : G.edgeSet := ⟨e, by rw [← hxe]; exact hux⟩
  have hue : u ∈ edge.val := by change u ∈ e; rw [← hxe]; exact Sym2.mem_mk_left _ _
  have hve : v ∈ edge.val := by change v ∈ e; rw [← hye]; exact Sym2.mem_mk_left _ _
  exact huv (row_endpoint_unique G U hU edge hu hv hue hve)

/-- Distinct spokes sharing a row are adjacent in the original-host conflict graph. -/
theorem spokeGraph_adj_of_common_endpoint (p q : V) (U : Finset V)
    (e f : ↥(spokeEdges G p q U)) (hne : e ≠ f)
    (u : V) (hue : u ∈ e.val) (huf : u ∈ f.val) :
    (spokeGraph G p q U).Adj e f := by
  rw [spokeGraph_adj_iff, conflict_iff_endpoints]
  exact ⟨fun h => hne (spokeToEdge_injective G p q U h),
    u, hue, u, huf, Or.inl rfl⟩

/-- The initial eight-spoke upper bound needs no fixed-edge or row-independence assumption.
Possible row-row edges may be counted twice in the row union, which only helps. -/
theorem spokeEdges_card_le_eight (p q : V) (U : Finset V) (hUcard : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U) :
    (spokeEdges G p q U).card ≤ 8 := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p ((hp p).mpr h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q ((hq q).mpr h)
  rw [spokeEdges_eq_biUnion G p q U hpU hqU]
  calc
    (U.biUnion (rowSpokeEdges G p q)).card ≤ ∑ u ∈ U, (rowSpokeEdges G p q u).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, 2 := by
      apply Finset.sum_le_sum
      intro u hu
      simpa [rowSpokeEdges] using rowCenters_card_le_two G p q U u hpq hdegree hp hq hu
    _ = 8 := by simp [hUcard]

/-- The upper bound is attained after the five-fixed-edge geometry excludes row-row edges. -/
theorem spokeEdges_card_eq_eight (p q : V) (U : Finset V) (hUcard : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    (spokeEdges G p q U).card = 8 := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p ((hp p).mpr h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q ((hq q).mpr h)
  have hi := rows_independent_of_five G p q U hpq hdegree hp hq hfive
  rw [spokeEdges_eq_biUnion G p q U hpU hqU,
    Finset.card_biUnion (rowSpokeEdges_pairwiseDisjoint G p q U hi)]
  calc
    ∑ u ∈ U, (rowSpokeEdges G p q u).card = ∑ _u ∈ U, 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      simpa [rowSpokeEdges] using
        rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu (hfive u hu)
    _ = 8 := by simp [hUcard]

/-- Every actual spoke has a distinct same-row mate; no center distinctness is assumed. -/
theorem spokeGraph_no_isolated (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    ∀ e : ↥(spokeEdges G p q U), ∃ f, (spokeGraph G p q U).Adj e f := by
  intro e
  have hpU : p ∉ U := fun h => G.loopless.irrefl p ((hp p).mpr h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q ((hq q).mpr h)
  obtain ⟨u, hu, x, hx, he⟩ := spoke_row_center G p q U e.val e.property
  have hc := rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu (hfive u hu)
  have hpos : 0 < ((rowCenters G p q u).erase x).card := by
    rw [Finset.card_erase_of_mem hx, hc]
    decide
  obtain ⟨y,hy⟩ := Finset.card_pos.mp hpos
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyc : y ∈ rowCenters G p q u := Finset.mem_of_mem_erase hy
  let f : ↥(spokeEdges G p q U) := ⟨s(u,y), row_center_is_spoke G p q U hpU hqU hu hyc⟩
  have hne : e ≠ f := by
    intro hef
    have hs : s(u,x) = s(u,y) := by simpa only [he] using congrArg Subtype.val hef
    exact hyx ((Sym2.mkEmbedding u).injective hs).symm
  refine ⟨f, spokeGraph_adj_of_common_endpoint G p q U e f hne u ?_ (Sym2.mem_mk_left _ _)⟩
  rw [he]
  exact Sym2.mem_mk_left _ _

open scoped Classical in
theorem spokeGraph_degree_pos (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    ∀ e, 0 < (spokeGraph G p q U).degree e := by
  intro e
  exact ((spokeGraph G p q U).degree_pos_iff_exists_adj e).mpr
    (spokeGraph_no_isolated G p q U hpq hdegree hp hq hfive e)

/-- Exact relabeling of the eight actual spoke edges. -/
noncomputable def spokeEquivFin8 (p q : V) (U : Finset V)
    (hcard : (spokeEdges G p q U).card = 8) : ↥(spokeEdges G p q U) ≃ Fin 8 :=
  Finset.equivFinOfCardEq hcard

noncomputable def spokeGraph8 (p q : V) (U : Finset V)
    (hcard : (spokeEdges G p q U).card = 8) : SimpleGraph (Fin 8) :=
  (spokeGraph G p q U).comap (spokeEquivFin8 G p q U hcard).symm

noncomputable def spokeGraph8Iso (p q : V) (U : Finset V)
    (hcard : (spokeEdges G p q U).card = 8) :
    spokeGraph8 G p q U hcard ≃g spokeGraph G p q U :=
  SimpleGraph.Iso.comap (spokeEquivFin8 G p q U hcard).symm (spokeGraph G p q U)

theorem spokeGraph8_adj_iff (p q : V) (U : Finset V)
    (hcard : (spokeEdges G p q U).card = 8) (i j : Fin 8) :
    (spokeGraph8 G p q U hcard).Adj i j ↔
      (strongConflict G).Adj
        (spokeToEdge G p q U ((spokeEquivFin8 G p q U hcard).symm i))
        (spokeToEdge G p q U ((spokeEquivFin8 G p q U hcard).symm j)) := Iff.rfl

open scoped Classical in
theorem spokeGraph8_degree_pos (p q : V) (U : Finset V)
    (hcard : (spokeEdges G p q U).card = 8)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    ∀ i, 0 < (spokeGraph8 G p q U hcard).degree i := by
  intro i
  apply ((spokeGraph8 G p q U hcard).degree_pos_iff_exists_adj i).mpr
  let e := (spokeEquivFin8 G p q U hcard).symm i
  obtain ⟨f,hf⟩ := spokeGraph_no_isolated G p q U hpq hdegree hp hq hfive e
  refine ⟨spokeEquivFin8 G p q U hcard f, ?_⟩
  change (spokeGraph G p q U).Adj e
    ((spokeEquivFin8 G p q U hcard).symm ((spokeEquivFin8 G p q U hcard) f))
  simpa using hf


end TwinReduction
end Part5

section Part6
-- Source module: TwinAvailable

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Endpoint form of the canonical conflict relation, for finite edge-set counting. -/
def endpointConflict (e f : Sym2 V) : Prop :=
  e ≠ f ∧ ∃ x ∈ e, ∃ y ∈ f, x = y ∨ G.Adj x y

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem endpointConflict_iff (e f : G.edgeSet) :
    endpointConflict G e.val f.val ↔ (strongConflict G).Adj e f := by
  rw [conflict_iff_endpoints]
  simp only [endpointConflict, ne_eq, Subtype.ext_iff]

open scoped Classical in
noncomputable def fixedConflictColors (p q : V) (U : Finset V)
    (e : G.edgeSet) (c : Sym2 V → Fin 20) : Finset (Fin 20) :=
  ((fixedEdges G p q U).filter (endpointConflict G e.val)).image c

noncomputable def availableColors (p q : V) (U : Finset V)
    (e : G.edgeSet) (c : Sym2 V → Fin 20) : Finset (Fin 20) :=
  univ \ fixedConflictColors G p q U e c

/-- These lists exclude exactly all conflicts with fixed edges in the full host. -/
theorem mem_availableColors (p q : V) (U : Finset V) (e : G.edgeSet)
    (c : Sym2 V → Fin 20) (a : Fin 20) :
    a ∈ availableColors G p q U e c ↔
      ∀ f : G.edgeSet, f.val ∈ fixedEdges G p q U →
        (strongConflict G).Adj e f → c f.val ≠ a := by
  classical
  simp only [availableColors, mem_sdiff, mem_univ, true_and]
  constructor
  · intro ha f hf hef hcolor
    apply ha
    exact mem_image.mpr ⟨f.val, mem_filter.mpr ⟨hf,
      (endpointConflict_iff G e f).mpr hef⟩, hcolor⟩
  · intro ha hbad
    obtain ⟨f, hf, hcolor⟩ := mem_image.mp hbad
    have hfixed := (mem_filter.mp hf).1
    let f' : G.edgeSet := ⟨f, ((mem_fixedEdges G p q U f).mp hfixed).1⟩
    exact ha f' hfixed ((endpointConflict_iff G e f').mp (mem_filter.mp hf).2) hcolor

/-- Every fixed exclusion at a row also excludes its color from each spoke in that row. -/
theorem row_colors_subset_fixed_conflicts (p q : V) (U : Finset V)
    (u : V) (hu : u ∈ U) (e : G.edgeSet) (hue : u ∈ e.val)
    (c : Sym2 V → Fin 20) :
    (rowSeen G p q U u).image c ⊆ fixedConflictColors G p q U e c := by
  classical
  intro a ha
  obtain ⟨f, hf, rfl⟩ := mem_image.mp ha
  have hseen := (mem_rowSeen G p q U u f).mp hf
  have hfixed := (mem_fixedEdges G p q U f).mp hseen.1
  obtain ⟨x, hxf, hux⟩ := hseen.2
  apply mem_image.mpr
  refine ⟨f, mem_filter.mpr ⟨hseen.1, ?_⟩, rfl⟩
  refine ⟨?_, u, hue, x, hxf, Or.inr hux⟩
  intro hef
  exact hfixed.2.2.2 u (hef ▸ hue) hu

/-- Common fixed row colors are already unavailable at every spoke. -/
theorem availableColors_subset_complement_common (p q : V) (U : Finset V)
    (u : V) (hu : u ∈ U) (e : G.edgeSet) (hue : u ∈ e.val)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hT : T ⊆ (rowSeen G p q U u).image c) :
    availableColors G p q U e c ⊆ univ \ T := by
  intro a ha
  have hnot := (mem_sdiff.mp ha).2
  exact mem_sdiff.mpr ⟨mem_univ _, fun haT =>
    hnot (row_colors_subset_fixed_conflicts G p q U u hu e hue c (hT haT))⟩


end TwinReduction
end Part6

section Part7
-- Source module: TwinInitial

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Restrict the retained coloring to the actual spokes, with conflicts still measured in G.
This initial coloring requires no fixed-edge-count or row-independence hypothesis. -/
def originalSpokeColoring (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c) :
    (spokeGraph G p q U).Coloring (Fin 20) :=
  Coloring.mk (fun e => c e.val) (by
    intro e f hef
    have he := (mem_spokeEdges G p q U e.val).mp e.property
    have hf := (mem_spokeEdges G p q U f.val).mp f.property
    exact hc (spokeToEdge G p q U e) (spokeToEdge G p q U f)
      he.2.1 he.2.2.1 hf.2.1 hf.2.2.1
      ((spokeGraph_adj_iff G p q U e f).mp hef))

@[simp] theorem originalSpokeColoring_apply (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (e : ↥(spokeEdges G p q U)) :
    originalSpokeColoring G p q U c hc e = c e.val := rfl

/-- The restriction is proper on the canonical original-host spoke conflict graph. -/
theorem originalSpokeColoring_valid (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    {e f : ↥(spokeEdges G p q U)} (hef : (spokeGraph G p q U).Adj e f) :
    originalSpokeColoring G p q U c hc e ≠ originalSpokeColoring G p q U c hc f :=
  (originalSpokeColoring G p q U c hc).valid hef

/-- Every original spoke color is compatible with all fixed colored edges. -/
theorem originalSpokeColoring_mem_available (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (e : ↥(spokeEdges G p q U)) :
    originalSpokeColoring G p q U c hc e ∈
      availableColors G p q U (spokeToEdge G p q U e) c := by
  apply (mem_availableColors G p q U (spokeToEdge G p q U e) c _).mpr
  intro f hf hef
  have he := (mem_spokeEdges G p q U e.val).mp e.property
  have hf' := (mem_fixedEdges G p q U f.val).mp hf
  change c f.val ≠ c e.val
  exact (hc (spokeToEdge G p q U e) f he.2.1 he.2.2.1 hf'.2.1 hf'.2.2.1 hef).symm

/-- The coloring's image is exactly the set of original colors on the finite spoke set. -/
theorem originalSpokeColoring_image (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c) :
    Finset.univ.image (originalSpokeColoring G p q U c hc) =
      (spokeEdges G p q U).image c := by
  ext a
  constructor
  · intro ha
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨e.val, e.property, he⟩
  · intro ha
    obtain ⟨e, he, hcolor⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, hcolor⟩

/-- Initially at most eight spoke colors are used; this uses the unconditional spoke bound. -/
theorem originalSpokeColoring_used_card_le_eight (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (hUcard : U.card = 4) (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U) :
    (Finset.univ.image (originalSpokeColoring G p q U c hc)).card ≤ 8 := by
  rw [originalSpokeColoring_image]
  exact Finset.card_image_le.trans
    (spokeEdges_card_le_eight G p q U hUcard hpq hdegree hp hq)

/-- Every common fixed row color is absent from the initial spoke-color image. -/
theorem originalSpokeColoring_image_disjoint_common (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20))
    (hT : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    Disjoint (Finset.univ.image (originalSpokeColoring G p q U c hc)) T := by
  rw [originalSpokeColoring_image]
  exact spoke_colors_disjoint_common G p q U c hc T hT


end TwinReduction
end Part7

section Part8
-- Source module: TwinHall

namespace TwinReduction

open Finset

/-- Four row lists, each repeated twice, need only the total Hall inequality
when every row list has at least six colors. -/
theorem repeated_row_hall {C : Type*} [DecidableEq C]
    (L : Fin 4 → Finset C) (hL : ∀ i, 6 ≤ (L i).card) :
    (∃ f : Fin 4 × Fin 2 → C, Function.Injective f ∧ ∀ v, f v ∈ L v.1) ↔
      8 ≤ ((univ : Finset (Fin 4)).biUnion L).card := by
  constructor
  · rintro ⟨f, hf, hmem⟩
    have hsub : (univ.image f) ⊆ (univ : Finset (Fin 4)).biUnion L := by
      intro c hc
      obtain ⟨v, _, rfl⟩ := mem_image.mp hc
      exact mem_biUnion.mpr ⟨v.1, mem_univ _, hmem v⟩
    have hc := card_le_card hsub
    simpa [card_image_of_injective _ hf] using hc
  · intro htotal
    apply (all_card_le_biUnion_card_iff_existsInjective' (fun v : Fin 4 × Fin 2 => L v.1)).mp
    intro S
    by_cases hsmall : S.card ≤ 6
    · by_cases hempty : S = ∅
      · simp [hempty]
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      exact hsmall.trans ((hL v.1).trans (card_le_card (subset_biUnion_of_mem (fun v => L v.1) hv)))
    · have hrows : ∀ i : Fin 4, ∃ v ∈ S, v.1 = i := by
        intro i
        by_contra! hn
        have hsub : S ⊆ (univ.erase i).product (univ : Finset (Fin 2)) := by
          intro v hv
          exact mem_product.mpr ⟨mem_erase.mpr ⟨hn v hv, mem_univ _⟩, mem_univ _⟩
        have hc : S.card ≤ 6 := by simpa using card_le_card hsub
        omega
      have hsub : (univ : Finset (Fin 4)).biUnion L ⊆ S.biUnion (fun v => L v.1) := by
        intro c hc
        obtain ⟨i, _, hci⟩ := mem_biUnion.mp hc
        obtain ⟨v, hv, rfl⟩ := hrows i
        exact mem_biUnion.mpr ⟨v, hv, hci⟩
      have hScard : S.card ≤ 8 := by simpa using card_le_univ S
      exact hScard.trans (htotal.trans (card_le_card hsub))

/-- These are exactly the possible palette counts when the total Hall test fails. -/
theorem hall_deficit_counts (C T : Finset (Fin 20))
    (hC : C.card ≤ 8) (hT : T.card ≤ 6) (hdis : Disjoint C T)
    (hdef : (univ \ (C ∪ T)).card < 8) :
    (C.card = 8 ∧ T.card = 6) ∨ (C.card = 7 ∧ T.card = 6) ∨
      (C.card = 8 ∧ T.card = 5) := by
  rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hdis] at hdef
  simp only [card_univ, Fintype.card_fin] at hdef
  omega

/-- Eight uncolored cell neighbors leave degree plus four available colors
at a spoke whose full conflict degree is at most twenty-four. -/
theorem fixed_palette_slack {E : Type*} [DecidableEq E]
    (N B M : Finset E) (c : E → Fin 20)
    (hN : N.card ≤ 24) (hB : B.card = 8) (hBN : B ⊆ N) (hBM : Disjoint B M) :
    (N ∩ M).card + 4 ≤ (univ \ ((N \ (B ∪ M)).image c)).card := by
  have hdis1 : Disjoint B (N ∩ M) := hBM.mono_right inter_subset_right
  have hdis2 : Disjoint (B ∪ (N ∩ M)) (N \ (B ∪ M)) := by
    rw [disjoint_left]
    intro e he hf
    have hnot := (mem_sdiff.mp hf).2
    rcases mem_union.mp he with hb | hm
    · exact hnot (mem_union_left _ hb)
    · exact hnot (mem_union_right _ (mem_inter.mp hm).2)
  have hcover : B ∪ (N ∩ M) ∪ (N \ (B ∪ M)) = N := by
    ext e
    constructor
    · intro he
      rcases mem_union.mp he with he | he
      · rcases mem_union.mp he with hb | hm
        · exact hBN hb
        · exact (mem_inter.mp hm).1
      · exact (mem_sdiff.mp he).1
    · intro he
      by_cases hb : e ∈ B
      · exact mem_union_left _ (mem_union_left _ hb)
      by_cases hm : e ∈ M
      · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨he, hm⟩))
      · exact mem_union_right _ (mem_sdiff.mpr ⟨he, by simp [hb, hm]⟩)
  have hcount := congrArg Finset.card hcover
  rw [card_union_of_disjoint hdis2, card_union_of_disjoint hdis1, hB] at hcount
  have himage := card_image_le (s := N \ (B ∪ M)) (f := c)
  rw [card_sdiff_of_subset (subset_univ _)]
  simp only [card_univ, Fintype.card_fin]
  omega

/-- The union of available row colors is the complement of the spoke colors
and the common fixed colors. -/
theorem available_union (Q T : Finset (Fin 20)) (F : Fin 4 → Finset (Fin 20))
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i) :
    (univ : Finset (Fin 4)).biUnion (fun i => univ \ (Q ∪ F i)) =
      univ \ (Q ∪ T) := by
  ext c
  simp only [mem_biUnion, mem_sdiff, mem_univ, true_and, mem_union, not_or, hT, not_forall]
  exact exists_and_left


end TwinReduction
end Part8

section Part9
-- Source module: TwinInitialHall

namespace TwinReduction

open Finset

/-- At most four common fixed colors leave a system of distinct representatives
without recoloring any of the at most eight surrounding spokes. -/
theorem small_common_cell_assignment (C T : Finset (Fin 20))
    (F : Fin 4 → Finset (Fin 20)) (hC : C.card ≤ 8) (hT : T.card ≤ 4)
    (hF : ∀ i, (F i).card ≤ 6) (hcommon : ∀ a, a ∈ T ↔ ∀ i, a ∈ F i) :
    ∃ f : Fin 4 × Fin 2 → Fin 20, Function.Injective f ∧
      ∀ v, f v ∉ C ∧ f v ∉ F v.1 := by
  let L : Fin 4 → Finset (Fin 20) := fun i => univ \ (C ∪ F i)
  have hL : ∀ i, 6 ≤ (L i).card := by
    intro i
    have h := card_union_le C (F i)
    have hi := hF i
    dsimp [L]
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  have htotal : 8 ≤ ((univ : Finset (Fin 4)).biUnion L).card := by
    rw [available_union C T F hcommon, card_sdiff_of_subset (subset_univ _)]
    have h := card_union_le C T
    simp only [card_univ, Fintype.card_fin]
    omega
  obtain ⟨f, hf, hmem⟩ := (repeated_row_hall L hL).mpr htotal
  refine ⟨f, hf, ?_⟩
  intro v
  have hnot := (mem_sdiff.mp (hmem v)).2
  exact ⟨fun h => hnot (mem_union_left _ h), fun h => hnot (mem_union_right _ h)⟩


end TwinReduction
end Part9

section Part10
-- Source module: TwinSixDegree

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the six-fixed-edge case every center is outside the rows and belongs to one row. -/
theorem allCenters_six_geometry (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card)
    {x : V} (hx : x ∈ U.biUnion (rowCenters G p q)) :
    x ∉ U ∧ rowMultiplicity G U x = 1 := by
  obtain ⟨u,hu,hxu⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨a,b,_,hab,haU,hbU,hma,hmb,_,_,_⟩ :=
    row_six_geometry G p q U u hpq hdegree hp hq hu (hsix u hu)
  have hxpair : x = a ∨ x = b := by simpa [hab] using hxu
  rcases hxpair with rfl | rfl
  · exact ⟨haU,hma⟩
  · exact ⟨hbU,hmb⟩

/-- Multiplicity one identifies any two rows adjacent to the same center. -/
lemma row_unique_of_multiplicity_one (U : Finset V) (x : V)
    (hm : rowMultiplicity G U x = 1) {u v : V}
    (hu : u ∈ U) (hv : v ∈ U) (hux : G.Adj u x) (hvx : G.Adj v x) : u = v := by
  have hcard : (G.neighborFinset x ∩ U).card ≤ 1 := by
    simpa [rowMultiplicity] using hm.le
  exact Finset.card_le_one.mp hcard u
    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x u).mpr hux.symm,hu⟩) v
    (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x v).mpr hvx.symm,hv⟩)

/-- With independent rows and multiplicity-one centers, distinct-row conflicts
between spokes can only come from an actual edge between their centers. -/
private theorem conflict_rows_or_centers (p q : V) (U : Finset V)
    (hU : G.IsIndepSet U) (e f : ↥(spokeEdges G p q U))
    (u x v y : V) (hu : u ∈ U) (hv : v ∈ U) (hxU : x ∉ U) (hyU : y ∉ U)
    (hmx : rowMultiplicity G U x = 1) (hmy : rowMultiplicity G U y = 1)
    (hux : G.Adj u x) (hvy : G.Adj v y) (he : e.val = s(u,x)) (hf : f.val = s(v,y))
    (hconf : (spokeGraph G p q U).Adj e f) : u = v ∨ G.Adj x y := by
  by_cases huv : u = v
  · exact Or.inl huv
  right
  have hc := (conflict_iff_endpoints G (spokeToEdge G p q U e) (spokeToEdge G p q U f)).mp hconf
  obtain ⟨_,a,ha,b,hb,hab⟩ := hc
  change a ∈ e.val at ha
  change b ∈ f.val at hb
  rw [he] at ha
  rw [hf] at hb
  rcases Sym2.mem_iff.mp ha with ha | ha <;> subst a <;>
    rcases Sym2.mem_iff.mp hb with hb | hb <;> subst b
  · rcases hab with huv' | huv'
    · exact (huv huv').elim
    · exact (hU hu hv huv huv').elim
  · rcases hab with huy | huy
    · exact (hyU (huy ▸ hu)).elim
    · exact (huv (row_unique_of_multiplicity_one G U y hmy hu hv huy hvy)).elim
  · rcases hab with hxv | hxv
    · exact (hxU (hxv.symm ▸ hv)).elim
    · exact (huv (row_unique_of_multiplicity_one G U x hmx hu hv hux hxv.symm)).elim
  · rcases hab with hxy | hxy
    · exact (huv (row_unique_of_multiplicity_one G U x hmx hu hv hux
        (by rw [hxy]; exact hvy))).elim
    · exact hxy

open scoped Classical in
/-- At most one same-row mate, plus one spoke per neighboring center, can conflict. -/
theorem spoke_degree_le_one_add_center_neighbors (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card)
    (e : ↥(spokeEdges G p q U)) (u x : V)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) (he : e.val = s(u,x)) :
    (spokeGraph G p q U).degree e ≤
      1 + (G.neighborFinset x ∩ U.biUnion (rowCenters G p q)).card := by
  classical
  let X := U.biUnion (rowCenters G p q)
  have hgeom : ∀ z ∈ X, z ∉ U ∧ rowMultiplicity G U z = 1 :=
    fun z hz => allCenters_six_geometry G p q U hpq hdegree hp hq hsix hz
  have hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card := by
    intro v hv
    have := hsix v hv
    omega
  have hi := rows_independent_of_five G p q U hpq hdegree hp hq hfive
  have hrepr : ∀ f : ↥(spokeEdges G p q U),
      ∃ y v, v ∈ U ∧ y ∈ rowCenters G p q v ∧ f.val = s(v,y) := by
    intro f
    obtain ⟨v,hv,y,hy,hf⟩ := spoke_row_center G p q U f.val f.property
    exact ⟨y,v,hv,hy,hf⟩
  choose center row hrow hcenter hrepr using hrepr
  have hcenterX : ∀ f, center f ∈ X := fun f => Finset.mem_biUnion.mpr
    ⟨row f,hrow f,hcenter f⟩
  have hcenterAdj : ∀ f, G.Adj (row f) (center f) := fun f =>
    ((mem_rowCenters G p q (row f) (center f)).mp (hcenter f)).1
  have hinj : Function.Injective center := by
    intro f g hfg
    have hrows : row f = row g := row_unique_of_multiplicity_one G U (center f)
      (hgeom _ (hcenterX f)).2 (hrow f) (hrow g) (hcenterAdj f)
      (by rw [hfg]; exact hcenterAdj g)
    apply Subtype.ext
    rw [hrepr f, hrepr g, hrows, hfg]
  have hxX : x ∈ X := Finset.mem_biUnion.mpr ⟨u,hu,hx⟩
  have hsub : ((spokeGraph G p q U).neighborFinset e).image center ⊆
      (rowCenters G p q u).erase x ∪ (G.neighborFinset x ∩ X) := by
    intro z hz
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hz
    have hconf := ((spokeGraph G p q U).mem_neighborFinset e f).mp hf
    have hclass := conflict_rows_or_centers G p q U hi e f u x (row f) (center f)
      hu (hrow f) (hgeom _ hxX).1 (hgeom _ (hcenterX f)).1
      (hgeom _ hxX).2 (hgeom _ (hcenterX f)).2
      ((mem_rowCenters G p q u x).mp hx).1 (hcenterAdj f) he (hrepr f) hconf
    rcases hclass with hr | hadj
    · apply Finset.mem_union_left
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro hcx
        have hef : e = f := Subtype.ext (by rw [he,hrepr f,← hr,hcx])
        exact hconf.ne hef
      · rw [hr]
        exact hcenter f
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x (center f)).mpr hadj,hcenterX f⟩)
  have hbound := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj,
    (spokeGraph G p q U).card_neighborFinset_eq_degree] at hbound
  have hrowCard := rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu (hfive u hu)
  have hmate : ((rowCenters G p q u).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hx,hrowCard]
  have hsum := Finset.card_union_le ((rowCenters G p q u).erase x) (G.neighborFinset x ∩ X)
  change (spokeGraph G p q U).degree e ≤ 1 + (G.neighborFinset x ∩ X).card
  omega

open scoped Classical in
/-- The six-case degree estimate needed by the list bound. All neighbors and conflicts
are counted in the actual full host, and b counts neighbors outside rows and centers. -/
theorem spoke_degree_add_exterior_le_four (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card)
    (e : ↥(spokeEdges G p q U)) (u x : V)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) (he : e.val = s(u,x)) :
    (spokeGraph G p q U).degree e +
      (G.neighborFinset x \ (U.biUnion (rowCenters G p q) ∪ U)).card ≤ 4 := by
  classical
  let X := U.biUnion (rowCenters G p q)
  let C := G.neighborFinset x ∩ X
  let B := G.neighborFinset x \ (X ∪ U)
  have hdeg := spoke_degree_le_one_add_center_neighbors G p q U hpq hdegree hp hq hsix e u x hu hx he
  have huN : u ∈ G.neighborFinset x := (G.mem_neighborFinset x u).mpr
    ((mem_rowCenters G p q u x).mp hx).1.symm
  have huC : u ∉ C := by
    intro h
    have huX := (Finset.mem_inter.mp h).2
    exact (allCenters_six_geometry G p q U hpq hdegree hp hq hsix huX).1 hu
  have hdis : Disjoint (insert u C) B := by
    apply Finset.disjoint_left.mpr
    intro z hz hzB
    have hn := (Finset.mem_sdiff.mp hzB).2
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hn (Finset.mem_union_right _ hu)
    · exact hn (Finset.mem_union_left _ (Finset.mem_inter.mp hz).2)
  have hsub : insert u C ∪ B ⊆ G.neighborFinset x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_insert.mp hz with rfl | hz
      · exact huN
      · exact (Finset.mem_inter.mp hz).1
    · exact (Finset.mem_sdiff.mp hz).1
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_insert_of_notMem huC,
    G.card_neighborFinset_eq_degree] at hcount
  have hg := (G.degree_le_maxDegree x).trans hdegree
  change (spokeGraph G p q U).degree e ≤ 1 + C.card at hdeg
  change (spokeGraph G p q U).degree e + B.card ≤ 4
  omega


end TwinReduction
end Part10

section Part11
-- Source module: TwinSixAvailable

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edges beyond selected neighbors, excluding the connecting edge itself. -/
def beyondEdges (x : V) (Z : Finset V) : Finset (Sym2 V) :=
  Z.biUnion (fun z => (G.incidenceFinset z).erase s(x,z))

theorem beyondEdges_card_le (x : V) (Z : Finset V) (hdegree : G.maxDegree ≤ 4)
    (hZ : Z ⊆ G.neighborFinset x) : (beyondEdges G x Z).card ≤ 3 * Z.card := by
  calc
    (beyondEdges G x Z).card ≤ ∑ z ∈ Z, ((G.incidenceFinset z).erase s(x,z)).card :=
      card_biUnion_le
    _ ≤ ∑ _z ∈ Z, 3 := by
      apply sum_le_sum
      intro z hz
      have hxz := (G.mem_neighborFinset x z).mp (hZ hz)
      have hmem : s(x,z) ∈ G.incidenceFinset z := by
        simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hxz]
      rw [card_erase_of_mem hmem, G.card_incidenceFinset_eq_degree]
      have hd := (G.degree_le_maxDegree z).trans hdegree
      omega
    _ = _ := by simp [Nat.mul_comm]

/-- Once all fixed colors at centers are in T, only edges beyond noncenters
can forbid additional colors at a spoke. -/
theorem fixed_colors_covered_by_beyond (p q : V) (U X : Finset V)
    (u x : V) (hu : u ∈ U) (hux : G.Adj u x) (hx : x ∈ X)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hrow : (rowSeen G p q U u).image c ⊆ T)
    (hX : ∀ z ∈ X, (fixedAt G p q U z).image c ⊆ T) :
    fixedConflictColors G p q U ⟨s(u,x), hux⟩ c ⊆
      T ∪ (beyondEdges G x (G.neighborFinset x \ (X ∪ U))).image c := by
  classical
  intro a ha
  obtain ⟨f, hf, rfl⟩ := mem_image.mp ha
  have hfix := (mem_filter.mp hf).1
  have hfixed := (mem_fixedEdges G p q U f).mp hfix
  by_cases hcT : c f ∈ T
  · exact mem_union_left _ hcT
  have hxnot : x ∉ f := by
    intro hxf
    exact hcT (hX x hx (mem_image.mpr ⟨f, mem_filter.mpr ⟨hfix, hxf⟩, rfl⟩))
  have hfar : ∃ z ∈ f, G.Adj x z ∧ z ∉ X ∧ z ∉ U := by
    obtain ⟨_, v, hv, z, hz, hvz⟩ := (mem_filter.mp hf).2
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · rcases hvz with rfl | huz
      · exact (hfixed.2.2.2 _ hz hu).elim
      · apply hcT.elim
        apply hrow
        exact mem_image.mpr ⟨f, (mem_rowSeen G p q U _ f).mpr
          ⟨hfix, z, hz, huz⟩, rfl⟩
    · rcases hvz with rfl | hxz
      · exact (hxnot hz).elim
      · refine ⟨z, hz, hxz, ?_, hfixed.2.2.2 z hz⟩
        intro hzX
        exact hcT (hX z hzX (mem_image.mpr ⟨f, mem_filter.mpr ⟨hfix, hz⟩, rfl⟩))
  obtain ⟨z, hzf, hxz, hzX, hzU⟩ := hfar
  apply mem_union_right
  apply mem_image.mpr
  refine ⟨f, ?_, rfl⟩
  apply mem_biUnion.mpr
  refine ⟨z, mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz, by simp [hzX, hzU]⟩,
    mem_erase.mpr ⟨?_, ?_⟩⟩
  · intro h
    apply hxnot
    rw [h]
    exact Sym2.mem_mk_left _ _
  · simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet] using
      And.intro hfixed.1 hzf

/-- The actual spoke list has at least fourteen minus three per exterior neighbor. -/
theorem six_available_card_lower (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ v ∈ U, T ⊆ (rowSeen G p q U v).image c) :
    (availableColors G p q U ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ c).card +
      3 * (G.neighborFinset x \ (U.biUnion (rowCenters G p q) ∪ U)).card ≥ 14 := by
  classical
  let X := U.biUnion (rowCenters G p q)
  let Z := G.neighborFinset x \ (X ∪ U)
  have hxX : x ∈ X := mem_biUnion.mpr ⟨u, hu, hx⟩
  have hrow : (rowSeen G p q U u).image c ⊆ T := by
    rw [row_colors_eq_common_of_six G p q U u hpq hdegree hp hq hu c T hT (hcommon u hu)]
  have hX : ∀ z ∈ X, (fixedAt G p q U z).image c ⊆ T := by
    intro z hz
    obtain ⟨v, hv, hz⟩ := mem_biUnion.mp hz
    exact center_fixed_colors_common_of_six G p q U v z hpq hdegree hp hq hv hz c T hT
      (hcommon v hv)
  have hcover := fixed_colors_covered_by_beyond G p q U X u x hu
    ((mem_rowCenters G p q u x).mp hx).1 hxX c T hrow hX
  have hcard := card_le_card hcover
  have hU := card_union_le T ((beyondEdges G x Z).image c)
  have himage := card_image_le (s := beyondEdges G x Z) (f := c)
  have hbeyond := beyondEdges_card_le G x Z hdegree sdiff_subset
  rw [hT] at hU
  change (availableColors G p q U _ c).card + 3 * Z.card ≥ 14
  rw [availableColors, card_sdiff_of_subset (subset_univ _)]
  simp only [card_univ, Fintype.card_fin]
  change (fixedConflictColors G p q U _ c).card ≤ (T ∪ (beyondEdges G x Z).image c).card at hcard
  omega


end TwinReduction
end Part11

section Part12
-- Source module: Palette

namespace Palette

open SimpleGraph Finset
open scoped BigOperators

lemma clique_card_le_degree_add_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s : Finset V} (hs : G.IsClique s) {v : V} (hv : v ∈ s) :
    s.card ≤ G.degree v + 1 := by
  classical
  have hsub : s.erase v ⊆ G.neighborFinset v := by
    intro w hw
    have hw' := Finset.mem_erase.mp hw
    exact (G.mem_neighborFinset v w).mpr (hs hv hw'.2 hw'.1.symm)
  have hcard := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree, Finset.card_erase_of_mem hv] at hcard
  have := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- Integer-scaled reciprocal-degree clique bound, with arbitrary scale. -/
theorem clique_weight_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s : Finset V} (hs : G.IsClique s) (M : ℕ) :
    ∑ v ∈ s, M / (G.degree v + 1) ≤ M := by
  classical
  by_cases hempty : s = ∅
  · simp [hempty]
  have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  calc
    ∑ v ∈ s, M / (G.degree v + 1) ≤ ∑ _v ∈ s, M / s.card := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.div_le_div_left (clique_card_le_degree_add_one G hs hv) hpos
    _ = s.card * (M / s.card) := by simp
    _ ≤ M := Nat.mul_div_le M s.card

/-- If every color support is a clique, its total list weight is palette-bounded. -/
theorem list_weight_bound {V C : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (L : V → Finset C) (P : Finset C)
    (hsub : ∀ v, L v ⊆ P) (h : ∀ c, G.IsClique {v | c ∈ L v}) (M : ℕ) :
    ∑ v, (L v).card * (M / (G.degree v + 1)) ≤ P.card * M := by
  classical
  have hid : ∑ v, (L v).card * (M / (G.degree v + 1)) =
      ∑ c ∈ P, ∑ v ∈ Finset.univ.filter (fun v => c ∈ L v), M / (G.degree v + 1) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_filter]
    have heq : P.filter (fun c => c ∈ L v) = L v := by
      ext c
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub v h, h⟩⟩
    rw [heq]
    simp
  rw [hid]
  calc
    ∑ c ∈ P, ∑ v ∈ Finset.univ.filter (fun v => c ∈ L v), M / (G.degree v + 1)
      ≤ ∑ _c ∈ P, M := by
        apply Finset.sum_le_sum
        intro c _
        apply clique_weight_bound G _ M
        simpa using h c
    _ = P.card * M := by simp

/-- A strict reverse weighted inequality supplies a shared color on an independent pair. -/
theorem independent_pair_of_weight {V C : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset C) (P : Finset C)
    (hsub : ∀ v, L v ⊆ P) (M : ℕ)
    (hweight : P.card * M < ∑ v, (L v).card * (M / (G.degree v + 1))) :
    ∃ v w, v ≠ w ∧ ¬G.Adj v w ∧ ∃ c, c ∈ L v ∧ c ∈ L w := by
  classical
  by_contra! hn
  have hclique : ∀ c, G.IsClique {v | c ∈ L v} := by
    intro c v hv w hw hne
    by_contra hadj
    exact hn v w hne hadj c hv hw
  exact (Nat.not_lt_of_ge (list_weight_bound G L P hsub hclique M)) hweight

/-- Greedy list-coloring when each list is larger than the full vertex degree. -/
theorem list_coloring_of_degree_lt {V C : Type*} [Fintype V] [Nonempty C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset C)
    (hdeg : ∀ v, G.degree v < (L v).card) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  classical
  have hpartial : ∀ s : Finset V, ∃ c : V → C,
      (∀ x ∈ s, c x ∈ L x) ∧ (∀ x ∈ s, ∀ y ∈ s, G.Adj x y → c x ≠ c y) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.arbitrary C, by simp⟩
    | @insert v s _hv ih =>
      obtain ⟨c, hcL, hc⟩ := ih
      have hcard : ((G.neighborFinset v).image c).card < (L v).card :=
        lt_of_le_of_lt Finset.card_image_le (hdeg v)
      obtain ⟨a, haL, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      refine ⟨Function.update c v a, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simpa using haL
        · by_cases hxv : x = v
          · subst x; simpa using haL
          · simpa [Function.update_apply, hxv] using hcL x hx
      · intro x hx y hy hxy
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
  obtain ⟨c, hcL, hc⟩ := hpartial Finset.univ
  exact ⟨Coloring.mk c (fun hxy => hc _ (Finset.mem_univ _) _ (Finset.mem_univ _) hxy),
    fun v => hcL v (Finset.mem_univ v)⟩

lemma scaled_weight_lower (d r l : ℕ) (hpos : 1 ≤ d) (hd : d ≤ 4)
    (hr : r ≤ d) (hl : 3*d+1 ≤ l) : 120 ≤ l * (60 / (r+1)) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

lemma scaled_weight_strict (d r l : ℕ) (hd : d ≤ 4)
    (hr : r < d) (hl : 3*d+1 ≤ l) : 195 ≤ l * (60 / (r+1)) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp <;> omega

lemma induced_degree_inter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = (G.neighborFinset v.val ∩ S).card := by
  classical
  have h := congrArg Finset.card (G.map_neighborFinset_induce (s := (S : Set V)) v)
  convert h using 1
  · simp only [Finset.card_map, card_neighborFinset_eq_degree]
    congr 1
    exact Subsingleton.elim _ _
  · simp

lemma induced_degree_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v ≤ G.degree v.val := by
  classical
  rw [induced_degree_inter]
  exact Finset.card_le_card Finset.inter_subset_left

lemma induced_degree_lt_of_neighbor_removed {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : S) {w : V}
    (hadj : G.Adj v.val w) (hw : w ∉ S) :
    (G.induce (S : Set V)).degree v < G.degree v.val := by
  classical
  rw [induced_degree_inter]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
  intro heq
  have hmem : w ∈ G.neighborFinset v.val := (G.mem_neighborFinset _ _).mpr hadj
  rw [← heq] at hmem
  exact hw (Finset.mem_inter.mp hmem).2

lemma indep_pair {V : Type*} (G : SimpleGraph V) {a b : V} (h : ¬G.Adj a b) :
    G.IsIndepSet ({a, b} : Set V) := by
  intro x hx y hy hne
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact False.elim (hne rfl)
  · exact h
  · exact fun hadj => h hadj.symm
  · exact False.elim (hne rfl)

/-- Two disjoint independent pairs can receive two different shared list colors. -/
theorem two_pairs (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (L : Fin 8 → Finset (Fin 14))
    (hpos : ∀ v, 0 < G.degree v) (hcard : ∀ v, 3*G.degree v+2 ≤ (L v).card) :
    ∃ A B : Finset (Fin 8), A.card = 2 ∧ B.card = 2 ∧ Disjoint A B ∧
      G.IsIndepSet A ∧ G.IsIndepSet B ∧
      ∃ c d : Fin 14, c ≠ d ∧ (∀ v ∈ A, c ∈ L v) ∧ (∀ v ∈ B, d ∈ L v) := by
  classical
  have hd : ∀ v, G.degree v ≤ 4 := by
    intro v
    have hL : (L v).card ≤ 14 := Finset.card_le_univ (L v)
    have := hcard v
    omega
  have hw : ∀ v, 120 ≤ (L v).card * (60 / (G.degree v+1)) := by
    intro v
    exact scaled_weight_lower _ _ _ (hpos v) (hd v) le_rfl (by have := hcard v; omega)
  have hfirst : (Finset.univ : Finset (Fin 14)).card * 60 <
      ∑ v, (L v).card * (60 / (G.degree v+1)) := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8))) (fun v _ => hw v)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum ⊢
    omega
  obtain ⟨a, b, hab, hnab, c, hca, hcb⟩ :=
    independent_pair_of_weight G L Finset.univ (fun _ => Finset.subset_univ _) 60 hfirst
  let S : Finset (Fin 8) := (Finset.univ.erase a).erase b
  let H := G.induce (S : Set (Fin 8))
  let K : S → Finset (Fin 14) := fun v => (L v.val).erase c
  have hScard : Fintype.card S = 6 := by
    rw [Fintype.card_coe]
    simp [S, hab.symm]
  have hK : ∀ v : S, 3*G.degree v.val+1 ≤ (K v).card := by
    intro v
    have := hcard v.val
    have := Finset.pred_card_le_card_erase (s := L v.val) (a := c)
    dsimp [K]
    omega
  have hres : ∀ v : S, H.degree v ≤ G.degree v.val := induced_degree_le G S
  have h120 : ∀ v : S, 120 ≤ (K v).card * (60 / (H.degree v+1)) := by
    intro v
    exact scaled_weight_lower _ _ _ (hpos v.val) (hd v.val) (hres v) (hK v)
  obtain ⟨z, haz⟩ := (G.degree_pos_iff_exists_adj a).mp (hpos a)
  have hzb : z ≠ b := fun he => hnab (he ▸ haz)
  have hzS : z ∈ S := by simp [S, haz.ne', hzb]
  let z' : S := ⟨z, hzS⟩
  have hstrict : H.degree z' < G.degree z :=
    induced_degree_lt_of_neighbor_removed G S z' haz.symm (by simp [S])
  have h195 : 195 ≤ (K z').card * (60 / (H.degree z'+1)) :=
    scaled_weight_strict _ _ _ (hd z) hstrict (hK z')
  have hremaining := Finset.sum_le_sum
    (s := (Finset.univ : Finset S).erase z') (fun v _ => h120 v)
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ z'),
    Finset.card_univ, hScard, smul_eq_mul] at hremaining
  have htotal := Finset.sum_erase_add (Finset.univ : Finset S)
    (fun v => (K v).card * (60 / (H.degree v+1))) (Finset.mem_univ z')
  have hsecond : ((Finset.univ : Finset (Fin 14)).erase c).card * 60 <
      ∑ v : S, (K v).card * (60 / (H.degree v+1)) := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
    omega
  have hsub : ∀ v : S, K v ⊆ (Finset.univ : Finset (Fin 14)).erase c := by
    intro v d hd
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hd).1, Finset.mem_univ _⟩
  obtain ⟨x, y, hxy, hnxy, d, hdx, hdy⟩ :=
    independent_pair_of_weight H K (Finset.univ.erase c) hsub 60 hsecond
  have hxS : x.val ∈ S := x.property
  have hyS : y.val ∈ S := y.property
  have hxy' : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  have hcd : c ≠ d := (Finset.mem_erase.mp hdx).1.symm
  refine ⟨{a,b}, {x.val,y.val}, by simp [hab], by simp [hxy'], ?_, ?_, ?_, c, d, hcd, ?_, ?_⟩
  · simp only [S, Finset.mem_erase, Finset.mem_univ, and_true] at hxS hyS
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    intro v hv hv'
    rcases hv with rfl | rfl <;> rcases hv' with hv' | hv'
    · exact hxS.2 hv'.symm
    · exact hyS.2 hv'.symm
    · exact hxS.1 hv'.symm
    · exact hyS.1 hv'.symm
  · simpa using indep_pair G hnab
  · simpa using indep_pair G hnxy
  · simpa using And.intro hca hcb
  · simpa using And.intro (Finset.mem_erase.mp hdx).2 (Finset.mem_erase.mp hdy).2

/-- Eight vertices, fourteen available colors, and these list sizes suffice for six used colors. -/
theorem six_color_list_compression (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (L : Fin 8 → Finset (Fin 14))
    (hpos : ∀ v, 0 < G.degree v) (hcard : ∀ v, 3*G.degree v+2 ≤ (L v).card) :
    ∃ g : G.Coloring (Fin 14), (∀ v, g v ∈ L v) ∧ (Finset.univ.image g).card ≤ 6 := by
  classical
  obtain ⟨A, B, hA, hB, hdis, hiA, hiB, c, d, hcd, hc, hd⟩ := two_pairs G L hpos hcard
  let K : Fin 8 → Finset (Fin 14) := fun v => ((L v).erase c).erase d
  have hK : ∀ v, G.degree v < (K v).card := by
    intro v
    have := hcard v
    have := hpos v
    have := Finset.pred_card_le_card_erase (s := L v) (a := c)
    have := Finset.pred_card_le_card_erase (s := (L v).erase c) (a := d)
    dsimp [K]
    omega
  obtain ⟨f, hf⟩ := list_coloring_of_degree_lt G K hK
  have hfC : ∀ v, f v ≠ c := fun v => (Finset.mem_erase.mp (Finset.mem_erase.mp (hf v)).2).1
  have hfD : ∀ v, f v ≠ d := fun v => (Finset.mem_erase.mp (hf v)).1
  let g : Fin 8 → Fin 14 := fun v => if v ∈ A then c else if v ∈ B then d else f v
  have hgproper : ∀ {v w}, G.Adj v w → g v ≠ g w := by
    intro v w hvw
    by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A <;>
      by_cases hvB : v ∈ B <;> by_cases hwB : w ∈ B <;>
      simp only [g, hvA, hwA, hvB, hwB, if_pos]
    all_goals first
      | exact False.elim (hiA hvA hwA hvw.ne hvw)
      | exact False.elim (hiB hvB hwB hvw.ne hvw)
      | exact hcd
      | exact hcd.symm
      | exact (hfC w).symm
      | exact hfC v
      | exact (hfD w).symm
      | exact hfD v
      | exact f.valid hvw
  refine ⟨Coloring.mk g hgproper, ?_, ?_⟩
  · intro v
    change g v ∈ L v
    by_cases hvA : v ∈ A
    · simpa [g, hvA] using hc v hvA
    · by_cases hvB : v ∈ B
      · simpa [g, hvA, hvB] using hd v hvB
      · simpa [g, hvA, hvB] using (Finset.mem_erase.mp (Finset.mem_erase.mp (hf v)).2).2
  · let T : Finset (Fin 8) := Finset.univ \ (A ∪ B)
    have hT : T.card = 4 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.card_union_of_disjoint hdis, hA, hB]
    have hsub : Finset.univ.image g ⊆ insert c (insert d (T.image f)) := by
      intro e he
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
      by_cases hvA : v ∈ A
      · simp [g, hvA]
      · by_cases hvB : v ∈ B
        · simp [g, hvA, hvB]
        · have hvT : v ∈ T := by simp [T, hvA, hvB]
          simpa [g, hvA, hvB] using
            Finset.mem_insert_of_mem (b := c) (Finset.mem_insert_of_mem (b := d) (Finset.mem_image_of_mem f hvT))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le c (insert d (T.image f))
    have h3 := Finset.card_insert_le d (T.image f)
    have h4 := Finset.card_image_le (s := T) (f := f)
    change (Finset.univ.image g).card ≤ 6
    omega

/-- A nonempty matching demonstrates that the list-compression hypotheses are satisfiable. -/
def witnessGraph : SimpleGraph (Fin 8) :=
  fromEdgeSet {s(0,1), s(2,3), s(4,5), s(6,7)}

instance : DecidableRel witnessGraph.Adj := by unfold witnessGraph; infer_instance

theorem witness_hypotheses :
    (∀ v, 0 < witnessGraph.degree v) ∧
    (∀ v, 3*witnessGraph.degree v+2 ≤ (Finset.univ : Finset (Fin 14)).card) := by
  decide


end Palette
end Part12

section Part13
-- Source module: FiveCase

namespace FiveCase

open SimpleGraph Finset
open scoped BigOperators

/-- A shared color on an independent pair saves one of eight colors.
The original-degree slack makes the six remaining lists greedily colorable. -/
theorem seven_colors_of_pair (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (L : Fin 8 → Finset (Fin 15))
    (hslack : ∀ v, G.degree v + 2 ≤ (L v).card)
    (a b : Fin 8) (hab : a ≠ b) (hnab : ¬G.Adj a b)
    (c : Fin 15) (hca : c ∈ L a) (hcb : c ∈ L b) :
    ∃ f : G.Coloring (Fin 15), (∀ v, f v ∈ L v) ∧
      (Finset.univ.image (fun v => f v)).card ≤ 7 := by
  classical
  let S : Finset (Fin 8) := (Finset.univ.erase a).erase b
  let H := G.induce (S : Set (Fin 8))
  let K : S → Finset (Fin 15) := fun v => (L v.val).erase c
  have hScard : Fintype.card S = 6 := by
    rw [Fintype.card_coe]
    simp [S, hab.symm]
  have hK : ∀ v : S, H.degree v < (K v).card := by
    intro v
    have hres := Palette.induced_degree_le G S v
    have hl := hslack v.val
    have he := Finset.pred_card_le_card_erase (s := L v.val) (a := c)
    dsimp [H, K] at *
    omega
  obtain ⟨g, hg⟩ := Palette.list_coloring_of_degree_lt H K hK
  have hout : ∀ v, v ∉ S → v = a ∨ v = b := by
    intro v hv
    by_contra hn
    push Not at hn
    exact hv (by simp [S, hn.1, hn.2])
  let f : Fin 8 → Fin 15 := fun v => if hv : v ∈ S then g ⟨v, hv⟩ else c
  have hf : ∀ {v w}, G.Adj v w → f v ≠ f w := by
    intro v w hvw
    by_cases hv : v ∈ S
    · by_cases hw : w ∈ S
      · have hproper := g.valid (show H.Adj ⟨v, hv⟩ ⟨w, hw⟩ from hvw)
        simpa [f, hv, hw] using hproper
      · have hc : g ⟨v, hv⟩ ≠ c := (Finset.mem_erase.mp (hg ⟨v, hv⟩)).1
        simpa [f, hv, hw] using hc
    · by_cases hw : w ∈ S
      · have hc : c ≠ g ⟨w, hw⟩ := (Finset.mem_erase.mp (hg ⟨w, hw⟩)).1.symm
        simpa [f, hv, hw] using hc
      · rcases hout v hv with rfl | rfl <;> rcases hout w hw with rfl | rfl
        · exact (hvw.ne rfl).elim
        · exact (hnab hvw).elim
        · exact (hnab hvw.symm).elim
        · exact (hvw.ne rfl).elim
  refine ⟨Coloring.mk f hf, ?_, ?_⟩
  · intro v
    change f v ∈ L v
    by_cases hv : v ∈ S
    · simpa [f, hv] using (Finset.mem_erase.mp (hg ⟨v, hv⟩)).2
    · rcases hout v hv with rfl | rfl
      · simpa [f, hv] using hca
      · simpa [f, hv] using hcb
  · change (Finset.univ.image f).card ≤ 7
    have hsub : Finset.univ.image f ⊆
        insert c (Finset.univ.image (fun v : S => g v)) := by
      intro z hz
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
      by_cases hv : v ∈ S
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, by simp [f, hv]⟩
      · simp [f, hv]
    have hcard := Finset.card_le_card hsub
    have hins := Finset.card_insert_le c (Finset.univ.image (fun v : S => g v))
    have himage := Finset.card_image_le (s := (Finset.univ : Finset S)) (f := fun v => g v)
    simp only [Finset.card_univ, hScard] at himage
    omega

/-- Integer-scaled weighted surplus plus degree slack compresses eight lists to seven colors. -/
theorem seven_colors_of_weight (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (L : Fin 8 → Finset (Fin 15)) (M : ℕ)
    (hslack : ∀ v, G.degree v + 2 ≤ (L v).card)
    (hweight : 15 * M < ∑ v, (L v).card * (M / (G.degree v + 1))) :
    ∃ f : G.Coloring (Fin 15), (∀ v, f v ∈ L v) ∧
      (Finset.univ.image (fun v => f v)).card ≤ 7 := by
  classical
  obtain ⟨a, b, hab, hnab, c, hca, hcb⟩ :=
    Palette.independent_pair_of_weight G L Finset.univ
      (fun _ => Finset.subset_univ _) M (by simpa using hweight)
  exact seven_colors_of_pair G L hslack a b hab hnab c hca hcb

lemma scaled_two (d l : ℕ) (hd : d ≤ 7) (hl : 2 * (d + 1) ≤ l) :
    1680 ≤ l * (840 / (d + 1)) := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at * <;> omega

lemma scaled_nine_fifths (d l : ℕ) (hd : d ≤ 7) (hl : 9 * (d + 1) ≤ 5 * l) :
    1512 ≤ l * (840 / (d + 1)) := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at * <;> omega

/-- The arithmetic consequence of the (r,s)=(1,1) geometry bounds. -/
lemma ratio_one_one (d l a1 a2 : ℕ) (h2 : a2 ≤ 1)
    (hl : 5 + 2*a1 + 3*a2 ≤ l) (hd : d ≤ 1 + a1 + 2*a2) :
    2 * (d + 1) ≤ l := by omega

/-- The arithmetic consequence of the (r,s)=(2,1) geometry bounds. -/
lemma ratio_two_one (d l a1 a2 : ℕ) (h2 : a2 ≤ 1)
    (hl : 9 + 2*a1 + 3*a2 ≤ l) (hd : d ≤ 3 + a1 + 2*a2) :
    2 * (d + 1) ≤ l := by omega

/-- The arithmetic consequence of the exceptional (r,s)=(1,2) geometry bounds. -/
lemma ratio_one_two (d l a1 a2 : ℕ) (h2 : a2 ≤ 1)
    (hl : 6 + 2*a1 + 3*a2 ≤ l) (hd : d ≤ 2 + a1 + 2*a2) :
    9 * (d + 1) ≤ 5 * l := by omega

/-- Four possible 9/5 ratios and four ratios at least two give total weight ≥76/5.
The scale 840 is divisible by every possible degree plus one on eight vertices. -/
theorem weight_of_four_exceptions (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (L : Fin 8 → Finset (Fin 15)) (E : Finset (Fin 8)) (hE : E.card ≤ 4)
    (hexception : ∀ v ∈ E, 9 * (G.degree v + 1) ≤ 5 * (L v).card)
    (hregular : ∀ v ∉ E, 2 * (G.degree v + 1) ≤ (L v).card) :
    15 * 840 < ∑ v, (L v).card * (840 / (G.degree v + 1)) := by
  classical
  let w : Fin 8 → ℕ := fun v => (L v).card * (840 / (G.degree v + 1))
  have hd : ∀ v, G.degree v ≤ 7 := by
    intro v
    have := G.degree_lt_card_verts v
    simp only [Fintype.card_fin] at this
    omega
  have hsE := Finset.sum_le_sum (s := E) (fun v hv =>
    scaled_nine_fifths (G.degree v) (L v).card (hd v) (hexception v hv))
  have hsR := Finset.sum_le_sum (s := Finset.univ \ E) (fun v hv =>
    scaled_two (G.degree v) (L v).card (hd v) (hregular v (Finset.mem_sdiff.mp hv).2))
  have hsplit := Finset.sum_sdiff (Finset.subset_univ E) (f := w)
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
  simp only [Finset.sum_const, smul_eq_mul] at hsE hsR
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  change 15 * 840 < ∑ v, w v
  change E.card * 1512 ≤ ∑ v ∈ E, w v at hsE
  change (Finset.univ \ E).card * 1680 ≤ ∑ v ∈ Finset.univ \ E, w v at hsR
  omega

/-- The pure list-compression conclusion required by the five-color-intersection case.
This theorem assumes the list inequalities; it does not prove host-graph geometry. -/
theorem five_case_list_compression (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (L : Fin 8 → Finset (Fin 15)) (E : Finset (Fin 8)) (hE : E.card ≤ 4)
    (hslack : ∀ v, G.degree v + 2 ≤ (L v).card)
    (hexception : ∀ v ∈ E, 9 * (G.degree v + 1) ≤ 5 * (L v).card)
    (hregular : ∀ v ∉ E, 2 * (G.degree v + 1) ≤ (L v).card) :
    ∃ f : G.Coloring (Fin 15), (∀ v, f v ∈ L v) ∧
      (Finset.univ.image (fun v => f v)).card ≤ 7 := by
  exact seven_colors_of_weight G L 840 hslack
    (weight_of_four_exceptions G L E hE hexception hregular)


end FiveCase
end Part13

section Part14
-- Source module: TwinCompletion

namespace TwinReduction

open SimpleGraph Finset

private def relabelList {n : ℕ} (P : Finset (Fin 20)) (e : P ≃ Fin n)
    (A : Finset (Fin 20)) (hA : A ⊆ P) : Finset (Fin n) :=
  A.attach.image (fun a => e ⟨a.val, hA a.property⟩)

private lemma relabelList_card {n : ℕ} (P : Finset (Fin 20)) (e : P ≃ Fin n)
    (A : Finset (Fin 20)) (hA : A ⊆ P) :
    (relabelList P e A hA).card = A.card := by
  classical
  unfold relabelList
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : P => x.val) (e.injective hab)

/-- Relabel a finite subpalette exactly, then transport its list coloring back. -/
private theorem transfer_coloring {n k : ℕ} (H : SimpleGraph (Fin 8))
    (P : Finset (Fin 20)) (e : P ≃ Fin n) (A : Fin 8 → Finset (Fin 20))
    (hA : ∀ v, A v ⊆ P) (g : H.Coloring (Fin n))
    (hg : ∀ v, g v ∈ relabelList P e (A v) (hA v))
    (hused : (Finset.univ.image g).card ≤ k) :
    ∃ q : H.Coloring (Fin 20), (∀ v, q v ∈ A v) ∧ (Finset.univ.image q).card ≤ k := by
  classical
  let decode : Fin n → Fin 20 := fun c => (e.symm c).val
  have hdecode : Function.Injective decode := by
    intro c d hcd
    exact e.symm.injective (Subtype.ext hcd)
  let q : H.Coloring (Fin 20) := Coloring.mk (fun v => decode (g v))
    (fun h => fun he => g.valid h (hdecode he))
  refine ⟨q, ?_, ?_⟩
  · intro v
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hg v)
    change decode (g v) ∈ A v
    rw [← ha]
    simp [decode]
  · change (Finset.univ.image (decode ∘ g)).card ≤ k
    rw [← Finset.image_image, Finset.card_image_of_injective _ hdecode]
    exact hused

/-- The fourteen-color compression transferred to the complement of six colors. -/
theorem six_color_subpalette (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (T : Finset (Fin 20)) (hT : T.card = 6) (A : Fin 8 → Finset (Fin 20))
    (hA : ∀ v, A v ⊆ Finset.univ \ T)
    (hpos : ∀ v, 0 < H.degree v)
    (hcard : ∀ v, 3 * H.degree v + 2 ≤ (A v).card) :
    ∃ q : H.Coloring (Fin 20), (∀ v, q v ∈ A v) ∧ (Finset.univ.image q).card ≤ 6 := by
  classical
  let P : Finset (Fin 20) := Finset.univ \ T
  have hP : P.card = 14 := by
    simp [P, Finset.card_sdiff_of_subset (Finset.subset_univ T), hT]
  let e : P ≃ Fin 14 := Finset.equivFinOfCardEq hP
  let L : Fin 8 → Finset (Fin 14) := fun v => relabelList P e (A v) (hA v)
  have hL : ∀ v, (L v).card = (A v).card := fun v => relabelList_card P e (A v) (hA v)
  obtain ⟨g, hg, hused⟩ := Palette.six_color_list_compression H L hpos (by
    intro v
    rw [hL]
    exact hcard v)
  exact transfer_coloring H P e A hA g hg hused

/-- The fifteen-color compression transferred to the complement of five colors. -/
theorem five_color_subpalette (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (T : Finset (Fin 20)) (hT : T.card = 5) (A : Fin 8 → Finset (Fin 20))
    (hA : ∀ v, A v ⊆ Finset.univ \ T) (E : Finset (Fin 8)) (hE : E.card ≤ 4)
    (hslack : ∀ v, H.degree v + 2 ≤ (A v).card)
    (hexception : ∀ v ∈ E, 9 * (H.degree v + 1) ≤ 5 * (A v).card)
    (hregular : ∀ v ∉ E, 2 * (H.degree v + 1) ≤ (A v).card) :
    ∃ q : H.Coloring (Fin 20), (∀ v, q v ∈ A v) ∧ (Finset.univ.image q).card ≤ 7 := by
  classical
  let P : Finset (Fin 20) := Finset.univ \ T
  have hP : P.card = 15 := by
    simp [P, Finset.card_sdiff_of_subset (Finset.subset_univ T), hT]
  let e : P ≃ Fin 15 := Finset.equivFinOfCardEq hP
  let L : Fin 8 → Finset (Fin 15) := fun v => relabelList P e (A v) (hA v)
  have hL : ∀ v, (L v).card = (A v).card := fun v => relabelList_card P e (A v) (hA v)
  obtain ⟨g, hg, hused⟩ := FiveCase.five_case_list_compression H L E hE
    (by intro v; rw [hL]; exact hslack v)
    (by intro v hv; rw [hL]; exact hexception v hv)
    (by intro v hv; rw [hL]; exact hregular v hv)
  exact transfer_coloring H P e A hA g hg hused

/-- Compressed spoke colors and fixed row exclusions leave eight distinct cell colors. -/
theorem cell_assignment_avoiding (Q T : Finset (Fin 20)) (F : Fin 4 → Finset (Fin 20))
    (hQ : Q.card ≤ 7) (hF : ∀ i, (F i).card ≤ 6)
    (hsum : Q.card + T.card ≤ 12)
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i) :
    ∃ f : Fin 4 × Fin 2 → Fin 20, Function.Injective f ∧
      ∀ v, f v ∉ Q ∧ f v ∉ F v.1 := by
  classical
  let L : Fin 4 → Finset (Fin 20) := fun i => Finset.univ \ (Q ∪ F i)
  have hL : ∀ i, 6 ≤ (L i).card := by
    intro i
    have hU := Finset.card_union_le Q (F i)
    have hi := hF i
    dsimp [L]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have htotal : 8 ≤ ((Finset.univ : Finset (Fin 4)).biUnion L).card := by
    rw [available_union Q T F hT, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hU := Finset.card_union_le Q T
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨f, hf, hmem⟩ := (repeated_row_hall L hL).mpr htotal
  refine ⟨f, hf, ?_⟩
  intro v
  have hnot := (Finset.mem_sdiff.mp (hmem v)).2
  exact ⟨fun h => hnot (Finset.mem_union_left _ h),
    fun h => hnot (Finset.mem_union_right _ h)⟩

/-- Pure combinatorial completion of the six-color-intersection case.
The hypotheses describe lists and row exclusions, not unproved host-graph geometry. -/
theorem complete_six_intersection (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (T : Finset (Fin 20)) (hT : T.card = 6) (F : Fin 4 → Finset (Fin 20))
    (hF : ∀ i, F i = T) (A : Fin 8 → Finset (Fin 20))
    (hA : ∀ v, A v ⊆ Finset.univ \ T)
    (hpos : ∀ v, 0 < H.degree v)
    (hcard : ∀ v, 3 * H.degree v + 2 ≤ (A v).card) :
    ∃ q : H.Coloring (Fin 20), (∀ v, q v ∈ A v) ∧
      (Finset.univ.image q).card ≤ 6 ∧
      ∃ f : Fin 4 × Fin 2 → Fin 20, Function.Injective f ∧
        ∀ v, f v ∉ Finset.univ.image q ∧ f v ∉ F v.1 := by
  classical
  obtain ⟨q, hq, hused⟩ := six_color_subpalette H T hT A hA hpos hcard
  have hinter : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i := by simp [hF]
  obtain ⟨f, hf, havoid⟩ := cell_assignment_avoiding (Finset.univ.image q) T F
    (by omega) (by intro i; rw [hF i, hT]) (by omega) hinter
  exact ⟨q, hq, hused, f, hf, havoid⟩

/-- Pure combinatorial completion of the five-color-intersection case.
The source of the list-size, ratio, and fixed-set bounds remains an explicit hypothesis. -/
theorem complete_five_intersection (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (T : Finset (Fin 20)) (hT : T.card = 5) (F : Fin 4 → Finset (Fin 20))
    (hF : ∀ i, (F i).card ≤ 6) (hinter : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i)
    (A : Fin 8 → Finset (Fin 20)) (hA : ∀ v, A v ⊆ Finset.univ \ T)
    (E : Finset (Fin 8)) (hE : E.card ≤ 4)
    (hslack : ∀ v, H.degree v + 2 ≤ (A v).card)
    (hexception : ∀ v ∈ E, 9 * (H.degree v + 1) ≤ 5 * (A v).card)
    (hregular : ∀ v ∉ E, 2 * (H.degree v + 1) ≤ (A v).card) :
    ∃ q : H.Coloring (Fin 20), (∀ v, q v ∈ A v) ∧
      (Finset.univ.image q).card ≤ 7 ∧
      ∃ f : Fin 4 × Fin 2 → Fin 20, Function.Injective f ∧
        ∀ v, f v ∉ Finset.univ.image q ∧ f v ∉ F v.1 := by
  classical
  obtain ⟨q, hq, hused⟩ := five_color_subpalette H T hT A hA E hE hslack hexception hregular
  obtain ⟨f, hf, havoid⟩ := cell_assignment_avoiding (Finset.univ.image q) T F
    hused hF (by omega) hinter
  exact ⟨q, hq, hused, f, hf, havoid⟩


end TwinReduction
end Part14

section Part15
-- Source module: TwinSixCase

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Six common fixed colors force at least six actual fixed edges at every row. -/
theorem six_common_forces_six_edges (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card := by
  intro u hu
  have hsub := Finset.card_le_card (hcommon u hu)
  have himage := Finset.card_image_le (s := rowSeen G p q U u) (f := c)
  rw [hT] at hsub
  omega

open scoped Classical in
/-- The actual available list satisfies the six-color compression bound. -/
theorem six_actual_list_bound (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∀ e : ↥(spokeEdges G p q U), 3 * (spokeGraph G p q U).degree e + 2 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card := by
  intro e
  have hsix := six_common_forces_six_edges G p q U c T hT hcommon
  obtain ⟨u,hu,x,hx,he⟩ := spoke_row_center G p q U e.val e.property
  have hd := spoke_degree_add_exterior_le_four G p q U hpq hdegree hp hq hsix e u x hu hx he
  have ha := six_available_card_lower G p q U u x hpq hdegree hp hq hu hx c T hT hcommon
  have hedge : spokeToEdge G p q U e =
      ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ := Subtype.ext he
  rw [← hedge] at ha
  omega

/-- Actual spoke lists avoid all common fixed row colors. -/
theorem actual_spoke_list_avoids_common (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∀ e : ↥(spokeEdges G p q U),
      availableColors G p q U (spokeToEdge G p q U e) c ⊆ Finset.univ \ T := by
  intro e
  obtain ⟨u,hu,hue⟩ := ((mem_spokeEdges G p q U e.val).mp e.property).2.2.2
  exact availableColors_subset_complement_common G p q U u hu
    (spokeToEdge G p q U e) hue c T (hcommon u hu)

open scoped Classical in
/-- The complete six-common-color case on the actual host spokes: a proper spoke
coloring compatible with every fixed edge, together with eight distinct cell colors.
This theorem does not yet merge those assignments into a coloring of all of G. -/
theorem six_case_actual_completion (p q : V) (U : Finset V) (hUcard : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∃ qcolor : (spokeGraph G p q U).Coloring (Fin 20),
      (∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c) ∧
      (Finset.univ.image qcolor).card ≤ 6 ∧
      ∃ f : Fin 4 × Fin 2 → Fin 20, Function.Injective f ∧
        ∀ v, f v ∉ T ∧ f v ∉ Finset.univ.image qcolor := by
  classical
  have hsix := six_common_forces_six_edges G p q U c T hT hcommon
  have hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card := by
    intro u hu
    have := hsix u hu
    omega
  have hcard := spokeEdges_card_eq_eight G p q U hUcard hpq hdegree hp hq hfive
  let H8 := spokeGraph8 G p q U hcard
  let iso : H8 ≃g spokeGraph G p q U := spokeGraph8Iso G p q U hcard
  let A : Fin 8 → Finset (Fin 20) := fun i =>
    availableColors G p q U (spokeToEdge G p q U (iso i)) c
  have hA : ∀ i, A i ⊆ Finset.univ \ T := fun i =>
    actual_spoke_list_avoids_common G p q U c T hcommon (iso i)
  have hpos : ∀ i, 0 < H8.degree i :=
    spokeGraph8_degree_pos G p q U hcard hpq hdegree hp hq hfive
  have hAlower : ∀ i, 3 * H8.degree i + 2 ≤ (A i).card := by
    intro i
    have hb := six_actual_list_bound G p q U hpq hdegree hp hq c T hT hcommon (iso i)
    rw [iso.degree_eq i] at hb
    exact hb
  obtain ⟨q8,hq8,hused,f,hf,havoid⟩ := complete_six_intersection H8 T hT (fun _ => T)
    (fun _ => rfl) A hA hpos hAlower
  let qcolor : (spokeGraph G p q U).Coloring (Fin 20) := q8.comp iso.symm.toHom
  have hcompatible : ∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c := by
    intro e
    change q8 (iso.symm e) ∈ availableColors G p q U (spokeToEdge G p q U e) c
    simpa [A] using hq8 (iso.symm e)
  have himage : Finset.univ.image qcolor = Finset.univ.image q8 := by
    ext a
    constructor
    · intro ha
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨iso.symm e,Finset.mem_univ _,rfl⟩
    · intro ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨iso i,Finset.mem_univ _,by simp [qcolor]⟩
  refine ⟨qcolor,hcompatible,?_,f,hf,?_⟩
  · rw [himage]
    exact hused
  · intro v
    rw [himage]
    exact ⟨(havoid v).2,(havoid v).1⟩


end TwinReduction
end Part15

section Part16
-- Source module: TwinFiveGeometry

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma rowMultiplicity_pos_of_adj {U : Finset V} {u x : V} (hu : u ∈ U)
    (hux : G.Adj u x) : 0 < rowMultiplicity G U x := by
  apply Finset.card_pos.mpr
  exact ⟨u, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hux.symm, hu⟩⟩

/-- A row seeing five edges has a total of at most three row incidences at its two centers. -/
theorem row_five_multiplicity_sum_le_three (p q : V) (U : Finset V) (u x y : V)
    (hdegree : G.maxDegree ≤ 4) (hcenters : rowCenters G p q u = {x,y})
    (hfive : 5 ≤ (rowSeen G p q U u).card) :
    rowMultiplicity G U x + rowMultiplicity G U y ≤ 3 := by
  have := rowSeen_card_add_multiplicities_le_eight G p q U u x y hdegree hcenters
  omega

/-- Every center of a row seeing at least five edges has row multiplicity one or two. -/
theorem rowCenter_multiplicity_one_or_two (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hfive : 5 ≤ (rowSeen G p q U u).card)
    (hx : x ∈ rowCenters G p q u) :
    rowMultiplicity G U x = 1 ∨ rowMultiplicity G U x = 2 := by
  obtain ⟨a, b, _, hc⟩ := Finset.card_eq_two.mp
    (rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu hfive)
  have ha : a ∈ rowCenters G p q u := by simp [hc]
  have hb : b ∈ rowCenters G p q u := by simp [hc]
  have hpa := rowMultiplicity_pos_of_adj G hu ((mem_rowCenters G p q u a).mp ha).1
  have hpb := rowMultiplicity_pos_of_adj G hu ((mem_rowCenters G p q u b).mp hb).1
  have hsum := row_five_multiplicity_sum_le_three G p q U u a b hdegree hc hfive
  rw [hc, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> omega

/-- Two distinct centers of the same row cannot both have multiplicity two. -/
theorem row_five_not_two_double_centers (p q : V) (U : Finset V) (u x y : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hfive : 5 ≤ (rowSeen G p q U u).card)
    (hx : x ∈ rowCenters G p q u) (hy : y ∈ rowCenters G p q u) (hxy : x ≠ y) :
    ¬ (rowMultiplicity G U x = 2 ∧ rowMultiplicity G U y = 2) := by
  have hcard := rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu hfive
  have hsub : {x,y} ⊆ rowCenters G p q u := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hx hy
  have hc : rowCenters G p q u = {x,y} := by
    apply (Finset.eq_of_subset_of_card_le hsub _).symm
    simp [hcard, Finset.card_pair hxy]
  have := row_five_multiplicity_sum_le_three G p q U u x y hdegree hc hfive
  omega

/-- A total row multiplicity of three saturates both center capacities and the five-edge bound. -/
theorem row_five_saturated_of_multiplicity_sum_three (p q : V) (U : Finset V)
    (u x y : V) (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hfive : 5 ≤ (rowSeen G p q U u).card)
    (hcenters : rowCenters G p q u = {x,y})
    (hsum : rowMultiplicity G U x + rowMultiplicity G U y = 3) :
    (fixedAt G p q U x).card = 4 - rowMultiplicity G U x ∧
      (fixedAt G p q U y).card = 4 - rowMultiplicity G U y ∧
      ¬ G.Adj x y ∧ (rowSeen G p q U u).card = 5 := by
  have hbx := fixedAt_card_add_rowMultiplicity_le_four G p q U x hdegree
  have hby := fixedAt_card_add_rowMultiplicity_le_four G p q U y hdegree
  have heq : rowSeen G p q U u = fixedAt G p q U x ∪ fixedAt G p q U y := by
    simp [rowSeen, hcenters]
  have hunion := Finset.card_union_le (fixedAt G p q U x) (fixedAt G p q U y)
  rw [← heq] at hunion
  have hdis := rowCenters_disjoint_rows_of_five G p q U u hpq hdegree hp hq hu hfive
  have hxU : x ∉ U := fun h => Finset.disjoint_left.mp hdis (by simp [hcenters]) h
  have hyU : y ∉ U := fun h => Finset.disjoint_left.mp hdis (by simp [hcenters]) h
  refine ⟨by omega, by omega, ?_, by omega⟩
  intro hxy
  have := rowSeen_card_add_multiplicities_le_seven_of_adjacent
    G p q U u x y hdegree hcenters hxU hyU hxy
  omega

/-- Centers adjacent to exactly two rows. Only centers belonging to the row configuration count. -/
def doubleCenters (p q : V) (U : Finset V) : Finset V :=
  (U.biUnion (rowCenters G p q)).filter (fun x => rowMultiplicity G U x = 2)

/-- Distinct multiplicity-two centers consume disjoint pairs of rows. -/
theorem doubleCenters_row_pairs_disjoint (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    (doubleCenters G p q U : Set V).PairwiseDisjoint (fun x => G.neighborFinset x ∩ U) := by
  intro x hx y hy hxy
  apply Finset.disjoint_left.mpr
  intro u hux huy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  obtain ⟨v, _, hxv⟩ := Finset.mem_biUnion.mp hx'.1
  obtain ⟨w, _, hyw⟩ := Finset.mem_biUnion.mp hy'.1
  have hxne := ((mem_rowCenters G p q v x).mp hxv).2
  have hyne := ((mem_rowCenters G p q w y).mp hyw).2
  have hu := (Finset.mem_inter.mp hux).2
  have hxcent : x ∈ rowCenters G p q u :=
    (mem_rowCenters G p q u x).mpr
      ⟨((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hux).1).symm, hxne⟩
  have hycent : y ∈ rowCenters G p q u :=
    (mem_rowCenters G p q u y).mpr
      ⟨((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp huy).1).symm, hyne⟩
  exact row_five_not_two_double_centers G p q U u x y hpq hdegree hp hq hu
    (hfive u hu) hxcent hycent hxy ⟨hx'.2, hy'.2⟩

/-- Each multiplicity-two center consumes two distinct rows, with no row consumed twice. -/
theorem doubleCenters_twice_card_le_rows (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    2 * (doubleCenters G p q U).card ≤ U.card := by
  have hdis := doubleCenters_row_pairs_disjoint G p q U hpq hdegree hp hq hfive
  have hsub : (doubleCenters G p q U).biUnion (fun x => G.neighborFinset x ∩ U) ⊆ U := by
    intro u hu
    obtain ⟨x, _, hux⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_inter.mp hux).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis] at hc
  have heq : ∑ x ∈ doubleCenters G p q U, (G.neighborFinset x ∩ U).card =
      2 * (doubleCenters G p q U).card := by
    calc
      ∑ x ∈ doubleCenters G p q U, (G.neighborFinset x ∩ U).card
          = ∑ _x ∈ doubleCenters G p q U, 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (Finset.mem_filter.mp hx).2
      _ = _ := by simp [Nat.mul_comm]
  rwa [heq] at hc

/-- With four rows, at most two centers have row multiplicity two. -/
theorem doubleCenters_card_le_two_of_four_rows (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) (hU : U.card = 4) :
    (doubleCenters G p q U).card ≤ 2 := by
  have := doubleCenters_twice_card_le_rows G p q U hpq hdegree hp hq hfive
  omega


end TwinReduction
end Part16

section Part17
-- Source module: TwinFiveColors

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each center has at most one fixed color outside the five colors seen by its row.
No properness assumption on the color function is required for this count. -/
theorem center_fixed_extra_colors_le_one (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hT : T.card = 5) (hsub : T ⊆ (rowSeen G p q U u).image c) :
    ((fixedAt G p q U x).image c \ T).card ≤ 1 := by
  have hcolors := fixedAt_colors_subset_row G p q U u x hx c
  have hdiff : (fixedAt G p q U x).image c \ T ⊆
      (rowSeen G p q U u).image c \ T := by
    intro a ha
    exact mem_sdiff.mpr ⟨hcolors (mem_sdiff.mp ha).1, (mem_sdiff.mp ha).2⟩
  exact (card_le_card hdiff).trans
    (row_extra_colors_le_one G p q U u hpq hdegree hp hq hu c T hT hsub)

/-- A row with a multiplicity-two center has exactly its five prescribed fixed colors. -/
theorem row_colors_eq_common_of_double_center (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (hdouble : rowMultiplicity G U x = 2)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hT : T.card = 5) (hsub : T ⊆ (rowSeen G p q U u).image c) :
    (rowSeen G p q U u).image c = T := by
  have hfive : 5 ≤ (rowSeen G p q U u).card := by
    calc
      5 = T.card := hT.symm
      _ ≤ ((rowSeen G p q U u).image c).card := card_le_card hsub
      _ ≤ (rowSeen G p q U u).card := card_image_le
  obtain ⟨a, b, _, hcenters⟩ := Finset.card_eq_two.mp
    (rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu hfive)
  have ha : a ∈ rowCenters G p q u := by simp [hcenters]
  have hb : b ∈ rowCenters G p q u := by simp [hcenters]
  have hapos := rowMultiplicity_pos_of_adj G hu ((mem_rowCenters G p q u a).mp ha).1
  have hbpos := rowMultiplicity_pos_of_adj G hu ((mem_rowCenters G p q u b).mp hb).1
  have hle := row_five_multiplicity_sum_le_three G p q U u a b hdegree hcenters hfive
  have hsum : rowMultiplicity G U a + rowMultiplicity G U b = 3 := by
    have hxab : x = a ∨ x = b := by simpa [hcenters] using hx
    rcases hxab with rfl | rfl <;> omega
  have hseen := (row_five_saturated_of_multiplicity_sum_three G p q U u a b
    hpq hdegree hp hq hu hfive hcenters hsum).2.2.2
  apply (eq_of_subset_of_card_le hsub ?_).symm
  calc
    ((rowSeen G p q U u).image c).card ≤ (rowSeen G p q U u).card := card_image_le
    _ = 5 := hseen
    _ = T.card := hT.symm

/-- Every fixed color at a multiplicity-two center is one of the five prescribed colors.
This uses only incidence and color cardinalities, not retained-coloring properness. -/
theorem double_center_fixed_colors_common_of_five (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (hdouble : rowMultiplicity G U x = 2)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hT : T.card = 5) (hsub : T ⊆ (rowSeen G p q U u).image c) :
    (fixedAt G p q U x).image c ⊆ T := by
  rw [← row_colors_eq_common_of_double_center G p q U u x hpq hdegree hp hq hu hx
    hdouble c T hT hsub]
  exact fixedAt_colors_subset_row G p q U u x hx c


end TwinReduction
end Part17

section Part18
-- Source module: TwinFiveAvailable

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Fixed conflicts are covered by the row, adjacent centers, and exterior edges. -/
theorem fixed_colors_covered_by_rows_centers (p q : V) (U X : Finset V)
    (u x : V) (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (c : Sym2 V → Fin 20) :
    fixedConflictColors G p q U ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ c ⊆
      (rowSeen G p q U u).image c ∪
        (G.neighborFinset x ∩ X).biUnion (fun z => (fixedAt G p q U z).image c) ∪
        (beyondEdges G x (G.neighborFinset x \ (X ∪ U))).image c := by
  classical
  let K := G.neighborFinset x ∩ X
  let R := (rowSeen G p q U u).image c
  let C := K.biUnion (fun z => (fixedAt G p q U z).image c)
  have hX : ∀ z ∈ insert x K, (fixedAt G p q U z).image c ⊆ R ∪ C := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact (fixedAt_colors_subset_row G p q U u _ hx c).trans subset_union_left
    · exact (subset_biUnion_of_mem (fun z => (fixedAt G p q U z).image c) hz).trans
        subset_union_right
  have hcover := fixed_colors_covered_by_beyond G p q U (insert x K) u x hu
    ((mem_rowCenters G p q u x).mp hx).1 (mem_insert_self _ _) c (R ∪ C)
    subset_union_left hX
  have hZ : G.neighborFinset x \ (insert x K ∪ U) = G.neighborFinset x \ (X ∪ U) := by
    ext z
    simp only [mem_sdiff, mem_union, mem_insert, K, mem_inter]
    have hne : z ∈ G.neighborFinset x → z ≠ x := by
      intro hz
      exact ((G.mem_neighborFinset _ _).mp hz).ne'
    tauto
  rw [hZ] at hcover
  exact hcover

/-- A counted palette bound, with the row and center excesses explicit.
The geometric lemmas supply these excess hypotheses for the five-color case. -/
theorem five_available_count (p q : V) (U X : Finset V) (u x : V)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) (hdegree : G.maxDegree ≤ 4)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5) (δ : ℕ)
    (hrow : ((rowSeen G p q U u).image c \ T).card ≤ δ)
    (hX : ∀ z ∈ G.neighborFinset x ∩ X,
      ((fixedAt G p q U z).image c \ T).card ≤ if rowMultiplicity G U z = 1 then 1 else 0) :
    (availableColors G p q U ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ c).card + δ +
      ((G.neighborFinset x ∩ X).filter (fun z => rowMultiplicity G U z = 1)).card +
      3 * (G.neighborFinset x \ (X ∪ U)).card ≥ 15 := by
  classical
  let K := G.neighborFinset x ∩ X
  let Z := G.neighborFinset x \ (X ∪ U)
  let R := (rowSeen G p q U u).image c
  let C := K.biUnion (fun z => (fixedAt G p q U z).image c)
  let D := (beyondEdges G x Z).image c
  let F := fixedConflictColors G p q U ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ c
  have hcover : F ⊆ R ∪ C ∪ D := fixed_colors_covered_by_rows_centers G p q U X u x hu hx c
  have hsplit : C \ T = K.biUnion (fun z => (fixedAt G p q U z).image c \ T) := by
    ext a
    simp only [C, mem_sdiff, mem_biUnion]
    aesop
  have hC : (C \ T).card ≤ (K.filter (fun z => rowMultiplicity G U z = 1)).card := by
    rw [hsplit]
    calc
      _ ≤ ∑ z ∈ K, ((fixedAt G p q U z).image c \ T).card := card_biUnion_le
      _ ≤ ∑ z ∈ K, if rowMultiplicity G U z = 1 then 1 else 0 :=
        sum_le_sum (fun z hz => hX z hz)
      _ = _ := by rw [← sum_filter]; simp
  have hD : (D \ T).card ≤ 3 * Z.card := by
    exact (card_le_card sdiff_subset).trans (card_image_le.trans
      (beyondEdges_card_le G x Z hdegree sdiff_subset))
  have hsub : F \ T ⊆ (R ∪ C ∪ D) \ T := by
    intro a ha
    exact mem_sdiff.mpr ⟨hcover (mem_sdiff.mp ha).1, (mem_sdiff.mp ha).2⟩
  have hcard := card_le_card hsub
  rw [union_sdiff_distrib, union_sdiff_distrib] at hcard
  have h1 := card_union_le (R \ T) (C \ T)
  have h2 := card_union_le (R \ T ∪ C \ T) (D \ T)
  have hFsplit := card_sdiff_add_card_inter F T
  have hFT : (F ∩ T).card ≤ 5 := by rw [← hT]; exact card_le_card inter_subset_right
  change (R \ T).card ≤ δ at hrow
  change (availableColors G p q U _ c).card + δ +
    (K.filter (fun z => rowMultiplicity G U z = 1)).card + 3 * Z.card ≥ 15
  rw [availableColors, card_sdiff_of_subset (subset_univ _)]
  simp only [card_univ, Fintype.card_fin]
  change 20 - F.card + δ + (K.filter (fun z => rowMultiplicity G U z = 1)).card + 3 * Z.card ≥ 15
  omega

/-- Discharge the row and center color-count hypotheses using the actual five-color geometry. -/
theorem five_available_card_lower (p q : V) (U : Finset V) (u x y : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hu : u ∈ U) (hcenters : rowCenters G p q u = {x,y})
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ v ∈ U, T ⊆ (rowSeen G p q U v).image c) :
    (availableColors G p q U ⟨s(u,x), (by
      apply ((mem_rowCenters G p q u x).mp _).1
      simp [hcenters])⟩ c).card +
      (if rowMultiplicity G U x + rowMultiplicity G U y = 3 then 0 else 1) +
      ((G.neighborFinset x ∩ U.biUnion (rowCenters G p q)).filter
        (fun z => rowMultiplicity G U z = 1)).card +
      3 * (G.neighborFinset x \ (U.biUnion (rowCenters G p q) ∪ U)).card ≥ 15 := by
  classical
  have hx : x ∈ rowCenters G p q u := by simp [hcenters]
  have hy : y ∈ rowCenters G p q u := by simp [hcenters]
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  apply five_available_count G p q U (U.biUnion (rowCenters G p q)) u x hu hx hdegree c T hT
  · by_cases hsum : rowMultiplicity G U x + rowMultiplicity G U y = 3
    · rw [if_pos hsum]
      have hxpos := rowMultiplicity_pos_of_adj G hu ((mem_rowCenters G p q u x).mp hx).1
      have hypos := rowMultiplicity_pos_of_adj G hu ((mem_rowCenters G p q u y).mp hy).1
      have hd : rowMultiplicity G U x = 2 ∨ rowMultiplicity G U y = 2 := by omega
      have hroweq : (rowSeen G p q U u).image c = T := by
        rcases hd with hd | hd
        · exact row_colors_eq_common_of_double_center G p q U u x hpq hdegree hp hq hu hx
            hd c T hT (hcommon u hu)
        · exact row_colors_eq_common_of_double_center G p q U u y hpq hdegree hp hq hu hy
            hd c T hT (hcommon u hu)
      simp [hroweq]
    · rw [if_neg hsum]
      exact row_extra_colors_le_one G p q U u hpq hdegree hp hq hu c T hT (hcommon u hu)
  · intro z hz
    obtain ⟨v, hv, hzv⟩ := mem_biUnion.mp (mem_inter.mp hz).2
    rcases rowCenter_multiplicity_one_or_two G p q U v z hpq hdegree hp hq hv
        (hfive v hv) hzv with hsingle | hdouble
    · rw [if_pos hsingle]
      exact center_fixed_extra_colors_le_one G p q U v z hpq hdegree hp hq hv hzv c T hT
        (hcommon v hv)
    · rw [if_neg (by omega)]
      have hsub := double_center_fixed_colors_common_of_five G p q U v z hpq hdegree hp hq
        hv hzv hdouble c T hT (hcommon v hv)
      simp [sdiff_eq_empty_iff_subset.mpr hsub]


end TwinReduction
end Part18

section Part19
-- Source module: TwinNeighborPartition

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All centers occurring at a row of the twin configuration. -/
def allCenters (p q : V) (U : Finset V) : Finset V :=
  U.biUnion (rowCenters G p q)

/-- Five seen fixed edges at every row separate the whole center set from the rows. -/
theorem allCenters_disjoint_rows_of_five (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    Disjoint (allCenters G p q U) U := by
  apply Finset.disjoint_left.mpr
  intro x hx hxU
  obtain ⟨u, hu, hux⟩ := Finset.mem_biUnion.mp hx
  exact Finset.disjoint_left.mp
    (rowCenters_disjoint_rows_of_five G p q U u hpq hdegree hp hq hu (hfive u hu))
    hux hxU

/-- Every center in the configuration has row multiplicity one or two. -/
theorem allCenters_multiplicity_one_or_two (p q : V) (U : Finset V) (x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card)
    (hx : x ∈ allCenters G p q U) :
    rowMultiplicity G U x = 1 ∨ rowMultiplicity G U x = 2 := by
  obtain ⟨u, hu, hux⟩ := Finset.mem_biUnion.mp hx
  exact rowCenter_multiplicity_one_or_two G p q U u x hpq hdegree hp hq hu
    (hfive u hu) hux

/-- Adjacent centers split into the single and doubled types, counted once each. -/
theorem neighbor_center_type_card (p q : V) (U : Finset V) (x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    ((G.neighborFinset x ∩ allCenters G p q U).filter
      (fun z => rowMultiplicity G U z = 1)).card +
      (G.neighborFinset x ∩ doubleCenters G p q U).card =
      (G.neighborFinset x ∩ allCenters G p q U).card := by
  let Z := G.neighborFinset x ∩ allCenters G p q U
  have hZ2 : Z.filter (fun z => ¬ rowMultiplicity G U z = 1) =
      G.neighborFinset x ∩ doubleCenters G p q U := by
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      have htype := allCenters_multiplicity_one_or_two G p q U z hpq hdegree hp hq
        hfive (Finset.mem_inter.mp hz'.1).2
      have hdouble := htype.resolve_left hz'.2
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz'.1).1,
        Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hz'.1).2, hdouble⟩⟩
    · intro hz
      have hz' := Finset.mem_inter.mp hz
      have hdouble := Finset.mem_filter.mp hz'.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨hz'.1, hdouble.1⟩, by omega⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Z)
    (fun z => rowMultiplicity G U z = 1)
  rw [hZ2] at hsplit
  exact hsplit

/-- Row neighbors, single centers, doubled centers, and outside neighbors partition N(x).
The identity holds for every vertex x and requires no prescribed number of rows. -/
theorem neighbor_partition_card_eq_degree (p q : V) (U : Finset V) (x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    rowMultiplicity G U x +
      ((G.neighborFinset x ∩ allCenters G p q U).filter
        (fun z => rowMultiplicity G U z = 1)).card +
      (G.neighborFinset x ∩ doubleCenters G p q U).card +
      (G.neighborFinset x \ (allCenters G p q U ∪ U)).card = G.degree x := by
  let X := allCenters G p q U
  let N := G.neighborFinset x
  have hdis := allCenters_disjoint_rows_of_five G p q U hpq hdegree hp hq hfive
  have hparts_disjoint : Disjoint (N ∩ X) (N ∩ U) := by
    apply Finset.disjoint_left.mpr
    intro z hzX hzU
    exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hzX).2
      (Finset.mem_inter.mp hzU).2
  have hparts := Finset.card_inter_add_card_sdiff N (X ∪ U)
  have hinter : N ∩ (X ∪ U) = (N ∩ X) ∪ (N ∩ U) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hinter, Finset.card_union_of_disjoint hparts_disjoint] at hparts
  have htypes := neighbor_center_type_card G p q U x hpq hdegree hp hq hfive
  change ((N ∩ X).filter (fun z => rowMultiplicity G U z = 1)).card +
    (N ∩ doubleCenters G p q U).card = (N ∩ X).card at htypes
  have hrows : (N ∩ U).card = rowMultiplicity G U x := rfl
  have hN : N.card = G.degree x := G.card_neighborFinset_eq_degree x
  change rowMultiplicity G U x +
    ((N ∩ X).filter (fun z => rowMultiplicity G U z = 1)).card +
    (N ∩ doubleCenters G p q U).card + (N \ (X ∪ U)).card = G.degree x
  omega

/-- The four neighbor counts together consume at most the four available incidence slots. -/
theorem neighbor_partition_le_four (p q : V) (U : Finset V) (x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    rowMultiplicity G U x +
      ((G.neighborFinset x ∩ allCenters G p q U).filter
        (fun z => rowMultiplicity G U z = 1)).card +
      (G.neighborFinset x ∩ doubleCenters G p q U).card +
      (G.neighborFinset x \ (allCenters G p q U ∪ U)).card ≤ 4 := by
  rw [neighbor_partition_card_eq_degree G p q U x hpq hdegree hp hq hfive]
  exact (G.degree_le_maxDegree x).trans hdegree


end TwinReduction
end Part19

section Part20
-- Source module: TwinDoubleNeighbors

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A row adjacent to no doubled center can be removed from the doubled-center count. -/
theorem doubleCenters_twice_card_le_rows_erase_of_unused_row (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card)
    (hunused : ∀ x ∈ doubleCenters G p q U, ¬ G.Adj u x) :
    2 * (doubleCenters G p q U).card ≤ (U.erase u).card := by
  have hdis := doubleCenters_row_pairs_disjoint G p q U hpq hdegree hp hq hfive
  have hsub : (doubleCenters G p q U).biUnion (fun x => G.neighborFinset x ∩ U)
      ⊆ U.erase u := by
    intro v hv
    obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.mp hv
    refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_inter.mp hvx).2⟩
    rintro rfl
    exact hunused x hx ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hvx).1).symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis] at hc
  have heq : ∑ x ∈ doubleCenters G p q U, (G.neighborFinset x ∩ U).card =
      2 * (doubleCenters G p q U).card := by
    calc
      ∑ x ∈ doubleCenters G p q U, (G.neighborFinset x ∩ U).card
          = ∑ _x ∈ doubleCenters G p q U, 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (Finset.mem_filter.mp hx).2
      _ = _ := by simp [Nat.mul_comm]
  rwa [heq] at hc

/-- Every actual center has at most one adjacent doubled center in a four-row configuration. -/
theorem rowCenter_adjacent_doubleCenters_card_le_one (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card) (hU : U.card = 4)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) :
    (G.neighborFinset x ∩ doubleCenters G p q U).card ≤ 1 := by
  have hD := doubleCenters_card_le_two_of_four_rows G p q U hpq hdegree hp hq hfive hU
  have hexclude (y : V) (hy : y ∈ doubleCenters G p q U) (hxy : ¬ G.Adj x y) :
      (G.neighborFinset x ∩ doubleCenters G p q U).card ≤ 1 := by
    have hsub : G.neighborFinset x ∩ doubleCenters G p q U ⊆
        (doubleCenters G p q U).erase y := by
      intro z hz
      refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_inter.mp hz).2⟩
      rintro rfl
      exact hxy ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hz).1)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy] at hc
    omega
  by_cases hxD : x ∈ doubleCenters G p q U
  · exact hexclude x hxD (G.loopless.irrefl x)
  obtain ⟨y, hcenters⟩ : ∃ y, rowCenters G p q u = {x,y} := by
    obtain ⟨a, b, _, hc⟩ := Finset.card_eq_two.mp
      (rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu (hfive u hu))
    have hx' : x = a ∨ x = b := by simpa [hc] using hx
    rcases hx' with rfl | rfl
    · exact ⟨b, hc⟩
    · exact ⟨a, hc.trans (Finset.pair_comm _ _)⟩
  by_cases hyD : y ∈ doubleCenters G p q U
  · have hmx : rowMultiplicity G U x = 1 := by
      rcases rowCenter_multiplicity_one_or_two G p q U u x hpq hdegree hp hq hu
        (hfive u hu) hx with h | h
      · exact h
      · exact False.elim (hxD (Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨u, hu, hx⟩, h⟩))
    have hmy : rowMultiplicity G U y = 2 := (Finset.mem_filter.mp hyD).2
    have hsat := row_five_saturated_of_multiplicity_sum_three G p q U u x y
      hpq hdegree hp hq hu (hfive u hu) hcenters (by omega)
    exact hexclude y hyD hsat.2.2.1
  · have hunused : ∀ z ∈ doubleCenters G p q U, ¬ G.Adj u z := by
      intro z hz huz
      obtain ⟨v, _, hzv⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hz).1
      have hzne := ((mem_rowCenters G p q v z).mp hzv).2
      have hzc : z ∈ rowCenters G p q u := (mem_rowCenters G p q u z).mpr ⟨huz, hzne⟩
      have hzxy : z = x ∨ z = y := by simpa [hcenters] using hzc
      rcases hzxy with rfl | rfl
      · exact hxD hz
      · exact hyD hz
    have hc := doubleCenters_twice_card_le_rows_erase_of_unused_row
      G p q U u hpq hdegree hp hq hfive hunused
    rw [Finset.card_erase_of_mem hu, hU] at hc
    have hsub : G.neighborFinset x ∩ doubleCenters G p q U ⊆ doubleCenters G p q U :=
      Finset.inter_subset_right
    have hb := Finset.card_le_card hsub
    omega


end TwinReduction
end Part20

section Part21
-- Source module: TwinFiveDegree

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual host edges from a center to its adjacent rows. -/
def centerSpokeEdges (U : Finset V) (x : V) : Finset (Sym2 V) :=
  (G.neighborFinset x ∩ U).map (Sym2.mkEmbedding x)

lemma centerSpokeEdges_card (U : Finset V) (x : V) :
    (centerSpokeEdges G U x).card = rowMultiplicity G U x := by
  simp [centerSpokeEdges, rowMultiplicity]

lemma mem_centerSpokeEdges {U : Finset V} {v z : V} (hv : v ∈ U) (hvz : G.Adj v z) :
    s(v,z) ∈ centerSpokeEdges G U z := by
  apply Finset.mem_map.mpr
  refine ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvz.symm, hv⟩, ?_⟩
  exact Sym2.eq_swap

/-- Every endpoint conflict belongs to a row group at x, the center group at y,
or a center group adjacent to x in the original host. -/
lemma spoke_conflict_three_way_cover (p q : V) (U : Finset V)
    (u x y v z : V) (hu : u ∈ U) (hv : v ∈ U)
    (hux : x ∈ rowCenters G p q u) (hvz : z ∈ rowCenters G p q v)
    (hcenters : rowCenters G p q u = {x,y}) (hi : G.IsIndepSet U)
    (hxU : x ∉ U) (hzU : z ∉ U)
    (e f : G.edgeSet) (he : e.val = s(u,x)) (hf : f.val = s(v,z))
    (hconf : (strongConflict G).Adj e f) :
    v ∈ G.neighborFinset x ∩ U ∨ z = y ∨ G.Adj x z := by
  have hux' := ((mem_rowCenters G p q u x).mp hux).1
  have hvz' := (mem_rowCenters G p q v z).mp hvz
  have hleft (h : G.Adj x v) : v ∈ G.neighborFinset x ∩ U :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, hv⟩
  obtain ⟨_, a, ha, b, hb, hab⟩ := (conflict_iff_endpoints G e f).mp hconf
  rw [he, Sym2.mem_iff] at ha
  rw [hf, Sym2.mem_iff] at hb
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at hab
  · rcases hab with h | h
    · exact Or.inl (hleft (h ▸ hux'.symm))
    · exact (hi hu hv h.ne h).elim
  · rcases hab with h | h
    · exact (hzU (h ▸ hu)).elim
    · have hzc : z ∈ rowCenters G p q u := (mem_rowCenters G p q u z).mpr ⟨h,hvz'.2⟩
      have hzxy : z = x ∨ z = y := by simpa [hcenters] using hzc
      rcases hzxy with rfl | hzy
      · exact Or.inl (hleft hvz'.1.symm)
      · exact Or.inr (Or.inl hzy)
  · rcases hab with h | h
    · exact (hxU (h.symm ▸ hv)).elim
    · exact Or.inl (hleft h)
  · rcases hab with h | h
    · exact Or.inl (hleft (h.symm ▸ hvz'.1.symm))
    · exact Or.inr (Or.inr h)

/-- A direct cover bound on the canonical spoke conflict graph, before splitting center types. -/
theorem spokeGraph_degree_le_row_center_sum (p q : V) (U : Finset V)
    (u x y : V) (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card)
    (hu : u ∈ U) (hcenters : rowCenters G p q u = {x,y})
    (e : ↥(spokeEdges G p q U)) (he : e.val = s(u,x)) :
    (spokeGraph G p q U).degree e + 2 ≤
      2 * rowMultiplicity G U x + rowMultiplicity G U y +
        ∑ z ∈ G.neighborFinset x ∩ U.biUnion (rowCenters G p q), rowMultiplicity G U z := by
  classical
  let R := G.neighborFinset x ∩ U
  let A := R.biUnion (rowSpokeEdges G p q)
  let B := centerSpokeEdges G U y
  let Z := G.neighborFinset x ∩ U.biUnion (rowCenters G p q)
  let C := Z.biUnion (centerSpokeEdges G U)
  let N := ((spokeGraph G p q U).neighborFinset e).image Subtype.val
  have hi := rows_independent_of_five G p q U hpq hdegree hp hq hfive
  have hx : x ∈ rowCenters G p q u := by simp [hcenters]
  have hy : y ∈ rowCenters G p q u := by simp [hcenters]
  have hux := ((mem_rowCenters G p q u x).mp hx).1
  have huy := ((mem_rowCenters G p q u y).mp hy).1
  have huR : u ∈ R := Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hux.symm, hu⟩
  have hxU : x ∉ U := fun h => Finset.disjoint_left.mp
    (rowCenters_disjoint_rows_of_five G p q U u hpq hdegree hp hq hu (hfive u hu)) hx h
  have hAsub (v : V) (hv : v ∈ R) {z : V} (hz : z ∈ rowCenters G p q v) :
      s(v,z) ∈ A := Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_map.mpr ⟨z,hz,rfl⟩⟩
  have hNsub : N ⊆ (A ∪ B).erase e.val ∪ C := by
    intro fval hfval
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hfval
    have hadj : (spokeGraph G p q U).Adj e f :=
      ((spokeGraph G p q U).mem_neighborFinset _ _).mp hf
    have hne : f.val ≠ e.val := fun h => hadj.ne (Subtype.ext h.symm)
    obtain ⟨v,hv,z,hvz,hfedge⟩ := spoke_row_center G p q U f.val f.property
    have hzU : z ∉ U := fun h => Finset.disjoint_left.mp
      (rowCenters_disjoint_rows_of_five G p q U v hpq hdegree hp hq hv (hfive v hv)) hvz h
    have hcover := spoke_conflict_three_way_cover G p q U u x y v z hu hv hx hvz
      hcenters hi hxU hzU (spokeToEdge G p q U e) (spokeToEdge G p q U f)
      he hfedge hadj
    rcases hcover with hvR | hzy | hxz
    · apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      refine ⟨hne, Finset.mem_union_left _ ?_⟩
      rw [hfedge]
      exact hAsub v hvR hvz
    · apply Finset.mem_union_left
      apply Finset.mem_erase.mpr
      refine ⟨hne, Finset.mem_union_right _ ?_⟩
      rw [hfedge, hzy]
      exact mem_centerSpokeEdges G hv (hzy ▸ ((mem_rowCenters G p q v z).mp hvz).1)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨z, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz,
        Finset.mem_biUnion.mpr ⟨v,hv,hvz⟩⟩, ?_⟩
      rw [hfedge]
      exact mem_centerSpokeEdges G hv ((mem_rowCenters G p q v z).mp hvz).1
  have hAcard : A.card = 2 * rowMultiplicity G U x := by
    have hdis : (R : Set V).PairwiseDisjoint (rowSpokeEdges G p q) := by
      intro v hv w hw hvw
      exact rowSpokeEdges_pairwiseDisjoint G p q U hi
        (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hw).2 hvw
    rw [Finset.card_biUnion hdis]
    calc
      ∑ v ∈ R, (rowSpokeEdges G p q v).card = ∑ _v ∈ R, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvU := (Finset.mem_inter.mp hv).2
        simpa [rowSpokeEdges] using
          rowCenters_card_eq_two_of_five G p q U v hpq hdegree hp hq hvU (hfive v hvU)
      _ = _ := by simp [R, rowMultiplicity, Nat.mul_comm]
  have hBcard : B.card = rowMultiplicity G U y := centerSpokeEdges_card G U y
  have hCcard : C.card ≤ ∑ z ∈ Z, rowMultiplicity G U z := by
    calc
      C.card ≤ ∑ z ∈ Z, (centerSpokeEdges G U z).card := Finset.card_biUnion_le
      _ = _ := by simp only [centerSpokeEdges_card]
  have heA : e.val ∈ A := by rw [he]; exact hAsub u huR hx
  have hmate : s(u,y) ∈ A ∩ B :=
    Finset.mem_inter.mpr ⟨hAsub u huR hy, mem_centerSpokeEdges G hu huy⟩
  have hinter : 0 < (A ∩ B).card := Finset.card_pos.mpr ⟨s(u,y), hmate⟩
  have hAB := Finset.card_union_add_card_inter A B
  have hUnionpos : 0 < (A ∪ B).card :=
    Finset.card_pos.mpr ⟨e.val, Finset.mem_union_left B heA⟩
  have herase := Finset.card_erase_of_mem (Finset.mem_union_left B heA)
  have hNcard : N.card = (spokeGraph G p q U).degree e := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact (spokeGraph G p q U).card_neighborFinset_eq_degree e
  have hNbound := (Finset.card_le_card hNsub).trans
    (Finset.card_union_le ((A ∪ B).erase e.val) C)
  change N.card ≤ ((A ∪ B).erase e.val).card + C.card at hNbound
  change (spokeGraph G p q U).degree e + 2 ≤
    2 * rowMultiplicity G U x + rowMultiplicity G U y + ∑ z ∈ Z, rowMultiplicity G U z
  omega

/-- The adjacent-center weight is exactly one per single center and two per doubled center. -/
theorem adjacent_center_multiplicity_sum (p q : V) (U : Finset V) (x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card) :
    (∑ z ∈ G.neighborFinset x ∩ U.biUnion (rowCenters G p q), rowMultiplicity G U z) =
      ((G.neighborFinset x ∩ U.biUnion (rowCenters G p q)).filter
        (fun z => rowMultiplicity G U z = 1)).card +
      2 * (G.neighborFinset x ∩ doubleCenters G p q U).card := by
  classical
  let Z := G.neighborFinset x ∩ U.biUnion (rowCenters G p q)
  have htypes (z : V) (hz : z ∈ Z) :
      rowMultiplicity G U z = 1 ∨ rowMultiplicity G U z = 2 := by
    obtain ⟨v,hv,hvz⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hz).2
    exact rowCenter_multiplicity_one_or_two G p q U v z hpq hdegree hp hq hv
      (hfive v hv) hvz
  have hZ2 : Z.filter (fun z => ¬ rowMultiplicity G U z = 1) =
      G.neighborFinset x ∩ doubleCenters G p q U := by
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      have hr2 : rowMultiplicity G U z = 2 := (htypes z hz'.1).resolve_left hz'.2
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz'.1).1,
        Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hz'.1).2,hr2⟩⟩
    · intro hz
      have hz' := Finset.mem_inter.mp hz
      have hzD := Finset.mem_filter.mp hz'.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hz'.1,hzD.1⟩, by omega⟩
  have hsum1 : (∑ z ∈ Z.filter (fun z => rowMultiplicity G U z = 1), rowMultiplicity G U z) =
      (Z.filter (fun z => rowMultiplicity G U z = 1)).card := by
    calc
      (∑ z ∈ Z.filter (fun z => rowMultiplicity G U z = 1), rowMultiplicity G U z) =
          ∑ _z ∈ Z.filter (fun z => rowMultiplicity G U z = 1), 1 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact (Finset.mem_filter.mp hz).2
      _ = _ := by simp
  have hsum2 : (∑ z ∈ Z.filter (fun z => ¬ rowMultiplicity G U z = 1), rowMultiplicity G U z) =
      2 * (G.neighborFinset x ∩ doubleCenters G p q U).card := by
    rw [hZ2]
    calc
      (∑ z ∈ G.neighborFinset x ∩ doubleCenters G p q U, rowMultiplicity G U z) =
          ∑ _z ∈ G.neighborFinset x ∩ doubleCenters G p q U, 2 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
      _ = _ := by simp [Nat.mul_comm]
  have hsplit := Finset.sum_filter_add_sum_filter_not Z
    (fun z => rowMultiplicity G U z = 1) (rowMultiplicity G U)
  rw [hsum1, hsum2] at hsplit
  exact hsplit.symm

/-- The actual canonical T5 spoke degree bound in terms of single and doubled neighboring centers. -/
theorem spokeGraph_degree_le_five_center_types (p q : V) (U : Finset V)
    (u x y : V) (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card)
    (hu : u ∈ U) (hcenters : rowCenters G p q u = {x,y})
    (e : ↥(spokeEdges G p q U)) (he : e.val = s(u,x)) :
    (spokeGraph G p q U).degree e + 2 ≤
      2 * rowMultiplicity G U x + rowMultiplicity G U y +
      ((G.neighborFinset x ∩ U.biUnion (rowCenters G p q)).filter
        (fun z => rowMultiplicity G U z = 1)).card +
      2 * (G.neighborFinset x ∩ doubleCenters G p q U).card := by
  have hbound := spokeGraph_degree_le_row_center_sum G p q U u x y hpq hdegree hp hq
    hfive hu hcenters e he
  rw [adjacent_center_multiplicity_sum G p q U x hpq hdegree hp hq hfive] at hbound
  simpa only [Nat.add_assoc] using hbound



end TwinReduction
end Part21

section Part22
-- Source module: TwinWeakSpokes

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual spokes oriented from a multiplicity-one center with a multiplicity-two row mate. -/
noncomputable def weakSpokes (p q : V) (U : Finset V) : Finset ↥(spokeEdges G p q U) :=
  Finset.univ.filter (fun e => ∃ u ∈ U, ∃ x y,
    rowCenters G p q u = {x,y} ∧ e.val = s(u,x) ∧
      rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 2)

lemma mem_weakSpokes (p q : V) (U : Finset V) (e : ↥(spokeEdges G p q U)) :
    e ∈ weakSpokes G p q U ↔ ∃ u ∈ U, ∃ x y,
      rowCenters G p q u = {x,y} ∧ e.val = s(u,x) ∧
        rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 2 := by
  simp [weakSpokes]

/-- A row has at most one spoke of type (1,2), even when centers are shared between rows. -/
lemma weak_spoke_unique_at_row (p q : V) (U : Finset V) (u : V)
    (e f : ↥(spokeEdges G p q U))
    (he : ∃ x y, rowCenters G p q u = {x,y} ∧ e.val = s(u,x) ∧
      rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 2)
    (hf : ∃ x y, rowCenters G p q u = {x,y} ∧ f.val = s(u,x) ∧
      rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 2) : e = f := by
  obtain ⟨x,y,hc,he,hrx,_⟩ := he
  obtain ⟨z,w,hc',hf,_,hrw⟩ := hf
  have hxc : x ∈ rowCenters G p q u := by simp [hc]
  have hxzw : x = z ∨ x = w := by simpa [hc'] using hxc
  have hxz : x = z := by
    rcases hxzw with h | h
    · exact h
    · have : rowMultiplicity G U x = 2 := h ▸ hrw
      omega
  apply Subtype.ext
  rw [he, hf, hxz]

/-- The exceptional actual-spoke set has at most one member per row. -/
theorem weakSpokes_card_le_rows (p q : V) (U : Finset V) :
    (weakSpokes G p q U).card ≤ U.card := by
  classical
  let W : V → Finset ↥(spokeEdges G p q U) := fun u => Finset.univ.filter (fun e =>
    ∃ x y, rowCenters G p q u = {x,y} ∧ e.val = s(u,x) ∧
      rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 2)
  have hWcard (u : V) : (W u).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    exact weak_spoke_unique_at_row G p q U u e f (Finset.mem_filter.mp he).2
      (Finset.mem_filter.mp hf).2
  have hsub : weakSpokes G p q U ⊆ U.biUnion W := by
    intro e he
    obtain ⟨u,hu,hw⟩ := (mem_weakSpokes G p q U e).mp he
    exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩⟩
  calc
    (weakSpokes G p q U).card ≤ (U.biUnion W).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ U, (W u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, 1 := Finset.sum_le_sum (fun u _ => hWcard u)
    _ = U.card := by simp

theorem weakSpokes_card_le_four (p q : V) (U : Finset V) (hU : U.card = 4) :
    (weakSpokes G p q U).card ≤ 4 := by
  simpa [hU] using weakSpokes_card_le_rows G p q U

/-- With a specified actual row orientation, failure to be exceptional excludes type (1,2). -/
theorem not_weakSpokes_not_one_two (p q : V) (U : Finset V) (u x y : V)
    (e : ↥(spokeEdges G p q U)) (hu : u ∈ U)
    (hcenters : rowCenters G p q u = {x,y}) (he : e.val = s(u,x))
    (hweak : e ∉ weakSpokes G p q U) :
    ¬ (rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 2) := by
  intro h
  exact hweak ((mem_weakSpokes G p q U e).mpr ⟨u,hu,x,y,hcenters,he,h⟩)

/-- Every nonexceptional orientation has type (1,1) or (2,1). -/
theorem not_weakSpokes_multiplicity_cases (p q : V) (U : Finset V) (u x y : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card)
    (e : ↥(spokeEdges G p q U)) (hu : u ∈ U)
    (hcenters : rowCenters G p q u = {x,y}) (he : e.val = s(u,x))
    (hweak : e ∉ weakSpokes G p q U) :
    (rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 1) ∨
      (rowMultiplicity G U x = 2 ∧ rowMultiplicity G U y = 1) := by
  have hx : x ∈ rowCenters G p q u := by simp [hcenters]
  have hy : y ∈ rowCenters G p q u := by simp [hcenters]
  have hmx := rowCenter_multiplicity_one_or_two G p q U u x hpq hdegree hp hq hu
    (hfive u hu) hx
  have hmy := rowCenter_multiplicity_one_or_two G p q U u y hpq hdegree hp hq hu
    (hfive u hu) hy
  have hsum := row_five_multiplicity_sum_le_three G p q U u x y hdegree hcenters (hfive u hu)
  have hnot := not_weakSpokes_not_one_two G p q U u x y e hu hcenters he hweak
  omega

/-- Every actual nonexceptional spoke admits an orientation in one of the two remaining types. -/
theorem not_weakSpokes_exists_orientation (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (hfive : ∀ v ∈ U, 5 ≤ (rowSeen G p q U v).card)
    (e : ↥(spokeEdges G p q U)) (hweak : e ∉ weakSpokes G p q U) :
    ∃ u ∈ U, ∃ x y, rowCenters G p q u = {x,y} ∧ e.val = s(u,x) ∧
      ((rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 1) ∨
        (rowMultiplicity G U x = 2 ∧ rowMultiplicity G U y = 1)) := by
  obtain ⟨u,hu,x,hx,he⟩ := spoke_row_center G p q U e.val e.property
  obtain ⟨y,hcenters⟩ : ∃ y, rowCenters G p q u = {x,y} := by
    obtain ⟨a,b,_,hc⟩ := Finset.card_eq_two.mp
      (rowCenters_card_eq_two_of_five G p q U u hpq hdegree hp hq hu (hfive u hu))
    have hx' : x = a ∨ x = b := by simpa [hc] using hx
    rcases hx' with rfl | rfl
    · exact ⟨b,hc⟩
    · exact ⟨a,hc.trans (Finset.pair_comm _ _)⟩
  exact ⟨u,hu,x,y,hcenters,he,not_weakSpokes_multiplicity_cases G p q U u x y hpq
    hdegree hp hq hfive e hu hcenters he hweak⟩


end TwinReduction
end Part22

section Part23
-- Source module: TwinFiveCase

namespace TwinReduction

open SimpleGraph Finset StructuralAttack
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual five-case list inequalities in each of the three oriented center types. -/
theorem five_actual_oriented_ratios (p q : V) (U : Finset V) (hUcard : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ v ∈ U, T ⊆ (rowSeen G p q U v).image c)
    (e : ↥(spokeEdges G p q U)) (u x y : V) (hu : u ∈ U)
    (hcenters : rowCenters G p q u = {x,y}) (he : e.val = s(u,x)) :
    (rowMultiplicity G U x = 1 → rowMultiplicity G U y = 1 →
      2 * ((spokeGraph G p q U).degree e + 1) ≤
        (availableColors G p q U (spokeToEdge G p q U e) c).card) ∧
    (rowMultiplicity G U x = 2 → rowMultiplicity G U y = 1 →
      2 * ((spokeGraph G p q U).degree e + 1) ≤
        (availableColors G p q U (spokeToEdge G p q U e) c).card) ∧
    (rowMultiplicity G U x = 1 → rowMultiplicity G U y = 2 →
      9 * ((spokeGraph G p q U).degree e + 1) ≤
        5 * (availableColors G p q U (spokeToEdge G p q U e) c).card) := by
  classical
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  have hx : x ∈ rowCenters G p q u := by simp [hcenters]
  let X := U.biUnion (rowCenters G p q)
  let a1 := ((G.neighborFinset x ∩ X).filter (fun z => rowMultiplicity G U z = 1)).card
  let a2 := (G.neighborFinset x ∩ doubleCenters G p q U).card
  let b := (G.neighborFinset x \ (X ∪ U)).card
  let r := rowMultiplicity G U x
  let s := rowMultiplicity G U y
  let A := (availableColors G p q U (spokeToEdge G p q U e) c).card
  let d := (spokeGraph G p q U).degree e
  have hlist := five_available_card_lower G p q U u x y hpq hdegree hp hq hu hcenters c T hT hcommon
  have hedge : spokeToEdge G p q U e = ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ :=
    Subtype.ext he
  rw [← hedge] at hlist
  change 15 ≤ A + (if r + s = 3 then 0 else 1) + a1 + 3 * b at hlist
  have hpart := neighbor_partition_le_four G p q U x hpq hdegree hp hq hfive
  change r + a1 + a2 + b ≤ 4 at hpart
  have hd := spokeGraph_degree_le_five_center_types G p q U u x y hpq hdegree hp hq
    hfive hu hcenters e he
  change d + 2 ≤ 2 * r + s + a1 + 2 * a2 at hd
  have ha2 := rowCenter_adjacent_doubleCenters_card_le_one G p q U u x hpq hdegree hp hq
    hfive hUcard hu hx
  change a2 ≤ 1 at ha2
  change (r = 1 → s = 1 → 2 * (d + 1) ≤ A) ∧
    (r = 2 → s = 1 → 2 * (d + 1) ≤ A) ∧
    (r = 1 → s = 2 → 9 * (d + 1) ≤ 5 * A)
  refine ⟨?_, ?_, ?_⟩
  · intro hr hs
    simp only [hr,hs,reduceIte,Nat.reduceAdd,Nat.reduceEqDiff] at hlist
    omega
  · intro hr hs
    simp only [hr,hs,reduceIte,Nat.reduceAdd] at hlist
    omega
  · intro hr hs
    simp only [hr,hs,reduceIte,Nat.reduceAdd] at hlist
    omega

/-- Weak actual spokes satisfy the 9/5 list ratio; all other spokes satisfy ratio two. -/
theorem five_actual_list_ratios (p q : V) (U : Finset V) (hUcard : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ v ∈ U, T ⊆ (rowSeen G p q U v).image c)
    (e : ↥(spokeEdges G p q U)) :
    (e ∈ weakSpokes G p q U → 9 * ((spokeGraph G p q U).degree e + 1) ≤
      5 * (availableColors G p q U (spokeToEdge G p q U e) c).card) ∧
    (e ∉ weakSpokes G p q U → 2 * ((spokeGraph G p q U).degree e + 1) ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card) := by
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  constructor
  · intro heweak
    obtain ⟨u,hu,x,y,hcenters,he,hr,hs⟩ := (mem_weakSpokes G p q U e).mp heweak
    exact (five_actual_oriented_ratios G p q U hUcard hpq hdegree hp hq c T hT hcommon
      e u x y hu hcenters he).2.2 hr hs
  · intro heweak
    obtain ⟨u,hu,x,y,hcenters,he,htype⟩ :=
      not_weakSpokes_exists_orientation G p q U hpq hdegree hp hq hfive e heweak
    have hratios := five_actual_oriented_ratios G p q U hUcard hpq hdegree hp hq
      c T hT hcommon e u x y hu hcenters he
    rcases htype with ⟨hr,hs⟩ | ⟨hr,hs⟩
    · exact hratios.1 hr hs
    · exact hratios.2.1 hr hs

/-- Both actual ratio bounds imply the degree slack needed after selecting an independent pair. -/
theorem five_actual_list_slack (p q : V) (U : Finset V) (hUcard : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ v ∈ U, T ⊆ (rowSeen G p q U v).image c)
    (e : ↥(spokeEdges G p q U)) :
    (spokeGraph G p q U).degree e + 2 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card := by
  have h := five_actual_list_ratios G p q U hUcard hpq hdegree hp hq c T hT hcommon e
  by_cases he : e ∈ weakSpokes G p q U
  · have := h.1 he
    omega
  · have := h.2 he
    omega

/-- Complete the five-common-color case on the actual host spokes and the eight cells.
The row labels use exactly `Finset.equivFinOfCardEq hUcard`, matching the whole-host merge. -/
theorem five_case_actual_completion (p q : V) (U : Finset V) (hUcard : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hinter : ∀ a, a ∈ T ↔ ∀ u ∈ U, a ∈ (rowSeen G p q U u).image c) :
    ∃ qcolor : (spokeGraph G p q U).Coloring (Fin 20),
      (∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c) ∧
      (Finset.univ.image qcolor).card ≤ 7 ∧
      ∃ f : Fin 4 × Fin 2 → Fin 20, Function.Injective f ∧
        ∀ v, f v ∉ Finset.univ.image qcolor ∧
          f v ∉ (rowSeen G p q U ((Finset.equivFinOfCardEq hUcard).symm v.1).val).image c := by
  classical
  have hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c := by
    intro u hu a ha
    exact (hinter a).mp ha u hu
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  have hcard := spokeEdges_card_eq_eight G p q U hUcard hpq hdegree hp hq hfive
  let H8 := spokeGraph8 G p q U hcard
  let iso : H8 ≃g spokeGraph G p q U := spokeGraph8Iso G p q U hcard
  let A : Fin 8 → Finset (Fin 20) := fun i =>
    availableColors G p q U (spokeToEdge G p q U (iso i)) c
  let E : Finset (Fin 8) := (weakSpokes G p q U).image iso.symm
  let rowEquiv : ↥U ≃ Fin 4 := Finset.equivFinOfCardEq hUcard
  let F : Fin 4 → Finset (Fin 20) := fun i =>
    (rowSeen G p q U (rowEquiv.symm i).val).image c
  have hE : E.card ≤ 4 := by
    rw [Finset.card_image_of_injective _ iso.symm.injective]
    exact weakSpokes_card_le_four G p q U hUcard
  have hEi (i : Fin 8) : i ∈ E ↔ iso i ∈ weakSpokes G p q U := by
    constructor
    · intro hi
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
      simpa using he
    · intro hi
      exact Finset.mem_image.mpr ⟨iso i,hi,iso.symm_apply_apply i⟩
  have hF : ∀ i, (F i).card ≤ 6 := by
    intro i
    exact row_colors_card_le_six G p q U (rowEquiv.symm i).val hpq hdegree hp hq
      (rowEquiv.symm i).property c
  have hFinter : ∀ a, a ∈ T ↔ ∀ i, a ∈ F i := by
    intro a
    constructor
    · intro ha i
      exact (hinter a).mp ha (rowEquiv.symm i).val (rowEquiv.symm i).property
    · intro ha
      apply (hinter a).mpr
      intro u hu
      have := ha (rowEquiv ⟨u,hu⟩)
      simpa [F] using this
  have hA : ∀ i, A i ⊆ Finset.univ \ T := fun i =>
    actual_spoke_list_avoids_common G p q U c T hcommon (iso i)
  have hslack : ∀ i, H8.degree i + 2 ≤ (A i).card := by
    intro i
    have h := five_actual_list_slack G p q U hUcard hpq hdegree hp hq c T hT hcommon (iso i)
    rw [iso.degree_eq i] at h
    exact h
  have hexception : ∀ i ∈ E, 9 * (H8.degree i + 1) ≤ 5 * (A i).card := by
    intro i hi
    have h := (five_actual_list_ratios G p q U hUcard hpq hdegree hp hq c T hT hcommon
      (iso i)).1 ((hEi i).mp hi)
    rw [iso.degree_eq i] at h
    exact h
  have hregular : ∀ i ∉ E, 2 * (H8.degree i + 1) ≤ (A i).card := by
    intro i hi
    have h := (five_actual_list_ratios G p q U hUcard hpq hdegree hp hq c T hT hcommon
      (iso i)).2 (fun h => hi ((hEi i).mpr h))
    rw [iso.degree_eq i] at h
    exact h
  obtain ⟨q8,hq8,hused,f,hf,havoid⟩ := complete_five_intersection H8 T hT F hF hFinter
    A hA E hE hslack hexception hregular
  let qcolor : (spokeGraph G p q U).Coloring (Fin 20) := q8.comp iso.symm.toHom
  have hcompatible : ∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c := by
    intro e
    change q8 (iso.symm e) ∈ availableColors G p q U (spokeToEdge G p q U e) c
    simpa [A] using hq8 (iso.symm e)
  have himage : Finset.univ.image qcolor = Finset.univ.image q8 := by
    ext a
    constructor
    · intro ha
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨iso.symm e,Finset.mem_univ _,rfl⟩
    · intro ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨iso i,Finset.mem_univ _,by simp [qcolor]⟩
  refine ⟨qcolor,hcompatible,?_,f,hf,?_⟩
  · rw [himage]
    exact hused
  · intro v
    rw [himage]
    exact havoid v


end TwinReduction
end Part23

section Part24
-- Source module: TwinGlue

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [DecidableEq V]

/-- The row coordinate used by both Hall assignments and actual cell edges. -/
noncomputable def cellRow (U : Finset V) (hU : U.card = 4) (i : Fin 4) : V :=
  ((Finset.equivFinOfCardEq hU).symm i).val

omit [DecidableEq V] in
theorem cellRow_mem (U : Finset V) (hU : U.card = 4) (i : Fin 4) :
    cellRow U hU i ∈ U := ((Finset.equivFinOfCardEq hU).symm i).property

omit [DecidableEq V] in
theorem cellRow_injective (U : Finset V) (hU : U.card = 4) :
    Function.Injective (cellRow U hU) := by
  intro i j hij
  exact (Finset.equivFinOfCardEq hU).symm.injective (Subtype.ext hij)

def cellColumn (p q : V) (j : Fin 2) : V := if j = 0 then p else q

omit [DecidableEq V] in
theorem cellColumn_injective (p q : V) (hpq : p ≠ q) :
    Function.Injective (cellColumn p q) := by
  intro i j hij
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact hi.trans hj.symm
  · exact (hpq (by simpa [cellColumn,hi,hj] using hij)).elim
  · exact (hpq (by simpa [cellColumn,hi,hj] using hij.symm)).elim
  · omega

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
theorem cellColumn_neighborhood (p q : V) (U : Finset V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (j : Fin 2) : ∀ v, G.Adj (cellColumn p q j) v ↔ v ∈ U := by
  intro v
  by_cases hj : j = 0
  · simpa [cellColumn,hj] using hp v
  · simpa [cellColumn,hj] using hq v

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
theorem cellColumn_not_row (p q : V) (U : Finset V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (j : Fin 2) : cellColumn p q j ∉ U := by
  intro h
  exact G.loopless.irrefl _ ((cellColumn_neighborhood G p q U hp hq j _).mpr h)

/-- The eight actual edges of the complete two-by-four twin cell. -/
noncomputable def cellEdge (p q : V) (U : Finset V) (hU : U.card = 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (z : Fin 4 × Fin 2) : G.edgeSet :=
  ⟨s(cellColumn p q z.2,cellRow U hU z.1),
    (cellColumn_neighborhood G p q U hp hq z.2 _).mpr (cellRow_mem U hU z.1)⟩

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
theorem cellEdge_injective (p q : V) (U : Finset V) (hU : U.card = 4) (hpq : p ≠ q)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U) :
    Function.Injective (cellEdge G p q U hU hp hq) := by
  intro z w hzw
  have heq := congrArg (fun e : G.edgeSet => e.val) hzw
  change s(cellColumn p q z.2,cellRow U hU z.1) =
    s(cellColumn p q w.2,cellRow U hU w.1) at heq
  have hr : cellRow U hU z.1 ∈ s(cellColumn p q w.2,cellRow U hU w.1) := by
    rw [← heq]
    exact Sym2.mem_mk_right _ _
  have hc : cellColumn p q z.2 ∈ s(cellColumn p q w.2,cellRow U hU w.1) := by
    rw [← heq]
    exact Sym2.mem_mk_left _ _
  have hrows : cellRow U hU z.1 = cellRow U hU w.1 := by
    rcases Sym2.mem_iff.mp hr with hr | hr
    · exact ((cellColumn_not_row G p q U hp hq w.2) (hr ▸ cellRow_mem U hU z.1)).elim
    · exact hr
  have hcols : cellColumn p q z.2 = cellColumn p q w.2 := by
    rcases Sym2.mem_iff.mp hc with hc | hc
    · exact hc
    · exact ((cellColumn_not_row G p q U hp hq z.2) (hc.symm ▸ cellRow_mem U hU w.1)).elim
  exact Prod.ext (cellRow_injective U hU hrows) (cellColumn_injective p q hpq hcols)

noncomputable def cellEmbedding (p q : V) (U : Finset V) (hU : U.card = 4) (hpq : p ≠ q)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U) :
    (Fin 4 × Fin 2) ↪ G.edgeSet where
  toFun := cellEdge G p q U hU hp hq
  inj' := cellEdge_injective G p q U hU hpq hp hq

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
theorem cellEdge_incident_twin (p q : V) (U : Finset V) (hU : U.card = 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (z : Fin 4 × Fin 2) :
    p ∈ (cellEdge G p q U hU hp hq z).val ∨ q ∈ (cellEdge G p q U hU hp hq z).val := by
  by_cases hz : z.2 = 0
  · left
    simp [cellEdge,cellColumn,hz]
  · right
    simp [cellEdge,cellColumn,hz]

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- The cell enumeration covers precisely the host edges incident with either twin. -/
theorem cellEdge_covers (p q : V) (U : Finset V) (hU : U.card = 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (e : G.edgeSet) :
    (p ∈ e.val ∨ q ∈ e.val) ↔ ∃ z, cellEdge G p q U hU hp hq z = e := by
  constructor
  · rintro (hpe | hqe)
    · obtain ⟨u,he⟩ := Sym2.mem_iff_exists.mp hpe
      have hpu : G.Adj p u := by simpa only [he,SimpleGraph.mem_edgeSet] using e.property
      let u' : U := ⟨u,(hp u).mp hpu⟩
      refine ⟨((Finset.equivFinOfCardEq hU) u',0),Subtype.ext ?_⟩
      simp [cellEdge,cellRow,cellColumn,u',he]
    · obtain ⟨u,he⟩ := Sym2.mem_iff_exists.mp hqe
      have hqu : G.Adj q u := by simpa only [he,SimpleGraph.mem_edgeSet] using e.property
      let u' : U := ⟨u,(hq u).mp hqu⟩
      refine ⟨((Finset.equivFinOfCardEq hU) u',1),Subtype.ext ?_⟩
      simp [cellEdge,cellRow,cellColumn,u',he]
  · rintro ⟨z,rfl⟩
    exact cellEdge_incident_twin G p q U hU hp hq z

theorem cellEdge_not_spoke (p q : V) (U : Finset V) (hU : U.card = 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (z : Fin 4 × Fin 2) : (cellEdge G p q U hU hp hq z).val ∉ spokeEdges G p q U := by
  intro hs
  have h := (mem_spokeEdges G p q U _).mp hs
  rcases cellEdge_incident_twin G p q U hU hp hq z with hp | hq
  · exact h.2.1 hp
  · exact h.2.2.1 hq

theorem cellEdge_not_fixed (p q : V) (U : Finset V) (hU : U.card = 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (z : Fin 4 × Fin 2) : (cellEdge G p q U hU hp hq z).val ∉ fixedEdges G p q U := by
  intro hs
  have h := (mem_fixedEdges G p q U _).mp hs
  rcases cellEdge_incident_twin G p q U hU hp hq z with hp | hq
  · exact h.2.1 hp
  · exact h.2.2.1 hq

theorem spoke_not_fixed (p q : V) (U : Finset V) (e : Sym2 V)
    (hs : e ∈ spokeEdges G p q U) : e ∉ fixedEdges G p q U := by
  intro hf
  obtain ⟨u,hu,hue⟩ := ((mem_spokeEdges G p q U e).mp hs).2.2.2
  exact ((mem_fixedEdges G p q U e).mp hf).2.2.2 u hue hu

/-- Every actual edge is a cell edge, a retained spoke, or a fixed edge. -/
theorem twin_edge_partition (p q : V) (U : Finset V) (hU : U.card = 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (e : G.edgeSet) :
    (∃ z, cellEdge G p q U hU hp hq z = e) ∨
      e.val ∈ spokeEdges G p q U ∨ e.val ∈ fixedEdges G p q U := by
  by_cases ht : p ∈ e.val ∨ q ∈ e.val
  · exact Or.inl ((cellEdge_covers G p q U hU hp hq e).mp ht)
  have hnot := not_or.mp ht
  by_cases hs : e.val ∈ spokeEdges G p q U
  · exact Or.inr (Or.inl hs)
  apply Or.inr ∘ Or.inr
  apply (mem_fixedEdges G p q U e.val).mpr
  refine ⟨e.property,hnot.1,hnot.2,?_⟩
  intro u hue hu
  exact hs ((mem_spokeEdges G p q U e.val).mpr ⟨e.property,hnot.1,hnot.2,u,hu,hue⟩)

/-- Canonical conflicts between a cell edge and fixed edges are exactly its row exclusions. -/
theorem cellEdge_fixed_conflict (p q : V) (U : Finset V) (hU : U.card = 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (z : Fin 4 × Fin 2) (e : G.edgeSet) (he : e.val ∈ fixedEdges G p q U) :
    (strongConflict G).Adj (cellEdge G p q U hU hp hq z) e ↔
      e.val ∈ rowSeen G p q U (cellRow U hU z.1) := by
  have hfixed := (mem_fixedEdges G p q U e.val).mp he
  have hcol : cellColumn p q z.2 ∉ e.val := by
    by_cases hz : z.2 = 0
    · simpa [cellColumn,hz] using hfixed.2.1
    · simpa [cellColumn,hz] using hfixed.2.2.1
  rw [mem_rowSeen,and_iff_right he]
  exact fixed_row_conflict G (cellColumn p q z.2) (cellRow U hU z.1) (U : Set V)
    (cellColumn_neighborhood G p q U hp hq z.2) (cellRow_mem U hU z.1) e hcol hfixed.2.2.2

/-- Merge compatible assignments for the actual cell, spoke, and fixed host edges.
Every resulting conflict is checked in the canonical strongConflict G. -/
theorem glue_twin_coloring (p q : V) (U : Finset V) (hU : U.card = 4) (hpq : p ≠ q)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (havailable : ∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c)
    (f : Fin 4 × Fin 2 → Fin 20) (hfinj : Function.Injective f)
    (havoid : ∀ v, f v ∉ Finset.univ.image qcolor ∧
      f v ∉ (rowSeen G p q U (cellRow U hU v.1)).image c) :
    ∃ C : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → C e = c e.val := by
  classical
  let index : (e : G.edgeSet) → (p ∈ e.val ∨ q ∈ e.val) → Fin 4 × Fin 2 :=
    fun e he => Classical.choose ((cellEdge_covers G p q U hU hp hq e).mp he)
  have hindex : ∀ e he, cellEdge G p q U hU hp hq (index e he) = e :=
    fun e he => Classical.choose_spec ((cellEdge_covers G p q U hU hp hq e).mp he)
  let paint : G.edgeSet → Fin 20 := fun e =>
    if ht : p ∈ e.val ∨ q ∈ e.val then f (index e ht)
    else if hs : e.val ∈ spokeEdges G p q U then qcolor ⟨e.val,hs⟩
    else c e.val
  have hpaint_cell : ∀ z, paint (cellEdge G p q U hU hp hq z) = f z := by
    intro z
    have hz := cellEdge_incident_twin G p q U hU hp hq z
    have hi : index (cellEdge G p q U hU hp hq z) hz = z :=
      cellEdge_injective G p q U hU hpq hp hq (hindex _ hz)
    simp [paint,hz,hi]
  have hpaint_spoke : ∀ (e : G.edgeSet) (hs : e.val ∈ spokeEdges G p q U),
      paint e = qcolor ⟨e.val,hs⟩ := by
    intro e hs
    have he := (mem_spokeEdges G p q U e.val).mp hs
    have ht : ¬(p ∈ e.val ∨ q ∈ e.val) := not_or.mpr ⟨he.2.1,he.2.2.1⟩
    simp [paint,ht,hs]
  have hpaint_fixed : ∀ (e : G.edgeSet), e.val ∈ fixedEdges G p q U → paint e = c e.val := by
    intro e he
    have hh := (mem_fixedEdges G p q U e.val).mp he
    have ht : ¬(p ∈ e.val ∨ q ∈ e.val) := not_or.mpr ⟨hh.2.1,hh.2.2.1⟩
    have hs : e.val ∉ spokeEdges G p q U := fun hs => spoke_not_fixed G p q U e.val hs he
    simp [paint,ht,hs]
  have hcompat : ∀ (s : ↥(spokeEdges G p q U)) (e : G.edgeSet),
      e.val ∈ fixedEdges G p q U → (strongConflict G).Adj (spokeToEdge G p q U s) e →
        c e.val ≠ qcolor s := by
    intro s
    exact (mem_availableColors G p q U (spokeToEdge G p q U s) c (qcolor s)).mp (havailable s)
  have hproper : ∀ {e g : G.edgeSet}, (strongConflict G).Adj e g → paint e ≠ paint g := by
    intro e g hadj
    rcases twin_edge_partition G p q U hU hp hq e with ⟨z,rfl⟩ | he | he <;>
      rcases twin_edge_partition G p q U hU hp hq g with ⟨w,rfl⟩ | hg | hg
    · rw [hpaint_cell z,hpaint_cell w]
      exact fun h => hadj.ne (congrArg (cellEdge G p q U hU hp hq) (hfinj h))
    · rw [hpaint_cell z,hpaint_spoke g hg]
      intro h
      exact (havoid z).1 (Finset.mem_image.mpr ⟨⟨g.val,hg⟩,Finset.mem_univ _,h.symm⟩)
    · rw [hpaint_cell z,hpaint_fixed g hg]
      intro h
      exact (havoid z).2 (Finset.mem_image.mpr ⟨g.val,
        (cellEdge_fixed_conflict G p q U hU hp hq z g hg).mp hadj,h.symm⟩)
    · rw [hpaint_spoke e he,hpaint_cell w]
      intro h
      exact (havoid w).1 (Finset.mem_image.mpr ⟨⟨e.val,he⟩,Finset.mem_univ _,h⟩)
    · rw [hpaint_spoke e he,hpaint_spoke g hg]
      exact qcolor.valid (show (spokeGraph G p q U).Adj ⟨e.val,he⟩ ⟨g.val,hg⟩ from hadj)
    · rw [hpaint_spoke e he,hpaint_fixed g hg]
      exact (hcompat ⟨e.val,he⟩ g hg hadj).symm
    · rw [hpaint_fixed e he,hpaint_cell w]
      intro h
      exact (havoid w).2 (Finset.mem_image.mpr ⟨e.val,
        (cellEdge_fixed_conflict G p q U hU hp hq w e he).mp hadj.symm,h⟩)
    · rw [hpaint_fixed e he,hpaint_spoke g hg]
      exact hcompat ⟨g.val,hg⟩ e he hadj.symm
    · rw [hpaint_fixed e he,hpaint_fixed g hg]
      have he' := (mem_fixedEdges G p q U e.val).mp he
      have hg' := (mem_fixedEdges G p q U g.val).mp hg
      exact hc e g he'.2.1 he'.2.2.1 hg'.2.1 hg'.2.2.1 hadj
  exact ⟨Coloring.mk paint hproper,hpaint_fixed⟩


end TwinReduction
end Part24

section Part25
-- Source module: TwinExtension

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every retained twenty-coloring extends across degree-four false twins,
allowing changes only to spokes and preserving every other retained edge. -/
theorem twenty_color_twin_extension (p q : V) (U : Finset V) (hU : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c) :
    ∃ C : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → C e = c e.val := by
  classical
  let T : Finset (Fin 20) := univ.filter (fun a => ∀ u ∈ U, a ∈ (rowSeen G p q U u).image c)
  have hinter : ∀ a, a ∈ T ↔ ∀ u ∈ U, a ∈ (rowSeen G p q U u).image c := by simp [T]
  have hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c := by
    intro u hu a ha
    exact (hinter a).mp ha u hu
  let F : Fin 4 → Finset (Fin 20) := fun i => (rowSeen G p q U (cellRow U hU i)).image c
  have hF : ∀ i, (F i).card ≤ 6 := fun i =>
    row_colors_card_le_six G p q U (cellRow U hU i) hpq hdegree hp hq (cellRow_mem U hU i) c
  have hTcard : T.card ≤ 6 :=
    (card_le_card (hcommon (cellRow U hU 0) (cellRow_mem U hU 0))).trans (hF 0)
  by_cases hsmall : T.card ≤ 4
  · let q0 := originalSpokeColoring G p q U c hc
    have hC : (univ.image q0).card ≤ 8 :=
      originalSpokeColoring_used_card_le_eight G p q U c hc hU hpq hdegree hp hq
    have hfinite : ∀ a, a ∈ T ↔ ∀ i, a ∈ F i := by
      intro a
      rw [hinter]
      constructor
      · intro ha i
        exact ha (cellRow U hU i) (cellRow_mem U hU i)
      · intro ha u hu
        simpa [F, cellRow] using ha ((Finset.equivFinOfCardEq hU) ⟨u,hu⟩)
    obtain ⟨f, hf, havoid⟩ := small_common_cell_assignment (univ.image q0) T F hC hsmall hF hfinite
    exact glue_twin_coloring G p q U hU hpq hp hq c hc q0
      (originalSpokeColoring_mem_available G p q U c hc) f hf havoid
  · have hcases : T.card = 5 ∨ T.card = 6 := by omega
    rcases hcases with hfive | hsix
    · obtain ⟨qcolor, hqcolor, _, f, hf, havoid⟩ :=
        five_case_actual_completion G p q U hU hpq hdegree hp hq c T hfive hinter
      exact glue_twin_coloring G p q U hU hpq hp hq c hc qcolor hqcolor f hf havoid
    · obtain ⟨qcolor, hqcolor, _, f, hf, havoid⟩ :=
        six_case_actual_completion G p q U hU hpq hdegree hp hq c T hsix hcommon
      apply glue_twin_coloring G p q U hU hpq hp hq c hc qcolor hqcolor f hf
      intro v
      refine ⟨(havoid v).2, ?_⟩
      rw [row_colors_eq_common_of_six G p q U (cellRow U hU v.1) hpq hdegree hp hq
        (cellRow_mem U hU v.1) c T hsix (hcommon _ (cellRow_mem U hU v.1))]
      exact (havoid v).1


end TwinReduction
end Part25

section Part26
-- Source module: InducedConflict

namespace TwinReduction

open SimpleGraph StructuralAttack

/-- Induced embeddings preserve and reflect canonical strong conflicts.
In particular, deleting vertices preserves every conflict between retained edges. -/
theorem embedded_conflict_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (e g : G.edgeSet) :
    (strongConflict H).Adj (f.mapEdgeSet e) (f.mapEdgeSet g) ↔
      (strongConflict G).Adj e g := by
  rw [conflict_iff_endpoints, conflict_iff_endpoints]
  constructor
  · rintro ⟨hne, x, hx, y, hy, hxy⟩
    change x ∈ Sym2.map f e.val at hx
    change y ∈ Sym2.map f g.val at hy
    obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Sym2.mem_map.mp hy
    refine ⟨fun he => hne (congrArg f.mapEdgeSet he), u, hu, v, hv, ?_⟩
    rcases hxy with he | ha
    · exact Or.inl (f.injective he)
    · exact Or.inr (f.map_adj_iff.mp ha)
  · rintro ⟨hne, u, hu, v, hv, huv⟩
    refine ⟨fun he => hne (f.mapEdgeSet.injective he), f u, ?_, f v, ?_, ?_⟩
    · exact Sym2.mem_map.mpr ⟨u, hu, rfl⟩
    · exact Sym2.mem_map.mpr ⟨v, hv, rfl⟩
    · rcases huv with he | ha
      · exact Or.inl (congrArg f he)
      · exact Or.inr (f.map_adj_iff.mpr ha)

def strongConflictEmbedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) : strongConflict G ↪g strongConflict H where
  toFun := f.mapEdgeSet
  inj' := f.mapEdgeSet.injective
  map_rel_iff' := embedded_conflict_iff f _ _


end TwinReduction
end Part26

section Part27
-- Source module: TwinVertexDeletion

namespace TwinReduction

open SimpleGraph Finset StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every host edge avoiding the deleted vertices comes from the induced graph. -/
lemma retained_edge_from_induce (p q : V) (e : G.edgeSet)
    (hep : p ∉ e.val) (heq : q ∉ e.val) :
    ∃ f : (G.induce {v | v ≠ p ∧ v ≠ q}).edgeSet,
      (SimpleGraph.Embedding.induce (G := G) {v | v ≠ p ∧ v ≠ q}).mapEdgeSet f = e := by
  obtain ⟨x, y, hxy⟩ := Sym2.exists.mp (show ∃ s : Sym2 V, s = e.val from ⟨e.val, rfl⟩)
  have hxmem : x ∈ e.val := by rw [← hxy]; exact Sym2.mem_mk_left _ _
  have hymem : y ∈ e.val := by rw [← hxy]; exact Sym2.mem_mk_right _ _
  have hx : x ≠ p ∧ x ≠ q := ⟨fun h => hep (h ▸ hxmem), fun h => heq (h ▸ hxmem)⟩
  have hy : y ≠ p ∧ y ≠ q := ⟨fun h => hep (h ▸ hymem), fun h => heq (h ▸ hymem)⟩
  have hadj : G.Adj x y := by simpa only [← hxy, SimpleGraph.mem_edgeSet] using e.property
  refine ⟨⟨s(⟨x, hx⟩, ⟨y, hy⟩), hadj⟩, Subtype.ext ?_⟩
  exact hxy

/-- An induced strong coloring extends to a total edge-color function that is proper
on all retained host edges, and agrees with the input on every induced edge. -/
theorem retainedProper_from_induced_coloring (p q : V)
    (g : (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Coloring (Fin 20)) :
    ∃ c : Sym2 V → Fin 20, RetainedProper G p q c ∧
      ∀ e : (G.induce {v | v ≠ p ∧ v ≠ q}).edgeSet,
        c ((SimpleGraph.Embedding.induce (G := G) {v | v ≠ p ∧ v ≠ q}).mapEdgeSet e).val = g e := by
  classical
  let emb := SimpleGraph.Embedding.induce (G := G) {v | v ≠ p ∧ v ≠ q}
  let f : (G.induce {v | v ≠ p ∧ v ≠ q}).edgeSet → Sym2 V :=
    fun e => (emb.mapEdgeSet e).val
  have hf : Function.Injective f := Subtype.val_injective.comp emb.mapEdgeSet.injective
  let c : Sym2 V → Fin 20 := Function.extend f g (fun _ => 0)
  have hagree (e) : c (f e) = g e := hf.extend_apply g (fun _ => 0) e
  refine ⟨c, ?_, hagree⟩
  intro e k hep heq hkp hkq hek
  obtain ⟨e', he'⟩ := retained_edge_from_induce G p q e hep heq
  obtain ⟨k', hk'⟩ := retained_edge_from_induce G p q k hkp hkq
  change emb.mapEdgeSet e' = e at he'
  change emb.mapEdgeSet k' = k at hk'
  have hconf : (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Adj e' k' := by
    apply (embedded_conflict_iff emb e' k').mp
    simpa only [he', hk'] using hek
  have hecolor : c e.val = g e' := by rw [← he']; exact hagree e'
  have hkcolor : c k.val = g k' := by rw [← hk']; exact hagree k'
  rw [hecolor, hkcolor]
  exact g.valid hconf

/-- Delete the twins, color the induced graph, and extend while preserving every fixed edge. -/
theorem twenty_color_twin_extension_from_induce (p q : V) (U : Finset V) (hU : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U)
    (g : (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Coloring (Fin 20)) :
    ∃ C : (strongConflict G).Coloring (Fin 20),
      ∀ e : (G.induce {v | v ≠ p ∧ v ≠ q}).edgeSet,
        ((SimpleGraph.Embedding.induce (G := G) {v | v ≠ p ∧ v ≠ q}).mapEdgeSet e).val ∈
          fixedEdges G p q U →
        C ((SimpleGraph.Embedding.induce (G := G) {v | v ≠ p ∧ v ≠ q}).mapEdgeSet e) = g e := by
  obtain ⟨c, hc, hagree⟩ := retainedProper_from_induced_coloring G p q g
  obtain ⟨C, hC⟩ := twenty_color_twin_extension G p q U hU hpq hdegree hp hq c hc
  exact ⟨C, fun e he => (hC _ he).trans (hagree e)⟩

/-- Strong twenty-colorability of the induced vertex deletion suffices for the whole host. -/
theorem twenty_color_twin_vertex_deletion (p q : V) (U : Finset V) (hU : U.card = 4)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U) (hq : ∀ v, G.Adj q v ↔ v ∈ U) :
    (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Colorable 20 →
      (strongConflict G).Colorable 20 := by
  rintro ⟨g⟩
  obtain ⟨C, _⟩ := twenty_color_twin_extension_from_induce G p q U hU hpq hdegree hp hq g
  exact ⟨C⟩


end TwinReduction
end Part27

open StructuralAttack

open scoped Classical in
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ p q : Fin n, ∀ U : Finset (Fin n),
    U.card = 4 → p ≠ q → G.maxDegree ≤ 4 →
    (∀ v, G.Adj p v ↔ v ∈ U) → (∀ v, G.Adj q v ↔ v ∈ U) →
    (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Colorable 20 →
      (strongConflict G).Colorable 20

/-- Degree-four false twins are reducible for strong twenty-colorability. -/
theorem proof : statement := by
  classical
  intro n G p q U hU hpq hdegree hp hq
  exact TwinReduction.twenty_color_twin_vertex_deletion G p q U hU hpq hdegree hp hq

#print axioms proof

end Submissions.Erdos149FalseTwinDeletion.Savcab

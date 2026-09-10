import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Submissions.Erdos149K23Deletion.Savcab

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
-- Source module: K23LocalCounts

namespace K23Reduction

open SimpleGraph Finset TwinReduction
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two distinct known neighbors leave at most two other neighbors.
No exact neighborhood equation is required. -/
theorem rowCenters_card_le_two_of_common (p q u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hpu : G.Adj p u) (hqu : G.Adj q u) :
    (rowCenters G p q u).card ≤ 2 := by
  have hsub : {p,q} ⊆ G.neighborFinset u := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact (G.mem_neighborFinset _ _).mpr hpu.symm
    · have h := mem_singleton.mp hx
      subst x
      exact (G.mem_neighborFinset u q).mpr hqu.symm
  have hd := (G.degree_le_maxDegree u).trans hdegree
  rw [rowCenters, card_sdiff_of_subset hsub, G.card_neighborFinset_eq_degree,
    card_pair hpq]
  omega

/-- The generic row-incidence bound applies to any row adjacent to both roots. -/
theorem rowSeen_card_le_six_of_common (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u) :
    (rowSeen G p q U u).card ≤ 6 := by
  have hcenters := rowCenters_card_le_two_of_common G p q u hpq hdegree hpu hqu
  have hrow := rowSeen_card_le_three_mul_centers G p q U u hdegree hu
  omega

/-- Color images have the same upper bound, without any coloring-properness premise. -/
theorem row_colors_card_le_six_of_common {C : Type*} [DecidableEq C]
    (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u) (c : Sym2 V → C) :
    ((rowSeen G p q U u).image c).card ≤ 6 :=
  card_image_le.trans (rowSeen_card_le_six_of_common G p q U u hpq hdegree hu hpu hqu)

/-- Counting at most two spokes per row remains valid when row-row edges occur. -/
theorem spokeEdges_card_le_two_mul_rows (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u) :
    (spokeEdges G p q U).card ≤ 2 * U.card := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  rw [spokeEdges_eq_biUnion G p q U hpU hqU]
  calc
    (U.biUnion (rowSpokeEdges G p q)).card ≤ ∑ u ∈ U, (rowSpokeEdges G p q u).card :=
      card_biUnion_le
    _ ≤ ∑ _u ∈ U, 2 := by
      apply sum_le_sum
      intro u hu
      simpa [rowSpokeEdges] using
        rowCenters_card_le_two_of_common G p q u hpq hdegree (hp u hu) (hq u hu)
    _ = 2 * U.card := by simp [Nat.mul_comm]

/-- Three common rows give at most six actual retained spokes. -/
theorem spokeEdges_card_le_six_of_common (p q : V) (U : Finset V)
    (hUcard : U.card = 3) (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u) :
    (spokeEdges G p q U).card ≤ 6 := by
  simpa [hUcard] using spokeEdges_card_le_two_mul_rows G p q U hpq hdegree hp hq

/-- At a neighbor of p, the excluded edge pa consumes one incidence slot. -/
theorem fixedAt_card_le_three_of_adj_left (p q : V) (U : Finset V) (a : V)
    (hdegree : G.maxDegree ≤ 4) (hpa : G.Adj p a) :
    (fixedAt G p q U a).card ≤ 3 := by
  have hsub : fixedAt G p q U a ⊆ (G.incidenceFinset a).erase s(p,a) := by
    intro e he
    refine mem_erase.mpr ⟨?_, fixedAt_subset_incidence G p q U a he⟩
    intro h
    have hf := (mem_fixedEdges G p q U e).mp (mem_filter.mp he).1
    apply hf.2.1
    rw [h]
    exact Sym2.mem_mk_left _ _
  have hmem : s(p,a) ∈ G.incidenceFinset a := by
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hpa]
  have hd := (G.degree_le_maxDegree a).trans hdegree
  have hc := card_le_card hsub
  rw [card_erase_of_mem hmem, G.card_incidenceFinset_eq_degree] at hc
  omega

/-- The exceptional fixed-color bound also holds for an arbitrary color function. -/
theorem fixedAt_colors_card_le_three_of_adj_left {C : Type*} [DecidableEq C]
    (p q : V) (U : Finset V) (a : V) (hdegree : G.maxDegree ≤ 4)
    (hpa : G.Adj p a) (c : Sym2 V → C) :
    ((fixedAt G p q U a).image c).card ≤ 3 :=
  card_image_le.trans (fixedAt_card_le_three_of_adj_left G p q U a hdegree hpa)

/-- The actual initial spoke coloring uses at most six colors for three common rows. -/
theorem originalSpokeColoring_used_card_le_six (p q : V) (U : Finset V)
    (hUcard : U.card = 3) (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c) :
    (univ.image (originalSpokeColoring G p q U c hc)).card ≤ 6 := by
  rw [originalSpokeColoring_image]
  exact card_image_le.trans
    (spokeEdges_card_le_six_of_common G p q U hUcard hpq hdegree hp hq)


end K23Reduction
end Part8

section Part9
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
end Part9

section Part10
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
end Part10

section Part11
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
end Part11

section Part12
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
end Part12

section Part13
-- Source module: K23FiveGeometry

namespace K23Reduction

open SimpleGraph Finset TwinReduction StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Five seen fixed edges force two centers even when the roots have other neighbors. -/
theorem five_rowCenters_card_of_common (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (hfive : 5 ≤ (rowSeen G p q U u).card) :
    (rowCenters G p q u).card = 2 := by
  have := rowCenters_card_le_two_of_common G p q u hpq hdegree hpu hqu
  have := rowSeen_card_le_three_mul_centers G p q U u hdegree hu
  omega

/-- A five-edge row has two outside centers, each of positive multiplicity,
with total row multiplicity at most three. -/
theorem row_five_geometry_of_common (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (hfive : 5 ≤ (rowSeen G p q U u).card) :
    ∃ x y, x ≠ y ∧ rowCenters G p q u = {x,y} ∧ x ∉ U ∧ y ∉ U ∧
      0 < rowMultiplicity G U x ∧ 0 < rowMultiplicity G U y ∧
      rowMultiplicity G U x + rowMultiplicity G U y ≤ 3 := by
  obtain ⟨x,y,hxy,hc⟩ := card_eq_two.mp
    (five_rowCenters_card_of_common G p q U u hpq hdegree hu hpu hqu hfive)
  have hx : x ∈ rowCenters G p q u := by simp [hc]
  have hy : y ∈ rowCenters G p q u := by simp [hc]
  have hux := ((mem_rowCenters G p q u x).mp hx).1
  have huy := ((mem_rowCenters G p q u y).mp hy).1
  have hax := fixedAt_card_le_three G p q U hdegree hu hux
  have hay := fixedAt_card_le_three G p q U hdegree hu huy
  have heq : rowSeen G p q U u = fixedAt G p q U x ∪ fixedAt G p q U y := by
    simp [rowSeen, hc]
  have hunion := card_union_le (fixedAt G p q U x) (fixedAt G p q U y)
  rw [← heq] at hunion
  have hxU : x ∉ U := by
    intro hxU
    rw [fixedAt_eq_empty_of_row G p q U hxU, card_empty] at hunion
    omega
  have hyU : y ∉ U := by
    intro hyU
    rw [fixedAt_eq_empty_of_row G p q U hyU, card_empty] at hunion
    omega
  exact ⟨x,y,hxy,hc,hxU,hyU,rowMultiplicity_pos_of_adj G hu hux,
    rowMultiplicity_pos_of_adj G hu huy,
    row_five_multiplicity_sum_le_three G p q U u x y hdegree hc hfive⟩

/-- Every actual center is outside the rows and belongs to either one or two rows. -/
theorem allCenters_five_geometry_of_common (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card)
    {x : V} (hx : x ∈ U.biUnion (rowCenters G p q)) :
    x ∉ U ∧ (rowMultiplicity G U x = 1 ∨ rowMultiplicity G U x = 2) := by
  obtain ⟨u,hu,hxu⟩ := mem_biUnion.mp hx
  obtain ⟨a,b,_,hc,haU,hbU,hma,hmb,hms⟩ :=
    row_five_geometry_of_common G p q U u hpq hdegree hu (hp u hu) (hq u hu) (hfive u hu)
  have hxpair : x = a ∨ x = b := by simpa [hc] using hxu
  rcases hxpair with rfl | rfl
  · exact ⟨haU, by omega⟩
  · exact ⟨hbU, by omega⟩

theorem five_rows_independent_of_common (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) : G.IsIndepSet U := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  intro u hu v hv _ huv
  have hvc : v ∈ rowCenters G p q u := (mem_rowCenters G p q u v).mpr
    ⟨huv, fun h => hpU (h ▸ hv), fun h => hqU (h ▸ hv)⟩
  exact (allCenters_five_geometry_of_common G p q U hpq hdegree hp hq hfive
    (mem_biUnion.mpr ⟨u,hu,hvc⟩)).1 hv

/-- Shared centers do not identify the two spokes with different row endpoints. -/
theorem five_spokeEdges_card (p q : V) (U : Finset V) (hUcard : U.card = 3)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    (spokeEdges G p q U).card = 6 := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  have hi := five_rows_independent_of_common G p q U hpq hdegree hp hq hfive
  rw [spokeEdges_eq_biUnion G p q U hpU hqU,
    card_biUnion (rowSpokeEdges_pairwiseDisjoint G p q U hi)]
  calc
    ∑ u ∈ U, (rowSpokeEdges G p q u).card = ∑ _u ∈ U, 2 := by
      apply sum_congr rfl
      intro u hu
      simpa [rowSpokeEdges] using
        five_rowCenters_card_of_common G p q U u hpq hdegree hu (hp u hu) (hq u hu)
          (hfive u hu)
    _ = 6 := by simp [hUcard]

theorem five_spokeGraph_no_isolated (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    ∀ e : ↥(spokeEdges G p q U), ∃ f, (spokeGraph G p q U).Adj e f := by
  intro e
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  obtain ⟨u,hu,x,hx,he⟩ := spoke_row_center G p q U e.val e.property
  have hc := five_rowCenters_card_of_common G p q U u hpq hdegree hu
    (hp u hu) (hq u hu) (hfive u hu)
  have hpos : 0 < ((rowCenters G p q u).erase x).card := by
    rw [card_erase_of_mem hx, hc]
    decide
  obtain ⟨y,hy⟩ := card_pos.mp hpos
  have hyx := (mem_erase.mp hy).1
  let f : ↥(spokeEdges G p q U) :=
    ⟨s(u,y), row_center_is_spoke G p q U hpU hqU hu (mem_of_mem_erase hy)⟩
  have hne : e ≠ f := by
    intro hef
    have hs : s(u,x) = s(u,y) := by simpa only [he] using congrArg Subtype.val hef
    exact hyx ((Sym2.mkEmbedding u).injective hs).symm
  refine ⟨f, spokeGraph_adj_of_common_endpoint G p q U e f hne u ?_ (Sym2.mem_mk_left _ _)⟩
  rw [he]
  exact Sym2.mem_mk_left _ _

/-- Two doubled centers cannot meet one row; only common adjacencies are used. -/
theorem five_row_not_two_double_centers (p q : V) (U : Finset V) (u x y : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (hfive : 5 ≤ (rowSeen G p q U u).card)
    (hx : x ∈ rowCenters G p q u) (hy : y ∈ rowCenters G p q u) (hxy : x ≠ y) :
    ¬ (rowMultiplicity G U x = 2 ∧ rowMultiplicity G U y = 2) := by
  have hcard := five_rowCenters_card_of_common G p q U u hpq hdegree hu hpu hqu hfive
  have hsub : {x,y} ⊆ rowCenters G p q u := by
    simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hx hy
  have hc : rowCenters G p q u = {x,y} := by
    apply (eq_of_subset_of_card_le hsub _).symm
    simp [hcard, card_pair hxy]
  have := row_five_multiplicity_sum_le_three G p q U u x y hdegree hc hfive
  omega

theorem five_doubleCenters_row_pairs_disjoint (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    (doubleCenters G p q U : Set V).PairwiseDisjoint (fun x => G.neighborFinset x ∩ U) := by
  intro x hx y hy hxy
  apply Finset.disjoint_left.mpr
  intro u hux huy
  have hx' := mem_filter.mp hx
  have hy' := mem_filter.mp hy
  obtain ⟨v,_,hxv⟩ := mem_biUnion.mp hx'.1
  obtain ⟨w,_,hyw⟩ := mem_biUnion.mp hy'.1
  have hxne := ((mem_rowCenters G p q v x).mp hxv).2
  have hyne := ((mem_rowCenters G p q w y).mp hyw).2
  have hu := (mem_inter.mp hux).2
  have hxcent : x ∈ rowCenters G p q u := (mem_rowCenters G p q u x).mpr
    ⟨((G.mem_neighborFinset _ _).mp (mem_inter.mp hux).1).symm, hxne⟩
  have hycent : y ∈ rowCenters G p q u := (mem_rowCenters G p q u y).mpr
    ⟨((G.mem_neighborFinset _ _).mp (mem_inter.mp huy).1).symm, hyne⟩
  exact five_row_not_two_double_centers G p q U u x y hpq hdegree hu (hp u hu) (hq u hu)
    (hfive u hu) hxcent hycent hxy ⟨hx'.2,hy'.2⟩

/-- With three common rows there is at most one doubled center. -/
theorem five_doubleCenters_card_le_one (p q : V) (U : Finset V) (hUcard : U.card = 3)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card) :
    (doubleCenters G p q U).card ≤ 1 := by
  have hdis := five_doubleCenters_row_pairs_disjoint G p q U hpq hdegree hp hq hfive
  have hsub : (doubleCenters G p q U).biUnion (fun x => G.neighborFinset x ∩ U) ⊆ U := by
    intro u hu
    obtain ⟨x,_,hux⟩ := mem_biUnion.mp hu
    exact (mem_inter.mp hux).2
  have hc := card_le_card hsub
  rw [card_biUnion hdis] at hc
  have heq : ∑ x ∈ doubleCenters G p q U, (G.neighborFinset x ∩ U).card =
      2 * (doubleCenters G p q U).card := by
    calc
      ∑ x ∈ doubleCenters G p q U, (G.neighborFinset x ∩ U).card
          = ∑ _x ∈ doubleCenters G p q U, 2 := by
            apply sum_congr rfl
            intro x hx
            exact (mem_filter.mp hx).2
      _ = _ := by simp [Nat.mul_comm]
  rw [heq, hUcard] at hc
  omega

/-- Total center multiplicity three saturates the five-edge row bound. -/
theorem five_row_saturated_of_sum_three (p q : V) (U : Finset V) (u x y : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (hfive : 5 ≤ (rowSeen G p q U u).card)
    (hcenters : rowCenters G p q u = {x,y})
    (hsum : rowMultiplicity G U x + rowMultiplicity G U y = 3) :
    (fixedAt G p q U x).card = 4 - rowMultiplicity G U x ∧
      (fixedAt G p q U y).card = 4 - rowMultiplicity G U y ∧
      ¬ G.Adj x y ∧ (rowSeen G p q U u).card = 5 := by
  have hbx := fixedAt_card_add_rowMultiplicity_le_four G p q U x hdegree
  have hby := fixedAt_card_add_rowMultiplicity_le_four G p q U y hdegree
  have heq : rowSeen G p q U u = fixedAt G p q U x ∪ fixedAt G p q U y := by
    simp [rowSeen, hcenters]
  have hunion := card_union_le (fixedAt G p q U x) (fixedAt G p q U y)
  rw [← heq] at hunion
  obtain ⟨a,b,_,hc,haU,hbU,_,_,_⟩ :=
    row_five_geometry_of_common G p q U u hpq hdegree hu hpu hqu hfive
  have hout : ∀ z ∈ rowCenters G p q u, z ∉ U := by
    intro z hz
    have hzab : z = a ∨ z = b := by simpa [hc] using hz
    rcases hzab with rfl | rfl
    · exact haU
    · exact hbU
  have hxU := hout x (by simp [hcenters])
  have hyU := hout y (by simp [hcenters])
  refine ⟨by omega, by omega, ?_, by omega⟩
  intro hxy
  have := rowSeen_card_add_multiplicities_le_seven_of_adjacent
    G p q U u x y hdegree hcenters hxU hyU hxy
  omega

theorem five_row_extra_colors_le_one (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : T ⊆ (rowSeen G p q U u).image c) :
    ((rowSeen G p q U u).image c \ T).card ≤ 1 := by
  have hc := row_colors_card_le_six_of_common G p q U u hpq hdegree hu hpu hqu c
  rw [card_sdiff_of_subset hcommon, hT]
  omega

theorem five_center_extra_colors_le_one (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u) (hx : x ∈ rowCenters G p q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : T ⊆ (rowSeen G p q U u).image c) :
    ((fixedAt G p q U x).image c \ T).card ≤ 1 := by
  have hcolors := fixedAt_colors_subset_row G p q U u x hx c
  have hsub : (fixedAt G p q U x).image c \ T ⊆ (rowSeen G p q U u).image c \ T := by
    intro a ha
    exact mem_sdiff.mpr ⟨hcolors (mem_sdiff.mp ha).1,(mem_sdiff.mp ha).2⟩
  exact (card_le_card hsub).trans
    (five_row_extra_colors_le_one G p q U u hpq hdegree hu hpu hqu c T hT hcommon)

theorem five_row_colors_eq_common_of_double_center (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u) (hx : x ∈ rowCenters G p q u)
    (hdouble : rowMultiplicity G U x = 2)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : T ⊆ (rowSeen G p q U u).image c) :
    (rowSeen G p q U u).image c = T := by
  have hfive : 5 ≤ (rowSeen G p q U u).card := by
    calc
      5 = T.card := hT.symm
      _ ≤ ((rowSeen G p q U u).image c).card := card_le_card hcommon
      _ ≤ (rowSeen G p q U u).card := card_image_le
  obtain ⟨a,b,_,hc,_,_,hapos,hbpos,hle⟩ :=
    row_five_geometry_of_common G p q U u hpq hdegree hu hpu hqu hfive
  have hsum : rowMultiplicity G U a + rowMultiplicity G U b = 3 := by
    have hxab : x = a ∨ x = b := by simpa [hc] using hx
    rcases hxab with rfl | rfl <;> omega
  have hseen := (five_row_saturated_of_sum_three G p q U u a b hpq hdegree hu
    hpu hqu hfive hc hsum).2.2.2
  apply (eq_of_subset_of_card_le hcommon ?_).symm
  calc
    ((rowSeen G p q U u).image c).card ≤ (rowSeen G p q U u).card := card_image_le
    _ = 5 := hseen
    _ = T.card := hT.symm

/-- The actual five-color list count, with all geometric excess premises discharged
using common adjacencies; no retained-coloring properness is needed for this bound. -/
theorem five_available_card_lower_of_common (p q : V) (U : Finset V) (u x y : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v ∈ U, G.Adj p v) (hq : ∀ v ∈ U, G.Adj q v)
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
        · exact five_row_colors_eq_common_of_double_center G p q U u x hpq hdegree hu
            (hp u hu) (hq u hu) hx hd c T hT (hcommon u hu)
        · exact five_row_colors_eq_common_of_double_center G p q U u y hpq hdegree hu
            (hp u hu) (hq u hu) hy hd c T hT (hcommon u hu)
      simp [hroweq]
    · rw [if_neg hsum]
      exact five_row_extra_colors_le_one G p q U u hpq hdegree hu (hp u hu) (hq u hu)
        c T hT (hcommon u hu)
  · intro z hz
    have hzX := (mem_inter.mp hz).2
    have hm := (allCenters_five_geometry_of_common G p q U hpq hdegree hp hq hfive hzX).2
    obtain ⟨v,hv,hzv⟩ := mem_biUnion.mp hzX
    rcases hm with hsingle | hdouble
    · rw [if_pos hsingle]
      exact five_center_extra_colors_le_one G p q U v z hpq hdegree hv (hp v hv) (hq v hv)
        hzv c T hT (hcommon v hv)
    · rw [if_neg (by omega)]
      have hsub := fixedAt_colors_subset_row G p q U v z hzv c
      rw [five_row_colors_eq_common_of_double_center G p q U v z hpq hdegree hv
        (hp v hv) (hq v hv) hzv hdouble c T hT (hcommon v hv)] at hsub
      simp [sdiff_eq_empty_iff_subset.mpr hsub]


end K23Reduction
end Part13

section Part14
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
end Part14

section Part15
-- Source module: K23FivePrivate

namespace K23Reduction

open SimpleGraph Finset TwinReduction StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Independent rows and private centers leave only a common row or an actual
center-center edge as possible connectors between conflicting spokes. -/
theorem private_spoke_conflict_rows_or_centers (p q : V) (U : Finset V)
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
theorem five_private_spoke_degree_le_one_add_center_neighbors (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v ∈ U, G.Adj p v) (hq : ∀ v ∈ U, G.Adj q v)
    (hfive : ∀ u ∈ U, 5 ≤ (rowSeen G p q U u).card)
    (hprivate : ∀ x ∈ U.biUnion (rowCenters G p q), rowMultiplicity G U x = 1)
    (e : ↥(spokeEdges G p q U)) (u x : V)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) (he : e.val = s(u,x)) :
    (spokeGraph G p q U).degree e ≤
      1 + (G.neighborFinset x ∩ U.biUnion (rowCenters G p q)).card := by
  classical
  let X := U.biUnion (rowCenters G p q)
  have hgeom : ∀ z ∈ X, z ∉ U ∧ rowMultiplicity G U z = 1 :=
    fun z hz => ⟨(allCenters_five_geometry_of_common G p q U hpq hdegree hp hq hfive hz).1,
      hprivate z hz⟩
  have hi := five_rows_independent_of_common G p q U hpq hdegree hp hq hfive
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
    have hclass := private_spoke_conflict_rows_or_centers G p q U hi e f u x (row f) (center f)
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
  have hrowCard := five_rowCenters_card_of_common G p q U u hpq hdegree hu (hp u hu) (hq u hu) (hfive u hu)
  have hmate : ((rowCenters G p q u).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hx,hrowCard]
  have hsum := Finset.card_union_le ((rowCenters G p q u).erase x) (G.neighborFinset x ∩ X)
  change (spokeGraph G p q U).degree e ≤ 1 + (G.neighborFinset x ∩ X).card
  omega

open scoped Classical in
/-- When all actual centers are private, every spoke has degree at most four and
at least twice its spoke degree plus three available colors in the full host. -/
theorem five_private_spoke_list_bound (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c)
    (hprivate : ∀ x ∈ U.biUnion (rowCenters G p q), rowMultiplicity G U x = 1)
    (e : ↥(spokeEdges G p q U)) :
    (spokeGraph G p q U).degree e ≤ 4 ∧
      2 * (spokeGraph G p q U).degree e + 3 ≤
        (availableColors G p q U (spokeToEdge G p q U e) c).card := by
  classical
  let X := U.biUnion (rowCenters G p q)
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  obtain ⟨u,hu,x,hx,he⟩ := spoke_row_center G p q U e.val e.property
  let C := G.neighborFinset x ∩ X
  let B := G.neighborFinset x \ (X ∪ U)
  have hdeg := five_private_spoke_degree_le_one_add_center_neighbors G p q U
    hpq hdegree hp hq hfive hprivate e u x hu hx he
  have hux := ((mem_rowCenters G p q u x).mp hx).1
  have huN : u ∈ G.neighborFinset x := (G.mem_neighborFinset x u).mpr hux.symm
  have huC : u ∉ C := by
    intro h
    have huX := (mem_inter.mp h).2
    exact (allCenters_five_geometry_of_common G p q U hpq hdegree hp hq hfive huX).1 hu
  have hdis : Disjoint (insert u C) B := by
    apply Finset.disjoint_left.mpr
    intro z hz hzB
    have hn := (mem_sdiff.mp hzB).2
    rcases mem_insert.mp hz with rfl | hz
    · exact hn (mem_union_right _ hu)
    · exact hn (mem_union_left _ (mem_inter.mp hz).2)
  have hsub : insert u C ∪ B ⊆ G.neighborFinset x := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · rcases mem_insert.mp hz with rfl | hz
      · exact huN
      · exact (mem_inter.mp hz).1
    · exact (mem_sdiff.mp hz).1
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hdis, card_insert_of_notMem huC,
    G.card_neighborFinset_eq_degree] at hcount
  have hg := (G.degree_le_maxDegree x).trans hdegree
  have hrow := five_row_extra_colors_le_one G p q U u hpq hdegree hu (hp u hu) (hq u hu)
    c T hT (hcommon u hu)
  have hX : ∀ z ∈ G.neighborFinset x ∩ X,
      ((fixedAt G p q U z).image c \ T).card ≤
        if rowMultiplicity G U z = 1 then 1 else 0 := by
    intro z hz
    have hzX := (mem_inter.mp hz).2
    rw [if_pos (hprivate z hzX)]
    obtain ⟨v,hv,hzv⟩ := mem_biUnion.mp hzX
    exact five_center_extra_colors_le_one G p q U v z hpq hdegree hv (hp v hv) (hq v hv)
      hzv c T hT (hcommon v hv)
  have hlist := five_available_count G p q U X u x hu hx hdegree c T hT 1 hrow hX
  have hfilter : (G.neighborFinset x ∩ X).filter
      (fun z => rowMultiplicity G U z = 1) = G.neighborFinset x ∩ X := by
    apply filter_eq_self.mpr
    intro z hz
    exact hprivate z (mem_inter.mp hz).2
  rw [hfilter] at hlist
  have hedge : spokeToEdge G p q U e = ⟨s(u,x),hux⟩ := Subtype.ext he
  rw [← hedge] at hlist
  change (spokeGraph G p q U).degree e ≤ 1 + C.card at hdeg
  change (availableColors G p q U (spokeToEdge G p q U e) c).card + 1 +
    C.card + 3 * B.card ≥ 15 at hlist
  constructor <;> omega


end K23Reduction
end Part15

section Part16
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
end Part16

section Part17
-- Source module: K23PairCompression

namespace K23Reduction

open SimpleGraph Finset

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- Assign a common available color on an independent set and greedily
complete the other vertices, avoiding that color there. -/
theorem one_set_list_completion (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : V → Finset C) (hslack : ∀ v, G.degree v + 2 ≤ (L v).card)
    (A : Finset V) (hiA : G.IsIndepSet A) (c : C) (hc : ∀ v ∈ A, c ∈ L v) :
    ∃ f : G.Coloring C, (∀ v, f v ∈ L v) ∧ (∀ v ∈ A, f v = c) ∧
      (univ.image f).card ≤ 1 + (univ \ A).card := by
  classical
  let : Nonempty C := ⟨c⟩
  let K : V → Finset C := fun v => (L v).erase c
  have hK : ∀ v, G.degree v < (K v).card := by
    intro v
    have h := hslack v
    have he := pred_card_le_card_erase (s := L v) (a := c)
    dsimp only [K]
    omega
  obtain ⟨g, hg⟩ := Palette.list_coloring_of_degree_lt G K hK
  have hgC : ∀ v, g v ≠ c := fun v => (mem_erase.mp (hg v)).1
  let paint : V → C := fun v => if v ∈ A then c else g v
  have hproper : ∀ {v w}, G.Adj v w → paint v ≠ paint w := by
    intro v w h
    by_cases hv : v ∈ A <;> by_cases hw : w ∈ A
    · exact (hiA hv hw h.ne h).elim
    · simpa [paint, hv, hw] using (hgC w).symm
    · simpa [paint, hv, hw] using hgC v
    · simpa [paint, hv, hw] using g.valid h
  refine ⟨Coloring.mk paint hproper, ?_, ?_, ?_⟩
  · intro v
    change paint v ∈ L v
    by_cases hv : v ∈ A
    · simpa [paint, hv] using hc v hv
    · simpa [paint, hv] using (mem_erase.mp (hg v)).2
  · intro v hv
    change paint v = c
    simp [paint, hv]
  · change (univ.image paint).card ≤ 1 + (univ \ A).card
    have hsub : univ.image paint ⊆ insert c ((univ \ A).image g) := by
      intro x hx
      obtain ⟨v, _, rfl⟩ := mem_image.mp hx
      by_cases hv : v ∈ A
      · simp [paint, hv]
      · have hm : v ∈ univ \ A := mem_sdiff.mpr ⟨mem_univ _, hv⟩
        simpa [paint, hv] using mem_insert_of_mem (b := c) (mem_image_of_mem g hm)
    have h1 := card_le_card hsub
    have h2 := card_insert_le c ((univ \ A).image g)
    have h3 := card_image_le (s := univ \ A) (f := g)
    omega

/-- Assign two distinct colors on disjoint independent sets, then complete
while avoiding both colors on all remaining vertices. -/
theorem two_set_list_completion (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : V → Finset C) (hslack : ∀ v, G.degree v + 3 ≤ (L v).card)
    (A B : Finset V) (hdis : Disjoint A B)
    (hiA : G.IsIndepSet A) (hiB : G.IsIndepSet B)
    (c d : C) (hcd : c ≠ d) (hc : ∀ v ∈ A, c ∈ L v) (hd : ∀ v ∈ B, d ∈ L v) :
    ∃ f : G.Coloring C, (∀ v, f v ∈ L v) ∧ (∀ v ∈ A, f v = c) ∧
      (∀ v ∈ B, f v = d) ∧ (univ.image f).card ≤ 2 + (univ \ (A ∪ B)).card := by
  classical
  let : Nonempty C := ⟨c⟩
  let K : V → Finset C := fun v => ((L v).erase c).erase d
  have hK : ∀ v, G.degree v < (K v).card := by
    intro v
    have h := hslack v
    have he := pred_card_le_card_erase (s := L v) (a := c)
    have he' := pred_card_le_card_erase (s := (L v).erase c) (a := d)
    dsimp only [K]
    omega
  obtain ⟨g, hg⟩ := Palette.list_coloring_of_degree_lt G K hK
  have hgC : ∀ v, g v ≠ c := fun v => (mem_erase.mp (mem_erase.mp (hg v)).2).1
  have hgD : ∀ v, g v ≠ d := fun v => (mem_erase.mp (hg v)).1
  let paint : V → C := fun v => if v ∈ A then c else if v ∈ B then d else g v
  have hproper : ∀ {v w}, G.Adj v w → paint v ≠ paint w := by
    intro v w h
    by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A <;>
      by_cases hvB : v ∈ B <;> by_cases hwB : w ∈ B <;>
      simp only [paint, hvA, hwA, hvB, hwB, if_pos]
    all_goals first
      | exact (hiA hvA hwA h.ne h).elim
      | exact (hiB hvB hwB h.ne h).elim
      | exact hcd
      | exact hcd.symm
      | exact (hgC w).symm
      | exact hgC v
      | exact (hgD w).symm
      | exact hgD v
      | exact g.valid h
  refine ⟨Coloring.mk paint hproper, ?_, ?_, ?_, ?_⟩
  · intro v
    change paint v ∈ L v
    by_cases hvA : v ∈ A
    · simpa [paint, hvA] using hc v hvA
    · by_cases hvB : v ∈ B
      · simpa [paint, hvA, hvB] using hd v hvB
      · simpa [paint, hvA, hvB] using (mem_erase.mp (mem_erase.mp (hg v)).2).2
  · intro v hv
    change paint v = c
    simp [paint, hv]
  · intro v hv
    have hvA : v ∉ A := fun h => disjoint_left.mp hdis h hv
    change paint v = d
    simp [paint, hvA, hv]
  · change (univ.image paint).card ≤ 2 + (univ \ (A ∪ B)).card
    have hsub : univ.image paint ⊆ insert c (insert d ((univ \ (A ∪ B)).image g)) := by
      intro x hx
      obtain ⟨v, _, rfl⟩ := mem_image.mp hx
      by_cases hvA : v ∈ A
      · simp [paint, hvA]
      · by_cases hvB : v ∈ B
        · simp [paint, hvA, hvB]
        · have hm : v ∈ univ \ (A ∪ B) := by simp [hvA, hvB]
          simpa [paint, hvA, hvB] using mem_insert_of_mem (b := c)
            (mem_insert_of_mem (b := d) (mem_image_of_mem g hm))
    have h1 := card_le_card hsub
    have h2 := card_insert_le c (insert d ((univ \ (A ∪ B)).image g))
    have h3 := card_insert_le d ((univ \ (A ∪ B)).image g)
    have h4 := card_image_le (s := univ \ (A ∪ B)) (f := g)
    omega


end K23Reduction
end Part17

section Part18
-- Source module: K23FiveDouble

namespace K23Reduction

open SimpleGraph Finset TwinReduction StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A doubled center has at most two neighbors outside the row set. -/
theorem double_center_nonrow_neighbors_le_two (U : Finset V) (x : V)
    (hdegree : G.maxDegree ≤ 4) (hdouble : rowMultiplicity G U x = 2) :
    (G.neighborFinset x \ U).card ≤ 2 := by
  have hpart := card_sdiff_add_card_inter (G.neighborFinset x) U
  rw [G.card_neighborFinset_eq_degree] at hpart
  change (G.neighborFinset x \ U).card + rowMultiplicity G U x = G.degree x at hpart
  have hd := (G.degree_le_maxDegree x).trans hdegree
  omega

/-- A doubled spoke sees its common five colors and at most six further fixed colors. -/
theorem five_double_spoke_available_card_ge_nine (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u) (hx : x ∈ rowCenters G p q u)
    (hdouble : rowMultiplicity G U x = 2)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : T ⊆ (rowSeen G p q U u).image c) :
    9 ≤ (availableColors G p q U
      ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ c).card := by
  classical
  have hrow := five_row_colors_eq_common_of_double_center G p q U u x hpq hdegree hu
    hpu hqu hx hdouble c T hT hcommon
  have hfx := fixedAt_colors_subset_row G p q U u x hx c
  rw [hrow] at hfx
  have hX : ∀ z ∈ ({x} : Finset V), (fixedAt G p q U z).image c ⊆ T := by
    intro z hz
    have hzx := mem_singleton.mp hz
    subst z
    exact hfx
  have hcover := fixed_colors_covered_by_beyond G p q U {x} u x hu
    ((mem_rowCenters G p q u x).mp hx).1 (mem_singleton_self x) c T
    (by rw [hrow]) hX
  let Z := G.neighborFinset x \ (({x} : Finset V) ∪ U)
  have hZsub : Z ⊆ G.neighborFinset x \ U := by
    intro z hz
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1,
      fun hzU => (mem_sdiff.mp hz).2 (mem_union_right _ hzU)⟩
  have hZcard : Z.card ≤ 2 := (card_le_card hZsub).trans
    (double_center_nonrow_neighbors_le_two G U x hdegree hdouble)
  have hcard := card_le_card hcover
  have hsum := card_union_le T ((beyondEdges G x Z).image c)
  have himage := card_image_le (s := beyondEdges G x Z) (f := c)
  have hbeyond := beyondEdges_card_le G x Z hdegree sdiff_subset
  rw [hT] at hsum
  rw [availableColors, card_sdiff_of_subset (subset_univ _)]
  simp only [card_univ, Fintype.card_fin]
  change (fixedConflictColors G p q U _ c).card ≤
    (T ∪ (beyondEdges G x Z).image c).card at hcard
  omega

/-- If a doubled center joins both centers of another row, every fixed exclusion
of its spoke lies in that row's fixed-color set, provided its own row colors do. -/
theorem double_spoke_fixed_colors_subset_row_of_two_connectors
    (p q : V) (U : Finset V) (u x v w z : V)
    (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (hdouble : rowMultiplicity G U x = 2)
    (hcenters : rowCenters G p q v = {w,z}) (hwz : w ≠ z) (hwU : w ∉ U) (hzU : z ∉ U)
    (hxw : G.Adj x w) (hxz : G.Adj x z) (c : Sym2 V → Fin 20)
    (hrows : (rowSeen G p q U u).image c ⊆ (rowSeen G p q U v).image c) :
    fixedConflictColors G p q U ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ c ⊆
      (rowSeen G p q U v).image c := by
  classical
  have hpair : {w,z} ⊆ G.neighborFinset x \ U := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hxw, hwU⟩
    · have haz := mem_singleton.mp ha
      subst a
      exact mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz, hzU⟩
  have hnonrow : G.neighborFinset x \ U = {w,z} := by
    apply (eq_of_subset_of_card_le hpair ?_).symm
    simpa [card_pair hwz] using double_center_nonrow_neighbors_le_two G U x hdegree hdouble
  have hX : ∀ a ∈ ({x,w,z} : Finset V),
      (fixedAt G p q U a).image c ⊆ (rowSeen G p q U v).image c := by
    intro a ha
    rcases mem_insert.mp ha with hax | ha
    · subst a
      exact (fixedAt_colors_subset_row G p q U u x hx c).trans hrows
    · rcases mem_insert.mp ha with haw | ha
      · subst a
        exact fixedAt_colors_subset_row G p q U v w (by simp [hcenters]) c
      · have haz := mem_singleton.mp ha
        subst a
        exact fixedAt_colors_subset_row G p q U v z (by simp [hcenters]) c
  have hcover := fixed_colors_covered_by_beyond G p q U {x,w,z} u x hu
    ((mem_rowCenters G p q u x).mp hx).1 (by simp) c
    ((rowSeen G p q U v).image c) hrows hX
  have hZ : G.neighborFinset x \ (({x,w,z} : Finset V) ∪ U) = ∅ := by
    apply sdiff_eq_empty_iff_subset.mpr
    intro a ha
    by_cases haU : a ∈ U
    · exact mem_union_right _ haU
    · have hawm : a ∈ ({w,z} : Finset V) := by
        rw [← hnonrow]
        exact mem_sdiff.mpr ⟨ha,haU⟩
      exact mem_union_left _ (mem_insert_of_mem hawm)
  rw [hZ] at hcover
  simpa [beyondEdges] using hcover

/-- Excluding three colors outside T prevents a doubled center from joining
both centers of any row. The exclusions are those of the actual host spoke. -/
theorem five_double_center_has_nonadjacent_center (p q : V) (U : Finset V) (u x v : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ a ∈ U, G.Adj p a) (hq : ∀ a ∈ U, G.Adj q a)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) (hv : v ∈ U)
    (hdouble : rowMultiplicity G U x = 2)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ a ∈ U, T ⊆ (rowSeen G p q U a).image c)
    (D : Finset (Fin 20)) (hD : D.card = 3) (hTD : Disjoint T D)
    (e : ↥(spokeEdges G p q U)) (he : e.val = s(u,x))
    (hpalette : availableColors G p q U (spokeToEdge G p q U e) c ⊆ univ \ (T ∪ D)) :
    ∃ w ∈ rowCenters G p q v, ¬ G.Adj x w := by
  classical
  by_contra hbad
  push Not at hbad
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  obtain ⟨w,z,hwz,hcenters,hwU,hzU,_,_,_⟩ := row_five_geometry_of_common G p q U v
    hpq hdegree hv (hp v hv) (hq v hv) (hfive v hv)
  have hrow := five_row_colors_eq_common_of_double_center G p q U u x hpq hdegree hu
    (hp u hu) (hq u hu) hx hdouble c T hT (hcommon u hu)
  have hrows : (rowSeen G p q U u).image c ⊆ (rowSeen G p q U v).image c := by
    rw [hrow]
    exact hcommon v hv
  have hcover := double_spoke_fixed_colors_subset_row_of_two_connectors G p q U u x v w z
    hdegree hu hx hdouble hcenters hwz hwU hzU
    (hbad w (by simp [hcenters])) (hbad z (by simp [hcenters])) c hrows
  have hedge : spokeToEdge G p q U e =
      ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ := Subtype.ext he
  rw [← hedge] at hcover
  have hDsub : D ⊆ (rowSeen G p q U v).image c \ T := by
    intro a ha
    have haF : a ∈ fixedConflictColors G p q U (spokeToEdge G p q U e) c := by
      by_contra hnot
      have haL : a ∈ availableColors G p q U (spokeToEdge G p q U e) c :=
        mem_sdiff.mpr ⟨mem_univ _,hnot⟩
      exact (mem_sdiff.mp (hpalette haL)).2 (mem_union_right _ ha)
    exact mem_sdiff.mpr ⟨hcover haF, fun haT => Finset.disjoint_left.mp hTD haT ha⟩
  have hcount := card_le_card hDsub
  have hextra := five_row_extra_colors_le_one G p q U v hpq hdegree hv (hp v hv) (hq v hv)
    c T hT (hcommon v hv)
  omega

open scoped Classical in
/-- A doubled center forces an actual nonconflicting spoke pair with a common
available color when all spoke lists exclude the disjoint three-color overlap. -/
theorem five_double_pair_of_unavailable_overlap (p q : V) (U : Finset V)
    (hUcard : U.card = 3) (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c)
    (D : Finset (Fin 20)) (hD : D.card = 3) (hTD : Disjoint T D)
    (hpalette : ∀ e : ↥(spokeEdges G p q U),
      availableColors G p q U (spokeToEdge G p q U e) c ⊆ univ \ (T ∪ D))
    (hslack : ∀ e : ↥(spokeEdges G p q U), (spokeGraph G p q U).degree e + 4 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card)
    (hdouble : (doubleCenters G p q U).Nonempty) :
    ∃ e f : ↥(spokeEdges G p q U), e ≠ f ∧ ¬ (spokeGraph G p q U).Adj e f ∧
      ∃ a : Fin 20, a ∈ availableColors G p q U (spokeToEdge G p q U e) c ∧
        a ∈ availableColors G p q U (spokeToEdge G p q U f) c := by
  classical
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  have hi := five_rows_independent_of_common G p q U hpq hdegree hp hq hfive
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  obtain ⟨x,hxD⟩ := hdouble
  have hxX := (mem_filter.mp hxD).1
  have hmx := (mem_filter.mp hxD).2
  obtain ⟨u,hu,hx⟩ := mem_biUnion.mp hxX
  have hux := ((mem_rowCenters G p q u x).mp hx).1
  have hless : (G.neighborFinset x ∩ U).card < U.card := by
    change rowMultiplicity G U x < U.card
    omega
  obtain ⟨v,hv,hvnot⟩ := exists_mem_notMem_of_card_lt_card hless
  have hnvx : ¬ G.Adj v x := by
    intro hvx
    exact hvnot (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvx.symm,hv⟩)
  have huv : u ≠ v := fun h => hnvx (h ▸ hux)
  let e : ↥(spokeEdges G p q U) := ⟨s(u,x),row_center_is_spoke G p q U hpU hqU hu hx⟩
  obtain ⟨w,hw,hnxw⟩ := five_double_center_has_nonadjacent_center G p q U u x v
    hpq hdegree hp hq hu hx hv hmx c T hT hcommon D hD hTD e rfl (hpalette e)
  have hvw := ((mem_rowCenters G p q v w).mp hw).1
  have hwX : w ∈ U.biUnion (rowCenters G p q) := mem_biUnion.mpr ⟨v,hv,hw⟩
  have hwgeom := allCenters_five_geometry_of_common G p q U hpq hdegree hp hq hfive hwX
  have hxU := (allCenters_five_geometry_of_common G p q U hpq hdegree hp hq hfive
    (mem_biUnion.mpr ⟨u,hu,hx⟩)).1
  have hmw : rowMultiplicity G U w = 1 := by
    rcases hwgeom.2 with hsingle | hdoublew
    · exact hsingle
    · have hwD : w ∈ doubleCenters G p q U := mem_filter.mpr ⟨hwX,hdoublew⟩
      have hcount := five_doubleCenters_card_le_one G p q U hUcard hpq hdegree hp hq hfive
      have hxw := card_le_one.mp hcount x hxD w hwD
      exact (hnvx (by rw [hxw]; exact hvw)).elim
  let f : ↥(spokeEdges G p q U) := ⟨s(v,w),row_center_is_spoke G p q U hpU hqU hv hw⟩
  have hef : e ≠ f := by
    intro heq
    have hum : u ∈ s(v,w) := by
      have hmem : u ∈ e.val := Sym2.mem_mk_left _ _
      simpa only [heq] using hmem
    rcases Sym2.mem_iff.mp hum with huv' | huw
    · exact huv huv'
    · exact hwgeom.1 (huw ▸ hu)
  have hnonadj : ¬ (spokeGraph G p q U).Adj e f := by
    intro hconf
    obtain ⟨_,a,ha,b,hb,hab⟩ :=
      (conflict_iff_endpoints G (spokeToEdge G p q U e) (spokeToEdge G p q U f)).mp hconf
    change a ∈ s(u,x) at ha
    change b ∈ s(v,w) at hb
    rcases Sym2.mem_iff.mp ha with ha | ha <;> subst a <;>
      rcases Sym2.mem_iff.mp hb with hb | hb <;> subst b
    · rcases hab with huv' | huv'
      · exact huv huv'
      · exact hi hu hv huv huv'
    · rcases hab with huw | huw
      · exact hwgeom.1 (huw ▸ hu)
      · exact huv (row_unique_of_multiplicity_one G U w hmw hu hv huw hvw)
    · rcases hab with hxv | hxv
      · exact hxU (hxv.symm ▸ hv)
      · exact hnvx hxv.symm
    · rcases hab with hxw | hxw
      · exact hnvx (by rw [hxw]; exact hvw)
      · exact hnxw hxw
  have hLe : 9 ≤ (availableColors G p q U (spokeToEdge G p q U e) c).card :=
    five_double_spoke_available_card_ge_nine G p q U u x hpq hdegree hu
      (hp u hu) (hq u hu) hx hmx c T hT (hcommon u hu)
  have hpos : 0 < (spokeGraph G p q U).degree f :=
    ((spokeGraph G p q U).degree_pos_iff_exists_adj f).mpr
      (five_spokeGraph_no_isolated G p q U hpq hdegree hp hq hfive f)
  have hLf := hslack f
  have hK : (univ \ (T ∪ D)).card = 12 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      card_union_of_disjoint hTD, hT, hD]
  refine ⟨e,f,hef,hnonadj,?_⟩
  by_contra hpair
  have hdis : Disjoint (availableColors G p q U (spokeToEdge G p q U e) c)
      (availableColors G p q U (spokeToEdge G p q U f) c) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hpair ⟨a,ha,hb⟩
  have hbound := card_le_card (union_subset (hpalette e) (hpalette f))
  rw [card_union_of_disjoint hdis, hK] at hbound
  omega


end K23Reduction
end Part18

section Part19
-- Source module: K23SixGeometry

namespace K23Reduction

open SimpleGraph Finset TwinReduction StructuralAttack
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Common adjacencies suffice for the saturated six-edge row geometry. -/
theorem row_six_geometry_of_common (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (hsix : 6 ≤ (rowSeen G p q U u).card) :
    ∃ x y, x ≠ y ∧ rowCenters G p q u = {x,y} ∧ x ∉ U ∧ y ∉ U ∧
      rowMultiplicity G U x = 1 ∧ rowMultiplicity G U y = 1 ∧
      (fixedAt G p q U x).card = 3 ∧ (fixedAt G p q U y).card = 3 ∧ ¬ G.Adj x y := by
  have hc2 : (rowCenters G p q u).card = 2 := by
    have := rowCenters_card_le_two_of_common G p q u hpq hdegree hpu hqu
    have := rowSeen_card_le_three_mul_centers G p q U u hdegree hu
    omega
  obtain ⟨x,y,hxy,hc⟩ := Finset.card_eq_two.mp hc2
  have hx : x ∈ rowCenters G p q u := by simp [hc]
  have hy : y ∈ rowCenters G p q u := by simp [hc]
  have hux := ((mem_rowCenters G p q u x).mp hx).1
  have huy := ((mem_rowCenters G p q u y).mp hy).1
  have hax := fixedAt_card_le_three G p q U hdegree hu hux
  have hay := fixedAt_card_le_three G p q U hdegree hu huy
  have heq : rowSeen G p q U u = fixedAt G p q U x ∪ fixedAt G p q U y := by
    simp [rowSeen, hc]
  have hunion := Finset.card_union_le (fixedAt G p q U x) (fixedAt G p q U y)
  rw [← heq] at hunion
  have hax3 : (fixedAt G p q U x).card = 3 := by omega
  have hay3 : (fixedAt G p q U y).card = 3 := by omega
  have hxU : x ∉ U := by
    intro hxU
    rw [fixedAt_eq_empty_of_row G p q U hxU, card_empty] at hax3
    omega
  have hyU : y ∉ U := by
    intro hyU
    rw [fixedAt_eq_empty_of_row G p q U hyU, card_empty] at hay3
    omega
  have hrx : 0 < rowMultiplicity G U x := by
    apply Finset.card_pos.mpr
    exact ⟨u, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hux.symm, hu⟩⟩
  have hry : 0 < rowMultiplicity G U y := by
    apply Finset.card_pos.mpr
    exact ⟨u, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huy.symm, hu⟩⟩
  have hb := rowSeen_card_add_multiplicities_le_eight G p q U u x y hdegree hc
  have hrx1 : rowMultiplicity G U x = 1 := by omega
  have hry1 : rowMultiplicity G U y = 1 := by omega
  refine ⟨x,y,hxy,hc,hxU,hyU,hrx1,hry1,hax3,hay3,?_⟩
  intro hxyAdj
  have := rowSeen_card_add_multiplicities_le_seven_of_adjacent
    G p q U u x y hdegree hc hxU hyU hxyAdj
  omega

/-- A saturated center is outside the rows, private to one row, and has three fixed edges. -/
theorem allCenters_six_geometry_of_common (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card)
    {x : V} (hx : x ∈ U.biUnion (rowCenters G p q)) :
    x ∉ U ∧ rowMultiplicity G U x = 1 ∧ (fixedAt G p q U x).card = 3 := by
  obtain ⟨u,hu,hxu⟩ := mem_biUnion.mp hx
  obtain ⟨a,b,_,hab,haU,hbU,hma,hmb,hfa,hfb,_⟩ :=
    row_six_geometry_of_common G p q U u hpq hdegree hu (hp u hu) (hq u hu) (hsix u hu)
  have hxpair : x = a ∨ x = b := by simpa [hab] using hxu
  rcases hxpair with rfl | rfl
  · exact ⟨haU,hma,hfa⟩
  · exact ⟨hbU,hmb,hfb⟩

/-- Three fixed incidences and one row incidence leave no incidence for either root. -/
theorem six_center_not_adj_roots (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card)
    {x : V} (hx : x ∈ U.biUnion (rowCenters G p q)) :
    ¬ G.Adj p x ∧ ¬ G.Adj q x := by
  have hcard := (allCenters_six_geometry_of_common G p q U hpq hdegree hp hq hsix hx).2.2
  obtain ⟨u,hu,hxu⟩ := mem_biUnion.mp hx
  have hux := ((mem_rowCenters G p q u x).mp hxu).1
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  have hnot : ∀ r, r = p ∨ r = q → ¬ G.Adj r x := by
    intro r hr hrx
    have hur : u ≠ r := by
      intro hur
      rcases hr with rfl | rfl
      · exact hpU (hur ▸ hu)
      · exact hqU (hur ▸ hu)
    have hunot : s(x,u) ∉ fixedAt G p q U x := by
      intro he
      exact ((mem_fixedEdges G p q U _).mp (mem_filter.mp he).1).2.2.2
        u (Sym2.mem_mk_right _ _) hu
    have hsub : insert s(x,u) (fixedAt G p q U x) ⊆
        (G.incidenceFinset x).erase s(x,r) := by
      intro e he
      rcases mem_insert.mp he with rfl | he
      · refine mem_erase.mpr ⟨fun h => hur ((Sym2.mkEmbedding x).injective h), ?_⟩
        simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hux.symm]
      · refine mem_erase.mpr ⟨?_, fixedAt_subset_incidence G p q U x he⟩
        intro her
        have hf := (mem_fixedEdges G p q U e).mp (mem_filter.mp he).1
        rw [her] at hf
        rcases hr with rfl | rfl
        · exact hf.2.1 (Sym2.mem_mk_right _ _)
        · exact hf.2.2.1 (Sym2.mem_mk_right _ _)
    have hrmem : s(x,r) ∈ G.incidenceFinset x := by
      simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hrx.symm]
    have hc := card_le_card hsub
    rw [card_insert_of_notMem hunot, hcard, card_erase_of_mem hrmem,
      G.card_incidenceFinset_eq_degree] at hc
    have hd := (G.degree_le_maxDegree x).trans hdegree
    omega
  exact ⟨hnot p (Or.inl rfl), hnot q (Or.inr rfl)⟩

theorem six_rows_independent_of_common (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card) : G.IsIndepSet U := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  intro u hu v hv _ huv
  have hvc : v ∈ rowCenters G p q u := (mem_rowCenters G p q u v).mpr
    ⟨huv, fun h => hpU (h ▸ hv), fun h => hqU (h ▸ hv)⟩
  exact (allCenters_six_geometry_of_common G p q U hpq hdegree hp hq hsix
    (mem_biUnion.mpr ⟨u,hu,hvc⟩)).1 hv

theorem six_rowCenters_card (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (hsix : 6 ≤ (rowSeen G p q U u).card) : (rowCenters G p q u).card = 2 := by
  have := rowCenters_card_le_two_of_common G p q u hpq hdegree hpu hqu
  have := rowSeen_card_le_three_mul_centers G p q U u hdegree hu
  omega

theorem six_spokeEdges_card (p q : V) (U : Finset V) (hUcard : U.card = 3)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card) :
    (spokeEdges G p q U).card = 6 := by
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  have hi := six_rows_independent_of_common G p q U hpq hdegree hp hq hsix
  rw [spokeEdges_eq_biUnion G p q U hpU hqU,
    card_biUnion (rowSpokeEdges_pairwiseDisjoint G p q U hi)]
  calc
    ∑ u ∈ U, (rowSpokeEdges G p q u).card = ∑ _u ∈ U, 2 := by
      apply sum_congr rfl
      intro u hu
      simpa [rowSpokeEdges] using
        six_rowCenters_card G p q U u hpq hdegree hu (hp u hu) (hq u hu) (hsix u hu)
    _ = 6 := by simp [hUcard]

theorem six_spokeGraph_no_isolated (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card) :
    ∀ e : ↥(spokeEdges G p q U), ∃ f, (spokeGraph G p q U).Adj e f := by
  intro e
  have hpU : p ∉ U := fun h => G.loopless.irrefl p (hp p h)
  have hqU : q ∉ U := fun h => G.loopless.irrefl q (hq q h)
  obtain ⟨u,hu,x,hx,he⟩ := spoke_row_center G p q U e.val e.property
  have hc := six_rowCenters_card G p q U u hpq hdegree hu (hp u hu) (hq u hu) (hsix u hu)
  have hpos : 0 < ((rowCenters G p q u).erase x).card := by
    rw [card_erase_of_mem hx, hc]
    decide
  obtain ⟨y,hy⟩ := card_pos.mp hpos
  have hyx := (mem_erase.mp hy).1
  let f : ↥(spokeEdges G p q U) :=
    ⟨s(u,y), row_center_is_spoke G p q U hpU hqU hu (mem_of_mem_erase hy)⟩
  have hne : e ≠ f := by
    intro hef
    have hs : s(u,x) = s(u,y) := by simpa only [he] using congrArg Subtype.val hef
    exact hyx ((Sym2.mkEmbedding u).injective hs).symm
  refine ⟨f, spokeGraph_adj_of_common_endpoint G p q U e f hne u ?_ (Sym2.mem_mk_left _ _)⟩
  rw [he]
  exact Sym2.mem_mk_left _ _

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
theorem six_spoke_degree_le_one_add_center_neighbors (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v ∈ U, G.Adj p v) (hq : ∀ v ∈ U, G.Adj q v)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card)
    (e : ↥(spokeEdges G p q U)) (u x : V)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) (he : e.val = s(u,x)) :
    (spokeGraph G p q U).degree e ≤
      1 + (G.neighborFinset x ∩ U.biUnion (rowCenters G p q)).card := by
  classical
  let X := U.biUnion (rowCenters G p q)
  have hgeom : ∀ z ∈ X, z ∉ U ∧ rowMultiplicity G U z = 1 :=
    fun z hz => ⟨(allCenters_six_geometry_of_common G p q U hpq hdegree hp hq hsix hz).1,
      (allCenters_six_geometry_of_common G p q U hpq hdegree hp hq hsix hz).2.1⟩
  have hi := six_rows_independent_of_common G p q U hpq hdegree hp hq hsix
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
  have hrowCard := six_rowCenters_card G p q U u hpq hdegree hu (hp u hu) (hq u hu) (hsix u hu)
  have hmate : ((rowCenters G p q u).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hx,hrowCard]
  have hsum := Finset.card_union_le ((rowCenters G p q u).erase x) (G.neighborFinset x ∩ X)
  change (spokeGraph G p q U).degree e ≤ 1 + (G.neighborFinset x ∩ X).card
  omega

open scoped Classical in
/-- The six-case degree estimate needed by the list bound. All neighbors and conflicts
are counted in the actual full host, and b counts neighbors outside rows and centers. -/
theorem six_spoke_degree_add_exterior_le_four (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v ∈ U, G.Adj p v) (hq : ∀ v ∈ U, G.Adj q v)
    (hsix : ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card)
    (e : ↥(spokeEdges G p q U)) (u x : V)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u) (he : e.val = s(u,x)) :
    (spokeGraph G p q U).degree e +
      (G.neighborFinset x \ (U.biUnion (rowCenters G p q) ∪ U)).card ≤ 4 := by
  classical
  let X := U.biUnion (rowCenters G p q)
  let C := G.neighborFinset x ∩ X
  let B := G.neighborFinset x \ (X ∪ U)
  have hdeg := six_spoke_degree_le_one_add_center_neighbors G p q U hpq hdegree hp hq hsix e u x hu hx he
  have huN : u ∈ G.neighborFinset x := (G.mem_neighborFinset x u).mpr
    ((mem_rowCenters G p q u x).mp hx).1.symm
  have huC : u ∉ C := by
    intro h
    have huX := (Finset.mem_inter.mp h).2
    exact (allCenters_six_geometry_of_common G p q U hpq hdegree hp hq hsix huX).1 hu
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


end K23Reduction
end Part19

section Part20
-- Source module: K23SixAvailable

namespace K23Reduction

open SimpleGraph Finset TwinReduction StructuralAttack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem common_six_forces_six_edges (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∀ u ∈ U, 6 ≤ (rowSeen G p q U u).card := by
  intro u hu
  have hsub := card_le_card (hcommon u hu)
  have himage := card_image_le (s := rowSeen G p q U u) (f := c)
  omega

/-- Common six colors exhaust a row under only its two known root adjacencies. -/
theorem six_row_colors_eq_common (p q : V) (U : Finset V) (u : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4) (hu : u ∈ U)
    (hpu : G.Adj p u) (hqu : G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hsub : T ⊆ (rowSeen G p q U u).image c) :
    (rowSeen G p q U u).image c = T := by
  apply (eq_of_subset_of_card_le hsub ?_).symm
  rw [hT]
  exact row_colors_card_le_six_of_common G p q U u hpq hdegree hu hpu hqu c

/-- Fixed exclusions outside T can come only from edges beyond exterior neighbors. -/
theorem six_available_card_lower_of_common (p q : V) (U : Finset V) (u x : V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ v ∈ U, G.Adj p v) (hq : ∀ v ∈ U, G.Adj q v)
    (hu : u ∈ U) (hx : x ∈ rowCenters G p q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ v ∈ U, T ⊆ (rowSeen G p q U v).image c) :
    (availableColors G p q U ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ c).card +
      3 * (G.neighborFinset x \ (U.biUnion (rowCenters G p q) ∪ U)).card ≥ 14 := by
  classical
  let X := U.biUnion (rowCenters G p q)
  let Z := G.neighborFinset x \ (X ∪ U)
  have hxX : x ∈ X := mem_biUnion.mpr ⟨u,hu,hx⟩
  have hrow : ∀ v ∈ U, (rowSeen G p q U v).image c = T := fun v hv =>
    six_row_colors_eq_common G p q U v hpq hdegree hv (hp v hv) (hq v hv) c T hT
      (hcommon v hv)
  have hX : ∀ z ∈ X, (fixedAt G p q U z).image c ⊆ T := by
    intro z hz
    obtain ⟨v,hv,hz⟩ := mem_biUnion.mp hz
    rw [← hrow v hv]
    exact fixedAt_colors_subset_row G p q U v z hz c
  have hcover := fixed_colors_covered_by_beyond G p q U X u x hu
    ((mem_rowCenters G p q u x).mp hx).1 hxX c T (by rw [hrow u hu]) hX
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

open scoped Classical in
/-- Actual full-host spoke lists satisfy the compression inequality with common adjacencies. -/
theorem six_actual_list_bound_of_common (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∀ e : ↥(spokeEdges G p q U), 3 * (spokeGraph G p q U).degree e + 2 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card := by
  intro e
  have hsix := common_six_forces_six_edges G p q U c T hT hcommon
  obtain ⟨u,hu,x,hx,he⟩ := spoke_row_center G p q U e.val e.property
  have hd := six_spoke_degree_add_exterior_le_four G p q U hpq hdegree hp hq hsix e u x hu hx he
  have ha := six_available_card_lower_of_common G p q U u x hpq hdegree hp hq hu hx c T hT hcommon
  have hedge : spokeToEdge G p q U e =
      ⟨s(u,x), ((mem_rowCenters G p q u x).mp hx).1⟩ := Subtype.ext he
  rw [← hedge] at ha
  omega

/-- No extra geometric premise is needed to exclude the common fixed colors. -/
theorem actual_spoke_lists_avoid_common (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20))
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∀ e : ↥(spokeEdges G p q U),
      availableColors G p q U (spokeToEdge G p q U e) c ⊆ univ \ T := by
  intro e
  obtain ⟨u,hu,hue⟩ := ((mem_spokeEdges G p q U e.val).mp e.property).2.2.2
  exact availableColors_subset_complement_common G p q U u hu
    (spokeToEdge G p q U e) hue c T (hcommon u hu)

open scoped Classical in
/-- Six actual spokes, no isolated spoke, and the actual list inputs for compression.
Only the spoke count needs U.card = 3; no exact twin neighborhoods are assumed. -/
theorem six_actual_geometry_and_lists (p q : V) (U : Finset V) (hUcard : U.card = 3)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    (spokeEdges G p q U).card = 6 ∧
    (∀ e : ↥(spokeEdges G p q U), ∃ f, (spokeGraph G p q U).Adj e f) ∧
    (∀ e : ↥(spokeEdges G p q U),
      availableColors G p q U (spokeToEdge G p q U e) c ⊆ univ \ T) ∧
    (∀ e : ↥(spokeEdges G p q U), 3 * (spokeGraph G p q U).degree e + 2 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card) := by
  have hsix := common_six_forces_six_edges G p q U c T hT hcommon
  exact ⟨six_spokeEdges_card G p q U hUcard hpq hdegree hp hq hsix,
    six_spokeGraph_no_isolated G p q U hpq hdegree hp hq hsix,
    actual_spoke_lists_avoid_common G p q U c T hcommon,
    six_actual_list_bound_of_common G p q U hpq hdegree hp hq c T hT hcommon⟩


end K23Reduction
end Part20

section Part21
-- Source module: K23FiveCompression

namespace K23Reduction

open SimpleGraph Finset TwinReduction
open scoped BigOperators

/-- Six private-center lists in twelve colors contain a nonadjacent shared-color pair. -/
theorem five_private_list_pair {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hV : Fintype.card V = 6)
    (L : V → Finset C) (P : Finset C) (hP : P.card ≤ 12)
    (hsub : ∀ v, L v ⊆ P) (hd : ∀ v, H.degree v ≤ 4)
    (hcard : ∀ v, 2 * H.degree v + 3 ≤ (L v).card) :
    ∃ a b, a ≠ b ∧ ¬ H.Adj a b ∧ ∃ c, c ∈ L a ∧ c ∈ L b := by
  classical
  have hw : ∀ v, 132 ≤ (L v).card * (60 / (H.degree v + 1)) := by
    intro v
    have hdeg := hd v
    have hl := hcard v
    have hcases : H.degree v = 0 ∨ H.degree v = 1 ∨ H.degree v = 2 ∨
        H.degree v = 3 ∨ H.degree v = 4 := by omega
    rcases hcases with h | h | h | h | h <;> rw [h] at hl ⊢ <;> simp <;> omega
  have hsum := sum_le_sum (s := (univ : Finset V)) (fun v _ => hw v)
  simp only [sum_const, card_univ, hV, smul_eq_mul] at hsum
  exact Palette.independent_pair_of_weight H L P hsub 60 (by omega)

/-- A common color on two nonadjacent vertices saves one of six colors. -/
theorem shared_pair_list_compression {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hV : Fintype.card V = 6)
    (L : V → Finset C) (hslack : ∀ v, H.degree v + 2 ≤ (L v).card)
    (hpair : ∃ a b, a ≠ b ∧ ¬ H.Adj a b ∧ ∃ c, c ∈ L a ∧ c ∈ L b) :
    ∃ f : H.Coloring C, (∀ v, f v ∈ L v) ∧ (univ.image f).card ≤ 5 := by
  classical
  obtain ⟨a,b,hab,hnab,c,hca,hcb⟩ := hpair
  have hi : H.IsIndepSet ({a,b} : Finset V) := by
    simpa using Palette.indep_pair H hnab
  have hc : ∀ v ∈ ({a,b} : Finset V), c ∈ L v := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hca
    · have he := mem_singleton.mp hv
      exact he.symm ▸ hcb
  obtain ⟨f,hf,_,hcount⟩ := one_set_list_completion H L hslack {a,b} hi c hc
  have hrest : (univ \ ({a,b} : Finset V)).card = 4 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV, card_pair hab]
  exact ⟨f,hf,by omega⟩

open scoped Classical in
/-- Common five-color actual spoke lists can be recolored while reserving
space for three disjoint exceptional colors. The degree slack is explicit. -/
theorem five_actual_spoke_compression {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 5)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c)
    (D : Finset (Fin 20)) (hD : D.card = 3) (hTD : Disjoint T D)
    (hslack : ∀ e : ↥(spokeEdges G p q U), (spokeGraph G p q U).degree e + 4 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card) :
    ∃ qcolor : (spokeGraph G p q U).Coloring (Fin 20),
      (∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c) ∧
      (univ.image qcolor ∪ T ∪ D).card ≤ 13 := by
  classical
  let H := spokeGraph G p q U
  let L := fun e => availableColors G p q U (spokeToEdge G p q U e) c
  have hfive := shared_colors_force_five_edges G p q U c T (by omega) hcommon
  have hV : Fintype.card ↥(spokeEdges G p q U) = 6 := by
    simpa only [Fintype.card_coe] using
      five_spokeEdges_card G p q U hU hpq hdegree hp hq hfive
  have hslack' : ∀ e, H.degree e + 2 ≤ (L e).card := by
    intro e
    have h := hslack e
    dsimp [H,L]
    omega
  by_cases hoccurs : ∃ d ∈ D, ∃ e, d ∈ L e
  · obtain ⟨d,hd,e,he⟩ := hoccurs
    have hi : H.IsIndepSet ({e} : Finset ↥(spokeEdges G p q U)) := by simp
    obtain ⟨qcolor,hqcolor,heq,hcount⟩ := one_set_list_completion H L hslack' {e} hi d
      (by intro v hv; have hve := mem_singleton.mp hv; exact hve.symm ▸ he)
    have hrest : (univ \ ({e} : Finset ↥(spokeEdges G p q U))).card = 5 := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hV, card_singleton]
    have hused : d ∈ univ.image qcolor := by
      rw [← heq e (mem_singleton_self e)]
      exact mem_image_of_mem qcolor (mem_univ e)
    have hinter : 1 ≤ (univ.image qcolor ∩ D).card :=
      card_pos.mpr ⟨d,mem_inter.mpr ⟨hused,hd⟩⟩
    have hQD := card_union_add_card_inter (univ.image qcolor) D
    have hjoin := card_union_le (univ.image qcolor ∪ D) T
    refine ⟨qcolor,hqcolor,?_⟩
    rw [union_right_comm]
    omega
  · have hpalette : ∀ e, L e ⊆ univ \ (T ∪ D) := by
      intro e d hd
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro hbad
      rcases mem_union.mp hbad with hTmem | hDmem
      · exact (mem_sdiff.mp (actual_spoke_lists_avoid_common G p q U c T hcommon e hd)).2 hTmem
      · exact hoccurs ⟨d,hDmem,e,hd⟩
    have hP : (univ \ (T ∪ D)).card ≤ 12 := by
      rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hTD, hT,hD]
      decide
    have hpair : ∃ e f, e ≠ f ∧ ¬ H.Adj e f ∧ ∃ d, d ∈ L e ∧ d ∈ L f := by
      by_cases hdouble : (doubleCenters G p q U).Nonempty
      · exact five_double_pair_of_unavailable_overlap G p q U hU hpq hdegree hp hq
          c T hT hcommon D hD hTD hpalette hslack hdouble
      · have hprivate : ∀ x ∈ U.biUnion (rowCenters G p q), rowMultiplicity G U x = 1 := by
          intro x hx
          rcases (allCenters_five_geometry_of_common G p q U hpq hdegree hp hq hfive hx).2
            with hsingle | htwo
          · exact hsingle
          · exact (hdouble ⟨x,mem_filter.mpr ⟨hx,htwo⟩⟩).elim
        have hbound := five_private_spoke_list_bound G p q U hpq hdegree hp hq c T hT
          hcommon hprivate
        exact five_private_list_pair H hV L (univ \ (T ∪ D)) hP hpalette
          (fun e => (hbound e).1) (fun e => (hbound e).2)
    obtain ⟨qcolor,hqcolor,hcount⟩ := shared_pair_list_compression H hV L hslack' hpair
    have h1 := card_union_le (univ.image qcolor) T
    have h2 := card_union_le (univ.image qcolor ∪ T) D
    exact ⟨qcolor,hqcolor,by omega⟩


end K23Reduction
end Part21

section Part22
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
end Part22

section Part23
-- Source module: K23Slack

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual host edges adjacent to an edge in the canonical full conflict graph. -/
noncomputable def conflictNeighborEdges (e : G.edgeSet) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (endpointConflict G e.val)

omit [DecidableEq V] in
theorem mem_conflictNeighborEdges (e : G.edgeSet) (f : Sym2 V) :
    f ∈ conflictNeighborEdges G e ↔ f ∈ G.edgeSet ∧ endpointConflict G e.val f := by
  classical
  simp [conflictNeighborEdges]

omit [DecidableEq V] in
theorem edge_mem_conflictNeighborEdges (e f : G.edgeSet) :
    f.val ∈ conflictNeighborEdges G e ↔ (strongConflict G).Adj e f := by
  rw [mem_conflictNeighborEdges, and_iff_right f.property, endpointConflict_iff]

open scoped Classical in
theorem conflictNeighborEdges_eq_image (e : G.edgeSet) :
    conflictNeighborEdges G e =
      ((strongConflict G).neighborFinset e).image Subtype.val := by
  classical
  ext f
  constructor
  · intro hf
    have h := (mem_conflictNeighborEdges G e f).mp hf
    exact mem_image.mpr ⟨⟨f, h.1⟩,
      ((strongConflict G).mem_neighborFinset e _).mpr
        ((endpointConflict_iff G e ⟨f, h.1⟩).mp h.2), rfl⟩
  · intro hf
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
    exact (edge_mem_conflictNeighborEdges G e g).mpr
      (((strongConflict G).mem_neighborFinset e g).mp hg)

open scoped Classical in
theorem conflictNeighborEdges_card (e : G.edgeSet) :
    (conflictNeighborEdges G e).card = (strongConflict G).degree e := by
  classical
  rw [conflictNeighborEdges_eq_image, card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree]

theorem conflictNeighborEdges_card_le_twenty_four (hdegree : G.maxDegree ≤ 4)
    (e : G.edgeSet) : (conflictNeighborEdges G e).card ≤ 24 := by
  classical
  rw [conflictNeighborEdges_card]
  exact conflict_degree_le_twenty_four G hdegree e

/-- Every edge removed when the two roots are deleted. -/
def rootIncidentEdges (p q : V) : Finset (Sym2 V) :=
  G.incidenceFinset p ∪ G.incidenceFinset q

theorem mem_rootIncidentEdges (p q : V) (e : Sym2 V) :
    e ∈ rootIncidentEdges G p q ↔ e ∈ G.edgeSet ∧ (p ∈ e ∨ q ∈ e) := by
  simp only [rootIncidentEdges, mem_union, SimpleGraph.mem_incidenceFinset,
    SimpleGraph.incidenceSet, Set.mem_ofPred_eq]
  tauto

theorem rootIncidentEdges_card (p q : V) (hpq : p ≠ q) (hn : ¬ G.Adj p q) :
    (rootIncidentEdges G p q).card = G.degree p + G.degree q := by
  have hdis : Disjoint (G.incidenceFinset p) (G.incidenceFinset q) := by
    apply Finset.disjoint_left.mpr
    intro e hp hq
    exact hn (G.adj_of_mem_incidenceSet hpq
      ((G.mem_incidenceFinset p e).mp hp) ((G.mem_incidenceFinset q e).mp hq))
  rw [rootIncidentEdges, card_union_of_disjoint hdis,
    G.card_incidenceFinset_eq_degree, G.card_incidenceFinset_eq_degree]

theorem rootIncidentEdges_disjoint_spokes (p q : V) (U : Finset V) :
    Disjoint (rootIncidentEdges G p q) (spokeEdges G p q U) := by
  apply Finset.disjoint_left.mpr
  intro e hb hm
  have hb' := (mem_rootIncidentEdges G p q e).mp hb
  have hm' := (mem_spokeEdges G p q U e).mp hm
  exact hb'.2.elim hm'.2.1 hm'.2.2.1

/-- A spoke sees every root-incident edge through its common row endpoint. -/
theorem rootIncidentEdges_subset_spoke_conflicts (p q : V) (U : Finset V)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (e : ↥(spokeEdges G p q U)) :
    rootIncidentEdges G p q ⊆ conflictNeighborEdges G (spokeToEdge G p q U e) := by
  intro f hf
  have hb := (mem_rootIncidentEdges G p q f).mp hf
  have he := (mem_spokeEdges G p q U e.val).mp e.property
  obtain ⟨u, hu, hue⟩ := he.2.2.2
  apply (mem_conflictNeighborEdges G _ f).mpr
  refine ⟨hb.1, ?_, ?_⟩
  · intro hef
    change e.val = f at hef
    exact hb.2.elim (fun h => he.2.1 (hef.symm ▸ h)) (fun h => he.2.2.1 (hef.symm ▸ h))
  · rcases hb.2 with hpf | hqf
    · exact ⟨u, hue, p, hpf, Or.inr (hp u hu).symm⟩
    · exact ⟨u, hue, q, hqf, Or.inr (hq u hu).symm⟩

open scoped Classical in
/-- Removing root-incident edges and spokes leaves exactly the fixed conflicts. -/
theorem fixed_conflict_edges_eq_sdiff (p q : V) (U : Finset V) (e : G.edgeSet) :
    (fixedEdges G p q U).filter (endpointConflict G e.val) =
      conflictNeighborEdges G e \ (rootIncidentEdges G p q ∪ spokeEdges G p q U) := by
  classical
  ext f
  simp only [mem_filter, mem_fixedEdges, mem_sdiff, mem_conflictNeighborEdges,
    mem_union, mem_rootIncidentEdges, mem_spokeEdges]
  aesop

open scoped Classical in
theorem spoke_conflict_inter_eq_image (p q : V) (U : Finset V)
    (e : ↥(spokeEdges G p q U)) :
    conflictNeighborEdges G (spokeToEdge G p q U e) ∩ spokeEdges G p q U =
      ((spokeGraph G p q U).neighborFinset e).image Subtype.val := by
  classical
  ext f
  constructor
  · intro hf
    have h := mem_inter.mp hf
    refine mem_image.mpr ⟨⟨f, h.2⟩, ?_, rfl⟩
    apply ((spokeGraph G p q U).mem_neighborFinset e _).mpr
    rw [spokeGraph_adj_iff]
    exact (edge_mem_conflictNeighborEdges G _ (spokeToEdge G p q U ⟨f, h.2⟩)).mp h.1
  · intro hf
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
    refine mem_inter.mpr ⟨?_, g.property⟩
    apply (edge_mem_conflictNeighborEdges G _ (spokeToEdge G p q U g)).mpr
    exact ((spokeGraph G p q U).mem_neighborFinset e g).mp hg

open scoped Classical in
theorem spoke_conflict_inter_card (p q : V) (U : Finset V)
    (e : ↥(spokeEdges G p q U)) :
    (conflictNeighborEdges G (spokeToEdge G p q U e) ∩ spokeEdges G p q U).card =
      (spokeGraph G p q U).degree e := by
  classical
  rw [spoke_conflict_inter_eq_image, card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree]

open scoped Classical in
/-- With two nonadjacent degree-four roots, every actual spoke has degree plus
four available fixed-compatible colors. No row cardinality or exact neighborhood is assumed. -/
theorem spoke_available_card_ge_degree_add_four (p q : V) (U : Finset V)
    (hpq : p ≠ q) (hn : ¬ G.Adj p q) (hdegree : G.maxDegree ≤ 4)
    (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (e : ↥(spokeEdges G p q U)) :
    (spokeGraph G p q U).degree e + 4 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card := by
  classical
  have hB : (rootIncidentEdges G p q).card = 8 := by
    rw [rootIncidentEdges_card G p q hpq hn, hdp, hdq]
  have h := fixed_palette_slack
    (conflictNeighborEdges G (spokeToEdge G p q U e)) (rootIncidentEdges G p q)
    (spokeEdges G p q U) c
    (conflictNeighborEdges_card_le_twenty_four G hdegree _) hB
    (rootIncidentEdges_subset_spoke_conflicts G p q U hp hq e)
    (rootIncidentEdges_disjoint_spokes G p q U)
  rw [spoke_conflict_inter_card, ← fixed_conflict_edges_eq_sdiff] at h
  exact h


end K23Reduction
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
-- Source module: K23Glue

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The original host edges split into root-incident, spoke, and fixed edges,
without any neighborhood or degree assumption. -/
theorem root_spoke_fixed_partition (p q : V) (U : Finset V) (e : G.edgeSet) :
    e.val ∈ rootIncidentEdges G p q ∨ e.val ∈ spokeEdges G p q U ∨
      e.val ∈ fixedEdges G p q U := by
  by_cases hb : e.val ∈ rootIncidentEdges G p q
  · exact Or.inl hb
  by_cases hs : e.val ∈ spokeEdges G p q U
  · exact Or.inr (Or.inl hs)
  have hp : p ∉ e.val := fun h => hb
    ((mem_rootIncidentEdges G p q e.val).mpr ⟨e.property, Or.inl h⟩)
  have hq : q ∉ e.val := fun h => hb
    ((mem_rootIncidentEdges G p q e.val).mpr ⟨e.property, Or.inr h⟩)
  exact Or.inr (Or.inr ((mem_fixedEdges G p q U e.val).mpr
    ⟨e.property, hp, hq, fun u hue hu => hs
      ((mem_spokeEdges G p q U e.val).mpr ⟨e.property, hp, hq, u, hu, hue⟩)⟩))

/-- Merge a proper blank assignment, a compatible actual spoke coloring, and
the retained fixed colors. Every conflict is checked in the original host.
Blank colors may repeat on nonconflicting edges, as the two exceptions do. -/
theorem glue_root_spoke_fixed (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (havailable : ∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c)
    (blank : G.edgeSet → Fin 20)
    (hblank : ∀ e f : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      f.val ∈ rootIncidentEdges G p q → (strongConflict G).Adj e f → blank e ≠ blank f)
    (hspokes : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      ∀ s : ↥(spokeEdges G p q U), blank e ≠ qcolor s)
    (hfixed : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      blank e ∈ availableColors G p q U e c) :
    ∃ C : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → C e = c e.val) ∧
      (∀ e : ↥(spokeEdges G p q U), C (spokeToEdge G p q U e) = qcolor e) ∧
      (∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q → C e = blank e) := by
  classical
  let paint : G.edgeSet → Fin 20 := fun e =>
    if e.val ∈ rootIncidentEdges G p q then blank e
    else if hs : e.val ∈ spokeEdges G p q U then qcolor ⟨e.val, hs⟩
    else c e.val
  have hpaint_blank : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      paint e = blank e := by
    intro e he
    simp [paint, he]
  have hpaint_spoke : ∀ (e : G.edgeSet) (he : e.val ∈ spokeEdges G p q U),
      paint e = qcolor ⟨e.val, he⟩ := by
    intro e he
    have hb : e.val ∉ rootIncidentEdges G p q := fun hb =>
      Finset.disjoint_left.mp (rootIncidentEdges_disjoint_spokes G p q U) hb he
    simp [paint, hb, he]
  have hpaint_fixed : ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U →
      paint e = c e.val := by
    intro e he
    have hf := (mem_fixedEdges G p q U e.val).mp he
    have hb : e.val ∉ rootIncidentEdges G p q := fun hb =>
      ((mem_rootIncidentEdges G p q e.val).mp hb).2.elim hf.2.1 hf.2.2.1
    have hs : e.val ∉ spokeEdges G p q U := fun hs => spoke_not_fixed G p q U e.val hs he
    simp [paint, hb, hs]
  have hcompat_spoke : ∀ (s : ↥(spokeEdges G p q U)) (e : G.edgeSet),
      e.val ∈ fixedEdges G p q U → (strongConflict G).Adj (spokeToEdge G p q U s) e →
        c e.val ≠ qcolor s := by
    intro s
    exact (mem_availableColors G p q U (spokeToEdge G p q U s) c (qcolor s)).mp (havailable s)
  have hcompat_blank : ∀ (e f : G.edgeSet), e.val ∈ rootIncidentEdges G p q →
      f.val ∈ fixedEdges G p q U → (strongConflict G).Adj e f → c f.val ≠ blank e := by
    intro e f he
    exact (mem_availableColors G p q U e c (blank e)).mp (hfixed e he) f
  have hproper : ∀ {e f : G.edgeSet}, (strongConflict G).Adj e f → paint e ≠ paint f := by
    intro e f hadj
    rcases root_spoke_fixed_partition G p q U e with he | he | he <;>
      rcases root_spoke_fixed_partition G p q U f with hf | hf | hf
    · rw [hpaint_blank e he, hpaint_blank f hf]
      exact hblank e f he hf hadj
    · rw [hpaint_blank e he, hpaint_spoke f hf]
      exact hspokes e he ⟨f.val, hf⟩
    · rw [hpaint_blank e he, hpaint_fixed f hf]
      exact (hcompat_blank e f he hf hadj).symm
    · rw [hpaint_spoke e he, hpaint_blank f hf]
      exact (hspokes f hf ⟨e.val, he⟩).symm
    · rw [hpaint_spoke e he, hpaint_spoke f hf]
      exact qcolor.valid (show (spokeGraph G p q U).Adj ⟨e.val, he⟩ ⟨f.val, hf⟩ from hadj)
    · rw [hpaint_spoke e he, hpaint_fixed f hf]
      exact (hcompat_spoke ⟨e.val, he⟩ f hf hadj).symm
    · rw [hpaint_fixed e he, hpaint_blank f hf]
      exact hcompat_blank f e hf he hadj.symm
    · rw [hpaint_fixed e he, hpaint_spoke f hf]
      exact hcompat_spoke ⟨f.val, hf⟩ e he hadj.symm
    · rw [hpaint_fixed e he, hpaint_fixed f hf]
      have he' := (mem_fixedEdges G p q U e.val).mp he
      have hf' := (mem_fixedEdges G p q U f.val).mp hf
      exact hc e f he'.2.1 he'.2.2.1 hf'.2.1 hf'.2.2.1 hadj
  refine ⟨Coloring.mk paint hproper, hpaint_fixed, ?_, hpaint_blank⟩
  intro e
  exact hpaint_spoke (spokeToEdge G p q U e) e.property


end K23Reduction
end Part25

section Part26
-- Source module: K23RetainedRecolor

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Replace the actual spoke colors, retaining every other value of c. -/
def retainedRecolor (p q : V) (U : Finset V) (c : Sym2 V → Fin 20)
    (qcolor : (spokeGraph G p q U).Coloring (Fin 20)) : Sym2 V → Fin 20 :=
  fun e => if he : e ∈ spokeEdges G p q U then qcolor ⟨e, he⟩ else c e

@[simp] theorem retainedRecolor_spoke (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (e : ↥(spokeEdges G p q U)) :
    retainedRecolor G p q U c qcolor e.val = qcolor e := by
  simp [retainedRecolor, e.property]

theorem retainedRecolor_of_not_spoke (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (e : Sym2 V) (he : e ∉ spokeEdges G p q U) :
    retainedRecolor G p q U c qcolor e = c e := by
  simp [retainedRecolor, he]

/-- Every fixed edge keeps its color, without geometry assumptions. -/
theorem retainedRecolor_fixed (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (e : Sym2 V) (he : e ∈ fixedEdges G p q U) :
    retainedRecolor G p q U c qcolor e = c e := by
  apply retainedRecolor_of_not_spoke G p q U c qcolor e
  intro hs
  exact spoke_not_fixed G p q U e hs he

/-- Any proper spoke coloring available against c's fixed edges gives a
proper retained coloring, with conflicts still measured in the original G. -/
theorem retainedRecolor_proper (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (hc : RetainedProper G p q c)
    (havailable : ∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c) :
    RetainedProper G p q (retainedRecolor G p q U c qcolor) := by
  have hpartition : ∀ e : G.edgeSet, p ∉ e.val → q ∉ e.val →
      e.val ∈ spokeEdges G p q U ∨ e.val ∈ fixedEdges G p q U := by
    intro e hep heq
    apply (root_spoke_fixed_partition G p q U e).resolve_left
    intro hr
    rcases ((mem_rootIncidentEdges G p q e.val).mp hr).2 with hp | hq
    · exact hep hp
    · exact heq hq
  have hcompat : ∀ (s : ↥(spokeEdges G p q U)) (e : G.edgeSet),
      e.val ∈ fixedEdges G p q U → (strongConflict G).Adj (spokeToEdge G p q U s) e →
        c e.val ≠ qcolor s := by
    intro s
    exact (mem_availableColors G p q U (spokeToEdge G p q U s) c (qcolor s)).mp
      (havailable s)
  intro e f hep heq hfp hfq hadj
  rcases hpartition e hep heq with he | he <;>
    rcases hpartition f hfp hfq with hf | hf
  · rw [retainedRecolor_spoke G p q U c qcolor ⟨e.val, he⟩,
      retainedRecolor_spoke G p q U c qcolor ⟨f.val, hf⟩]
    exact qcolor.valid (show (spokeGraph G p q U).Adj ⟨e.val, he⟩ ⟨f.val, hf⟩ from hadj)
  · rw [retainedRecolor_spoke G p q U c qcolor ⟨e.val, he⟩,
      retainedRecolor_fixed G p q U c qcolor f.val hf]
    exact (hcompat ⟨e.val, he⟩ f hf hadj).symm
  · rw [retainedRecolor_fixed G p q U c qcolor e.val he,
      retainedRecolor_spoke G p q U c qcolor ⟨f.val, hf⟩]
    exact hcompat ⟨f.val, hf⟩ e he hadj.symm
  · rw [retainedRecolor_fixed G p q U c qcolor e.val he,
      retainedRecolor_fixed G p q U c qcolor f.val hf]
    exact hc e f hep heq hfp hfq hadj

/-- Agreement on fixed edges preserves the image of every finite subset. -/
theorem fixed_image_eq_of_agree (p q : V) (U : Finset V)
    (c c' : Sym2 V → Fin 20)
    (hagree : ∀ e, e ∈ fixedEdges G p q U → c' e = c e)
    (S : Finset (Sym2 V)) (hS : S ⊆ fixedEdges G p q U) :
    S.image c' = S.image c := by
  apply Finset.image_congr
  intro e he
  exact hagree e (hS he)

theorem retainedRecolor_fixedAt_image (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (u : V) :
    (fixedAt G p q U u).image (retainedRecolor G p q U c qcolor) =
      (fixedAt G p q U u).image c := by
  apply fixed_image_eq_of_agree G p q U c (retainedRecolor G p q U c qcolor)
    (retainedRecolor_fixed G p q U c qcolor)
  exact filter_subset _ _

theorem retainedRecolor_rowSeen_image (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (u : V) :
    (rowSeen G p q U u).image (retainedRecolor G p q U c qcolor) =
      (rowSeen G p q U u).image c := by
  apply fixed_image_eq_of_agree G p q U c (retainedRecolor G p q U c qcolor)
    (retainedRecolor_fixed G p q U c qcolor)
  intro e he
  exact ((mem_rowSeen G p q U u e).mp he).1

theorem retainedRecolor_fixedConflictColors (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (e : G.edgeSet) :
    fixedConflictColors G p q U e (retainedRecolor G p q U c qcolor) =
      fixedConflictColors G p q U e c := by
  classical
  unfold fixedConflictColors
  apply fixed_image_eq_of_agree G p q U c (retainedRecolor G p q U c qcolor)
    (retainedRecolor_fixed G p q U c qcolor)
  exact filter_subset _ _

theorem retainedRecolor_availableColors (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (e : G.edgeSet) :
    availableColors G p q U e (retainedRecolor G p q U c qcolor) =
      availableColors G p q U e c := by
  unfold availableColors
  rw [retainedRecolor_fixedConflictColors]

/-- The new spoke image is precisely the image of the supplied coloring. -/
theorem retainedRecolor_spoke_image (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20)) :
    (spokeEdges G p q U).image (retainedRecolor G p q U c qcolor) =
      univ.image qcolor := by
  ext a
  constructor
  · intro ha
    obtain ⟨e, he, hcolor⟩ := mem_image.mp ha
    refine mem_image.mpr ⟨⟨e, he⟩, mem_univ _, ?_⟩
    rw [retainedRecolor_spoke G p q U c qcolor ⟨e, he⟩] at hcolor
    exact hcolor
  · intro ha
    obtain ⟨e, _, hcolor⟩ := mem_image.mp ha
    refine mem_image.mpr ⟨e.val, e.property, ?_⟩
    rw [retainedRecolor_spoke G p q U c qcolor e]
    exact hcolor

/-- Restricting the recolored retained function recovers the supplied image,
independently of the proof used for its retained properness. -/
theorem retainedRecolor_originalSpokeColoring_image (p q : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (hc' : RetainedProper G p q (retainedRecolor G p q U c qcolor)) :
    univ.image (originalSpokeColoring G p q U (retainedRecolor G p q U c qcolor) hc') =
      univ.image qcolor := by
  rw [originalSpokeColoring_image]
  exact retainedRecolor_spoke_image G p q U c qcolor


end K23Reduction
end Part26

section Part27
-- Source module: K23Hall

namespace K23Reduction

open Finset

/-- Six lists of size at least four have an SDR if their union has size at
least six and each list has a different partner missing at most one color. -/
theorem six_list_hall {I C : Type*} [Fintype I] [DecidableEq I] [DecidableEq C]
    (hI : Fintype.card I = 6) (L : I → Finset C)
    (hL : ∀ v, 4 ≤ (L v).card)
    (hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1)
    (htotal : 6 ≤ (univ.biUnion L).card) :
    ∃ f : I → C, Function.Injective f ∧ ∀ v, f v ∈ L v := by
  apply (all_card_le_biUnion_card_iff_existsInjective' L).mp
  intro S
  by_cases hsmall : S.card ≤ 4
  · by_cases hempty : S = ∅
    · simp [hempty]
    obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr hempty
    exact hsmall.trans ((hL v).trans
      (card_le_card (subset_biUnion_of_mem L hv)))
  · by_cases hfull : S = univ
    · simpa [hfull, hI] using htotal
    have hv : ∃ v, v ∉ S := by
      by_contra! h
      exact hfull (eq_univ_of_forall h)
    obtain ⟨v, hv⟩ := hv
    have hsub : S ⊆ univ.erase v := by
      intro u hu
      exact mem_erase.mpr ⟨by intro huv; exact hv (huv ▸ hu), mem_univ _⟩
    have hcard : (univ.erase v).card = 5 := by simp [hI]
    have hScard := card_le_card hsub
    have heq : S = univ.erase v := eq_of_subset_of_card_le hsub (by omega)
    obtain ⟨u, huv, hdiff⟩ := hnear v
    have hu : u ∈ S := by rw [heq]; simp [huv]
    have hcover : univ.biUnion L ⊆ S.biUnion L ∪ (L v \ L u) := by
      intro c hc
      obtain ⟨j, _, hcj⟩ := mem_biUnion.mp hc
      by_cases hj : j ∈ S
      · exact mem_union_left _ (mem_biUnion.mpr ⟨j, hj, hcj⟩)
      have hjv : j = v := by
        by_contra hjv
        exact hj (by rw [heq]; simp [hjv])
      subst j
      by_cases hcu : c ∈ L u
      · exact mem_union_left _ (mem_biUnion.mpr ⟨u, hu, hcu⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hcj, hcu⟩)
    have hc := card_le_card hcover
    have hU := card_union_le (S.biUnion L) (L v \ L u)
    omega

/-- Any chosen common exceptional color can be reserved once the six cell
lists have size at least five, near partners, and a union of size at least seven. -/
theorem six_cells_avoiding_common_color {I C : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq C]
    (hI : Fintype.card I = 6) (L : I → Finset C)
    (hL : ∀ v, 5 ≤ (L v).card)
    (hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1)
    (htotal : 7 ≤ (univ.biUnion L).card) (w : C) :
    ∃ f : I → C, Function.Injective f ∧ ∀ v, f v ∈ L v ∧ f v ≠ w := by
  let A : I → Finset C := fun v => (L v).erase w
  have hA : ∀ v, 4 ≤ (A v).card := by
    intro v
    have hc := pred_card_le_card_erase (s := L v) (a := w)
    have hv := hL v
    dsimp [A]
    omega
  have hpartner : ∀ v, ∃ u, u ≠ v ∧ (A v \ A u).card ≤ 1 := by
    intro v
    obtain ⟨u, huv, hdiff⟩ := hnear v
    refine ⟨u, huv, le_trans (card_le_card ?_) hdiff⟩
    intro c hc
    obtain ⟨hcv, hcu⟩ := mem_sdiff.mp hc
    obtain ⟨hcw, hcv⟩ := mem_erase.mp hcv
    exact mem_sdiff.mpr ⟨hcv, fun h => hcu (mem_erase.mpr ⟨hcw, h⟩)⟩
  have htotalA : 6 ≤ (univ.biUnion A).card := by
    change 6 ≤ (univ.biUnion (fun v => (L v).erase w)).card
    rw [← erase_biUnion]
    have hc := pred_card_le_card_erase (s := univ.biUnion L) (a := w)
    omega
  obtain ⟨f, hf, hmem⟩ := six_list_hall hI A hA hpartner htotalA
  exact ⟨f, hf, fun v => ⟨(mem_erase.mp (hmem v)).2, (mem_erase.mp (hmem v)).1⟩⟩

/-- Overlapping exceptional exclusions make the two lists in a row differ
by at most one color. This is a finite-set fact, independent of host geometry. -/
theorem complement_list_difference {C : Type*} [DecidableEq C]
    (P F A B : Finset C) (hB : B.card ≤ 3) (hAB : 2 ≤ (A ∩ B).card) :
    ((P \ (F ∪ A)) \ (P \ (F ∪ B))).card ≤ 1 := by
  have hsub : (P \ (F ∪ A)) \ (P \ (F ∪ B)) ⊆ B \ A := by
    intro c hc
    obtain ⟨hca, hcb⟩ := mem_sdiff.mp hc
    obtain ⟨hcP, hcFA⟩ := mem_sdiff.mp hca
    have hcF : c ∉ F := fun h => hcFA (mem_union_left _ h)
    have hcA : c ∉ A := fun h => hcFA (mem_union_right _ h)
    have hcB : c ∈ B := by
      by_contra hcB
      exact hcb (mem_sdiff.mpr ⟨hcP, by simp [hcF, hcB]⟩)
    exact mem_sdiff.mpr ⟨hcB, hcA⟩
  have hcard := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at hcard
  have hc := card_le_card hsub
  omega

/-- The union of the six actual-form cell lists is the complement of the
spoke colors, common row exclusions, and common exceptional exclusions. -/
theorem six_cell_union (Q T Da Db : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20))
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i) :
    univ.biUnion (fun v : Fin 3 × Bool =>
      univ \ (Q ∪ F v.1 ∪ (if v.2 then Da else Db))) =
      univ \ (Q ∪ T ∪ (Da ∩ Db)) := by
  ext c
  constructor
  · intro hc
    obtain ⟨v, _, hcv⟩ := mem_biUnion.mp hc
    have hn := (mem_sdiff.mp hcv).2
    have hcQ : c ∉ Q := fun h => hn (mem_union_left _ (mem_union_left _ h))
    have hcT : c ∉ T := fun h =>
      hn (mem_union_left _ (mem_union_right _ ((hT c).mp h v.1)))
    have hcD : c ∉ Da ∩ Db := by
      intro h
      have hd : c ∈ (if v.2 then Da else Db) := by
        cases v.2 <;> simp_all
      exact hn (mem_union_right _ hd)
    exact mem_sdiff.mpr ⟨mem_univ _, by simp [hcQ, hcT, hcD]⟩
  · intro hc
    have hn := (mem_sdiff.mp hc).2
    have hcQ : c ∉ Q := fun h => hn (mem_union_left _ (mem_union_left _ h))
    have hcT : c ∉ T := fun h => hn (mem_union_left _ (mem_union_right _ h))
    have hcD : c ∉ Da ∩ Db := fun h => hn (mem_union_right _ h)
    have hi : ∃ i, c ∉ F i := by
      by_contra! h
      exact hcT ((hT c).mpr h)
    obtain ⟨i, hi⟩ := hi
    by_cases hDa : c ∈ Da
    · have hDb : c ∉ Db := fun h => hcD (mem_inter.mpr ⟨hDa, h⟩)
      exact mem_biUnion.mpr ⟨(i, false), mem_univ _, by simp [hcQ, hi, hDb]⟩
    · exact mem_biUnion.mpr ⟨(i, true), mem_univ _, by simp [hcQ, hi, hDa]⟩

/-- Concrete cell assignment used after either singleton-spoke repair.
Availability of the reserved color on the exceptions is a separate obligation. -/
theorem cell_assignment_common_color (Q T Da Db : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20)) (w : Fin 20)
    (hQ : Q.card ≤ 6) (hF : ∀ i, (F i).card ≤ 6)
    (hDa : Da.card ≤ 3) (hDb : Db.card ≤ 3) (hD : 2 ≤ (Da ∩ Db).card)
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i)
    (hcount : (Q ∪ T ∪ (Da ∩ Db)).card ≤ 13) :
    ∃ f : Fin 3 × Bool → Fin 20, Function.Injective f ∧ ∀ v,
      f v ∉ Q ∧ f v ∉ F v.1 ∧ f v ∉ (if v.2 then Da else Db) ∧ f v ≠ w := by
  let L : Fin 3 × Bool → Finset (Fin 20) := fun v =>
    univ \ (Q ∪ F v.1 ∪ (if v.2 then Da else Db))
  have hL : ∀ v, 5 ≤ (L v).card := by
    intro v
    have hv : (if v.2 then Da else Db).card ≤ 3 := by cases v.2 <;> assumption
    have h1 := card_union_le Q (F v.1)
    have h2 := card_union_le (Q ∪ F v.1) (if v.2 then Da else Db)
    have hrow := hF v.1
    dsimp [L]
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  have hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1 := by
    intro v
    refine ⟨(v.1, !v.2), ?_, ?_⟩
    · intro h
      have he := congrArg Prod.snd h
      cases v.2 <;> simp at he
    · cases h : v.2
      · simpa [L, h, inter_comm] using
          complement_list_difference univ (Q ∪ F v.1) Db Da hDa (by simpa [inter_comm] using hD)
      · simpa [L, h] using complement_list_difference univ (Q ∪ F v.1) Da Db hDb hD
  have htotal : 7 ≤ (univ.biUnion L).card := by
    rw [show univ.biUnion L = univ \ (Q ∪ T ∪ (Da ∩ Db)) from six_cell_union Q T Da Db F hT]
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  obtain ⟨f, hf, hmem⟩ := six_cells_avoiding_common_color (by decide) L hL hnear htotal w
  refine ⟨f, hf, ?_⟩
  intro v
  have hn := (mem_sdiff.mp (hmem v).1).2
  refine ⟨?_, ?_, ?_, (hmem v).2⟩
  · exact fun h => hn (mem_union_left _ (mem_union_left _ h))
  · exact fun h => hn (mem_union_left _ (mem_union_right _ h))
  · exact fun h => hn (mem_union_right _ h)


end K23Reduction
end Part27

section Part28
-- Source module: K23DirectCriterion

namespace K23Reduction

open Finset

variable {I C : Type*} [Fintype I] [DecidableEq I] [DecidableEq C]

/-- Six pairwise distinct cell colors and two exception colors, each different
from every cell color. The exception colors may coincide. -/
def TwoExceptionAssignment (L : I → Finset C) (Ea Eb : Finset C) : Prop :=
  ∃ (f : I → C) (x y : C), Function.Injective f ∧
    (∀ v, f v ∈ L v ∧ f v ≠ x ∧ f v ≠ y) ∧ x ∈ Ea ∧ y ∈ Eb

/-- With seven cell-union colors, two prescribed exception colors can be
reserved exactly when they coincide or at least one is outside that union. -/
theorem six_cells_avoiding_two_colors_iff
    (hI : Fintype.card I = 6) (L : I → Finset C)
    (hL : ∀ v, 5 ≤ (L v).card)
    (hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1)
    (hR : (univ.biUnion L).card = 7) (x y : C) :
    (∃ f : I → C, Function.Injective f ∧
      ∀ v, f v ∈ L v ∧ f v ≠ x ∧ f v ≠ y) ↔
      x = y ∨ x ∉ univ.biUnion L ∨ y ∉ univ.biUnion L := by
  constructor
  · rintro ⟨f, hf, hmem⟩
    by_cases hxy : x = y
    · exact Or.inl hxy
    by_cases hx : x ∈ univ.biUnion L
    · by_cases hy : y ∈ univ.biUnion L
      · exfalso
        let F : Finset C := univ.image f
        have hFcard : F.card = 6 := by
          dsimp only [F]
          rw [card_image_of_injective _ hf, card_univ, hI]
        have hFx : x ∉ F := by
          intro hc
          obtain ⟨v, _, hv⟩ := mem_image.mp hc
          exact (hmem v).2.1 hv
        have hFy : y ∉ F := by
          intro hc
          obtain ⟨v, _, hv⟩ := mem_image.mp hc
          exact (hmem v).2.2 hv
        have hFx' : x ∉ insert y F := by
          simpa only [mem_insert, not_or] using And.intro hxy hFx
        have hsub : insert x (insert y F) ⊆ univ.biUnion L := by
          refine insert_subset hx (insert_subset hy ?_)
          intro c hc
          obtain ⟨v, _, rfl⟩ := mem_image.mp hc
          exact mem_biUnion.mpr ⟨v, mem_univ _, (hmem v).1⟩
        have hcount := card_le_card hsub
        rw [card_insert_of_notMem hFx', card_insert_of_notMem hFy, hFcard, hR] at hcount
        omega
      · exact Or.inr (Or.inr hy)
    · exact Or.inr (Or.inl hx)
  · intro h
    have htotal : 7 ≤ (univ.biUnion L).card := by omega
    rcases h with hxy | hx | hy
    · subst y
      obtain ⟨f, hf, hmem⟩ := six_cells_avoiding_common_color hI L hL hnear htotal x
      exact ⟨f, hf, fun v => ⟨(hmem v).1, (hmem v).2, (hmem v).2⟩⟩
    · obtain ⟨f, hf, hmem⟩ := six_cells_avoiding_common_color hI L hL hnear htotal y
      refine ⟨f, hf, fun v => ⟨(hmem v).1, ?_, (hmem v).2⟩⟩
      intro heq
      have hv : f v ∈ univ.biUnion L := mem_biUnion.mpr ⟨v, mem_univ _, (hmem v).1⟩
      exact hx (heq ▸ hv)
    · obtain ⟨f, hf, hmem⟩ := six_cells_avoiding_common_color hI L hL hnear htotal x
      refine ⟨f, hf, fun v => ⟨(hmem v).1, (hmem v).2, ?_⟩⟩
      intro heq
      have hv : f v ∈ univ.biUnion L := mem_biUnion.mpr ⟨v, mem_univ _, (hmem v).1⟩
      exact hy (heq ▸ hv)

/-- Exact list criterion for the six-cell clique joined to two nonadjacent
exceptions. Each exceptional list is explicitly assumed nonempty. -/
theorem six_cells_two_exceptions_iff
    (hI : Fintype.card I = 6) (L : I → Finset C)
    (hL : ∀ v, 5 ≤ (L v).card)
    (hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1)
    (hR : (univ.biUnion L).card = 7) (Ea Eb : Finset C)
    (hEa : Ea.Nonempty) (hEb : Eb.Nonempty) :
    TwoExceptionAssignment L Ea Eb ↔
      (Ea ∩ Eb).Nonempty ∨ ((Ea ∪ Eb) \ univ.biUnion L).Nonempty := by
  constructor
  · rintro ⟨f, x, y, hf, hmem, hx, hy⟩
    have h := (six_cells_avoiding_two_colors_iff hI L hL hnear hR x y).mp ⟨f, hf, hmem⟩
    rcases h with hxy | hxR | hyR
    · subst y
      exact Or.inl ⟨x, mem_inter.mpr ⟨hx, hy⟩⟩
    · exact Or.inr ⟨x, mem_sdiff.mpr ⟨mem_union_left _ hx, hxR⟩⟩
    · exact Or.inr ⟨y, mem_sdiff.mpr ⟨mem_union_right _ hy, hyR⟩⟩
  · rintro (⟨w, hw⟩ | ⟨w, hw⟩)
    · obtain ⟨f, hf, hmem⟩ :=
        (six_cells_avoiding_two_colors_iff hI L hL hnear hR w w).mpr (Or.inl rfl)
      exact ⟨f, w, w, hf, hmem, (mem_inter.mp hw).1, (mem_inter.mp hw).2⟩
    · obtain ⟨hwUnion, hwR⟩ := mem_sdiff.mp hw
      rcases mem_union.mp hwUnion with hwEa | hwEb
      · obtain ⟨y, hy⟩ := hEb
        obtain ⟨f, hf, hmem⟩ :=
          (six_cells_avoiding_two_colors_iff hI L hL hnear hR w y).mpr (Or.inr (Or.inl hwR))
        exact ⟨f, w, y, hf, hmem, hwEa, hy⟩
      · obtain ⟨x, hx⟩ := hEa
        obtain ⟨f, hf, hmem⟩ :=
          (six_cells_avoiding_two_colors_iff hI L hL hnear hR x w).mpr (Or.inr (Or.inr hwR))
        exact ⟨f, x, w, hf, hmem, hx, hwEb⟩

/-- Failure supplies exactly the exceptional-list obstruction used by the
seven-union spoke-recoloring case: two subsets of the cell union, disjoint. -/
theorem seven_union_obstruction_iff
    (hI : Fintype.card I = 6) (L : I → Finset C)
    (hL : ∀ v, 5 ≤ (L v).card)
    (hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1)
    (hR : (univ.biUnion L).card = 7) (Ea Eb : Finset C)
    (hEa : Ea.Nonempty) (hEb : Eb.Nonempty) :
    ¬TwoExceptionAssignment L Ea Eb ↔
      Ea ⊆ univ.biUnion L ∧ Eb ⊆ univ.biUnion L ∧ Disjoint Ea Eb := by
  rw [six_cells_two_exceptions_iff hI L hL hnear hR Ea Eb hEa hEb]
  constructor
  · intro hn
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      by_contra hcR
      exact hn (Or.inr ⟨c, mem_sdiff.mpr ⟨mem_union_left _ hc, hcR⟩⟩)
    · intro c hc
      by_contra hcR
      exact hn (Or.inr ⟨c, mem_sdiff.mpr ⟨mem_union_right _ hc, hcR⟩⟩)
    · rw [disjoint_left]
      intro c hca hcb
      exact hn (Or.inl ⟨c, mem_inter.mpr ⟨hca, hcb⟩⟩)
  · rintro ⟨hEaR, hEbR, hdis⟩ (hcommon | hout)
    · obtain ⟨c, hc⟩ := hcommon
      exact (disjoint_left.mp hdis) (mem_inter.mp hc).1 (mem_inter.mp hc).2
    · obtain ⟨c, hc⟩ := hout
      obtain ⟨hcUnion, hcR⟩ := mem_sdiff.mp hc
      exact hcR ((mem_union.mp hcUnion).elim (fun h => hEaR h) (fun h => hEbR h))


end K23Reduction
end Part28

section Part29
-- Source module: K23LargeLists

namespace K23Reduction

open Finset

variable {I C : Type*} [Fintype I] [DecidableEq I] [DecidableEq C]

/-- Six lists of size at least six and union at least eight can reserve
any two colors under the same near-partner condition. -/
theorem six_cells_avoiding_two_colors
    (hI : Fintype.card I = 6) (L : I → Finset C)
    (hL : ∀ v, 6 ≤ (L v).card)
    (hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1)
    (hR : 8 ≤ (univ.biUnion L).card) (x y : C) :
    ∃ f : I → C, Function.Injective f ∧
      ∀ v, f v ∈ L v ∧ f v ≠ x ∧ f v ≠ y := by
  let A : I → Finset C := fun v => (L v).erase x
  have hA : ∀ v, 5 ≤ (A v).card := by
    intro v
    have hc := pred_card_le_card_erase (s := L v) (a := x)
    have hv := hL v
    dsimp [A]
    omega
  have hpartner : ∀ v, ∃ u, u ≠ v ∧ (A v \ A u).card ≤ 1 := by
    intro v
    obtain ⟨u, huv, hdiff⟩ := hnear v
    refine ⟨u, huv, le_trans (card_le_card ?_) hdiff⟩
    intro c hc
    obtain ⟨hcv, hcu⟩ := mem_sdiff.mp hc
    obtain ⟨hcx, hcv⟩ := mem_erase.mp hcv
    exact mem_sdiff.mpr ⟨hcv, fun h => hcu (mem_erase.mpr ⟨hcx, h⟩)⟩
  have htotal : 7 ≤ (univ.biUnion A).card := by
    change 7 ≤ (univ.biUnion (fun v => (L v).erase x)).card
    rw [← erase_biUnion]
    have hc := pred_card_le_card_erase (s := univ.biUnion L) (a := x)
    omega
  obtain ⟨f, hf, hmem⟩ := six_cells_avoiding_common_color hI A hA hpartner htotal y
  exact ⟨f, hf, fun v => ⟨(mem_erase.mp (hmem v).1).2,
    (mem_erase.mp (hmem v).1).1, (hmem v).2⟩⟩

/-- Nonempty exceptional lists suffice in this larger-list case. -/
theorem two_exception_assignment_of_large_union
    (hI : Fintype.card I = 6) (L : I → Finset C)
    (hL : ∀ v, 6 ≤ (L v).card)
    (hnear : ∀ v, ∃ u, u ≠ v ∧ (L v \ L u).card ≤ 1)
    (hR : 8 ≤ (univ.biUnion L).card) (Ea Eb : Finset C)
    (hEa : Ea.Nonempty) (hEb : Eb.Nonempty) :
    TwoExceptionAssignment L Ea Eb := by
  obtain ⟨x, hx⟩ := hEa
  obtain ⟨y, hy⟩ := hEb
  obtain ⟨f, hf, hmem⟩ := six_cells_avoiding_two_colors hI L hL hnear hR x y
  exact ⟨f, x, y, hf, hmem, hx, hy⟩


end K23Reduction
end Part29

section Part30
-- Source module: K23Interface

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A cell edge sees its row exclusions and the extra root-neighbor's
incident fixed edges. All connecting edges remain in the original host. -/
theorem fixed_row_exception_conflict (p a u : V) (U : Finset V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a) (hu : u ∈ U)
    (e : G.edgeSet) (hpe : p ∉ e.val) (hUe : ∀ v ∈ e.val, v ∉ U) :
    (strongConflict G).Adj ⟨s(p,u), (hp u).mpr (Or.inl hu)⟩ e ↔
      (∃ x ∈ e.val, G.Adj u x) ∨ a ∈ e.val := by
  rw [conflict_iff_endpoints]
  constructor
  · rintro ⟨_, y, hy, x, hx, hyx⟩
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · rcases hyx with rfl | hpx
      · exact (hpe hx).elim
      · rcases (hp x).mp hpx with hxU | hxa
        · exact (hUe x hx hxU).elim
        · exact Or.inr (hxa ▸ hx)
    · rcases hyx with rfl | hux
      · exact (hUe _ hx hu).elim
      · exact Or.inl ⟨x, hx, hux⟩
  · intro h
    have hne : (⟨s(p,u), (hp u).mpr (Or.inl hu)⟩ : G.edgeSet) ≠ e := by
      intro he
      apply hpe
      rw [← he]
      exact Sym2.mem_mk_left _ _
    rcases h with ⟨x, hx, hux⟩ | hae
    · exact ⟨hne, u, Sym2.mem_mk_right _ _, x, hx, Or.inr hux⟩
    · exact ⟨hne, p, Sym2.mem_mk_left _ _, a, hae,
        Or.inr ((hp a).mpr (Or.inr rfl))⟩

/-- Exact original-host fixed-edge conflict classification for a K2,3 cell. -/
theorem cell_fixed_conflict (p q a u : V) (U : Finset V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a) (hu : u ∈ U)
    (e : G.edgeSet) (he : e.val ∈ fixedEdges G p q U) :
    (strongConflict G).Adj ⟨s(p,u), (hp u).mpr (Or.inl hu)⟩ e ↔
      e.val ∈ rowSeen G p q U u ∨ e.val ∈ fixedAt G p q U a := by
  have hf := (mem_fixedEdges G p q U e.val).mp he
  rw [fixed_row_exception_conflict G p a u U hp hu e hf.2.1 hf.2.2.2]
  simp only [mem_rowSeen, he, true_and, fixedAt, mem_filter]

/-- The exact fixed forbidden-color set, without any assumption of distinct
fixed colors or disjoint row and exceptional exclusions. -/
theorem cell_fixed_colors (p q a u : V) (U : Finset V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a) (hu : u ∈ U)
    (c : Sym2 V → Fin 20) :
    fixedConflictColors G p q U ⟨s(p,u), (hp u).mpr (Or.inl hu)⟩ c =
      (rowSeen G p q U u).image c ∪ (fixedAt G p q U a).image c := by
  classical
  have hsets : (fixedEdges G p q U).filter (endpointConflict G s(p,u)) =
      rowSeen G p q U u ∪ fixedAt G p q U a := by
    ext f
    constructor
    · intro hf
      obtain ⟨hfix, hconf⟩ := mem_filter.mp hf
      let e : G.edgeSet := ⟨f, ((mem_fixedEdges G p q U f).mp hfix).1⟩
      exact mem_union.mpr ((cell_fixed_conflict G p q a u U hp hu e hfix).mp
        ((endpointConflict_iff G _ e).mp hconf))
    · intro hf
      have hfix : f ∈ fixedEdges G p q U := by
        rcases mem_union.mp hf with hrow | hat
        · exact ((mem_rowSeen G p q U u f).mp hrow).1
        · exact (mem_filter.mp hat).1
      let e : G.edgeSet := ⟨f, ((mem_fixedEdges G p q U f).mp hfix).1⟩
      exact mem_filter.mpr ⟨hfix, (endpointConflict_iff G _ e).mpr
        ((cell_fixed_conflict G p q a u U hp hu e hfix).mpr (mem_union.mp hf))⟩
  unfold fixedConflictColors
  rw [hsets, image_union]

/-- Every actual retained spoke conflicts with a cell at either root. -/
theorem cell_conflicts_all_spokes (p q a u : V) (U : Finset V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a) (hu : u ∈ U)
    (e : ↥(spokeEdges G p q U)) :
    (strongConflict G).Adj ⟨s(p,u), (hp u).mpr (Or.inl hu)⟩
      (spokeToEdge G p q U e) := by
  have he := (mem_spokeEdges G p q U e.val).mp e.property
  obtain ⟨y, hy, hye⟩ := he.2.2.2
  exact spoke_conflicts_cell G p u y ((hp u).mpr (Or.inl hu))
    ((hp y).mpr (Or.inl hy)) (spokeToEdge G p q U e) hye he.2.1

/-- Colors conflicting with an edge among all edges retained by vertex deletion. -/
noncomputable def retainedConflictColors (p q : V) (e : G.edgeSet)
    (c : Sym2 V → Fin 20) : Finset (Fin 20) := by
  classical
  exact (G.edgeFinset.filter (fun f => p ∉ f ∧ q ∉ f ∧ endpointConflict G e.val f)).image c

/-- Retained edges split into actual spokes and fixed edges. If all spokes
conflict with the target, their entire color image is forbidden. -/
theorem retained_colors_partition (p q : V) (U : Finset V)
    (e : G.edgeSet) (c : Sym2 V → Fin 20)
    (hspoke : ∀ f : G.edgeSet, f.val ∈ spokeEdges G p q U →
      (strongConflict G).Adj e f) :
    retainedConflictColors G p q e c =
      (spokeEdges G p q U).image c ∪ fixedConflictColors G p q U e c := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨f, hf, rfl⟩ := mem_image.mp ha
    obtain ⟨hed, hpe, hqe, hconf⟩ := mem_filter.mp hf
    have hedge : f ∈ G.edgeSet := by simpa using hed
    by_cases hrow : ∃ u ∈ U, u ∈ f
    · exact mem_union_left _ (mem_image.mpr
        ⟨f, (mem_spokeEdges G p q U f).mpr ⟨hedge, hpe, hqe, hrow⟩, rfl⟩)
    · have hfixed : f ∈ fixedEdges G p q U := by
        apply (mem_fixedEdges G p q U f).mpr
        exact ⟨hedge, hpe, hqe, fun u hue hu => hrow ⟨u, hu, hue⟩⟩
      exact mem_union_right _ (mem_image.mpr ⟨f, mem_filter.mpr ⟨hfixed, hconf⟩, rfl⟩)
  · intro ha
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨f, hf, rfl⟩ := mem_image.mp ha
      have hs := (mem_spokeEdges G p q U f).mp hf
      let f' : G.edgeSet := ⟨f, hs.1⟩
      exact mem_image.mpr ⟨f, mem_filter.mpr ⟨by simpa using hs.1,
        hs.2.1, hs.2.2.1, (endpointConflict_iff G e f').mpr (hspoke f' hf)⟩, rfl⟩
    · obtain ⟨f, hf, rfl⟩ := mem_image.mp ha
      obtain ⟨hfixed, hconf⟩ := mem_filter.mp hf
      have hs := (mem_fixedEdges G p q U f).mp hfixed
      exact mem_image.mpr ⟨f, mem_filter.mpr
        ⟨by simpa using hs.1, hs.2.1, hs.2.2.1, hconf⟩, rfl⟩

/-- Exact full-host forbidden colors for a cell, including every retained spoke. -/
theorem cell_retained_colors (p q a u : V) (U : Finset V)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a) (hu : u ∈ U)
    (c : Sym2 V → Fin 20) :
    retainedConflictColors G p q ⟨s(p,u), (hp u).mpr (Or.inl hu)⟩ c =
      (spokeEdges G p q U).image c ∪ (rowSeen G p q U u).image c ∪
        (fixedAt G p q U a).image c := by
  rw [retained_colors_partition G p q U _ c, cell_fixed_colors G p q a u U hp hu c,
    union_assoc]
  intro f hf
  exact cell_conflicts_all_spokes G p q a u U hp hu ⟨f.val, hf⟩

/-- If the exceptional centers are adjacent, their fixed incident-color
sets share at most the color of that connecting edge. -/
theorem fixedAt_color_inter_le_one_of_adj (p q a b : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c) (hab : G.Adj a b) :
    ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c).card ≤ 1 := by
  have hsub : (fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c ⊆
      {c s(a,b)} := by
    intro color hcolor
    obtain ⟨he, hf⟩ := mem_inter.mp hcolor
    obtain ⟨e, he, hce⟩ := mem_image.mp he
    obtain ⟨f, hf, hcf⟩ := mem_image.mp hf
    have hea := (mem_filter.mp he).2
    have hfb := (mem_filter.mp hf).2
    have hefix := (mem_fixedEdges G p q U e).mp (mem_filter.mp he).1
    have hffix := (mem_fixedEdges G p q U f).mp (mem_filter.mp hf).1
    have hef : e = f := by
      by_contra hne
      let e' : G.edgeSet := ⟨e, hefix.1⟩
      let f' : G.edgeSet := ⟨f, hffix.1⟩
      have hconf : (strongConflict G).Adj e' f' := by
        apply (conflict_iff_endpoints G e' f').mpr
        exact ⟨fun h => hne (congrArg Subtype.val h), a, hea, b, hfb, Or.inr hab⟩
      exact hc e' f' hefix.2.1 hefix.2.2.1 hffix.2.1 hffix.2.2.1 hconf
        (hce.trans hcf.symm)
    have heq : e = s(a,b) := (Sym2.mem_and_mem_iff hab.ne).mp ⟨hea, hef.symm ▸ hfb⟩
    exact mem_singleton.mpr (by rw [heq] at hce; exact hce.symm)
  simpa using card_le_card hsub

theorem not_adj_of_fixedAt_color_overlap (p q a b : V) (U : Finset V)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (hD : 2 ≤ ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c).card) :
    ¬G.Adj a b := by
  intro hab
  have h := fixedAt_color_inter_le_one_of_adj G p q a b U c hc hab
  omega


end K23Reduction
end Part30

section Part31
-- Source module: K23Blank

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*}

/-- The common-row indexing used by the six-list Hall assignment. -/
noncomputable def cellRow3 (U : Finset V) (hU : U.card = 3) (i : Fin 3) : V :=
  ((Finset.equivFinOfCardEq hU).symm i).val

theorem cellRow3_mem (U : Finset V) (hU : U.card = 3) (i : Fin 3) :
    cellRow3 U hU i ∈ U := ((Finset.equivFinOfCardEq hU).symm i).property

theorem cellRow3_injective (U : Finset V) (hU : U.card = 3) :
    Function.Injective (cellRow3 U hU) := by
  intro i j hij
  exact (Finset.equivFinOfCardEq hU).symm.injective (Subtype.ext hij)

theorem cellRow3_coverage (U : Finset V) (hU : U.card = 3) (u : V) (hu : u ∈ U) :
    ∃ i, cellRow3 U hU i = u := by
  exact ⟨(Finset.equivFinOfCardEq hU) ⟨u, hu⟩, by simp [cellRow3]⟩

/-- True selects the p/a side, as in the checked Hall lists. -/
def rootSide (p q : V) (j : Bool) : V := if j then p else q

theorem rootSide_injective (p q : V) (hpq : p ≠ q) :
    Function.Injective (rootSide p q) := by
  intro i j hij
  cases i <;> cases j <;> simp_all [rootSide, Ne.symm hpq]

variable (G : SimpleGraph V)

theorem rootSide_adj_common (p q : V) (U : Finset V)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (j : Bool) {u : V} (hu : u ∈ U) : G.Adj (rootSide p q j) u := by
  cases j
  · exact hq u hu
  · exact hp u hu

theorem rootSide_not_row (p q : V) (U : Finset V)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (j : Bool) : rootSide p q j ∉ U := by
  intro h
  exact G.loopless.irrefl _ (rootSide_adj_common G p q U hp hq j h)

/-- Six actual common-row edges, indexed by Fin 3 times Bool. -/
noncomputable def cellEdge3 (p q : V) (U : Finset V) (hU : U.card = 3)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (z : Fin 3 × Bool) : G.edgeSet :=
  ⟨s(rootSide p q z.2, cellRow3 U hU z.1),
    rootSide_adj_common G p q U hp hq z.2 (cellRow3_mem U hU z.1)⟩

/-- The two actual exceptional edges; true is pa and false is qb. -/
def exceptionEdge (p q a b : V) (hpa : G.Adj p a) (hqb : G.Adj q b)
    (j : Bool) : G.edgeSet := if j then ⟨s(p,a), hpa⟩ else ⟨s(q,b), hqb⟩

theorem cellEdge3_injective (p q : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u) :
    Function.Injective (cellEdge3 G p q U hU hp hq) := by
  intro z w hzw
  have heq := congrArg (fun e : G.edgeSet => e.val) hzw
  change s(rootSide p q z.2, cellRow3 U hU z.1) =
    s(rootSide p q w.2, cellRow3 U hU w.1) at heq
  have hr : cellRow3 U hU z.1 ∈ s(rootSide p q w.2, cellRow3 U hU w.1) := by
    rw [← heq]
    exact Sym2.mem_mk_right _ _
  have hc : rootSide p q z.2 ∈ s(rootSide p q w.2, cellRow3 U hU w.1) := by
    rw [← heq]
    exact Sym2.mem_mk_left _ _
  have hrows : cellRow3 U hU z.1 = cellRow3 U hU w.1 := by
    rcases Sym2.mem_iff.mp hr with hr | hr
    · exact (rootSide_not_row G p q U hp hq w.2 (hr ▸ cellRow3_mem U hU z.1)).elim
    · exact hr
  have hcols : rootSide p q z.2 = rootSide p q w.2 := by
    rcases Sym2.mem_iff.mp hc with hc | hc
    · exact hc
    · exact (rootSide_not_row G p q U hp hq z.2
        (hc.symm ▸ cellRow3_mem U hU w.1)).elim
  exact Prod.ext (cellRow3_injective U hU hrows) (rootSide_injective p q hpq hcols)

theorem exceptionEdge_true_ne_false (p q a b : V) (hpq : p ≠ q)
    (hn : ¬ G.Adj p q) (hpa : G.Adj p a) (hqb : G.Adj q b) :
    exceptionEdge G p q a b hpa hqb true ≠ exceptionEdge G p q a b hpa hqb false := by
  intro heq
  have he := congrArg (fun e : G.edgeSet => e.val) heq
  change s(p,a) = s(q,b) at he
  have hpm : p ∈ s(q,b) := by rw [← he]; exact Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.mp hpm with h | h
  · exact hpq h
  · exact hn (h.symm ▸ hqb.symm)

theorem exceptionEdge_injective (p q a b : V) (hpq : p ≠ q)
    (hn : ¬ G.Adj p q) (hpa : G.Adj p a) (hqb : G.Adj q b) :
    Function.Injective (exceptionEdge G p q a b hpa hqb) := by
  intro i j hij
  have hne := exceptionEdge_true_ne_false G p q a b hpq hn hpa hqb
  cases i <;> cases j
  · rfl
  · exact (hne hij.symm).elim
  · exact (hne hij).elim
  · rfl

theorem exceptionEdge_avoids_rows (p q a b : V) (U : Finset V)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (haU : a ∉ U) (hbU : b ∉ U) (hpa : G.Adj p a) (hqb : G.Adj q b)
    (j : Bool) : ∀ u ∈ (exceptionEdge G p q a b hpa hqb j).val, u ∉ U := by
  have hpU : p ∉ U := rootSide_not_row G p q U hp hq true
  have hqU : q ∉ U := rootSide_not_row G p q U hp hq false
  cases j <;> intro u hu
  · change u ∈ s(q,b) at hu
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact hqU
    · exact hbU
  · change u ∈ s(p,a) at hu
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact hpU
    · exact haU

theorem cellEdge3_ne_exceptionEdge (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (haU : a ∉ U) (hbU : b ∉ U) (hpa : G.Adj p a) (hqb : G.Adj q b)
    (z : Fin 3 × Bool) (j : Bool) :
    cellEdge3 G p q U hU hp hq z ≠ exceptionEdge G p q a b hpa hqb j := by
  intro heq
  have hr : cellRow3 U hU z.1 ∈ (exceptionEdge G p q a b hpa hqb j).val := by
    rw [← heq]
    exact Sym2.mem_mk_right _ _
  exact exceptionEdge_avoids_rows G p q a b U hp hq haU hbU hpa hqb j _ hr
    (cellRow3_mem U hU z.1)

/-- All distinct cell edges conflict in the full host. -/
theorem cellEdge3_conflict (p q : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (z w : Fin 3 × Bool) (hzw : z ≠ w) :
    (strongConflict G).Adj (cellEdge3 G p q U hU hp hq z) (cellEdge3 G p q U hU hp hq w) := by
  rw [conflict_iff_endpoints]
  exact ⟨fun h => hzw (cellEdge3_injective G p q U hU hpq hp hq h),
    rootSide p q z.2, Sym2.mem_mk_left _ _, cellRow3 U hU w.1, Sym2.mem_mk_right _ _,
    Or.inr (rootSide_adj_common G p q U hp hq z.2 (cellRow3_mem U hU w.1))⟩

/-- Every cell conflicts with both exceptional edges through a root-row connector. -/
theorem cellEdge3_exception_conflict (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (haU : a ∉ U) (hbU : b ∉ U) (hpa : G.Adj p a) (hqb : G.Adj q b)
    (z : Fin 3 × Bool) (j : Bool) :
    (strongConflict G).Adj (cellEdge3 G p q U hU hp hq z) (exceptionEdge G p q a b hpa hqb j) := by
  rw [conflict_iff_endpoints]
  refine ⟨cellEdge3_ne_exceptionEdge G p q a b U hU hp hq haU hbU hpa hqb z j,
    cellRow3 U hU z.1, Sym2.mem_mk_right _ _, rootSide p q j, ?_,
    Or.inr (rootSide_adj_common G p q U hp hq j (cellRow3_mem U hU z.1)).symm⟩
  cases j <;> exact Sym2.mem_mk_left _ _

/-- The two exception edges conflict precisely through ab; all other cross
connectors and endpoint coincidences are excluded by the exact neighborhoods. -/
theorem exceptionEdge_conflict_iff (p q a b : V) (U : Finset V)
    (hpq : p ≠ q) (hn : ¬ G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b) :
    (strongConflict G).Adj
      (exceptionEdge G p q a b ((hp a).mpr (Or.inr rfl)) ((hq b).mpr (Or.inr rfl)) true)
      (exceptionEdge G p q a b ((hp a).mpr (Or.inr rfl)) ((hq b).mpr (Or.inr rfl)) false) ↔
      G.Adj a b := by
  have hpa : G.Adj p a := (hp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hq b).mpr (Or.inr rfl)
  have hpb : ¬ G.Adj p b := fun h => ((hp b).mp h).elim hbU hab.symm
  have haq : ¬ G.Adj a q := fun h => ((hq a).mp h.symm).elim haU hab
  have hpbne : p ≠ b := fun h => hn (h.symm ▸ hqb.symm)
  have haqne : a ≠ q := fun h => hn (h ▸ hpa)
  rw [conflict_iff_endpoints]
  constructor
  · rintro ⟨_, x, hx, y, hy, hxy⟩
    change x ∈ s(p,a) at hx
    change y ∈ s(q,b) at hy
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> rcases Sym2.mem_iff.mp hy with rfl | rfl
    · exact (hxy.elim hpq hn).elim
    · exact (hxy.elim hpbne hpb).elim
    · exact (hxy.elim haqne haq).elim
    · exact hxy.resolve_left hab
  · intro hadj
    exact ⟨exceptionEdge_true_ne_false G p q a b hpq hn hpa hqb,
      a, Sym2.mem_mk_right _ _, b, Sym2.mem_mk_right _ _, Or.inr hadj⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Exact enumeration of all root-incident host edges by six cells or two exceptions. -/
theorem rootIncidentEdges_cell_exception_coverage (p q a b : V) (U : Finset V)
    (hU : U.card = 3) (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hpa : G.Adj p a) (hqb : G.Adj q b)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b) (e : G.edgeSet) :
    e.val ∈ rootIncidentEdges G p q ↔
      (∃ z, cellEdge3 G p q U hU hp hq z = e) ∨
      (∃ j, exceptionEdge G p q a b hpa hqb j = e) := by
  rw [mem_rootIncidentEdges, and_iff_right e.property]
  constructor
  · rintro (hpe | hqe)
    · obtain ⟨u, he⟩ := Sym2.mem_iff_exists.mp hpe
      have hpu : G.Adj p u := by simpa only [he, SimpleGraph.mem_edgeSet] using e.property
      rcases (hNp u).mp hpu with hu | hua
      · let u' : U := ⟨u, hu⟩
        refine Or.inl ⟨((Finset.equivFinOfCardEq hU) u', true), Subtype.ext ?_⟩
        simp [cellEdge3, cellRow3, rootSide, u', he]
      · exact Or.inr ⟨true, Subtype.ext (by simpa [exceptionEdge, hua] using he.symm)⟩
    · obtain ⟨u, he⟩ := Sym2.mem_iff_exists.mp hqe
      have hqu : G.Adj q u := by simpa only [he, SimpleGraph.mem_edgeSet] using e.property
      rcases (hNq u).mp hqu with hu | hub
      · let u' : U := ⟨u, hu⟩
        refine Or.inl ⟨((Finset.equivFinOfCardEq hU) u', false), Subtype.ext ?_⟩
        simp [cellEdge3, cellRow3, rootSide, u', he]
      · exact Or.inr ⟨false, Subtype.ext (by simpa [exceptionEdge, hub] using he.symm)⟩
  · rintro (⟨z, rfl⟩ | ⟨j, rfl⟩)
    · cases hz : z.2
      · exact Or.inr (by simp [cellEdge3, rootSide, hz])
      · exact Or.inl (by simp [cellEdge3, rootSide, hz])
    · cases j
      · exact Or.inr (Sym2.mem_mk_left _ _)
      · exact Or.inl (Sym2.mem_mk_left _ _)


end K23Reduction
end Part31

section Part32
-- Source module: K23TwoExceptionAssembly

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The two-side color assignment is proper on the actual exception edges
when adjacent outer endpoints force distinct colors. -/
theorem exception_assignment_compatible (p q a b : V) (U : Finset V)
    (hpq : p ≠ q) (hn : ¬ G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hpa : G.Adj p a) (hqb : G.Adj q b)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (w : Bool → Fin 20) (hpair : G.Adj a b → w true ≠ w false) :
    ∀ j k, (strongConflict G).Adj
      (exceptionEdge G p q a b hpa hqb j) (exceptionEdge G p q a b hpa hqb k) →
      w j ≠ w k := by
  intro j k h
  cases j <;> cases k
  · exact (h.ne rfl).elim
  · exact (hpair
      ((exceptionEdge_conflict_iff G p q a b U hpq hn hab haU hbU hNp hNq).mp h.symm)).symm
  · exact hpair ((exceptionEdge_conflict_iff G p q a b U hpq hn hab haU hbU hNp hNq).mp h)
  · exact (h.ne rfl).elim

/-- Six distinct compatible cell colors and two compatible exception colors
extend an actual spoke coloring, preserving every fixed host edge. -/
theorem color_from_two_exception_assignment (p q a b : V) (U : Finset V)
    (hU : U.card = 3) (hpq : p ≠ q) (hn : ¬ G.Adj p q) (haU : a ∉ U) (hbU : b ∉ U)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hpa : G.Adj p a) (hqb : G.Adj q b)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (havailable : ∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c)
    (f : Fin 3 × Bool → Fin 20) (hfinj : Function.Injective f) (w : Bool → Fin 20)
    (hfspokes : ∀ z, f z ∉ univ.image qcolor)
    (hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c)
    (hfw : ∀ z j, f z ≠ w j)
    (hwspokes : ∀ j, w j ∉ univ.image qcolor)
    (hwc : ∀ j, w j ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c)
    (hwproper : ∀ j k, (strongConflict G).Adj
      (exceptionEdge G p q a b hpa hqb j) (exceptionEdge G p q a b hpa hqb k) → w j ≠ w k) :
    ∃ C : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → C e = c e.val) ∧
      (∀ e : ↥(spokeEdges G p q U), C (spokeToEdge G p q U e) = qcolor e) ∧
      (∀ z, C (cellEdge3 G p q U hU hp hq z) = f z) ∧
      (∀ j, C (exceptionEdge G p q a b hpa hqb j) = w j) := by
  classical
  let cell := cellEdge3 G p q U hU hp hq
  let ex := exceptionEdge G p q a b hpa hqb
  have hinj : Function.Injective cell := cellEdge3_injective G p q U hU hpq hp hq
  have hexinj : Function.Injective ex := exceptionEdge_injective G p q a b hpq hn hpa hqb
  have hce : ∀ z j, cell z ≠ ex j :=
    cellEdge3_ne_exceptionEdge G p q a b U hU hp hq haU hbU hpa hqb
  have hcover : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q ↔
      (∃ z, cell z = e) ∨ (∃ j, ex j = e) :=
    rootIncidentEdges_cell_exception_coverage G p q a b U hU hp hq hpa hqb hNp hNq
  let blank : G.edgeSet → Fin 20 := fun e =>
    if he : ∃ z, cell z = e then f (Classical.choose he)
    else if hx : ∃ j, ex j = e then w (Classical.choose hx) else w false
  have hblank_cell : ∀ z, blank (cell z) = f z := by
    intro z
    have hz : ∃ t, cell t = cell z := ⟨z, rfl⟩
    dsimp only [blank]
    rw [dif_pos hz]
    exact congrArg f (hinj (Classical.choose_spec hz))
  have hblank_ex : ∀ j, blank (ex j) = w j := by
    intro j
    have hj : ¬ ∃ z, cell z = ex j := by
      rintro ⟨z, hz⟩
      exact hce z j hz
    have hx : ∃ k, ex k = ex j := ⟨j, rfl⟩
    dsimp only [blank]
    rw [dif_neg hj, dif_pos hx]
    exact congrArg w (hexinj (Classical.choose_spec hx))
  have hblank : ∀ e g : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      g.val ∈ rootIncidentEdges G p q → (strongConflict G).Adj e g → blank e ≠ blank g := by
    intro e g he hg hadj
    rcases (hcover e).mp he with ⟨z, rfl⟩ | ⟨j, rfl⟩ <;>
      rcases (hcover g).mp hg with ⟨t, rfl⟩ | ⟨k, rfl⟩
    · rw [hblank_cell, hblank_cell]
      exact fun h => hadj.ne (congrArg cell (hfinj h))
    · rw [hblank_cell, hblank_ex]
      exact hfw z k
    · rw [hblank_ex, hblank_cell]
      exact (hfw t j).symm
    · rw [hblank_ex, hblank_ex]
      exact hwproper j k hadj
  have hspokes : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      ∀ s : ↥(spokeEdges G p q U), blank e ≠ qcolor s := by
    intro e he s
    rcases (hcover e).mp he with ⟨z, rfl⟩ | ⟨j, rfl⟩
    · rw [hblank_cell]
      intro h
      exact hfspokes z (mem_image.mpr ⟨s, mem_univ _, h.symm⟩)
    · rw [hblank_ex]
      intro h
      exact hwspokes j (mem_image.mpr ⟨s, mem_univ _, h.symm⟩)
  have hfixed : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      blank e ∈ availableColors G p q U e c := by
    intro e he
    rcases (hcover e).mp he with ⟨z, rfl⟩ | ⟨j, rfl⟩
    · rw [hblank_cell]
      exact hfc z
    · rw [hblank_ex]
      exact hwc j
  obtain ⟨C, hCfixed, hCspoke, hCblank⟩ :=
    glue_root_spoke_fixed G p q U c hc qcolor havailable blank hblank hspokes hfixed
  refine ⟨C, hCfixed, hCspoke, ?_, ?_⟩
  · intro z
    exact (hCblank (cell z) ((hcover _).mpr (Or.inl ⟨z, rfl⟩))).trans (hblank_cell z)
  · intro j
    exact (hCblank (ex j) ((hcover _).mpr (Or.inr ⟨j, rfl⟩))).trans (hblank_ex j)


end K23Reduction
end Part32

section Part33
-- Source module: K23Assembly

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Six distinct compatible cell colors and one common compatible exception
color extend an actual spoke coloring, preserving every fixed host edge. -/
theorem color_from_common_exception_assignment (p q a b : V) (U : Finset V)
    (hU : U.card = 3) (hpq : p ≠ q) (hn : ¬ G.Adj p q)
    (hab : a ≠ b) (hnab : ¬ G.Adj a b) (haU : a ∉ U) (hbU : b ∉ U)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hpa : G.Adj p a) (hqb : G.Adj q b)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (qcolor : (spokeGraph G p q U).Coloring (Fin 20))
    (havailable : ∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c)
    (f : Fin 3 × Bool → Fin 20) (hfinj : Function.Injective f) (w : Fin 20)
    (hfspokes : ∀ z, f z ∉ univ.image qcolor)
    (hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c)
    (hfw : ∀ z, f z ≠ w)
    (hwspokes : w ∉ univ.image qcolor)
    (hwc : ∀ j, w ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c) :
    ∃ C : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → C e = c e.val) ∧
      (∀ e : ↥(spokeEdges G p q U), C (spokeToEdge G p q U e) = qcolor e) ∧
      (∀ z, C (cellEdge3 G p q U hU hp hq z) = f z) ∧
      (∀ j, C (exceptionEdge G p q a b hpa hqb j) = w) := by
  classical
  let cell := cellEdge3 G p q U hU hp hq
  let ex := exceptionEdge G p q a b hpa hqb
  have hinj : Function.Injective cell := cellEdge3_injective G p q U hU hpq hp hq
  have hce : ∀ z j, cell z ≠ ex j :=
    cellEdge3_ne_exceptionEdge G p q a b U hU hp hq haU hbU hpa hqb
  have hcover : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q ↔
      (∃ z, cell z = e) ∨ (∃ j, ex j = e) :=
    rootIncidentEdges_cell_exception_coverage G p q a b U hU hp hq hpa hqb hNp hNq
  have hexx : ∀ j k, ¬ (strongConflict G).Adj (ex j) (ex k) := by
    intro j k h
    cases j <;> cases k
    · exact (strongConflict G).loopless.irrefl _ h
    · exact hnab ((exceptionEdge_conflict_iff G p q a b U hpq hn hab haU hbU hNp hNq).mp h.symm)
    · exact hnab ((exceptionEdge_conflict_iff G p q a b U hpq hn hab haU hbU hNp hNq).mp h)
    · exact (strongConflict G).loopless.irrefl _ h
  let blank : G.edgeSet → Fin 20 := fun e =>
    if he : ∃ z, cell z = e then f (Classical.choose he) else w
  have hblank_cell : ∀ z, blank (cell z) = f z := by
    intro z
    have hz : ∃ t, cell t = cell z := ⟨z, rfl⟩
    dsimp only [blank]
    rw [dif_pos hz]
    exact congrArg f (hinj (Classical.choose_spec hz))
  have hblank_ex : ∀ j, blank (ex j) = w := by
    intro j
    have hj : ¬ ∃ z, cell z = ex j := by
      rintro ⟨z, hz⟩
      exact hce z j hz
    simp only [blank, dif_neg hj]
  have hblank : ∀ e g : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      g.val ∈ rootIncidentEdges G p q → (strongConflict G).Adj e g → blank e ≠ blank g := by
    intro e g he hg hadj
    rcases (hcover e).mp he with ⟨z, rfl⟩ | ⟨j, rfl⟩ <;>
      rcases (hcover g).mp hg with ⟨t, rfl⟩ | ⟨k, rfl⟩
    · rw [hblank_cell, hblank_cell]
      exact fun h => hadj.ne (congrArg cell (hfinj h))
    · rw [hblank_cell, hblank_ex]
      exact hfw z
    · rw [hblank_ex, hblank_cell]
      exact (hfw t).symm
    · exact (hexx j k hadj).elim
  have hspokes : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      ∀ s : ↥(spokeEdges G p q U), blank e ≠ qcolor s := by
    intro e he s
    rcases (hcover e).mp he with ⟨z, rfl⟩ | ⟨j, rfl⟩
    · rw [hblank_cell]
      intro h
      exact hfspokes z (mem_image.mpr ⟨s, mem_univ _, h.symm⟩)
    · rw [hblank_ex]
      intro h
      exact hwspokes (mem_image.mpr ⟨s, mem_univ _, h.symm⟩)
  have hfixed : ∀ e : G.edgeSet, e.val ∈ rootIncidentEdges G p q →
      blank e ∈ availableColors G p q U e c := by
    intro e he
    rcases (hcover e).mp he with ⟨z, rfl⟩ | ⟨j, rfl⟩
    · rw [hblank_cell]
      exact hfc z
    · rw [hblank_ex]
      exact hwc j
  obtain ⟨C, hCfixed, hCspoke, hCblank⟩ :=
    glue_root_spoke_fixed G p q U c hc qcolor havailable blank hblank hspokes hfixed
  refine ⟨C, hCfixed, hCspoke, ?_, ?_⟩
  · intro z
    exact (hCblank (cell z) ((hcover _).mpr (Or.inl ⟨z, rfl⟩))).trans (hblank_cell z)
  · intro j
    exact (hCblank (ex j) ((hcover _).mpr (Or.inr ⟨j, rfl⟩))).trans (hblank_ex j)


end K23Reduction
end Part33

section Part34
-- Source module: K23Exceptional

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An exceptional edge sees three other edges at its root and the three
common-row edges at the other root. These are six distinct blank neighbors. -/
theorem exceptional_blank_neighbors_ge_six (p q a : V) (U : Finset V)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hdp : G.degree p = 4)
    (hpa : G.Adj p a) (hU : U.card = 3)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u) :
    6 ≤ (conflictNeighborEdges G ⟨s(p,a), hpa⟩ ∩ rootIncidentEdges G p q).card := by
  classical
  let A := (G.incidenceFinset p).erase s(p,a)
  let B := U.map (Sym2.mkEmbedding q)
  have hpaI : s(p,a) ∈ G.incidenceFinset p := by
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, hpa]
  have hA : A.card = 3 := by
    simp [A, card_erase_of_mem hpaI, G.card_incidenceFinset_eq_degree, hdp]
  have hB : B.card = 3 := by simpa [B] using hU
  have hBI : B ⊆ G.incidenceFinset q := by
    intro f hf
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hf
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet] using hq u hu
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro f hfA hfB
    exact hn (G.adj_of_mem_incidenceSet hpq
      ((G.mem_incidenceFinset p f).mp (mem_erase.mp hfA).2)
      ((G.mem_incidenceFinset q f).mp (hBI hfB)))
  have hsub : A ∪ B ⊆ conflictNeighborEdges G ⟨s(p,a), hpa⟩ ∩
      rootIncidentEdges G p q := by
    intro f hf
    rcases mem_union.mp hf with hf | hf
    · have hi := (mem_erase.mp hf).2
      have hed := ((G.mem_incidenceFinset p f).mp hi).1
      have hpf := ((G.mem_incidenceFinset p f).mp hi).2
      exact mem_inter.mpr ⟨(mem_conflictNeighborEdges G _ f).mpr
        ⟨hed, (mem_erase.mp hf).1.symm, p, Sym2.mem_mk_left _ _, p, hpf, Or.inl rfl⟩,
        mem_union_left _ hi⟩
    · obtain ⟨u, hu, rfl⟩ := mem_map.mp hf
      have hqu := hq u hu
      have hne : s(p,a) ≠ s(q,u) := by
        intro heq
        have hpm : p ∈ s(q,u) := by rw [← heq]; exact Sym2.mem_mk_left _ _
        rcases Sym2.mem_iff.mp hpm with heq | heq
        · exact hpq heq
        · exact G.loopless.irrefl p (heq.symm ▸ hp u hu)
      refine mem_inter.mpr ⟨(mem_conflictNeighborEdges G _ s(q,u)).mpr
        ⟨hqu, hne, p, Sym2.mem_mk_left _ _, u, Sym2.mem_mk_right _ _, Or.inr (hp u hu)⟩, ?_⟩
      exact (mem_rootIncidentEdges G p q _).mpr ⟨hqu, Or.inr (Sym2.mem_mk_left _ _)⟩
  have hc := card_le_card hsub
  rwa [card_union_of_disjoint hdis, hA, hB] at hc

/-- Every actual retained spoke conflicts with an exceptional edge through
its common-row endpoint, irrespective of the other root's neighborhood. -/
theorem exceptional_conflicts_all_spokes (p q a : V) (U : Finset V)
    (hpa : G.Adj p a) (hp : ∀ u ∈ U, G.Adj p u) :
    spokeEdges G p q U ⊆ conflictNeighborEdges G ⟨s(p,a), hpa⟩ := by
  intro f hf
  have hs := (mem_spokeEdges G p q U f).mp hf
  obtain ⟨u, hu, huf⟩ := hs.2.2.2
  exact (edge_mem_conflictNeighborEdges G _ ⟨f, hs.1⟩).mpr
    (spoke_conflicts_cell G p a u hpa (hp u hu) ⟨f, hs.1⟩ huf hs.2.1)

/-- The actual fixed forbidden-color set at an exceptional edge has at most
eighteen minus the number of retained spokes. No color injectivity is assumed. -/
theorem exceptional_fixed_colors_card_le (p q a : V) (U : Finset V)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hdegree : G.maxDegree ≤ 4)
    (hdp : G.degree p = 4) (hpa : G.Adj p a) (hU : U.card = 3)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) :
    (fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c).card ≤
      18 - (spokeEdges G p q U).card := by
  classical
  let N := conflictNeighborEdges G ⟨s(p,a), hpa⟩
  let B := rootIncidentEdges G p q
  let M := spokeEdges G p q U
  have hMN : M ⊆ N := exceptional_conflicts_all_spokes G p q a U hpa hp
  have hdis : Disjoint (N ∩ B) M :=
    (rootIncidentEdges_disjoint_spokes G p q U).mono_left inter_subset_right
  have hpart : N ∩ (B ∪ M) = (N ∩ B) ∪ M := by
    ext f
    constructor
    · intro hf
      rcases mem_union.mp (mem_inter.mp hf).2 with hb | hm
      · exact mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hf).1, hb⟩)
      · exact mem_union_right _ hm
    · intro hf
      rcases mem_union.mp hf with hb | hm
      · exact mem_inter.mpr ⟨(mem_inter.mp hb).1, mem_union_left _ (mem_inter.mp hb).2⟩
      · exact mem_inter.mpr ⟨hMN hm, mem_union_right _ hm⟩
  have hcount := card_inter_add_card_sdiff N (B ∪ M)
  rw [hpart, card_union_of_disjoint hdis] at hcount
  have hN : N.card ≤ 24 := conflictNeighborEdges_card_le_twenty_four G hdegree _
  have hB : 6 ≤ (N ∩ B).card :=
    exceptional_blank_neighbors_ge_six G p q a U hpq hn hdp hpa hU hp hq
  have hF : (fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c).card ≤
      (N \ (B ∪ M)).card := by
    unfold fixedConflictColors
    rw [fixed_conflict_edges_eq_sdiff]
    exact card_image_le
  change (fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c).card ≤ 18 - M.card
  omega


end K23Reduction
end Part34

section Part35
-- Source module: K23Singleton

namespace K23Reduction

open Finset
open scoped BigOperators

/-- More safe colors than repeated occurrences force a safe singleton color class. -/
theorem safe_singleton_fiber {E C : Type*} [DecidableEq E] [DecidableEq C]
    (M : Finset E) (c : E → C) (W : Finset C) (hW : W ⊆ M.image c)
    (hcount : M.card - (M.image c).card < W.card) :
    ∃ w ∈ W, (M.filter (fun e => c e = w)).card = 1 := by
  classical
  by_contra h
  push Not at h
  have hbound (a : C) (ha : a ∈ M.image c) :
      1 + (if a ∈ W then 1 else 0) ≤ (M.filter (fun e => c e = a)).card := by
    have hpos := (fiber_card_ne_zero_iff_mem_image M c a).mpr ha
    by_cases haw : a ∈ W
    · have hne := h a haw
      simp only [if_pos haw]
      omega
    · simp only [if_neg haw]
      omega
  have hfilter : (M.image c).filter (fun a => a ∈ W) = W := by
    ext a
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun ha => ⟨hW ha, ha⟩⟩
  have hboole : (∑ a ∈ M.image c, if a ∈ W then 1 else 0) = W.card := by
    rw [← sum_filter]
    simp [hfilter]
  have hsum : (M.image c).card + W.card ≤ M.card := by
    calc
      (M.image c).card + W.card =
          ∑ a ∈ M.image c, (1 + if a ∈ W then 1 else 0) := by
        simp [sum_add_distrib, hboole]
      _ ≤ ∑ a ∈ M.image c, (M.filter (fun e => c e = a)).card :=
        sum_le_sum hbound
      _ = M.card := (card_eq_sum_card_image c M).symm
  omega

/-- The exact finite counting step in the seven-color-union repair.
The host graph supplies the displayed cardinality and containment hypotheses. -/
theorem seven_union_safe_singleton {E : Type*} [DecidableEq E]
    (M : Finset E) (c : E → Fin 20) (S Γa Γb : Finset (Fin 20))
    (hM : M.card ≤ 6) (hS : S.card ≤ 9)
    (hunion : ((M.image c) ∪ S).card = 13)
    (hSa : S ⊆ Γa) (hSb : S ⊆ Γb)
    (ha : Γa.card ≤ 18 - M.card) (hb : Γb.card ≤ 18 - M.card)
    (hsafe : univ \ (Γa ∪ Γb) ⊆ M.image c) :
    ∃ w ∈ univ \ (Γa ∪ Γb), (M.filter (fun e => c e = w)).card = 1 := by
  have hc := card_image_le (s := M) (f := c)
  have hcs := card_union_le (M.image c) S
  rw [hunion] at hcs
  have hsi : S.card ≤ (Γa ∩ Γb).card :=
    card_le_card (fun _ h => mem_inter.mpr ⟨hSa h, hSb h⟩)
  have hab := card_union_add_card_inter Γa Γb
  have hgu : (Γa ∪ Γb).card ≤ 20 := by
    simpa using card_le_univ (Γa ∪ Γb)
  have hw : (univ \ (Γa ∪ Γb)).card + (Γa ∪ Γb).card = 20 := by
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  apply safe_singleton_fiber M c (univ \ (Γa ∪ Γb)) hsafe
  omega


end K23Reduction
end Part35

section Part36
-- Source module: K23Recolor

namespace K23Reduction

open Finset SimpleGraph

/-- With degree-plus-two list slack, a singleton color can be freed by
changing exactly its vertex. Unions with sets avoiding that color do not grow. -/
theorem free_singleton_color {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : V → Finset (Fin 20)) (q : H.Coloring (Fin 20))
    (hq : ∀ v, q v ∈ L v) (v : V)
    (hslack : H.degree v + 2 ≤ (L v).card)
    (hsingle : ∀ u, q u = q v → u = v) :
    ∃ q' : H.Coloring (Fin 20), (∀ u, q' u ∈ L u) ∧
      (∀ u, u ≠ v → q' u = q u) ∧ (∀ u, q' u ≠ q v) ∧
      ∀ S : Finset (Fin 20), q v ∉ S →
        (univ.image q' ∪ S).card ≤ (univ.image q ∪ S).card := by
  classical
  let forbidden := (H.neighborFinset v).image q ∪ {q v}
  have hforbidden : forbidden.card < (L v).card := by
    have h1 := card_image_le (s := H.neighborFinset v) (f := q)
    have h2 := card_union_le ((H.neighborFinset v).image q) {q v}
    rw [H.card_neighborFinset_eq_degree] at h1
    simp only [card_singleton] at h2
    dsimp [forbidden]
    omega
  obtain ⟨a, haL, ha⟩ := exists_mem_notMem_of_card_lt_card hforbidden
  have hav : a ≠ q v := fun h => ha (mem_union_right _ (mem_singleton.mpr h))
  have haneighbor : ∀ u, H.Adj v u → a ≠ q u := by
    intro u hu he
    exact ha (mem_union_left _ (mem_image.mpr
      ⟨u, (H.mem_neighborFinset v u).mpr hu, he.symm⟩))
  let q' : H.Coloring (Fin 20) := Coloring.mk (Function.update q v a) (by
    intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy : y ≠ v := hxy.ne'
      simpa [Function.update_apply, hy] using haneighbor y hxy
    · by_cases hy : y = v
      · subst y
        simpa [Function.update_apply, hx] using (haneighbor x hxy.symm).symm
      · simpa [Function.update_apply, hx, hy] using q.valid hxy)
  have hvalue : q' v = a := by
    change Function.update (q : V → Fin 20) v a v = a
    simp
  have hsame : ∀ u, u ≠ v → q' u = q u := by
    intro u hu
    change Function.update (q : V → Fin 20) v a u = q u
    simp [hu]
  have hfree : ∀ u, q' u ≠ q v := by
    intro u
    by_cases hu : u = v
    · subst u; simpa [hvalue] using hav
    · rw [hsame u hu]
      exact fun h => hu (hsingle u h)
  refine ⟨q', ?_, hsame, hfree, ?_⟩
  · intro u
    by_cases hu : u = v
    · subst u; simpa [hvalue] using haL
    · rw [hsame u hu]; exact hq u
  · intro S hS
    have hw : q v ∈ univ.image q ∪ S :=
      mem_union_left _ (mem_image.mpr ⟨v, mem_univ _, rfl⟩)
    have hcover : univ.image q' ∪ S ⊆ (univ.image q ∪ S).erase (q v) ∪ {a} := by
      intro c hc
      rcases mem_union.mp hc with hc | hc
      · obtain ⟨u, _, rfl⟩ := mem_image.mp hc
        by_cases hu : u = v
        · subst u; exact mem_union_right _ (by simp [hvalue])
        · apply mem_union_left
          refine mem_erase.mpr ⟨hfree u, ?_⟩
          exact mem_union_left _ (mem_image.mpr ⟨u, mem_univ _, (hsame u hu).symm⟩)
      · exact mem_union_left _ (mem_erase.mpr
          ⟨by intro h; exact hS (h ▸ hc), mem_union_right _ hc⟩)
    have h1 := card_le_card hcover
    have h2 := card_union_le ((univ.image q ∪ S).erase (q v)) {a}
    have h3 := card_erase_add_one hw
    simp only [card_singleton] at h2
    omega

/-- The full list-theoretic seven-union repair. The input graph is the
actual spoke-conflict graph when applied to a host; its host counts and fixed
availability must still be supplied. Only one spoke color changes. -/
theorem seven_union_list_repair {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : V → Finset (Fin 20)) (q : H.Coloring (Fin 20))
    (hq : ∀ v, q v ∈ L v) (hslack : ∀ v, H.degree v + 2 ≤ (L v).card)
    (hV : Fintype.card V ≤ 6) (T Da Db Γa Γb : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20))
    (hTcard : T.card ≤ 6) (hF : ∀ i, (F i).card ≤ 6)
    (hDa : Da.card ≤ 3) (hDb : Db.card ≤ 3) (hD : 2 ≤ (Da ∩ Db).card)
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i)
    (hunion : (univ.image q ∪ (T ∪ (Da ∩ Db))).card = 13)
    (hSa : T ∪ (Da ∩ Db) ⊆ Γa) (hSb : T ∪ (Da ∩ Db) ⊆ Γb)
    (ha : Γa.card ≤ 18 - Fintype.card V) (hb : Γb.card ≤ 18 - Fintype.card V)
    (hsafe : univ \ (Γa ∪ Γb) ⊆ univ.image q) :
    ∃ v : V, ∃ q' : H.Coloring (Fin 20), ∃ w : Fin 20,
      (∀ u, q' u ∈ L u) ∧ (∀ u, u ≠ v → q' u = q u) ∧
      q' v ≠ q v ∧ (∀ u, q' u ≠ w) ∧ w ∉ Γa ∧ w ∉ Γb ∧
      ∃ f : Fin 3 × Bool → Fin 20, Function.Injective f ∧ ∀ x,
        f x ∉ univ.image q' ∧ f x ∉ F x.1 ∧
        f x ∉ (if x.2 then Da else Db) ∧ f x ≠ w := by
  classical
  have hS : (T ∪ (Da ∩ Db)).card ≤ 9 := by
    have h1 := card_union_le T (Da ∩ Db)
    have h2 := card_le_card (inter_subset_left : Da ∩ Db ⊆ Da)
    omega
  obtain ⟨w, hw, hsingle⟩ := seven_union_safe_singleton univ q (T ∪ (Da ∩ Db)) Γa Γb
    (by simpa using hV) hS hunion hSa hSb (by simpa using ha) (by simpa using hb) hsafe
  obtain ⟨v, hv⟩ := card_eq_one.mp hsingle
  have hvw : q v = w := by
    have : v ∈ univ.filter (fun u => q u = w) := by rw [hv]; simp
    exact (mem_filter.mp this).2
  have huniq : ∀ u, q u = q v → u = v := by
    intro u hu
    have : u ∈ univ.filter (fun u => q u = w) := by simp [hu, hvw]
    rw [hv] at this
    exact mem_singleton.mp this
  have hwΓa : w ∉ Γa := fun h => (mem_sdiff.mp hw).2 (mem_union_left _ h)
  have hwΓb : w ∉ Γb := fun h => (mem_sdiff.mp hw).2 (mem_union_right _ h)
  have hwS : q v ∉ T ∪ (Da ∩ Db) := by rw [hvw]; exact fun h => hwΓa (hSa h)
  obtain ⟨q', hq', hsame, hfree, hcount⟩ := free_singleton_color H L q hq v (hslack v) huniq
  have hQ : (univ.image q').card ≤ 6 := by
    have h := card_image_le (s := univ) (f := q')
    simp only [card_univ] at h
    omega
  have hnew : (univ.image q' ∪ T ∪ (Da ∩ Db)).card ≤ 13 := by
    have h := hcount (T ∪ (Da ∩ Db)) hwS
    rw [hunion] at h
    simpa [union_assoc] using h
  obtain ⟨f, hf, hmem⟩ := cell_assignment_common_color (univ.image q') T Da Db F w
    hQ hF hDa hDb hD hT hnew
  exact ⟨v, q', w, hq', hsame, hfree v, (by simpa [hvw] using hfree),
    hwΓa, hwΓb, f, hf, hmem⟩


end K23Reduction
end Part36

section Part37
-- Source module: K23HostLists

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem fixedEdges_swap (p q : V) (U : Finset V) :
    fixedEdges G q p U = fixedEdges G p q U := by
  ext e
  simp only [mem_fixedEdges]
  tauto

theorem fixedAt_swap (p q : V) (U : Finset V) (x : V) :
    fixedAt G q p U x = fixedAt G p q U x := by
  unfold fixedAt
  rw [fixedEdges_swap]

theorem rowSeen_swap (p q : V) (U : Finset V) (u : V) :
    rowSeen G q p U u = rowSeen G p q U u := by
  ext e
  simp only [mem_rowSeen, fixedEdges_swap]

theorem spokeEdges_swap (p q : V) (U : Finset V) :
    spokeEdges G q p U = spokeEdges G p q U := by
  ext e
  simp only [mem_spokeEdges]
  tauto

theorem fixedConflictColors_swap (p q : V) (U : Finset V)
    (e : G.edgeSet) (c : Sym2 V → Fin 20) :
    fixedConflictColors G q p U e c = fixedConflictColors G p q U e c := by
  classical
  unfold fixedConflictColors
  rw [fixedEdges_swap]

/-- Every fixed edge incident with an exception's outer endpoint conflicts
with the exception itself. This applies to an arbitrary fixed color function. -/
theorem exceptional_incident_colors_subset (p q a : V) (U : Finset V)
    (hpa : G.Adj p a) (c : Sym2 V → Fin 20) :
    (fixedAt G p q U a).image c ⊆ fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c := by
  classical
  intro color hcolor
  obtain ⟨f, hf, rfl⟩ := mem_image.mp hcolor
  have hfixed := (mem_filter.mp hf).1
  have hfa := (mem_filter.mp hf).2
  have hp := ((mem_fixedEdges G p q U f).mp hfixed).2.1
  exact mem_image.mpr ⟨f, mem_filter.mpr ⟨hfixed,
    ⟨fun h => hp (h ▸ Sym2.mem_mk_left p a), a, Sym2.mem_mk_right _ _, a, hfa, Or.inl rfl⟩⟩, rfl⟩

/-- The actual exceptional-list Hall obstruction forces the forbidden-set
containments and safe-color inclusion used by the singleton repair. -/
theorem exception_list_obstruction_exclusions (C T Da Db Γa Γb : Finset (Fin 20))
    (hCT : Disjoint C T) (ha : Da ⊆ Γa) (hb : Db ⊆ Γb)
    (hEa : univ \ (C ∪ Γa) ⊆ univ \ (C ∪ (T ∪ (Da ∩ Db))))
    (hEb : univ \ (C ∪ Γb) ⊆ univ \ (C ∪ (T ∪ (Da ∩ Db))))
    (hEab : Disjoint (univ \ (C ∪ Γa)) (univ \ (C ∪ Γb))) :
    T ∪ (Da ∩ Db) ⊆ Γa ∧ T ∪ (Da ∩ Db) ⊆ Γb ∧
      univ \ (Γa ∪ Γb) ⊆ C := by
  have hcommon (Γ : Finset (Fin 20))
      (hE : univ \ (C ∪ Γ) ⊆ univ \ (C ∪ (T ∪ (Da ∩ Db)))) : T ⊆ Γ := by
    intro color ht
    by_contra hnot
    have hC : color ∉ C := fun hc => Finset.disjoint_left.mp hCT hc ht
    have he := hE (mem_sdiff.mpr ⟨mem_univ color, by simp [hC, hnot]⟩)
    exact (mem_sdiff.mp he).2 (mem_union_right _ (mem_union_left _ ht))
  refine ⟨union_subset (hcommon Γa hEa) (inter_subset_left.trans ha),
    union_subset (hcommon Γb hEb) (inter_subset_right.trans hb), ?_⟩
  intro color hw
  by_contra hC
  have hΓ : color ∉ Γa ∧ color ∉ Γb := by
    simpa only [mem_union, not_or] using (mem_sdiff.mp hw).2
  exact Finset.disjoint_left.mp hEab
    (mem_sdiff.mpr ⟨mem_univ color, by simp [hC, hΓ.1]⟩)
    (mem_sdiff.mpr ⟨mem_univ color, by simp [hC, hΓ.2]⟩)

/-- The seven-union repair now runs on the actual host's retained spokes.
All numerical bounds, availability and exceptional exclusions are derived
from the host; the hypotheses specify this one Hall-obstruction case. -/
theorem seven_union_actual_spoke_repair (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hdegree : G.maxDegree ≤ 4)
    (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hpa : G.Adj p a) (hqb : G.Adj q b)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20))
    (hT : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c) :
    let C := (spokeEdges G p q U).image c
    let Da := (fixedAt G p q U a).image c
    let Db := (fixedAt G p q U b).image c
    let Γa := fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c
    let Γb := fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c
    2 ≤ (Da ∩ Db).card →
    (C ∪ (T ∪ (Da ∩ Db))).card = 13 →
    univ \ (C ∪ Γa) ⊆ univ \ (C ∪ (T ∪ (Da ∩ Db))) →
    univ \ (C ∪ Γb) ⊆ univ \ (C ∪ (T ∪ (Da ∩ Db))) →
    Disjoint (univ \ (C ∪ Γa)) (univ \ (C ∪ Γb)) →
    ∃ v : ↥(spokeEdges G p q U), ∃ q' : (spokeGraph G p q U).Coloring (Fin 20),
      ∃ w : Fin 20,
        (∀ e, q' e ∈ availableColors G p q U (spokeToEdge G p q U e) c) ∧
        (∀ e, e ≠ v → q' e = c e.val) ∧ q' v ≠ c v.val ∧
        (∀ e, q' e ≠ w) ∧ w ∉ Γa ∧ w ∉ Γb ∧
        ∃ f : Fin 3 × Bool → Fin 20, Function.Injective f ∧ ∀ z,
          f z ∉ univ.image q' ∧
          f z ∉ (rowSeen G p q U (cellRow3 U hU z.1)).image c ∧
          f z ∉ (if z.2 then Da else Db) ∧ f z ≠ w := by
  classical
  dsimp only
  intro hD hunion hEa hEb hEab
  let q0 := originalSpokeColoring G p q U c hc
  let F : Fin 3 → Finset (Fin 20) := fun i =>
    (rowSeen G p q U (cellRow3 U hU i)).image c
  have hF : ∀ i, (F i).card ≤ 6 := fun i =>
    row_colors_card_le_six_of_common G p q U _ hpq hdegree
      (cellRow3_mem U hU i) (hp _ (cellRow3_mem U hU i)) (hq _ (cellRow3_mem U hU i)) c
  have hTi : ∀ color, color ∈ T ↔ ∀ i, color ∈ F i := by
    intro color
    constructor
    · intro ht i
      exact (hT color).mp ht _ (cellRow3_mem U hU i)
    · intro h
      apply (hT color).mpr
      intro u hu
      obtain ⟨i, hi⟩ := cellRow3_coverage U hU u hu
      exact hi ▸ h i
  have hTcard : T.card ≤ 6 := (card_le_card
    (show T ⊆ F 0 from fun color hcolor => (hTi color).mp hcolor 0)).trans (hF 0)
  have hDa := fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c
  have hDb : ((fixedAt G p q U b).image c).card ≤ 3 := by
    simpa only [fixedAt_swap] using
      fixedAt_colors_card_le_three_of_adj_left G q p U b hdegree hqb c
  have hΓa := exceptional_fixed_colors_card_le G p q a U hpq hn hdegree hdp hpa hU hp hq c
  have hΓb : (fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c).card ≤
      18 - (spokeEdges G p q U).card := by
    simpa only [fixedConflictColors_swap, spokeEdges_swap] using
      exceptional_fixed_colors_card_le G q p b U hpq.symm (fun h => hn h.symm)
        hdegree hdq hqb hU hq hp c
  have hCT : Disjoint ((spokeEdges G p q U).image c) T :=
    spoke_colors_disjoint_common G p q U c hc T (fun u hu color ht => (hT color).mp ht u hu)
  have hDΓa := exceptional_incident_colors_subset G p q a U hpa c
  have hDΓb : (fixedAt G p q U b).image c ⊆ fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c := by
    simpa only [fixedAt_swap, fixedConflictColors_swap] using
      exceptional_incident_colors_subset G q p b U hqb c
  obtain ⟨hSa, hSb, hsafe⟩ := exception_list_obstruction_exclusions _ _ _ _ _ _
    hCT hDΓa hDΓb hEa hEb hEab
  have hV : Fintype.card ↥(spokeEdges G p q U) ≤ 6 := by
    simpa only [Fintype.card_coe] using spokeEdges_card_le_six_of_common G p q U hU hpq hdegree hp hq
  have hslack : ∀ e, (spokeGraph G p q U).degree e + 2 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card := by
    intro e
    have h := spoke_available_card_ge_degree_add_four G p q U hpq hn hdegree hdp hdq hp hq c e
    omega
  have hqimage : univ.image q0 = (spokeEdges G p q U).image c :=
    originalSpokeColoring_image G p q U c hc
  obtain ⟨v, q', w, hav, hsame, hchange, hfree, hwa, hwb, f, hfinj, hf⟩ :=
    seven_union_list_repair (spokeGraph G p q U)
      (fun e => availableColors G p q U (spokeToEdge G p q U e) c) q0
      (originalSpokeColoring_mem_available G p q U c hc) hslack hV T
      ((fixedAt G p q U a).image c) ((fixedAt G p q U b).image c)
      (fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c)
      (fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c)
      F hTcard hF hDa hDb hD hTi (by simpa only [hqimage] using hunion)
      hSa hSb (by simpa only [Fintype.card_coe] using hΓa)
      (by simpa only [Fintype.card_coe] using hΓb) (by simpa only [hqimage] using hsafe)
  exact ⟨v, q', w, hav, hsame, hchange, hfree, hwa, hwb, f, hfinj, hf⟩


end K23Reduction
end Part37

section Part38
-- Source module: K23SevenCase

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The six enumerated cells have exactly the fixed forbidden sets used by
the checked Hall assignment, on both root sides. -/
theorem cellEdge3_fixed_colors (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (z : Fin 3 × Bool) :
    fixedConflictColors G p q U (cellEdge3 G p q U hU hp hq z) c =
      (rowSeen G p q U (cellRow3 U hU z.1)).image c ∪
        (if z.2 then (fixedAt G p q U a).image c else (fixedAt G p q U b).image c) := by
  cases hz : z.2
  · have h := cell_fixed_colors G q p b (cellRow3 U hU z.1) U hNq
      (cellRow3_mem U hU z.1) c
    rw [fixedConflictColors_swap G p q U, rowSeen_swap G p q U, fixedAt_swap G p q U] at h
    simpa [cellEdge3, rootSide, hz] using h
  · have h := cell_fixed_colors G p q a (cellRow3 U hU z.1) U hNp
      (cellRow3_mem U hU z.1) c
    simpa [cellEdge3, rootSide, hz] using h

/-- Full-host extension in the seven-union obstruction case. Exactly one
actual retained spoke changes; every fixed edge and every other spoke agrees
with the input. This is one case of the full K2,3 extension, not the root bound. -/
theorem seven_union_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20))
    (hT : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c) :
    let C := (spokeEdges G p q U).image c
    let Da := (fixedAt G p q U a).image c
    let Db := (fixedAt G p q U b).image c
    let Γa := fixedConflictColors G p q U ⟨s(p,a), (hNp a).mpr (Or.inr rfl)⟩ c
    let Γb := fixedConflictColors G p q U ⟨s(q,b), (hNq b).mpr (Or.inr rfl)⟩ c
    2 ≤ (Da ∩ Db).card →
    (C ∪ (T ∪ (Da ∩ Db))).card = 13 →
    univ \ (C ∪ Γa) ⊆ univ \ (C ∪ (T ∪ (Da ∩ Db))) →
    univ \ (C ∪ Γb) ⊆ univ \ (C ∪ (T ∪ (Da ∩ Db))) →
    Disjoint (univ \ (C ∪ Γa)) (univ \ (C ∪ Γb)) →
    ∃ v : ↥(spokeEdges G p q U), ∃ color : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val) ∧
      (∀ e : ↥(spokeEdges G p q U), e ≠ v → color (spokeToEdge G p q U e) = c e.val) ∧
      color (spokeToEdge G p q U v) ≠ c v.val := by
  classical
  dsimp only
  intro hD hunion hEa hEb hEab
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hNq b).mpr (Or.inr rfl)
  obtain ⟨v, q', w, hav, hsame, hchange, hfree, hwa, hwb, f, hfinj, hf⟩ :=
    seven_union_actual_spoke_repair G p q a b U hU hpq hn hdegree hdp hdq
      hpa hqb hp hq c hc T hT hD hunion hEa hEb hEab
  have hnab : ¬G.Adj a b := not_adj_of_fixedAt_color_overlap G p q a b U c hc hD
  have hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c := by
    intro z
    rw [availableColors, cellEdge3_fixed_colors G p q a b U hU hp hq hNp hNq c z]
    exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_union.mp h).elim (hf z).2.1 (hf z).2.2.1⟩
  have hwspokes : w ∉ univ.image q' := by
    intro hw
    obtain ⟨e, _, he⟩ := mem_image.mp hw
    exact hfree e he
  have hwc : ∀ j, w ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c := by
    intro j
    cases j
    · exact mem_sdiff.mpr ⟨mem_univ _, hwb⟩
    · exact mem_sdiff.mpr ⟨mem_univ _, hwa⟩
  obtain ⟨color, hfixed, hspoke, _, _⟩ := color_from_common_exception_assignment G
    (p := p) (q := q) (a := a) (b := b) (U := U) (hU := hU)
    (hpq := hpq) (hn := hn) (hab := hab) (hnab := hnab) (haU := haU) (hbU := hbU)
    (hp := hp) (hq := hq) (hpa := hpa) (hqb := hqb) (hNp := hNp) (hNq := hNq)
    (c := c) (hc := hc) (qcolor := q') (havailable := hav)
    (f := f) (hfinj := hfinj) (w := w) (hfspokes := fun z => (hf z).1)
    (hfc := hfc) (hfw := fun z => (hf z).2.2.2) (hwspokes := hwspokes) (hwc := hwc)
  exact ⟨v, color, hfixed, fun e he => (hspoke e).trans (hsame e he),
    fun h => hchange ((hspoke v).symm.trans h)⟩


end K23Reduction
end Part38

section Part39
-- Source module: K23SixLargeHost

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the common-six case, a cell-list union of size at least eight permits
completion with every retained color unchanged, even if the exceptions conflict. -/
theorem six_large_union_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬ G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20)) (hT : T.card = 6)
    (hrows : ∀ u ∈ U, (rowSeen G p q U u).image c = T)
    (hspokes : (spokeEdges G p q U).card = 6)
    (hQ : ((spokeEdges G p q U).image c).card ≤ 5)
    (hunion : ((spokeEdges G p q U).image c ∪ T ∪
      ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c)).card ≤ 12) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val) ∧
      (∀ e : ↥(spokeEdges G p q U), color (spokeToEdge G p q U e) = c e.val) := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hNq b).mpr (Or.inr rfl)
  let Q := (spokeEdges G p q U).image c
  let Da := (fixedAt G p q U a).image c
  let Db := (fixedAt G p q U b).image c
  let Γa := fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c
  let Γb := fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c
  let Ea := univ \ (Q ∪ Γa)
  let Eb := univ \ (Q ∪ Γb)
  let L : Fin 3 × Bool → Finset (Fin 20) := fun z =>
    univ \ (Q ∪ T ∪ (if z.2 then Da else Db))
  have hDa : Da.card ≤ 3 :=
    fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c
  have hDb : Db.card ≤ 3 := by
    simpa only [fixedAt_swap] using
      fixedAt_colors_card_le_three_of_adj_left G q p U b hdegree hqb c
  have hL : ∀ z, 6 ≤ (L z).card := by
    intro z
    have hz : (if z.2 then Da else Db).card ≤ 3 := by cases z.2 <;> assumption
    have h1 := card_union_le Q T
    have h2 := card_union_le (Q ∪ T) (if z.2 then Da else Db)
    dsimp only [L]
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    change Q.card ≤ 5 at hQ
    omega
  have hnear : ∀ z, ∃ z', z' ≠ z ∧ (L z \ L z').card ≤ 1 := by
    intro z
    obtain ⟨i,hi⟩ := card_pos.mp
      (show 0 < ((univ : Finset (Fin 3)).erase z.1).card by simp)
    refine ⟨(i,z.2), ?_, ?_⟩
    · intro he
      exact (mem_erase.mp hi).1 (congrArg Prod.fst he)
    · simp [L]
  have hR : 8 ≤ (univ.biUnion L).card := by
    have heq : univ.biUnion L = univ \ (Q ∪ T ∪ (Da ∩ Db)) :=
      six_cell_union Q T Da Db (fun _ => T) (by simp)
    rw [heq, card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    change (Q ∪ T ∪ (Da ∩ Db)).card ≤ 12 at hunion
    omega
  have hΓa : Γa.card ≤ 12 := by
    have h := exceptional_fixed_colors_card_le G p q a U hpq hn hdegree hdp hpa hU hp hq c
    simpa only [hspokes] using h
  have hΓb : Γb.card ≤ 12 := by
    have h := exceptional_fixed_colors_card_le G q p b U hpq.symm (fun h => hn h.symm)
      hdegree hdq hqb hU hq hp c
    simpa only [fixedConflictColors_swap, spokeEdges_swap, hspokes] using h
  have hEcard : ∀ Γ : Finset (Fin 20), Γ.card ≤ 12 → 3 ≤ (univ \ (Q ∪ Γ)).card := by
    intro Γ hΓ
    have hbound := card_union_le Q Γ
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    change Q.card ≤ 5 at hQ
    omega
  have hEa : 3 ≤ Ea.card := hEcard Γa hΓa
  have hEb : 3 ≤ Eb.card := hEcard Γb hΓb
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < Ea.card by omega)
  have hEbErase : 0 < (Eb.erase x).card := by
    have h := pred_card_le_card_erase (s := Eb) (a := x)
    omega
  obtain ⟨y,hy'⟩ := card_pos.mp hEbErase
  have hy : y ∈ Eb := (mem_erase.mp hy').2
  have hxy : x ≠ y := (mem_erase.mp hy').1.symm
  obtain ⟨f,hfinj,hf⟩ := six_cells_avoiding_two_colors (by decide) L hL hnear hR x y
  let w : Bool → Fin 20 := fun j => if j then x else y
  let q0 := originalSpokeColoring G p q U c hc
  have hqimage : univ.image q0 = Q := originalSpokeColoring_image G p q U c hc
  have hfQ : ∀ z, f z ∉ Q := fun z h =>
    (mem_sdiff.mp (hf z).1).2 (mem_union_left _ (mem_union_left _ h))
  have hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c := by
    intro z
    rw [availableColors, cellEdge3_fixed_colors G p q a b U hU hp hq hNp hNq c z,
      hrows _ (cellRow3_mem U hU z.1)]
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro h
    exact (mem_sdiff.mp (hf z).1).2
      ((mem_union.mp h).elim (fun h => mem_union_left _ (mem_union_right _ h))
        (fun h => mem_union_right _ h))
  have hwQ : ∀ j, w j ∉ Q := by
    intro j
    cases j
    · exact fun h => (mem_sdiff.mp hy).2 (mem_union_left _ h)
    · exact fun h => (mem_sdiff.mp hx).2 (mem_union_left _ h)
  have hwc : ∀ j, w j ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c := by
    intro j
    cases j
    · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hy).2 (mem_union_right _ h)⟩
    · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hx).2 (mem_union_right _ h)⟩
  have hfw : ∀ z j, f z ≠ w j := by
    intro z j
    cases j
    · exact (hf z).2.2
    · exact (hf z).2.1
  have hwproper := exception_assignment_compatible G p q a b U hpq hn hab haU hbU
    hpa hqb hNp hNq w (fun _ => hxy)
  obtain ⟨color,hfixed,hspoke,_,_⟩ := color_from_two_exception_assignment G
    (p := p) (q := q) (a := a) (b := b) (U := U) (hU := hU) (hpq := hpq) (hn := hn)
    (haU := haU) (hbU := hbU) (hp := hp) (hq := hq) (hpa := hpa) (hqb := hqb)
    (hNp := hNp) (hNq := hNq) (c := c) (hc := hc) (qcolor := q0)
    (havailable := originalSpokeColoring_mem_available G p q U c hc)
    (f := f) (hfinj := hfinj) (w := w) (hfspokes := by simpa only [hqimage] using hfQ)
    (hfc := hfc) (hfw := hfw) (hwspokes := by simpa only [hqimage] using hwQ)
    (hwc := hwc) (hwproper := hwproper)
  exact ⟨color,hfixed,hspoke⟩


end K23Reduction
end Part39

section Part40
-- Source module: K23ForcedColor

namespace K23Reduction

open SimpleGraph Finset
open scoped BigOperators

/-- The original list bound retains weight at least five halves when a
nonneighbor is deleted and the forced color was absent. -/
lemma forced_color_scaled_weight (d r l : ℕ) (hpos : 1 ≤ d) (hd : d ≤ 4)
    (hr : r ≤ d) (hl : 3 * d + 2 ≤ l) :
    150 ≤ l * (60 / (r + 1)) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- If the forced color has no independent supporting pair, deleting one
vertex carrying it supplies a disjoint independent pair with another color. -/
theorem forced_color_second_pair {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 6) (L : V → Finset C) (P : Finset C)
    (hP : P.card ≤ 14) (hsub : ∀ u, L u ⊆ P)
    (hpos : ∀ u, 0 < G.degree u)
    (hcard : ∀ u, 3 * G.degree u + 2 ≤ (L u).card)
    (v : V) (c : C) (hcv : c ∈ L v)
    (hpair : ¬ ∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧ c ∈ L a ∧ c ∈ L b) :
    ∃ x y, x ≠ y ∧ x ≠ v ∧ y ≠ v ∧ ¬ G.Adj x y ∧
      ∃ d, d ≠ c ∧ d ∈ L x ∧ d ∈ L y := by
  classical
  have hd : ∀ u, G.degree u ≤ 4 := by
    intro u
    have hLu := (card_le_card (hsub u)).trans hP
    have hu := hcard u
    omega
  let S : Finset V := univ.erase v
  let H := G.induce (S : Set V)
  let K : S → Finset C := fun u => (L u.val).erase c
  have hScard : Fintype.card S = 5 := by
    rw [Fintype.card_coe]
    simp [S, hV]
  have hK : ∀ u : S, 3 * G.degree u.val + 1 ≤ (K u).card := by
    intro u
    have hu := hcard u.val
    have he := pred_card_le_card_erase (s := L u.val) (a := c)
    dsimp [K]
    omega
  have hres : ∀ u : S, H.degree u ≤ G.degree u.val :=
    Palette.induced_degree_le G S
  have h150 : ∀ u : S, 150 ≤ (K u).card * (60 / (H.degree u + 1)) := by
    intro u
    by_cases huv : G.Adj u.val v
    · have hstrict : H.degree u < G.degree u.val :=
        Palette.induced_degree_lt_of_neighbor_removed G S u huv (by simp [S])
      have hw := Palette.scaled_weight_strict _ _ _ (hd u.val) hstrict (hK u)
      omega
    · have huc : c ∉ L u.val := by
        intro hcu
        exact hpair ⟨u.val, v, (mem_erase.mp u.property).1, huv, hcu, hcv⟩
      have hKu : 3 * G.degree u.val + 2 ≤ (K u).card := by
        simpa [K, huc] using hcard u.val
      exact forced_color_scaled_weight _ _ _ (hpos u.val) (hd u.val) (hres u) hKu
  obtain ⟨z, hvz⟩ := (G.degree_pos_iff_exists_adj v).mp (hpos v)
  have hzS : z ∈ S := by simp [S, hvz.ne']
  let z' : S := ⟨z, hzS⟩
  have hstrict : H.degree z' < G.degree z :=
    Palette.induced_degree_lt_of_neighbor_removed G S z' hvz.symm (by simp [S])
  have h195 : 195 ≤ (K z').card * (60 / (H.degree z' + 1)) :=
    Palette.scaled_weight_strict _ _ _ (hd z) hstrict (hK z')
  have hremaining := sum_le_sum
    (s := (univ : Finset S).erase z') (fun u _ => h150 u)
  simp only [sum_const, card_erase_of_mem (mem_univ z'),
    card_univ, hScard, smul_eq_mul] at hremaining
  have htotal := sum_erase_add (univ : Finset S)
    (fun u => (K u).card * (60 / (H.degree u + 1))) (mem_univ z')
  have hcP : c ∈ P := hsub v hcv
  have hPsmall : (P.erase c).card ≤ 13 := by
    rw [card_erase_of_mem hcP]
    omega
  have hweight : (P.erase c).card * 60 <
      ∑ u : S, (K u).card * (60 / (H.degree u + 1)) := by omega
  have hKsub : ∀ u : S, K u ⊆ P.erase c := by
    intro u d hd
    obtain ⟨hdc, hdL⟩ := mem_erase.mp hd
    exact mem_erase.mpr ⟨hdc, hsub u.val hdL⟩
  obtain ⟨x, y, hxy, hnxy, d, hdx, hdy⟩ :=
    Palette.independent_pair_of_weight H K (P.erase c) hKsub 60 hweight
  refine ⟨x.val, y.val, ?_, (mem_erase.mp x.property).1,
    (mem_erase.mp y.property).1, hnxy, d,
    (mem_erase.mp hdx).1, (mem_erase.mp hdx).2, (mem_erase.mp hdy).2⟩
  exact fun he => hxy (Subtype.ext he)

/-- On six vertices with no isolates, the fourteen-color list bound admits
a coloring with at most five colors that uses any prescribed occurring color. -/
theorem forced_five_color_list_compression {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 6) (L : V → Finset C) (P : Finset C)
    (hP : P.card ≤ 14) (hsub : ∀ u, L u ⊆ P)
    (hpos : ∀ u, 0 < G.degree u)
    (hcard : ∀ u, 3 * G.degree u + 2 ≤ (L u).card)
    (c : C) (hc : ∃ v, c ∈ L v) :
    ∃ f : G.Coloring C, (∀ v, f v ∈ L v) ∧
      (univ.image f).card ≤ 5 ∧ c ∈ univ.image f := by
  classical
  have hslack1 : ∀ u, G.degree u + 2 ≤ (L u).card := by
    intro u
    have hu := hcard u
    omega
  have hslack2 : ∀ u, G.degree u + 3 ≤ (L u).card := by
    intro u
    have hu := hcard u
    have hp := hpos u
    omega
  by_cases hpair : ∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧ c ∈ L a ∧ c ∈ L b
  · obtain ⟨a, b, hab, hnab, hca, hcb⟩ := hpair
    have hiA : G.IsIndepSet ({a, b} : Finset V) := by
      simpa using Palette.indep_pair G hnab
    have hcA : ∀ u ∈ ({a, b} : Finset V), c ∈ L u := by
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact hca
      · have hub : u = b := mem_singleton.mp hu
        subst u
        exact hcb
    obtain ⟨f, hf, hfixed, himage⟩ :=
      one_set_list_completion G L hslack1 {a, b} hiA c hcA
    have hrest : (univ \ ({a, b} : Finset V)).card = 4 := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hV]
      simp [hab]
    refine ⟨f, hf, ?_, mem_image.mpr ⟨a, mem_univ _, hfixed a (by simp)⟩⟩
    omega
  · obtain ⟨v, hcv⟩ := hc
    obtain ⟨x, y, hxy, hxv, hyv, hnxy, d, hdc, hdx, hdy⟩ :=
      forced_color_second_pair G hV L P hP hsub hpos hcard v c hcv hpair
    have hdis : Disjoint ({v} : Finset V) ({x, y} : Finset V) := by
      apply Finset.disjoint_left.mpr
      intro u hu huxy
      have huv : u = v := mem_singleton.mp hu
      subst u
      rcases mem_insert.mp huxy with hvx | hvy
      · exact hxv hvx.symm
      · exact hyv (mem_singleton.mp hvy).symm
    have hiA : G.IsIndepSet ({v} : Finset V) := by
      intro a ha b hb hab
      have hav : a = v := by simpa using ha
      have hbv : b = v := by simpa using hb
      exact (hab (hav.trans hbv.symm)).elim
    have hiB : G.IsIndepSet ({x, y} : Finset V) := by
      simpa using Palette.indep_pair G hnxy
    have hcA : ∀ u ∈ ({v} : Finset V), c ∈ L u := by
      intro u hu
      have huv : u = v := mem_singleton.mp hu
      subst u
      exact hcv
    have hdB : ∀ u ∈ ({x, y} : Finset V), d ∈ L u := by
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact hdx
      · have huy : u = y := mem_singleton.mp hu
        subst u
        exact hdy
    obtain ⟨f, hf, hfixed, _, himage⟩ :=
      two_set_list_completion G L hslack2 {v} {x, y} hdis hiA hiB c d hdc.symm hcA hdB
    have hrest : (univ \ (({v} : Finset V) ∪ {x, y})).card = 3 := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hV,
        card_union_of_disjoint hdis]
      simp [hxy]
    refine ⟨f, hf, ?_, mem_image.mpr ⟨v, mem_univ _, hfixed v (by simp)⟩⟩
    omega


end K23Reduction
end Part40

section Part41
-- Source module: K23TwelveColor

namespace K23Reduction

open SimpleGraph Finset
open scoped BigOperators

/-- A linear lower bound in the number of deleted neighbors. -/
lemma twelve_scaled_weight (d r k l : ℕ) (hpos : 1 ≤ d) (hd : d ≤ 3)
    (hk : k ≤ 2) (hr : r + k = d) (hl : 3 * d + 1 ≤ l) :
    120 + 80 * k ≤ l * (60 / (r + 1)) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- Original degree one gives a stronger gain per deleted neighbor. -/
lemma twelve_matching_weight (r k l : ℕ) (hr : r + k = 1) (hl : 4 ≤ l) :
    120 + 120 * k ≤ l * (60 / (r + 1)) := by
  have : r = 0 ∨ r = 1 := by omega
  rcases this with rfl | rfl <;> simp <;> omega

/-- Count neighbors of a vertex inside a finite set containing all of them. -/
lemma twelve_neighbor_indicator_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (a : V)
    (hN : G.neighborFinset a ⊆ S) :
    (∑ u : S, if G.Adj u.val a then 1 else 0) = G.degree a := by
  classical
  rw [Finset.sum_coe_sort S (fun u : V => if G.Adj u a then (1 : ℕ) else 0),
    ← Finset.sum_filter]
  have hfilter : S.filter (fun u => G.Adj u a) = G.neighborFinset a := by
    ext u
    constructor
    · intro hu
      exact (G.mem_neighborFinset a u).mpr (mem_filter.mp hu).2.symm
    · intro hu
      exact mem_filter.mpr ⟨hN hu, ((G.mem_neighborFinset a u).mp hu).symm⟩
  rw [hfilter]
  simp

/-- The residual degree and the two removed-neighbor incidences partition
the original neighborhood, without assuming the removed pair independent. -/
lemma twelve_pair_loss_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V)
    (u : ↥((univ : Finset V) \ {a, b})) :
    (G.induce (↑((univ : Finset V) \ {a, b}) : Set V)).degree u +
      (G.neighborFinset u.val ∩ {a, b}).card = G.degree u.val := by
  classical
  rw [Palette.induced_degree_inter]
  have hinter : G.neighborFinset u.val ∩ (univ \ ({a, b} : Finset V)) =
      G.neighborFinset u.val \ {a, b} := by
    ext w
    simp
  rw [hinter]
  rw [card_sdiff_add_card_inter, G.card_neighborFinset_eq_degree]

/-- An independent removed pair has all its incident edges going to the
remaining vertices, so the total lost incidence is its degree sum. -/
lemma twelve_pair_loss_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V)
    (hab : a ≠ b) (hnab : ¬ G.Adj a b) :
    (∑ u : ↥((univ : Finset V) \ {a, b}),
      (G.neighborFinset u.val ∩ {a, b}).card) = G.degree a + G.degree b := by
  classical
  let S : Finset V := univ \ {a, b}
  have hNa : G.neighborFinset a ⊆ S := by
    intro u hu
    have hau := (G.mem_neighborFinset a u).mp hu
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hum
    rcases mem_insert.mp hum with rfl | hum
    · exact hau.ne rfl
    · have hub : u = b := mem_singleton.mp hum
      exact hnab (hub ▸ hau)
  have hNb : G.neighborFinset b ⊆ S := by
    intro u hu
    have hbu := (G.mem_neighborFinset b u).mp hu
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hum
    rcases mem_insert.mp hum with rfl | hum
    · exact hnab hbu.symm
    · have hub : u = b := mem_singleton.mp hum
      exact hbu.ne hub.symm
  have hloss : ∀ u : S, (G.neighborFinset u.val ∩ {a, b}).card =
      (if G.Adj u.val a then 1 else 0) + (if G.Adj u.val b then 1 else 0) := by
    intro u
    have heq : G.neighborFinset u.val ∩ {a, b} =
        ({a, b} : Finset V).filter (G.Adj u.val) := by
      ext w
      simp only [mem_inter, mem_filter, G.mem_neighborFinset]
      exact and_comm
    rw [heq]
    by_cases hua : G.Adj u.val a
    · by_cases hub : G.Adj u.val b
      · simp [Finset.filter_insert, Finset.filter_singleton, hua, hub, hab]
      · simp [Finset.filter_insert, Finset.filter_singleton, hua, hub]
    · by_cases hub : G.Adj u.val b
      · simp [Finset.filter_insert, Finset.filter_singleton, hua, hub]
      · simp [Finset.filter_insert, Finset.filter_singleton, hua, hub]
  change (∑ u : S, (G.neighborFinset u.val ∩ {a, b}).card) = _
  simp_rw [hloss]
  rw [sum_add_distrib, twelve_neighbor_indicator_sum G S a hNa,
    twelve_neighbor_indicator_sum G S b hNb]

/-- Choose a first shared-color independent pair so that either the graph
is a matching or the pair has degree sum at least three. -/
theorem twelve_first_pair {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 6) (L : V → Finset C) (P : Finset C)
    (hP : P.card ≤ 12) (hsub : ∀ u, L u ⊆ P)
    (hpos : ∀ u, 0 < G.degree u)
    (hcard : ∀ u, 3 * G.degree u + 2 ≤ (L u).card) :
    ∃ a b, a ≠ b ∧ ¬ G.Adj a b ∧ ∃ c, c ∈ L a ∧ c ∈ L b ∧
      ((∀ u, G.degree u = 1) ∨ 3 ≤ G.degree a + G.degree b) := by
  classical
  have hd : ∀ u, G.degree u ≤ 3 := by
    intro u
    have hu := hcard u
    have hp := (card_le_card (hsub u)).trans hP
    omega
  by_cases hmatch : ∀ u, G.degree u = 1
  · have hw : ∀ u, 150 ≤ (L u).card * (60 / (G.degree u + 1)) := by
      intro u
      have hu := hcard u
      rw [hmatch u] at hu ⊢
      simp
      omega
    have hsum := sum_le_sum (s := (univ : Finset V)) (fun u _ => hw u)
    simp only [sum_const, card_univ, hV, smul_eq_mul] at hsum
    have hweight : P.card * 60 < ∑ u, (L u).card * (60 / (G.degree u + 1)) := by
      omega
    obtain ⟨a, b, hab, hnab, c, hca, hcb⟩ :=
      Palette.independent_pair_of_weight G L P hsub 60 hweight
    exact ⟨a, b, hab, hnab, c, hca, hcb, Or.inl hmatch⟩
  · obtain ⟨a, ha⟩ := not_forall.mp hmatch
    have hage : 2 ≤ G.degree a := by
      have hp := hpos a
      omega
    have hsmall : (insert a (G.neighborFinset a)).card < (univ : Finset V).card := by
      have hi := card_insert_le a (G.neighborFinset a)
      have ha := hd a
      rw [G.card_neighborFinset_eq_degree] at hi
      simp only [card_univ, hV]
      omega
    obtain ⟨b, _, hb⟩ := exists_mem_notMem_of_card_lt_card hsmall
    have hba : b ≠ a := fun he => hb (mem_insert.mpr (Or.inl he))
    have hnab : ¬ G.Adj a b := fun h => hb
      (mem_insert_of_mem ((G.mem_neighborFinset a b).mpr h))
    have hLa : 8 ≤ (L a).card := by have h := hcard a; omega
    have hLb : 5 ≤ (L b).card := by have h := hcard b; have hp := hpos b; omega
    have hU := card_le_card (Finset.union_subset (hsub a) (hsub b))
    have hI := card_union_add_card_inter (L a) (L b)
    have hIpos : 0 < (L a ∩ L b).card := by omega
    obtain ⟨c, hc⟩ := card_pos.mp hIpos
    refine ⟨a, b, hba.symm, hnab, c, (mem_inter.mp hc).1, (mem_inter.mp hc).2, Or.inr ?_⟩
    have hbpos := hpos b
    omega

/-- Six vertices without isolates and the twelve-color list bound have a
proper available coloring using at most four distinct colors. -/
theorem twelve_color_four_color_compression {V C : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 6) (L : V → Finset C) (P : Finset C)
    (hP : P.card ≤ 12) (hsub : ∀ u, L u ⊆ P)
    (hpos : ∀ u, 0 < G.degree u)
    (hcard : ∀ u, 3 * G.degree u + 2 ≤ (L u).card) :
    ∃ f : G.Coloring C, (∀ v, f v ∈ L v) ∧ (univ.image f).card ≤ 4 := by
  classical
  have hd : ∀ u, G.degree u ≤ 3 := by
    intro u
    have hu := hcard u
    have hp := (card_le_card (hsub u)).trans hP
    omega
  obtain ⟨a, b, hab, hnab, c, hca, hcb, hchoice⟩ :=
    twelve_first_pair G hV L P hP hsub hpos hcard
  let S : Finset V := univ \ {a, b}
  let H := G.induce (S : Set V)
  let K : S → Finset C := fun u => (L u.val).erase c
  let k : S → ℕ := fun u => (G.neighborFinset u.val ∩ {a, b}).card
  have hScard : Fintype.card S = 4 := by
    rw [Fintype.card_coe]
    change (univ \ ({a, b} : Finset V)).card = 4
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV]
    simp [hab]
  have hK : ∀ u : S, 3 * G.degree u.val + 1 ≤ (K u).card := by
    intro u
    have hu := hcard u.val
    have he := pred_card_le_card_erase (s := L u.val) (a := c)
    dsimp [K]
    omega
  have hk : ∀ u : S, k u ≤ 2 := by
    intro u
    have hi := card_le_card (inter_subset_right :
      G.neighborFinset u.val ∩ {a, b} ⊆ ({a, b} : Finset V))
    simpa [k, hab] using hi
  have hdegrees : ∀ u : S, H.degree u + k u = G.degree u.val :=
    fun u => twelve_pair_loss_degree G a b u
  have hsumk : ∑ u : S, k u = G.degree a + G.degree b :=
    twelve_pair_loss_sum G a b hab hnab
  have h720 : 720 ≤ ∑ u : S, (K u).card * (60 / (H.degree u + 1)) := by
    rcases hchoice with hmatch | hbig
    · have hw : ∀ u : S,
          120 + 120 * k u ≤ (K u).card * (60 / (H.degree u + 1)) := by
        intro u
        have hr : H.degree u + k u = 1 := by simpa [hmatch u.val] using hdegrees u
        have hl : 4 ≤ (K u).card := by simpa [hmatch u.val] using hK u
        exact twelve_matching_weight _ _ _ hr hl
      have hsum := sum_le_sum (s := (univ : Finset S)) (fun u _ => hw u)
      have hscale : (∑ u : S, 120 * k u) = 120 * ∑ u : S, k u := by
        simpa only [smul_eq_mul] using Finset.sum_nsmul (univ : Finset S) 120 k
      rw [sum_add_distrib, hscale] at hsum
      simp only [sum_const, card_univ, hScard, smul_eq_mul] at hsum
      have htwo : ∑ u : S, k u = 2 := by simpa [hmatch a, hmatch b] using hsumk
      rw [htwo] at hsum
      omega
    · have hw : ∀ u : S,
          120 + 80 * k u ≤ (K u).card * (60 / (H.degree u + 1)) := by
        intro u
        exact twelve_scaled_weight _ _ _ _ (hpos u.val) (hd u.val) (hk u)
          (hdegrees u) (hK u)
      have hsum := sum_le_sum (s := (univ : Finset S)) (fun u _ => hw u)
      have hscale : (∑ u : S, 80 * k u) = 80 * ∑ u : S, k u := by
        simpa only [smul_eq_mul] using Finset.sum_nsmul (univ : Finset S) 80 k
      rw [sum_add_distrib, hscale] at hsum
      simp only [sum_const, card_univ, hScard, smul_eq_mul] at hsum
      rw [hsumk] at hsum
      omega
  have hcP : c ∈ P := hsub a hca
  have hPsmall : (P.erase c).card ≤ 11 := by
    rw [card_erase_of_mem hcP]
    omega
  have hweight : (P.erase c).card * 60 <
      ∑ u : S, (K u).card * (60 / (H.degree u + 1)) := by omega
  have hKsub : ∀ u : S, K u ⊆ P.erase c := by
    intro u d hd
    obtain ⟨hdc, hdL⟩ := mem_erase.mp hd
    exact mem_erase.mpr ⟨hdc, hsub u.val hdL⟩
  obtain ⟨x, y, hxy, hnxy, d, hdx, hdy⟩ :=
    Palette.independent_pair_of_weight H K (P.erase c) hKsub 60 hweight
  have hxy' : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  have hdis : Disjoint ({a, b} : Finset V) ({x.val, y.val} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro u hu huxy
    rcases mem_insert.mp huxy with hux | huy
    · have hxnot : x.val ∉ ({a, b} : Finset V) := (mem_sdiff.mp x.property).2
      exact hxnot (hux ▸ hu)
    · have huy' : u = y.val := mem_singleton.mp huy
      have hynot : y.val ∉ ({a, b} : Finset V) := (mem_sdiff.mp y.property).2
      exact hynot (huy' ▸ hu)
  have hiA : G.IsIndepSet ({a, b} : Finset V) := by
    simpa using Palette.indep_pair G hnab
  have hiB : G.IsIndepSet ({x.val, y.val} : Finset V) := by
    simpa using Palette.indep_pair G hnxy
  have hcA : ∀ u ∈ ({a, b} : Finset V), c ∈ L u := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact hca
    · have hub : u = b := mem_singleton.mp hu
      subst u
      exact hcb
  have hdB : ∀ u ∈ ({x.val, y.val} : Finset V), d ∈ L u := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact (mem_erase.mp hdx).2
    · have huy : u = y.val := mem_singleton.mp hu
      subst u
      exact (mem_erase.mp hdy).2
  have hslack : ∀ u, G.degree u + 3 ≤ (L u).card := by
    intro u
    have hu := hcard u
    have hp := hpos u
    omega
  have hcd : c ≠ d := (mem_erase.mp hdx).1.symm
  obtain ⟨f, hf, _, _, himage⟩ := two_set_list_completion G L hslack
    {a, b} {x.val, y.val} hdis hiA hiB c d hcd hcA hdB
  have hrest : (univ \ (({a, b} : Finset V) ∪ {x.val, y.val})).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV,
      card_union_of_disjoint hdis]
    simp [hab, hxy']
  refine ⟨f, hf, ?_⟩
  omega


end K23Reduction
end Part41

section Part42
-- Source module: K23SixCompression

namespace K23Reduction

open SimpleGraph Finset TwinReduction

/-- Compress six lists while reserving room for six common fixed colors and
at most three additional exceptional colors. This is a finite-list result. -/
theorem six_color_list_compression_with_exception {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hV : Fintype.card V = 6)
    (L : V → Finset (Fin 20)) (T : Finset (Fin 20)) (hT : T.card = 6)
    (D : Finset (Fin 20)) (hD : D.card ≤ 3)
    (hsub : ∀ v, L v ⊆ univ \ T)
    (hpos : ∀ v, 0 < H.degree v)
    (hcard : ∀ v, 3 * H.degree v + 2 ≤ (L v).card) :
    ∃ q : H.Coloring (Fin 20), (∀ v, q v ∈ L v) ∧
      (univ.image q).card ≤ 5 ∧ (univ.image q ∪ T ∪ D).card ≤ 13 := by
  classical
  let E := D \ T
  have hE : E.card ≤ 3 := (card_le_card sdiff_subset).trans hD
  have hP : (univ \ T).card ≤ 14 := by
    simp [card_sdiff_of_subset (subset_univ T), hT]
  have hjoin : ∀ Q : Finset (Fin 20), (Q ∪ E).card ≤ 7 → (Q ∪ T ∪ D).card ≤ 13 := by
    intro Q hQ
    have heq : Q ∪ T ∪ D = T ∪ (Q ∪ E) := by
      ext a
      simp only [E, mem_union, mem_sdiff]
      tauto
    rw [heq]
    have hbound := card_union_le T (Q ∪ E)
    omega
  by_cases hsmall : E.card ≤ 1
  · obtain ⟨v,_⟩ := card_pos.mp (show 0 < (univ : Finset V).card by simp [hV])
    have hLpos : 0 < (L v).card := by
      have hv := hcard v
      omega
    obtain ⟨a,ha⟩ := card_pos.mp hLpos
    obtain ⟨q,hq,hfive,_⟩ := forced_five_color_list_compression H hV L (univ \ T)
      hP hsub hpos hcard a ⟨v,ha⟩
    refine ⟨q,hq,hfive,hjoin (univ.image q) ?_⟩
    have hbound := card_union_le (univ.image q) E
    omega
  · by_cases hoccurs : ∃ a ∈ E, ∃ v, a ∈ L v
    · obtain ⟨a,haE,haL⟩ := hoccurs
      obtain ⟨q,hq,hfive,haQ⟩ := forced_five_color_list_compression H hV L (univ \ T)
        hP hsub hpos hcard a haL
      have hinter : 0 < (univ.image q ∩ E).card :=
        card_pos.mpr ⟨a,mem_inter.mpr ⟨haQ,haE⟩⟩
      have hcount := card_union_add_card_inter (univ.image q) E
      refine ⟨q,hq,hfive,hjoin (univ.image q) ?_⟩
      omega
    · have hsub' : ∀ v, L v ⊆ univ \ (T ∪ E) := by
        intro v a ha
        refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
        intro hbad
        rcases mem_union.mp hbad with haT | haE
        · exact (mem_sdiff.mp (hsub v ha)).2 haT
        · exact hoccurs ⟨a,haE,v,ha⟩
      have hdis : Disjoint T E := by
        apply Finset.disjoint_left.mpr
        intro a haT haE
        exact (mem_sdiff.mp haE).2 haT
      have hPsmall : (univ \ (T ∪ E)).card ≤ 12 := by
        rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hdis, hT]
        simp only [card_univ, Fintype.card_fin]
        omega
      obtain ⟨q,hq,hfour⟩ := twelve_color_four_color_compression H hV L (univ \ (T ∪ E))
        hPsmall hsub' hpos hcard
      refine ⟨q,hq,by omega,hjoin (univ.image q) ?_⟩
      have hbound := card_union_le (univ.image q) E
      omega

open scoped Classical in
/-- Actual full-host spoke compression in the common-six-color case.
This colors only the retained spokes; it does not assemble a coloring of the host. -/
theorem six_actual_spoke_compression {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hdegree : G.maxDegree ≤ 4)
    (hp : ∀ u ∈ U, G.Adj p u) (hq : ∀ u ∈ U, G.Adj q u)
    (c : Sym2 V → Fin 20) (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c)
    (D : Finset (Fin 20)) (hD : D.card ≤ 3) :
    ∃ qcolor : (spokeGraph G p q U).Coloring (Fin 20),
      (∀ e, qcolor e ∈ availableColors G p q U (spokeToEdge G p q U e) c) ∧
      (univ.image qcolor).card ≤ 5 ∧ (univ.image qcolor ∪ T ∪ D).card ≤ 13 := by
  classical
  obtain ⟨hspokes,hnoisolates,hsub,hcard⟩ :=
    six_actual_geometry_and_lists G p q U hU hpq hdegree hp hq c T hT hcommon
  have hV : Fintype.card ↥(spokeEdges G p q U) = 6 := by
    simpa only [Fintype.card_coe] using hspokes
  have hpos : ∀ e, 0 < (spokeGraph G p q U).degree e := fun e =>
    ((spokeGraph G p q U).degree_pos_iff_exists_adj e).mpr (hnoisolates e)
  exact six_color_list_compression_with_exception (spokeGraph G p q U) hV
    (fun e => availableColors G p q U (spokeToEdge G p q U e) c)
    T hT D hD hsub hpos hcard


end K23Reduction
end Part42

section Part43
-- Source module: K23SevenDispatch

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

/-- The exceptional list has at least two colors after excluding at most m
spoke colors and at most 18-m fixed colors. -/
theorem exceptional_list_card_ge_two (Q Γ : Finset (Fin 20)) (m : ℕ)
    (hm : m ≤ 6) (hQ : Q.card ≤ m) (hΓ : Γ.card ≤ 18 - m) :
    2 ≤ (univ \ (Q ∪ Γ)).card := by
  have h := card_union_le Q Γ
  rw [card_sdiff_of_subset (subset_univ _)]
  simp only [card_univ, Fintype.card_fin]
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every seven-union host with exceptional overlap at least two extends.
The exceptional-list obstruction is derived when direct coloring fails.
At most one actual retained spoke changes, and every fixed color is preserved. -/
theorem seven_union_host_dispatch (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20))
    (hT : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c)
    (hD : 2 ≤ ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c).card)
    (hunion : ((spokeEdges G p q U).image c ∪
      (T ∪ ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c))).card = 13) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val) ∧
      (univ.filter (fun e : ↥(spokeEdges G p q U) =>
        color (spokeToEdge G p q U e) ≠ c e.val)).card ≤ 1 := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hNq b).mpr (Or.inr rfl)
  let Q := (spokeEdges G p q U).image c
  let Da := (fixedAt G p q U a).image c
  let Db := (fixedAt G p q U b).image c
  let Γa := fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c
  let Γb := fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c
  let Ea := univ \ (Q ∪ Γa)
  let Eb := univ \ (Q ∪ Γb)
  let F : Fin 3 → Finset (Fin 20) := fun i =>
    (rowSeen G p q U (cellRow3 U hU i)).image c
  let L : Fin 3 × Bool → Finset (Fin 20) := fun z =>
    univ \ (Q ∪ F z.1 ∪ (if z.2 then Da else Db))
  let R := univ \ (Q ∪ (T ∪ (Da ∩ Db)))
  have hm : (spokeEdges G p q U).card ≤ 6 :=
    spokeEdges_card_le_six_of_common G p q U hU hpq hdegree hp hq
  have hQ : Q.card ≤ 6 := card_image_le.trans hm
  have hF : ∀ i, (F i).card ≤ 6 := fun i =>
    row_colors_card_le_six_of_common G p q U _ hpq hdegree
      (cellRow3_mem U hU i) (hp _ (cellRow3_mem U hU i))
      (hq _ (cellRow3_mem U hU i)) c
  have hDa : Da.card ≤ 3 :=
    fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c
  have hDb : Db.card ≤ 3 := by
    simpa only [fixedAt_swap] using
      fixedAt_colors_card_le_three_of_adj_left G q p U b hdegree hqb c
  have hTi : ∀ color, color ∈ T ↔ ∀ i, color ∈ F i := by
    intro color
    constructor
    · intro ht i
      exact (hT color).mp ht _ (cellRow3_mem U hU i)
    · intro ht
      apply (hT color).mpr
      intro u hu
      obtain ⟨i, hi⟩ := cellRow3_coverage U hU u hu
      exact hi ▸ ht i
  have hR : univ.biUnion L = R := by
    simpa only [L, R, union_assoc] using six_cell_union Q T Da Db F hTi
  have hRcard : (univ.biUnion L).card = 7 := by
    rw [hR]
    change (univ \ (Q ∪ (T ∪ (Da ∩ Db)))).card = 7
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    change 20 - ((spokeEdges G p q U).image c ∪
      (T ∪ ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c))).card = 7
    omega
  have hL : ∀ z, 5 ≤ (L z).card := by
    intro z
    have hz : (if z.2 then Da else Db).card ≤ 3 := by cases z.2 <;> assumption
    have h1 := card_union_le Q (F z.1)
    have h2 := card_union_le (Q ∪ F z.1) (if z.2 then Da else Db)
    have hrow := hF z.1
    dsimp only [L]
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  have hnear : ∀ z, ∃ z', z' ≠ z ∧ (L z \ L z').card ≤ 1 := by
    intro z
    refine ⟨(z.1, !z.2), ?_, ?_⟩
    · intro he
      have he' := congrArg Prod.snd he
      cases z.2 <;> simp at he'
    · cases hz : z.2
      · simpa [L, hz, inter_comm] using
          complement_list_difference univ (Q ∪ F z.1) Db Da hDa
            (by simpa only [inter_comm] using hD)
      · simpa [L, hz] using complement_list_difference univ (Q ∪ F z.1) Da Db hDb hD
  have hΓa : Γa.card ≤ 18 - (spokeEdges G p q U).card :=
    exceptional_fixed_colors_card_le G p q a U hpq hn hdegree hdp hpa hU hp hq c
  have hΓb : Γb.card ≤ 18 - (spokeEdges G p q U).card := by
    simpa only [fixedConflictColors_swap, spokeEdges_swap] using
      exceptional_fixed_colors_card_le G q p b U hpq.symm (fun h => hn h.symm)
        hdegree hdq hqb hU hq hp c
  have hEa : Ea.Nonempty := card_pos.mp (by
    have h := exceptional_list_card_ge_two Q Γa _ hm card_image_le hΓa
    change 0 < (univ \ (Q ∪ Γa)).card
    omega)
  have hEb : Eb.Nonempty := card_pos.mp (by
    have h := exceptional_list_card_ge_two Q Γb _ hm card_image_le hΓb
    change 0 < (univ \ (Q ∪ Γb)).card
    omega)
  by_cases hassign : TwoExceptionAssignment L Ea Eb
  · obtain ⟨f, x, y, hfinj, hf, hx, hy⟩ := hassign
    let w : Bool → Fin 20 := fun j => if j then x else y
    let q0 := originalSpokeColoring G p q U c hc
    have hqimage : univ.image q0 = Q := originalSpokeColoring_image G p q U c hc
    have hfQ : ∀ z, f z ∉ Q := fun z h =>
      (mem_sdiff.mp (hf z).1).2 (mem_union_left _ (mem_union_left _ h))
    have hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c := by
      intro z
      rw [availableColors, cellEdge3_fixed_colors G p q a b U hU hp hq hNp hNq c z]
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro h
      exact (mem_sdiff.mp (hf z).1).2
        ((mem_union.mp h).elim (fun h => mem_union_left _ (mem_union_right _ h))
          (fun h => mem_union_right _ h))
    have hwQ : ∀ j, w j ∉ Q := by
      intro j
      cases j
      · exact fun h => (mem_sdiff.mp hy).2 (mem_union_left _ h)
      · exact fun h => (mem_sdiff.mp hx).2 (mem_union_left _ h)
    have hwc : ∀ j, w j ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c := by
      intro j
      cases j
      · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hy).2 (mem_union_right _ h)⟩
      · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hx).2 (mem_union_right _ h)⟩
    have hfw : ∀ z j, f z ≠ w j := by
      intro z j
      cases j
      · exact (hf z).2.2
      · exact (hf z).2.1
    have hnab := not_adj_of_fixedAt_color_overlap G p q a b U c hc hD
    have hwproper := exception_assignment_compatible G p q a b U hpq hn hab haU hbU
      hpa hqb hNp hNq w (fun h => (hnab h).elim)
    obtain ⟨color, hfixed, hspoke, _, _⟩ := color_from_two_exception_assignment G
      (p := p) (q := q) (a := a) (b := b) (U := U) (hU := hU) (hpq := hpq) (hn := hn)
      (haU := haU) (hbU := hbU) (hp := hp) (hq := hq) (hpa := hpa) (hqb := hqb)
      (hNp := hNp) (hNq := hNq) (c := c) (hc := hc) (qcolor := q0)
      (havailable := originalSpokeColoring_mem_available G p q U c hc)
      (f := f) (hfinj := hfinj) (w := w) (hfspokes := by simpa only [hqimage] using hfQ)
      (hfc := hfc) (hfw := hfw) (hwspokes := by simpa only [hqimage] using hwQ)
      (hwc := hwc) (hwproper := hwproper)
    refine ⟨color, hfixed, ?_⟩
    have hsame : ∀ e, color (spokeToEdge G p q U e) = c e.val := hspoke
    simp [hsame]
  · obtain ⟨ha, hb, hd⟩ := (seven_union_obstruction_iff (by decide) L hL hnear
      hRcard Ea Eb hEa hEb).mp hassign
    rw [hR] at ha hb
    obtain ⟨v, color, hfixed, hsame, _⟩ :=
      seven_union_host_extension G p q a b U hU hpq hn hab haU hbU hdegree hdp hdq
        hNp hNq c hc T hT hD hunion ha hb hd
    refine ⟨color, hfixed, ?_⟩
    have hsub : univ.filter (fun e : ↥(spokeEdges G p q U) =>
        color (spokeToEdge G p q U e) ≠ c e.val) ⊆ {v} := by
      intro e he
      apply mem_singleton.mpr
      by_contra hev
      exact (mem_filter.mp he).2 (hsame e hev)
    exact (card_le_card hsub).trans (by simp)


end K23Reduction
end Part43

section Part44
-- Source module: K23SixHost

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The full common-six-color K2,3 case extends, preserving all fixed edges.
The retained spokes may be recolored; no seven-union or overlap premise is needed. -/
theorem six_common_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20)) (hT : T.card = 6)
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  let D := (fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c
  have hD : D.card ≤ 3 := (card_le_card inter_subset_left).trans
    (fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c)
  obtain ⟨qcolor, havailable, hfive, hthirteen⟩ :=
    six_actual_spoke_compression G p q U hU hpq hdegree hp hq c T hT hcommon D hD
  let c' := retainedRecolor G p q U c qcolor
  have hc' : RetainedProper G p q c' :=
    retainedRecolor_proper G p q U c qcolor hc havailable
  have hfixed : ∀ e ∈ fixedEdges G p q U, c' e = c e :=
    retainedRecolor_fixed G p q U c qcolor
  have hrows : ∀ u ∈ U, (rowSeen G p q U u).image c' = T := by
    intro u hu
    rw [retainedRecolor_rowSeen_image]
    exact six_row_colors_eq_common G p q U u hpq hdegree hu (hp u hu) (hq u hu)
      c T hT (hcommon u hu)
  have hspokes : (spokeEdges G p q U).card = 6 :=
    (six_actual_geometry_and_lists G p q U hU hpq hdegree hp hq c T hT hcommon).1
  have hQ : ((spokeEdges G p q U).image c').card ≤ 5 := by
    rw [retainedRecolor_spoke_image]
    exact hfive
  have hunion : ((spokeEdges G p q U).image c' ∪ T ∪
      ((fixedAt G p q U a).image c' ∩ (fixedAt G p q U b).image c')).card ≤ 13 := by
    rw [retainedRecolor_spoke_image, retainedRecolor_fixedAt_image,
      retainedRecolor_fixedAt_image]
    exact hthirteen
  have hresult : ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c' e.val := by
    by_cases hsmall : ((spokeEdges G p q U).image c' ∪ T ∪
        ((fixedAt G p q U a).image c' ∩ (fixedAt G p q U b).image c')).card ≤ 12
    · obtain ⟨color, hcolor, _⟩ := six_large_union_host_extension G p q a b U hU hpq hn
        hab haU hbU hdegree hdp hdq hNp hNq c' hc' T hT hrows hspokes hQ hsmall
      exact ⟨color, hcolor⟩
    · have hexact : ((spokeEdges G p q U).image c' ∪ T ∪
          ((fixedAt G p q U a).image c' ∩ (fixedAt G p q U b).image c')).card = 13 := by omega
      have hDtwo : 2 ≤ ((fixedAt G p q U a).image c' ∩
          (fixedAt G p q U b).image c').card := by
        have h1 := card_union_le ((spokeEdges G p q U).image c') T
        have h2 := card_union_le ((spokeEdges G p q U).image c' ∪ T)
          ((fixedAt G p q U a).image c' ∩ (fixedAt G p q U b).image c')
        omega
      have hTiff : ∀ color, color ∈ T ↔
          ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c' := by
        intro color
        constructor
        · intro ht u hu
          simpa only [hrows u hu] using ht
        · intro ht
          have hm := ht (cellRow3 U hU 0) (cellRow3_mem U hU 0)
          simpa only [hrows _ (cellRow3_mem U hU 0)] using hm
      obtain ⟨color, hcolor, _⟩ := seven_union_host_dispatch G p q a b U hU hpq hn
        hab haU hbU hdegree hdp hdq hNp hNq c' hc' T hTiff hDtwo
        (by simpa only [union_assoc] using hexact)
      exact ⟨color, hcolor⟩
  obtain ⟨color, hcolor⟩ := hresult
  exact ⟨color, fun e he => (hcolor e he).trans (hfixed e.val he)⟩


end K23Reduction
end Part44

section Part45
-- Source module: K23SmallHost

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Saturation of the spoke/common-row/exceptional-overlap union forces six
common row colors and hence a full extension. This covers overlap two with
cell union at most six, and overlap three with cell union at most five. -/
theorem saturated_union_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20))
    (hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c)
    (hsaturated : 12 + ((fixedAt G p q U a).image c ∩
      (fixedAt G p q U b).image c).card ≤
      ((spokeEdges G p q U).image c ∪ T ∪
      ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c)).card) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hQ : ((spokeEdges G p q U).image c).card ≤ 6 := card_image_le.trans
    (spokeEdges_card_le_six_of_common G p q U hU hpq hdegree hp hq)
  have hu := cellRow3_mem U hU 0
  have hTle : T.card ≤ 6 := (card_le_card (hcommon _ hu)).trans
    (row_colors_card_le_six_of_common G p q U _ hpq hdegree hu (hp _ hu) (hq _ hu) c)
  have h1 := card_union_le ((spokeEdges G p q U).image c) T
  have h2 := card_union_le ((spokeEdges G p q U).image c ∪ T)
    ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c)
  have hT : T.card = 6 := by omega
  exact six_common_host_extension G p q a b U hU hpq hn hab haU hbU hdegree hdp hdq
    hNp hNq c hc T hT hcommon


end K23Reduction
end Part45

section Part46
-- Source module: K23LowOverlapLists

namespace K23Reduction

open Finset

/-- Shared Hall argument for the two direct six-cell/two-exception cases. -/
private theorem paired_eight_lists {C : Type*} [DecidableEq C]
    (L : Fin 3 × Bool → Finset C) (Ea Eb : Finset C)
    (hL : ∀ z, 5 ≤ (L z).card) (hEa : 2 ≤ Ea.card) (hEb : 2 ≤ Eb.card)
    (hpair : ∀ i, 6 ≤ (L (i, true) ∪ L (i, false)).card)
    (hseven : (∀ i, 7 ≤ (L (i, true) ∪ L (i, false)).card) ∨
      (∀ z, (L z \ L (z.1, !z.2)).card ≤ 1))
    (htotal : 8 ≤ (univ.biUnion L).card) :
    ∃ (f : Fin 3 × Bool → C) (x y : C), Function.Injective f ∧
      (∀ z, f z ∈ L z ∧ f z ≠ x ∧ f z ≠ y) ∧ x ∈ Ea ∧ y ∈ Eb ∧ x ≠ y := by
  classical
  let N : (Fin 3 × Bool) ⊕ Bool → Finset C :=
    Sum.elim L (fun b => if b then Ea else Eb)
  have hhall : ∀ S : Finset ((Fin 3 × Bool) ⊕ Bool), S.card ≤ (S.biUnion N).card := by
    intro S
    by_cases hempty : S = ∅
    · simp [hempty]
    by_cases hcell : ∃ z : Fin 3 × Bool, Sum.inl z ∈ S
    · obtain ⟨z, hz⟩ := hcell
      by_cases hsmall : S.card ≤ 5
      · exact hsmall.trans ((hL z).trans
          (card_le_card (subset_biUnion_of_mem N hz)))
      by_cases hfull : S = univ
      · have hcover : univ.biUnion L ⊆ univ.biUnion N := by
          intro c hc
          obtain ⟨z, _, hz⟩ := mem_biUnion.mp hc
          exact mem_biUnion.mpr ⟨Sum.inl z, mem_univ _, hz⟩
        have hcount := htotal.trans (card_le_card hcover)
        simpa [hfull] using hcount
      have hScard : S.card ≤ 7 := by
        have hout : ∃ v, v ∉ S := by
          by_contra! h
          exact hfull (eq_univ_of_forall h)
        obtain ⟨v, hv⟩ := hout
        have hsub : S ⊆ univ.erase v := by
          intro u hu
          exact mem_erase.mpr ⟨by intro huv; exact hv (huv ▸ hu), mem_univ _⟩
        simpa using card_le_card hsub
      have hrow : ∃ i : Fin 3, Sum.inl (i, true) ∈ S ∧ Sum.inl (i, false) ∈ S := by
        let π : (Fin 3 × Bool) ⊕ Bool → Fin 3 ⊕ Bool :=
          Sum.elim (fun z => Sum.inl z.1) Sum.inr
        have hsize : (univ : Finset (Fin 3 ⊕ Bool)).card < S.card := by
          have hu : (univ : Finset (Fin 3 ⊕ Bool)).card = 5 := by decide
          omega
        obtain ⟨v, hv, u, hu, hne, heq⟩ :=
          exists_ne_map_eq_of_card_lt_of_maps_to hsize
            (f := π) (fun _ _ => mem_univ _)
        rcases v with ⟨i, b⟩ | b <;> rcases u with ⟨j, d⟩ | d
        · have hij : i = j := by simpa [π] using heq
          subst j
          cases b <;> cases d
          · exact (hne rfl).elim
          · exact ⟨i, hu, hv⟩
          · exact ⟨i, hv, hu⟩
          · exact (hne rfl).elim
        · simp [π] at heq
        · simp [π] at heq
        · have hbd : b = d := by simpa [π] using heq
          exact (hne (congrArg Sum.inr hbd)).elim
      obtain ⟨i, hi, hi'⟩ := hrow
      have hcover : L (i, true) ∪ L (i, false) ⊆ S.biUnion N :=
        union_subset (subset_biUnion_of_mem N hi) (subset_biUnion_of_mem N hi')
      rcases hseven with hseven | hnear
      · exact hScard.trans ((hseven i).trans (card_le_card hcover))
      · by_cases hsix : S.card ≤ 6
        · exact hsix.trans ((hpair i).trans (card_le_card hcover))
        have hout : ∃ v, v ∉ S := by
          by_contra! h
          exact hfull (eq_univ_of_forall h)
        obtain ⟨v, hv⟩ := hout
        have hsub : S ⊆ univ.erase v := by
          intro u hu
          exact mem_erase.mpr ⟨by intro huv; exact hv (huv ▸ hu), mem_univ _⟩
        have herase : (univ.erase v).card = 7 := by simp
        have heq : S = univ.erase v := eq_of_subset_of_card_le hsub (by omega)
        have hother : ∀ u, u ≠ v → u ∈ S := by
          intro u huv
          rw [heq]
          simp [huv]
        rcases v with z | b
        · have hmate : (z.1, !z.2) ≠ z := by
            intro h
            have h' := congrArg Prod.snd h
            cases z.2 <;> simp at h'
          have hm : Sum.inl (z.1, !z.2) ∈ S :=
            hother _ (fun h => hmate (Sum.inl.inj h))
          have hcover' : univ.biUnion L ⊆ S.biUnion N ∪ (L z \ L (z.1, !z.2)) := by
            intro c hc
            obtain ⟨j, _, hcj⟩ := mem_biUnion.mp hc
            by_cases hj : j = z
            · subst j
              by_cases hmcolor : c ∈ L (z.1, !z.2)
              · exact mem_union_left _ (mem_biUnion.mpr ⟨_, hm, hmcolor⟩)
              · exact mem_union_right _ (mem_sdiff.mpr ⟨hcj, hmcolor⟩)
            · exact mem_union_left _ (mem_biUnion.mpr
                ⟨Sum.inl j, hother _ (fun h => hj (Sum.inl.inj h)), hcj⟩)
          have hcount := card_le_card hcover'
          have hsum := card_union_le (S.biUnion N) (L z \ L (z.1, !z.2))
          have hdiff := hnear z
          omega
        · have hcover' : univ.biUnion L ⊆ S.biUnion N := by
            intro c hc
            obtain ⟨z, _, hz⟩ := mem_biUnion.mp hc
            exact mem_biUnion.mpr
              ⟨Sum.inl z, hother _ (fun h => by cases h), hz⟩
          have hcount := htotal.trans (card_le_card hcover')
          omega
    · have hsub : S ⊆ (univ : Finset Bool).image
          (Sum.inr : Bool → (Fin 3 × Bool) ⊕ Bool) := by
        intro v hv
        rcases v with z | b
        · exact (hcell ⟨z, hv⟩).elim
        · exact mem_image.mpr ⟨b, mem_univ _, rfl⟩
      have hScard : S.card ≤ 2 := by
        have hcount := card_le_card hsub
        rw [card_image_of_injective _ (fun a b h => Sum.inr.inj h)] at hcount
        simpa using hcount
      obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr hempty
      rcases v with z | b
      · exact (hcell ⟨z, hv⟩).elim
      · have hb : 2 ≤ (N (Sum.inr b)).card := by cases b <;> assumption
        exact hScard.trans (hb.trans (card_le_card (subset_biUnion_of_mem N hv)))
  obtain ⟨g, hg, hmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hhall
  refine ⟨fun z => g (Sum.inl z), g (Sum.inr true), g (Sum.inr false),
    fun _ _ h => Sum.inl.inj (hg h), ?_, hmem _, hmem _, ?_⟩
  · intro z
    refine ⟨hmem _, ?_, ?_⟩
    · intro heq
      have hbad := hg heq
      cases hbad
    · intro heq
      have hbad := hg heq
      cases hbad
  · intro heq
    have h : true = false := Sum.inr.inj (hg heq)
    cases h

/-- Large row-pair unions give eight distinct colors, including distinct
exception colors, without requiring near partners. -/
theorem low_overlap_eight_lists {C : Type*} [DecidableEq C]
    (L : Fin 3 × Bool → Finset C) (Ea Eb : Finset C)
    (hL : ∀ z, 5 ≤ (L z).card) (hEa : 2 ≤ Ea.card) (hEb : 2 ≤ Eb.card)
    (hpair : ∀ i, 7 ≤ (L (i, true) ∪ L (i, false)).card)
    (htotal : 8 ≤ (univ.biUnion L).card) :
    ∃ (f : Fin 3 × Bool → C) (x y : C), Function.Injective f ∧
      (∀ z, f z ∈ L z ∧ f z ≠ x ∧ f z ≠ y) ∧ x ∈ Ea ∧ y ∈ Eb ∧ x ≠ y := by
  exact paired_eight_lists L Ea Eb hL hEa hEb (fun i => by have h := hpair i; omega)
    (Or.inl hpair) htotal

/-- Row unions of size six suffice when removing one cell loses at most
one color beyond its row mate, and the full cell union has at least eight colors. -/
theorem overlap_two_eight_lists {C : Type*} [DecidableEq C]
    (L : Fin 3 × Bool → Finset C) (Ea Eb : Finset C)
    (hL : ∀ z, 5 ≤ (L z).card) (hEa : 2 ≤ Ea.card) (hEb : 2 ≤ Eb.card)
    (hpair : ∀ i, 6 ≤ (L (i, true) ∪ L (i, false)).card)
    (hnear : ∀ z, (L z \ L (z.1, !z.2)).card ≤ 1)
    (htotal : 8 ≤ (univ.biUnion L).card) :
    ∃ (f : Fin 3 × Bool → C) (x y : C), Function.Injective f ∧
      (∀ z, f z ∈ L z ∧ f z ≠ x ∧ f z ≠ y) ∧ x ∈ Ea ∧ y ∈ Eb ∧ x ≠ y := by
  exact paired_eight_lists L Ea Eb hL hEa hEb hpair (Or.inr hnear) htotal


end K23Reduction
end Part46

section Part47
-- Source module: K23LowOverlapHost

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

private theorem row_pair_list_union (Q F Da Db : Finset (Fin 20)) :
    (univ \ (Q ∪ F ∪ Da)) ∪ (univ \ (Q ∪ F ∪ Db)) =
      univ \ (Q ∪ F ∪ (Da ∩ Db)) := by
  ext color
  simp only [mem_union, mem_sdiff, mem_univ, true_and, mem_inter, not_or]
  tauto

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every actual K2,3 host with exceptional fixed-color overlap at most two extends,
preserving all fixed-edge colors. No cell-union restriction remains. -/
theorem overlap_at_most_two_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (hD : ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c).card ≤ 2) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hNq b).mpr (Or.inr rfl)
  let Q := (spokeEdges G p q U).image c
  let Da := (fixedAt G p q U a).image c
  let Db := (fixedAt G p q U b).image c
  let Γa := fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c
  let Γb := fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c
  let Ea := univ \ (Q ∪ Γa)
  let Eb := univ \ (Q ∪ Γb)
  let F : Fin 3 → Finset (Fin 20) := fun i =>
    (rowSeen G p q U (cellRow3 U hU i)).image c
  let L : Fin 3 × Bool → Finset (Fin 20) := fun z =>
    univ \ (Q ∪ F z.1 ∪ (if z.2 then Da else Db))
  let T : Finset (Fin 20) := univ.filter
    (fun color => ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c)
  have hT : ∀ color, color ∈ T ↔
      ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c := by
    intro color
    simp only [T, mem_filter, mem_univ, true_and]
  let R := univ \ (Q ∪ (T ∪ (Da ∩ Db)))
  have hm : (spokeEdges G p q U).card ≤ 6 :=
    spokeEdges_card_le_six_of_common G p q U hU hpq hdegree hp hq
  have hQ : Q.card ≤ 6 := card_image_le.trans hm
  have hF : ∀ i, (F i).card ≤ 6 := fun i =>
    row_colors_card_le_six_of_common G p q U _ hpq hdegree
      (cellRow3_mem U hU i) (hp _ (cellRow3_mem U hU i))
      (hq _ (cellRow3_mem U hU i)) c
  have hDa : Da.card ≤ 3 :=
    fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c
  have hDb : Db.card ≤ 3 := by
    simpa only [fixedAt_swap] using
      fixedAt_colors_card_le_three_of_adj_left G q p U b hdegree hqb c
  have hTi : ∀ color, color ∈ T ↔ ∀ i, color ∈ F i := by
    intro color
    constructor
    · intro ht i
      exact (hT color).mp ht _ (cellRow3_mem U hU i)
    · intro ht
      apply (hT color).mpr
      intro u hu
      obtain ⟨i, hi⟩ := cellRow3_coverage U hU u hu
      exact hi ▸ ht i
  have hR : univ.biUnion L = R := by
    simpa only [L, R, union_assoc] using six_cell_union Q T Da Db F hTi
  have hcount : (univ.biUnion L).card + (Q ∪ T ∪ (Da ∩ Db)).card = 20 := by
    rw [hR]
    simpa only [card_univ, Fintype.card_fin, union_assoc] using
      card_sdiff_add_card_eq_card (subset_univ (Q ∪ (T ∪ (Da ∩ Db))))
  by_cases hsmall : (univ.biUnion L).card ≤ 6
  · exact saturated_union_host_extension G p q a b U hU hpq hn hab haU hbU
      hdegree hdp hdq hNp hNq c hc T
      (fun u hu color ht => (hT color).mp ht u hu) (by
        change 12 + (Da ∩ Db).card ≤ (Q ∪ T ∪ (Da ∩ Db)).card
        change (Da ∩ Db).card ≤ 2 at hD
        omega)
  by_cases hseven : (univ.biUnion L).card = 7
  · by_cases hDlow : (Da ∩ Db).card ≤ 1
    · exact saturated_union_host_extension G p q a b U hU hpq hn hab haU hbU
        hdegree hdp hdq hNp hNq c hc T
        (fun u hu color ht => (hT color).mp ht u hu) (by
          change 12 + (Da ∩ Db).card ≤ (Q ∪ T ∪ (Da ∩ Db)).card
          omega)
    · obtain ⟨color, hfixed, _⟩ := seven_union_host_dispatch G p q a b U hU hpq hn
        hab haU hbU hdegree hdp hdq hNp hNq c hc T hT
        (by change 2 ≤ (Da ∩ Db).card; omega) (by
          change (Q ∪ (T ∪ (Da ∩ Db))).card = 13
          rw [← union_assoc]
          omega)
      exact ⟨color, hfixed⟩
  have htotal : 8 ≤ (univ.biUnion L).card := by omega
  have hL : ∀ z, 5 ≤ (L z).card := by
    intro z
    have hz : (if z.2 then Da else Db).card ≤ 3 := by cases z.2 <;> assumption
    have h1 := card_union_le Q (F z.1)
    have h2 := card_union_le (Q ∪ F z.1) (if z.2 then Da else Db)
    have hrow := hF z.1
    dsimp only [L]
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  have hpair : ∀ i, 8 - (Da ∩ Db).card ≤ (L (i, true) ∪ L (i, false)).card := by
    intro i
    have heq : L (i, true) ∪ L (i, false) = univ \ (Q ∪ F i ∪ (Da ∩ Db)) :=
      row_pair_list_union Q (F i) Da Db
    rw [heq, card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    have h1 := card_union_le Q (F i)
    have h2 := card_union_le (Q ∪ F i) (Da ∩ Db)
    have hi := hF i
    change (Da ∩ Db).card ≤ 2 at hD
    omega
  have hΓa : Γa.card ≤ 18 - (spokeEdges G p q U).card :=
    exceptional_fixed_colors_card_le G p q a U hpq hn hdegree hdp hpa hU hp hq c
  have hΓb : Γb.card ≤ 18 - (spokeEdges G p q U).card := by
    simpa only [fixedConflictColors_swap, spokeEdges_swap] using
      exceptional_fixed_colors_card_le G q p b U hpq.symm (fun h => hn h.symm)
        hdegree hdq hqb hU hq hp c
  have hEa : 2 ≤ Ea.card := exceptional_list_card_ge_two Q Γa _ hm card_image_le hΓa
  have hEb : 2 ≤ Eb.card := exceptional_list_card_ge_two Q Γb _ hm card_image_le hΓb
  have hassign : ∃ (f : Fin 3 × Bool → Fin 20) (x y : Fin 20), Function.Injective f ∧
      (∀ z, f z ∈ L z ∧ f z ≠ x ∧ f z ≠ y) ∧ x ∈ Ea ∧ y ∈ Eb ∧ x ≠ y := by
    by_cases hDlow : (Da ∩ Db).card ≤ 1
    · exact low_overlap_eight_lists L Ea Eb hL hEa hEb
        (fun i => by have hi := hpair i; omega) htotal
    · have hDtwo : 2 ≤ (Da ∩ Db).card := by omega
      have hnear : ∀ z, (L z \ L (z.1, !z.2)).card ≤ 1 := by
        intro z
        cases hz : z.2
        · simpa [L, hz, inter_comm] using
            complement_list_difference univ (Q ∪ F z.1) Db Da hDa
              (by simpa only [inter_comm] using hDtwo)
        · simpa [L, hz] using
            complement_list_difference univ (Q ∪ F z.1) Da Db hDb hDtwo
      exact overlap_two_eight_lists L Ea Eb hL hEa hEb
        (fun i => by
          have hi := hpair i
          change (Da ∩ Db).card ≤ 2 at hD
          omega) hnear htotal
  obtain ⟨f, x, y, hfinj, hf, hx, hy, hxy⟩ := hassign
  let w : Bool → Fin 20 := fun j => if j then x else y
  let q0 := originalSpokeColoring G p q U c hc
  have hqimage : univ.image q0 = Q := originalSpokeColoring_image G p q U c hc
  have hfQ : ∀ z, f z ∉ Q := fun z h =>
    (mem_sdiff.mp (hf z).1).2 (mem_union_left _ (mem_union_left _ h))
  have hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c := by
    intro z
    rw [availableColors, cellEdge3_fixed_colors G p q a b U hU hp hq hNp hNq c z]
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro h
    exact (mem_sdiff.mp (hf z).1).2
      ((mem_union.mp h).elim (fun h => mem_union_left _ (mem_union_right _ h))
        (fun h => mem_union_right _ h))
  have hwQ : ∀ j, w j ∉ Q := by
    intro j
    cases j
    · exact fun h => (mem_sdiff.mp hy).2 (mem_union_left _ h)
    · exact fun h => (mem_sdiff.mp hx).2 (mem_union_left _ h)
  have hwc : ∀ j, w j ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c := by
    intro j
    cases j
    · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hy).2 (mem_union_right _ h)⟩
    · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hx).2 (mem_union_right _ h)⟩
  have hfw : ∀ z j, f z ≠ w j := by
    intro z j
    cases j
    · exact (hf z).2.2
    · exact (hf z).2.1
  have hwproper := exception_assignment_compatible G p q a b U hpq hn hab haU hbU
    hpa hqb hNp hNq w (fun _ => hxy)
  obtain ⟨color, hfixed, _, _, _⟩ := color_from_two_exception_assignment G
    (p := p) (q := q) (a := a) (b := b) (U := U) (hU := hU) (hpq := hpq) (hn := hn)
    (haU := haU) (hbU := hbU) (hp := hp) (hq := hq) (hpa := hpa) (hqb := hqb)
    (hNp := hNp) (hNq := hNq) (c := c) (hc := hc) (qcolor := q0)
    (havailable := originalSpokeColoring_mem_available G p q U c hc)
    (f := f) (hfinj := hfinj) (w := w) (hfspokes := by simpa only [hqimage] using hfQ)
    (hfc := hfc) (hfw := hfw) (hwspokes := by simpa only [hqimage] using hwQ)
    (hwc := hwc) (hwproper := hwproper)
  exact ⟨color, hfixed⟩


end K23Reduction
end Part47

section Part48
-- Source module: K23Saturation

namespace K23Reduction

open Finset

/-- Equality in the sum of three separate cardinal bounds forces every bound
to be sharp and the three sets to be pairwise disjoint. -/
theorem three_set_card_saturation {C : Type*} [DecidableEq C]
    (A B D : Finset C) (a b d : ℕ)
    (hA : A.card ≤ a) (hB : B.card ≤ b) (hD : D.card ≤ d)
    (hunion : (A ∪ B ∪ D).card = a + b + d) :
    A.card = a ∧ B.card = b ∧ D.card = d ∧
      Disjoint A B ∧ Disjoint A D ∧ Disjoint B D := by
  have hABbound := card_union_le A B
  have hABDbound := card_union_le (A ∪ B) D
  have hAc : A.card = a := by omega
  have hBc : B.card = b := by omega
  have hDc : D.card = d := by omega
  have hABc : (A ∪ B).card = A.card + B.card := by omega
  have hABDc : (A ∪ B ∪ D).card = (A ∪ B).card + D.card := by omega
  have hAB := card_union_eq_card_add_card.mp hABc
  have hABD := card_union_eq_card_add_card.mp hABDc
  refine ⟨hAc, hBc, hDc, hAB, ?_, ?_⟩
  · exact disjoint_left.mpr fun _ hA hD =>
      disjoint_left.mp hABD (mem_union_left _ hA) hD
  · exact disjoint_left.mpr fun _ hB hD =>
      disjoint_left.mp hABD (mem_union_right _ hB) hD

/-- The union of the six cell lists, retaining both exceptional exclusions. -/
abbrev sixCellUnion (Q Da Db : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20)) : Finset (Fin 20) :=
  univ.biUnion (fun v : Fin 3 × Bool =>
    univ \ (Q ∪ F v.1 ∪ (if v.2 then Da else Db)))

/-- Exact partition of the twenty-color palette, using the checked cell-union
identity and an explicit description of the common row intersection. -/
theorem sixCellUnion_card_add (Q T Da Db : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20))
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i) :
    (sixCellUnion Q Da Db F).card + (Q ∪ T ∪ (Da ∩ Db)).card = 20 := by
  change (univ.biUnion (fun v : Fin 3 × Bool =>
    univ \ (Q ∪ F v.1 ∪ (if v.2 then Da else Db)))).card +
      (Q ∪ T ∪ (Da ∩ Db)).card = 20
  rw [six_cell_union Q T Da Db F hT]
  simpa only [card_univ, Fintype.card_fin] using
    card_sdiff_add_card_eq_card (subset_univ (Q ∪ T ∪ (Da ∩ Db)))

/-- Overlap two and a six-color cell union force six distinct spoke colors,
three identical six-color row sets, and pairwise disjoint exclusions. -/
theorem overlap_two_six_union_saturation (Q T Da Db : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20))
    (hQ : Q.card ≤ 6) (hF : ∀ i, (F i).card ≤ 6)
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i)
    (hD : (Da ∩ Db).card = 2)
    (hR : (sixCellUnion Q Da Db F).card = 6) :
    Q.card = 6 ∧ T.card = 6 ∧ (∀ i, F i = T) ∧
      Disjoint Q T ∧ Disjoint Q (Da ∩ Db) ∧ Disjoint T (Da ∩ Db) := by
  have hTsub : ∀ i, T ⊆ F i := fun i c hc => (hT c).mp hc i
  have hTle : T.card ≤ 6 := (card_le_card (hTsub 0)).trans (hF 0)
  have hpartition := sixCellUnion_card_add Q T Da Db F hT
  have hsum : (Q ∪ T ∪ (Da ∩ Db)).card = 6 + 6 + 2 := by omega
  obtain ⟨hQc, hTc, _, hQT, hQD, hTD⟩ :=
    three_set_card_saturation Q T (Da ∩ Db) 6 6 2 hQ hTle (by omega) hsum
  refine ⟨hQc, hTc, ?_, hQT, hQD, hTD⟩
  intro i
  have hFi := hF i
  exact (eq_of_subset_of_card_le (hTsub i) (by omega)).symm

/-- With overlap three, a cell union of size at most six requires at least
five common row colors. No upper bound on the separate row sets is needed. -/
theorem overlap_three_small_union_common_ge_five (Q T Da Db : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20))
    (hQ : Q.card ≤ 6)
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i)
    (hD : (Da ∩ Db).card = 3)
    (hR : (sixCellUnion Q Da Db F).card ≤ 6) :
    5 ≤ T.card := by
  have hpartition := sixCellUnion_card_add Q T Da Db F hT
  have hQT := card_union_le Q T
  have hQTD := card_union_le (Q ∪ T) (Da ∩ Db)
  omega

/-- Five common row colors and a cell union of size at most six force exact
six-color union, six spoke colors, overlap three, and pairwise disjointness.
Neither exact overlap nor exact cell-union size is assumed. -/
theorem common_five_small_union_saturation (Q T Da Db : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20))
    (hQ : Q.card ≤ 6)
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i) (hTc : T.card = 5)
    (hD : (Da ∩ Db).card ≤ 3)
    (hR : (sixCellUnion Q Da Db F).card ≤ 6) :
    (sixCellUnion Q Da Db F).card = 6 ∧ Q.card = 6 ∧ (Da ∩ Db).card = 3 ∧
      Disjoint Q T ∧ Disjoint Q (Da ∩ Db) ∧ Disjoint T (Da ∩ Db) := by
  have hpartition := sixCellUnion_card_add Q T Da Db F hT
  have hQT := card_union_le Q T
  have hQTD := card_union_le (Q ∪ T) (Da ∩ Db)
  have hRc : (sixCellUnion Q Da Db F).card = 6 := by omega
  have hsum : (Q ∪ T ∪ (Da ∩ Db)).card = 6 + 5 + 3 := by omega
  obtain ⟨hQc, _, hDc, hQTdisj, hQDdisj, hTDdisj⟩ :=
    three_set_card_saturation Q T (Da ∩ Db) 6 5 3 hQ (by omega) hD hsum
  exact ⟨hRc, hQc, hDc, hQTdisj, hQDdisj, hTDdisj⟩


end K23Reduction
end Part48

section Part49
-- Source module: K23TightHost

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

private theorem tight_row_list_repair {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (L : V → Finset (Fin 20)) (q : H.Coloring (Fin 20))
    (hq : ∀ v, q v ∈ L v) (hslack : ∀ v, H.degree v + 2 ≤ (L v).card)
    (hV : Fintype.card V ≤ 6) (T Da Db Γa Γb S : Finset (Fin 20))
    (F : Fin 3 → Finset (Fin 20))
    (hF : ∀ i, (F i).card ≤ 6)
    (hDa : Da.card ≤ 3) (hDb : Db.card ≤ 3) (hD : 2 ≤ (Da ∩ Db).card)
    (hT : ∀ c, c ∈ T ↔ ∀ i, c ∈ F i)
    (hunion : (univ.image q ∪ (T ∪ (Da ∩ Db))).card ≤ 13)
    (hQcard : (univ.image q).card = 6) (hS : S.card = 9)
    (hsmall : T ∪ (Da ∩ Db) ⊆ S) (hSa : S ⊆ Γa) (hSb : S ⊆ Γb)
    (ha : Γa.card ≤ 12) (hb : Γb.card ≤ 12)
    (hsafe : univ \ (Γa ∪ Γb) ⊆ univ.image q) :
    ∃ v : V, ∃ q' : H.Coloring (Fin 20), ∃ w : Fin 20,
      (∀ u, q' u ∈ L u) ∧ (∀ u, u ≠ v → q' u = q u) ∧
      q' v ≠ q v ∧ (∀ u, q' u ≠ w) ∧ w ∉ Γa ∧ w ∉ Γb ∧
      ∃ f : Fin 3 × Bool → Fin 20, Function.Injective f ∧ ∀ x,
        f x ∉ univ.image q' ∧ f x ∉ F x.1 ∧
        f x ∉ (if x.2 then Da else Db) ∧ f x ≠ w := by
  classical
  have hsi : 9 ≤ (Γa ∩ Γb).card := by
    rw [← hS]
    exact card_le_card (fun _ h => mem_inter.mpr ⟨hSa h, hSb h⟩)
  have hab := card_union_add_card_inter Γa Γb
  have hwcard : (univ \ (Γa ∪ Γb)).card + (Γa ∪ Γb).card = 20 := by
    simpa only [card_univ, Fintype.card_fin] using
      card_sdiff_add_card_eq_card (subset_univ (Γa ∪ Γb))
  obtain ⟨w, hw, hsingle⟩ := safe_singleton_fiber univ q (univ \ (Γa ∪ Γb)) hsafe (by
    simp only [card_univ]
    omega)
  obtain ⟨v, hv⟩ := card_eq_one.mp hsingle
  have hvw : q v = w := by
    have : v ∈ univ.filter (fun u => q u = w) := by rw [hv]; simp
    exact (mem_filter.mp this).2
  have huniq : ∀ u, q u = q v → u = v := by
    intro u hu
    have : u ∈ univ.filter (fun u => q u = w) := by simp [hu, hvw]
    rw [hv] at this
    exact mem_singleton.mp this
  have hwΓa : w ∉ Γa := fun h => (mem_sdiff.mp hw).2 (mem_union_left _ h)
  have hwΓb : w ∉ Γb := fun h => (mem_sdiff.mp hw).2 (mem_union_right _ h)
  have hwS : q v ∉ T ∪ (Da ∩ Db) := by rw [hvw]; exact fun h => hwΓa (hSa (hsmall h))
  obtain ⟨q', hq', hsame, hfree, hcount⟩ := free_singleton_color H L q hq v (hslack v) huniq
  have hQ : (univ.image q').card ≤ 6 := by
    have h := card_image_le (s := univ) (f := q')
    simp only [card_univ] at h
    omega
  have hnew : (univ.image q' ∪ T ∪ (Da ∩ Db)).card ≤ 13 := by
    have h := hcount (T ∪ (Da ∩ Db)) hwS
    exact (by simpa only [union_assoc] using h.trans hunion)
  obtain ⟨f, hf, hmem⟩ := cell_assignment_common_color (univ.image q') T Da Db F w
    hQ hF hDa hDb hD hT hnew
  exact ⟨v, q', w, hq', hsame, hfree v, (by simpa [hvw] using hfree),
    hwΓa, hwΓb, f, hf, hmem⟩


variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One tight row containing both disjoint exceptional lists permits a
one-spoke repair when the full cell union has at least seven colors.
The complete two-tight-row Hall obstruction supplies these premises. -/
theorem tight_row_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20))
    (hT : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c) (i : Fin 3) :
    let C := (spokeEdges G p q U).image c
    let Da := (fixedAt G p q U a).image c
    let Db := (fixedAt G p q U b).image c
    let Γa := fixedConflictColors G p q U ⟨s(p,a), (hNp a).mpr (Or.inr rfl)⟩ c
    let Γb := fixedConflictColors G p q U ⟨s(q,b), (hNq b).mpr (Or.inr rfl)⟩ c
    (Da ∩ Db).card = 3 →
    (C ∪ (T ∪ (Da ∩ Db))).card ≤ 13 →
    (univ \ (C ∪ (rowSeen G p q U (cellRow3 U hU i)).image c ∪ (Da ∩ Db))).card = 5 →
    univ \ (C ∪ Γa) ⊆ univ \ (C ∪ ((rowSeen G p q U (cellRow3 U hU i)).image c ∪ (Da ∩ Db))) →
    univ \ (C ∪ Γb) ⊆ univ \ (C ∪ ((rowSeen G p q U (cellRow3 U hU i)).image c ∪ (Da ∩ Db))) →
    Disjoint (univ \ (C ∪ Γa)) (univ \ (C ∪ Γb)) →
    ∃ v : ↥(spokeEdges G p q U), ∃ color : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val) ∧
      (∀ e : ↥(spokeEdges G p q U), e ≠ v → color (spokeToEdge G p q U e) = c e.val) ∧
      color (spokeToEdge G p q U v) ≠ c v.val := by
  classical
  dsimp only
  intro hD hunion htight hEa hEb hEab
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hNq b).mpr (Or.inr rfl)
  let Q := (spokeEdges G p q U).image c
  let Da := (fixedAt G p q U a).image c
  let Db := (fixedAt G p q U b).image c
  let Γa := fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c
  let Γb := fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c
  let F : Fin 3 → Finset (Fin 20) := fun j =>
    (rowSeen G p q U (cellRow3 U hU j)).image c
  let S := F i ∪ (Da ∩ Db)
  let q0 := originalSpokeColoring G p q U c hc
  have hm : (spokeEdges G p q U).card ≤ 6 :=
    spokeEdges_card_le_six_of_common G p q U hU hpq hdegree hp hq
  have hQ : Q.card ≤ 6 := card_image_le.trans hm
  have hF : ∀ j, (F j).card ≤ 6 := fun j =>
    row_colors_card_le_six_of_common G p q U _ hpq hdegree
      (cellRow3_mem U hU j) (hp _ (cellRow3_mem U hU j)) (hq _ (cellRow3_mem U hU j)) c
  have hDa : Da.card ≤ 3 := fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c
  have hDb : Db.card ≤ 3 := by
    simpa only [fixedAt_swap] using fixedAt_colors_card_le_three_of_adj_left G q p U b hdegree hqb c
  change (Da ∩ Db).card = 3 at hD
  change (univ \ (Q ∪ F i ∪ (Da ∩ Db))).card = 5 at htight
  have hpart := card_sdiff_add_card_eq_card (subset_univ (Q ∪ F i ∪ (Da ∩ Db)))
  simp only [card_univ, Fintype.card_fin] at hpart
  have hsum : (Q ∪ F i ∪ (Da ∩ Db)).card = 6 + 6 + 3 := by omega
  obtain ⟨hQc,hFi,_,hQFi,_,hFiD⟩ := three_set_card_saturation Q (F i) (Da ∩ Db)
    6 6 3 hQ (hF i) (by omega) hsum
  have hmc : (spokeEdges G p q U).card = 6 := by
    have h := card_image_le (s := spokeEdges G p q U) (f := c)
    change Q.card ≤ _ at h
    omega
  have hS : S.card = 9 := by
    change (F i ∪ (Da ∩ Db)).card = 9
    rw [card_union_of_disjoint hFiD, hFi, hD]
  have hTi : ∀ color, color ∈ T ↔ ∀ j, color ∈ F j := by
    intro color
    constructor
    · intro ht j
      exact (hT color).mp ht _ (cellRow3_mem U hU j)
    · intro ht
      apply (hT color).mpr
      intro u hu
      obtain ⟨j,hj⟩ := cellRow3_coverage U hU u hu
      exact hj ▸ ht j
  have hTsmall : T ∪ (Da ∩ Db) ⊆ S := union_subset_union
    (fun color ht => (hTi color).mp ht i) subset_rfl
  have hΓa : Γa.card ≤ 12 := by
    have h := exceptional_fixed_colors_card_le G p q a U hpq hn hdegree hdp hpa hU hp hq c
    simpa only [hmc] using h
  have hΓb : Γb.card ≤ 12 := by
    have h := exceptional_fixed_colors_card_le G q p b U hpq.symm (fun h => hn h.symm)
      hdegree hdq hqb hU hq hp c
    simpa only [fixedConflictColors_swap, spokeEdges_swap, hmc] using h
  have hDaΓ : Da ⊆ Γa := exceptional_incident_colors_subset G p q a U hpa c
  have hDbΓ : Db ⊆ Γb := by
    simpa only [fixedAt_swap, fixedConflictColors_swap] using
      exceptional_incident_colors_subset G q p b U hqb c
  obtain ⟨hSa,hSb,hsafe⟩ := exception_list_obstruction_exclusions Q (F i) Da Db Γa Γb
    hQFi hDaΓ hDbΓ hEa hEb hEab
  have hqimage : univ.image q0 = Q := originalSpokeColoring_image G p q U c hc
  have hslack : ∀ e, (spokeGraph G p q U).degree e + 2 ≤
      (availableColors G p q U (spokeToEdge G p q U e) c).card := by
    intro e
    have h := spoke_available_card_ge_degree_add_four G p q U hpq hn hdegree hdp hdq hp hq c e
    omega
  obtain ⟨v,q',w,hav,hsame,hchange,hfree,hwa,hwb,f,hfinj,hf⟩ :=
    tight_row_list_repair (spokeGraph G p q U)
      (fun e => availableColors G p q U (spokeToEdge G p q U e) c) q0
      (originalSpokeColoring_mem_available G p q U c hc) hslack
      (by simpa only [Fintype.card_coe] using hm) T Da Db Γa Γb S F hF hDa hDb (by omega)
      hTi (by simpa only [hqimage] using hunion) (by simpa only [hqimage] using hQc)
      hS hTsmall hSa hSb hΓa hΓb (by simpa only [hqimage] using hsafe)
  have hnab : ¬G.Adj a b := not_adj_of_fixedAt_color_overlap G p q a b U c hc (by change 2 ≤ (Da ∩ Db).card; omega)
  have hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c := by
    intro z
    rw [availableColors, cellEdge3_fixed_colors G p q a b U hU hp hq hNp hNq c z]
    exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_union.mp h).elim (hf z).2.1 (hf z).2.2.1⟩
  have hwspokes : w ∉ univ.image q' := by
    intro hw
    obtain ⟨e, _, he⟩ := mem_image.mp hw
    exact hfree e he
  have hwc : ∀ j, w ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c := by
    intro j
    cases j
    · exact mem_sdiff.mpr ⟨mem_univ _, hwb⟩
    · exact mem_sdiff.mpr ⟨mem_univ _, hwa⟩
  obtain ⟨color, hfixed, hspoke, _, _⟩ := color_from_common_exception_assignment G
    (p := p) (q := q) (a := a) (b := b) (U := U) (hU := hU)
    (hpq := hpq) (hn := hn) (hab := hab) (hnab := hnab) (haU := haU) (hbU := hbU)
    (hp := hp) (hq := hq) (hpa := hpa) (hqb := hqb) (hNp := hNp) (hNq := hNq)
    (c := c) (hc := hc) (qcolor := q') (havailable := hav)
    (f := f) (hfinj := hfinj) (w := w) (hfspokes := fun z => (hf z).1)
    (hfc := hfc) (hfw := fun z => (hf z).2.2.2) (hwspokes := hwspokes) (hwc := hwc)
  exact ⟨v, color, hfixed, fun e he => (hspoke e).trans (hsame e he),
    fun h => hchange ((hspoke v).symm.trans h)⟩


end K23Reduction
end Part49

section Part50
-- Source module: K23RepeatedCriterion

namespace K23Reduction

open Finset

private theorem repeated_rows_assignment_of_pair_unions {C : Type*} [DecidableEq C]
    (A : Fin 3 → Finset C) (Ea Eb : Finset C)
    (hA : ∀ i, 5 ≤ (A i).card) (hEa : 2 ≤ Ea.card) (hEb : 2 ≤ Eb.card)
    (htotal : 8 ≤ (univ.biUnion (fun z : Fin 3 × Bool => A z.1)).card)
    (hpair : ∀ i j, i ≠ j → 6 ≤ (A i ∪ A j ∪ Ea ∪ Eb).card) :
    TwoExceptionAssignment (fun z : Fin 3 × Bool => A z.1) Ea Eb := by
  classical
  let L : Fin 3 × Bool → Finset C := fun z => A z.1
  let N : (Fin 3 × Bool) ⊕ Bool → Finset C :=
    Sum.elim L (fun b => if b then Ea else Eb)
  have hhall : ∀ S : Finset ((Fin 3 × Bool) ⊕ Bool), S.card ≤ (S.biUnion N).card := by
    intro S
    by_cases hempty : S = ∅
    · simp [hempty]
    by_cases hcell : ∃ z : Fin 3 × Bool, Sum.inl z ∈ S
    · obtain ⟨z, hz⟩ := hcell
      by_cases hsmall : S.card ≤ 5
      · exact hsmall.trans ((hA z.1).trans
          (card_le_card (subset_biUnion_of_mem N hz)))
      by_cases hrows : ∀ i : Fin 3, ∃ b : Bool, Sum.inl (i,b) ∈ S
      · have hcover : univ.biUnion L ⊆ S.biUnion N := by
          intro c hc
          obtain ⟨z, _, hz⟩ := mem_biUnion.mp hc
          obtain ⟨b, hb⟩ := hrows z.1
          exact mem_biUnion.mpr ⟨Sum.inl (z.1,b), hb, hz⟩
        have hScard : S.card ≤ 8 := by simpa using card_le_univ S
        exact hScard.trans (htotal.trans (card_le_card hcover))
      · push Not at hrows
        obtain ⟨i, hi⟩ := hrows
        let B : Finset ((Fin 3 × Bool) ⊕ Bool) :=
          (((univ : Finset (Fin 3)).erase i).product (univ : Finset Bool)).image Sum.inl ∪
            (univ : Finset Bool).image Sum.inr
        have hsub : S ⊆ B := by
          intro v hv
          rcases v with ⟨j,b⟩ | b
          · have hji : j ≠ i := by intro h; subst j; exact hi b hv
            exact mem_union_left _ (mem_image.mpr
              ⟨(j,b), mem_product.mpr ⟨by simp [hji], mem_univ _⟩, rfl⟩)
          · exact mem_union_right _ (mem_image.mpr ⟨b, mem_univ _, rfl⟩)
        have hB : B.card ≤ 6 := by
          have h1 := card_union_le
            ((((univ : Finset (Fin 3)).erase i).product (univ : Finset Bool)).image
              (Sum.inl : Fin 3 × Bool → (Fin 3 × Bool) ⊕ Bool))
            ((univ : Finset Bool).image (Sum.inr : Bool → (Fin 3 × Bool) ⊕ Bool))
          have h2 := card_image_le (s := ((univ : Finset (Fin 3)).erase i).product
            (univ : Finset Bool)) (f := (Sum.inl : Fin 3 × Bool → (Fin 3 × Bool) ⊕ Bool))
          have h3 := card_image_le (s := (univ : Finset Bool))
            (f := (Sum.inr : Bool → (Fin 3 × Bool) ⊕ Bool))
          have hp : (((univ : Finset (Fin 3)).erase i).product (univ : Finset Bool)).card = 4 := by simp
          have hb : (univ : Finset Bool).card = 2 := by decide
          dsimp only [B]
          omega
        have hSB : S = B := eq_of_subset_of_card_le hsub (by omega)
        obtain ⟨j,k,hjk,hjkset⟩ := card_eq_two.mp
          (show ((univ : Finset (Fin 3)).erase i).card = 2 by simp)
        have hj : j ∈ (univ : Finset (Fin 3)).erase i := by rw [hjkset]; simp
        have hk : k ∈ (univ : Finset (Fin 3)).erase i := by rw [hjkset]; simp
        have hjS : Sum.inl (j,true) ∈ S := by
          rw [hSB]
          exact mem_union_left _ (mem_image.mpr
            ⟨(j,true), mem_product.mpr ⟨hj, mem_univ _⟩, rfl⟩)
        have hkS : Sum.inl (k,true) ∈ S := by
          rw [hSB]
          exact mem_union_left _ (mem_image.mpr
            ⟨(k,true), mem_product.mpr ⟨hk, mem_univ _⟩, rfl⟩)
        have haS : Sum.inr true ∈ S := by
          rw [hSB]
          exact mem_union_right _ (mem_image.mpr ⟨true, mem_univ _, rfl⟩)
        have hbS : Sum.inr false ∈ S := by
          rw [hSB]
          exact mem_union_right _ (mem_image.mpr ⟨false, mem_univ _, rfl⟩)
        have hcover : A j ∪ A k ∪ Ea ∪ Eb ⊆ S.biUnion N :=
          union_subset (union_subset (union_subset
            (subset_biUnion_of_mem N hjS) (subset_biUnion_of_mem N hkS))
              (subset_biUnion_of_mem N haS)) (subset_biUnion_of_mem N hbS)
        exact ((card_le_card hsub).trans hB).trans
          ((hpair j k hjk).trans (card_le_card hcover))
    · have hsub : S ⊆ (univ : Finset Bool).image
          (Sum.inr : Bool → (Fin 3 × Bool) ⊕ Bool) := by
        intro v hv
        rcases v with z | b
        · exact (hcell ⟨z, hv⟩).elim
        · exact mem_image.mpr ⟨b, mem_univ _, rfl⟩
      have hScard : S.card ≤ 2 := by
        have hcount := card_le_card hsub
        rw [card_image_of_injective _ (fun a b h => Sum.inr.inj h)] at hcount
        simpa using hcount
      obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr hempty
      rcases v with z | b
      · exact (hcell ⟨z, hv⟩).elim
      · have hb : 2 ≤ (N (Sum.inr b)).card := by cases b <;> assumption
        exact hScard.trans (hb.trans (card_le_card (subset_biUnion_of_mem N hv)))
  obtain ⟨g,hg,hmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hhall
  refine ⟨fun z => g (Sum.inl z), g (Sum.inr true), g (Sum.inr false),
    fun _ _ h => Sum.inl.inj (hg h), ?_, hmem _, hmem _⟩
  intro z
  refine ⟨hmem _, ?_, ?_⟩
  · intro heq
    have hbad := hg heq
    cases hbad
  · intro heq
    have hbad := hg heq
    cases hbad

/-- For three repeated row lists with total union at least eight, either
the cells and nonadjacent exceptions can be assigned, or two tight equal rows
contain both disjoint exceptional lists. This is an abstract list criterion. -/
theorem repeated_rows_large_union_assignment_or_obstruction {C : Type*} [DecidableEq C]
    (A : Fin 3 → Finset C) (Ea Eb : Finset C)
    (hA : ∀ i, 5 ≤ (A i).card) (hEa : 2 ≤ Ea.card) (hEb : 2 ≤ Eb.card)
    (htotal : 8 ≤ (univ.biUnion (fun z : Fin 3 × Bool => A z.1)).card) :
    TwoExceptionAssignment (fun z : Fin 3 × Bool => A z.1) Ea Eb ∨
      ∃ i j, i ≠ j ∧ A i = A j ∧ (A i).card = 5 ∧
        Ea ⊆ A i ∧ Eb ⊆ A i ∧ Disjoint Ea Eb := by
  classical
  by_cases hcommon : (Ea ∩ Eb).Nonempty
  · obtain ⟨w,hw⟩ := hcommon
    have hnear : ∀ z : Fin 3 × Bool, ∃ z', z' ≠ z ∧
        (A z.1 \ A z'.1).card ≤ 1 := by
      intro z
      refine ⟨(z.1,!z.2), ?_, by simp⟩
      intro h
      have hb := congrArg Prod.snd h
      cases z.2 <;> simp at hb
    obtain ⟨f,hf,hmem⟩ := six_cells_avoiding_common_color (by decide)
      (fun z : Fin 3 × Bool => A z.1) (fun z => hA z.1) hnear (by omega) w
    exact Or.inl ⟨f,w,w,hf,fun z => ⟨(hmem z).1,(hmem z).2,(hmem z).2⟩,
      (mem_inter.mp hw).1,(mem_inter.mp hw).2⟩
  have hdis : Disjoint Ea Eb := disjoint_left.mpr
    (fun c ha hb => hcommon ⟨c,mem_inter.mpr ⟨ha,hb⟩⟩)
  by_cases hpair : ∀ i j, i ≠ j → 6 ≤ (A i ∪ A j ∪ Ea ∪ Eb).card
  · exact Or.inl (repeated_rows_assignment_of_pair_unions A Ea Eb hA hEa hEb htotal hpair)
  · push Not at hpair
    obtain ⟨i,j,hij,hbad⟩ := hpair
    let K := A i ∪ A j ∪ Ea ∪ Eb
    have hK : K.card < 6 := hbad
    have hiK : A i ⊆ K := fun c hc =>
      mem_union_left _ (mem_union_left _ (mem_union_left _ hc))
    have hjK : A j ⊆ K := fun c hc =>
      mem_union_left _ (mem_union_left _ (mem_union_right _ hc))
    have hi := hA i
    have hj := hA j
    have hicount := card_le_card hiK
    have hjcount := card_le_card hjK
    have hiEq : A i = K := eq_of_subset_of_card_le hiK (by omega)
    have hjEq : A j = K := eq_of_subset_of_card_le hjK (by omega)
    refine Or.inr ⟨i,j,hij,hiEq.trans hjEq.symm,by omega,?_,?_,hdis⟩
    · rw [hiEq]
      exact fun c hc => mem_union_left _ (mem_union_right _ hc)
    · rw [hiEq]
      exact subset_union_right


end K23Reduction
end Part50

section Part51
-- Source module: K23ThreeLargeHost

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every overlap-three host with a cell union of at least eight colors extends.
At most one actual spoke changes and every fixed color is preserved. -/
theorem overlap_three_large_union_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20))
    (hT : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c)
    (hD : ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c).card = 3)
    (hunion : ((spokeEdges G p q U).image c ∪
      (T ∪ ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c))).card ≤ 12) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      (∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val) ∧
      (univ.filter (fun e : ↥(spokeEdges G p q U) =>
        color (spokeToEdge G p q U e) ≠ c e.val)).card ≤ 1 := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  have hqb : G.Adj q b := (hNq b).mpr (Or.inr rfl)
  let Q := (spokeEdges G p q U).image c
  let Da := (fixedAt G p q U a).image c
  let Db := (fixedAt G p q U b).image c
  let Γa := fixedConflictColors G p q U ⟨s(p,a), hpa⟩ c
  let Γb := fixedConflictColors G p q U ⟨s(q,b), hqb⟩ c
  let Ea := univ \ (Q ∪ Γa)
  let Eb := univ \ (Q ∪ Γb)
  let F : Fin 3 → Finset (Fin 20) := fun i =>
    (rowSeen G p q U (cellRow3 U hU i)).image c
  let L : Fin 3 × Bool → Finset (Fin 20) := fun z =>
    univ \ (Q ∪ F z.1 ∪ (if z.2 then Da else Db))
  let R := univ \ (Q ∪ (T ∪ (Da ∩ Db)))
  have hm : (spokeEdges G p q U).card ≤ 6 :=
    spokeEdges_card_le_six_of_common G p q U hU hpq hdegree hp hq
  have hQ : Q.card ≤ 6 := card_image_le.trans hm
  have hF : ∀ i, (F i).card ≤ 6 := fun i =>
    row_colors_card_le_six_of_common G p q U _ hpq hdegree
      (cellRow3_mem U hU i) (hp _ (cellRow3_mem U hU i))
      (hq _ (cellRow3_mem U hU i)) c
  have hDa : Da.card ≤ 3 :=
    fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c
  have hDb : Db.card ≤ 3 := by
    simpa only [fixedAt_swap] using
      fixedAt_colors_card_le_three_of_adj_left G q p U b hdegree hqb c
  have hTi : ∀ color, color ∈ T ↔ ∀ i, color ∈ F i := by
    intro color
    constructor
    · intro ht i
      exact (hT color).mp ht _ (cellRow3_mem U hU i)
    · intro ht
      apply (hT color).mpr
      intro u hu
      obtain ⟨i, hi⟩ := cellRow3_coverage U hU u hu
      exact hi ▸ ht i
  have hR : univ.biUnion L = R := by
    simpa only [L, R, union_assoc] using six_cell_union Q T Da Db F hTi
  have hRcard : 8 ≤ (univ.biUnion L).card := by
    rw [hR]
    change 8 ≤ (univ \ (Q ∪ (T ∪ (Da ∩ Db)))).card
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    change 8 ≤ 20 - ((spokeEdges G p q U).image c ∪
      (T ∪ ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c))).card
    omega
  have hL : ∀ z, 5 ≤ (L z).card := by
    intro z
    have hz : (if z.2 then Da else Db).card ≤ 3 := by cases z.2 <;> assumption
    have h1 := card_union_le Q (F z.1)
    have h2 := card_union_le (Q ∪ F z.1) (if z.2 then Da else Db)
    have hrow := hF z.1
    dsimp only [L]
    rw [card_sdiff_of_subset (subset_univ _)]
    simp only [card_univ, Fintype.card_fin]
    omega
  have hΓa : Γa.card ≤ 18 - (spokeEdges G p q U).card :=
    exceptional_fixed_colors_card_le G p q a U hpq hn hdegree hdp hpa hU hp hq c
  have hΓb : Γb.card ≤ 18 - (spokeEdges G p q U).card := by
    simpa only [fixedConflictColors_swap, spokeEdges_swap] using
      exceptional_fixed_colors_card_le G q p b U hpq.symm (fun h => hn h.symm)
        hdegree hdq hqb hU hq hp c
  have hEa : 2 ≤ Ea.card := exceptional_list_card_ge_two Q Γa _ hm card_image_le hΓa
  have hEb : 2 ≤ Eb.card := exceptional_list_card_ge_two Q Γb _ hm card_image_le hΓb
  let A : Fin 3 → Finset (Fin 20) := fun i => univ \ (Q ∪ F i ∪ (Da ∩ Db))
  have hDc : (Da ∩ Db).card = 3 := hD
  have hDaD : Da = Da ∩ Db :=
    (eq_of_subset_of_card_le inter_subset_left (by omega)).symm
  have hDbD : Db = Da ∩ Db :=
    (eq_of_subset_of_card_le inter_subset_right (by omega)).symm
  have hLA : L = fun z : Fin 3 × Bool => A z.1 := by
    funext z
    have he : (if z.2 then Da else Db) = Da ∩ Db := by cases z.2 <;> assumption
    change univ \ (Q ∪ F z.1 ∪ (if z.2 then Da else Db)) = univ \ (Q ∪ F z.1 ∪ (Da ∩ Db))
    rw [he]
  have hA : ∀ i, 5 ≤ (A i).card := by
    intro i
    have h := hL (i,true)
    rw [hLA] at h
    exact h
  have hAtotal : 8 ≤ (univ.biUnion (fun z : Fin 3 × Bool => A z.1)).card := by
    rw [← hLA]
    exact hRcard
  rcases repeated_rows_large_union_assignment_or_obstruction A Ea Eb hA hEa hEb hAtotal with
    hassign | hobstruction
  · rw [← hLA] at hassign
    obtain ⟨f, x, y, hfinj, hf, hx, hy⟩ := hassign
    let w : Bool → Fin 20 := fun j => if j then x else y
    let q0 := originalSpokeColoring G p q U c hc
    have hqimage : univ.image q0 = Q := originalSpokeColoring_image G p q U c hc
    have hfQ : ∀ z, f z ∉ Q := fun z h =>
      (mem_sdiff.mp (hf z).1).2 (mem_union_left _ (mem_union_left _ h))
    have hfc : ∀ z, f z ∈ availableColors G p q U (cellEdge3 G p q U hU hp hq z) c := by
      intro z
      rw [availableColors, cellEdge3_fixed_colors G p q a b U hU hp hq hNp hNq c z]
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro h
      exact (mem_sdiff.mp (hf z).1).2
        ((mem_union.mp h).elim (fun h => mem_union_left _ (mem_union_right _ h))
          (fun h => mem_union_right _ h))
    have hwQ : ∀ j, w j ∉ Q := by
      intro j
      cases j
      · exact fun h => (mem_sdiff.mp hy).2 (mem_union_left _ h)
      · exact fun h => (mem_sdiff.mp hx).2 (mem_union_left _ h)
    have hwc : ∀ j, w j ∈ availableColors G p q U (exceptionEdge G p q a b hpa hqb j) c := by
      intro j
      cases j
      · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hy).2 (mem_union_right _ h)⟩
      · exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hx).2 (mem_union_right _ h)⟩
    have hfw : ∀ z j, f z ≠ w j := by
      intro z j
      cases j
      · exact (hf z).2.2
      · exact (hf z).2.1
    have hnab := not_adj_of_fixedAt_color_overlap G p q a b U c hc (by omega)
    have hwproper := exception_assignment_compatible G p q a b U hpq hn hab haU hbU
      hpa hqb hNp hNq w (fun h => (hnab h).elim)
    obtain ⟨color, hfixed, hspoke, _, _⟩ := color_from_two_exception_assignment G
      (p := p) (q := q) (a := a) (b := b) (U := U) (hU := hU) (hpq := hpq) (hn := hn)
      (haU := haU) (hbU := hbU) (hp := hp) (hq := hq) (hpa := hpa) (hqb := hqb)
      (hNp := hNp) (hNq := hNq) (c := c) (hc := hc) (qcolor := q0)
      (havailable := originalSpokeColoring_mem_available G p q U c hc)
      (f := f) (hfinj := hfinj) (w := w) (hfspokes := by simpa only [hqimage] using hfQ)
      (hfc := hfc) (hfw := hfw) (hwspokes := by simpa only [hqimage] using hwQ)
      (hwc := hwc) (hwproper := hwproper)
    refine ⟨color, hfixed, ?_⟩
    have hsame : ∀ e, color (spokeToEdge G p q U e) = c e.val := hspoke
    simp [hsame]
  · obtain ⟨i,_,_,_,hi,ha,hb,hd⟩ := hobstruction
    obtain ⟨v, color, hfixed, hsame, _⟩ := tight_row_host_extension G p q a b U hU hpq hn
      hab haU hbU hdegree hdp hdq hNp hNq c hc T hT i hD (by omega) hi
      (by simpa only [A, union_assoc] using ha)
      (by simpa only [A, union_assoc] using hb) hd
    refine ⟨color, hfixed, ?_⟩
    have hsub : univ.filter (fun e : ↥(spokeEdges G p q U) =>
        color (spokeToEdge G p q U e) ≠ c e.val) ⊆ {v} := by
      intro e he
      apply mem_singleton.mpr
      by_contra hev
      exact (mem_filter.mp he).2 (hsame e hev)
    exact (card_le_card hsub).trans (by simp)


end K23Reduction
end Part51

section Part52
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
end Part52

section Part53
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
end Part53

section Part54
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
end Part54

section Part55
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
end Part55

section Part56
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
end Part56

section Part57
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
end Part57

section Part58
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
end Part58

section Part59
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
end Part59

section Part60
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
end Part60

section Part61
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
end Part61

section Part62
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
end Part62

section Part63
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
end Part63

section Part64
-- Source module: K23Host

namespace K23Reduction

open SimpleGraph Finset StructuralAttack TwinReduction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The common-five overlap-three case extends after recoloring actual spokes. -/
theorem five_common_overlap_three_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c)
    (T : Finset (Fin 20)) (hTc : T.card = 5)
    (hT : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c)
    (hD : ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c).card = 3)
    (hTD : Disjoint T ((fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c)) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c :=
    fun u hu color ht => (hT color).mp ht u hu
  let D := (fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c
  obtain ⟨qcolor,havailable,hunion⟩ := five_actual_spoke_compression G p q U hU hpq hdegree
    hp hq c T hTc hcommon D hD hTD
    (spoke_available_card_ge_degree_add_four G p q U hpq hn hdegree hdp hdq hp hq c)
  let c' := retainedRecolor G p q U c qcolor
  have hc' : RetainedProper G p q c' :=
    retainedRecolor_proper G p q U c qcolor hc havailable
  have hfixed : ∀ e ∈ fixedEdges G p q U, c' e = c e :=
    retainedRecolor_fixed G p q U c qcolor
  have hT' : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c' := by
    intro color
    simpa only [c', retainedRecolor_rowSeen_image] using hT color
  have hD' : ((fixedAt G p q U a).image c' ∩ (fixedAt G p q U b).image c').card = 3 := by
    simpa only [c', retainedRecolor_fixedAt_image] using hD
  have hunion' : ((spokeEdges G p q U).image c' ∪
      (T ∪ ((fixedAt G p q U a).image c' ∩ (fixedAt G p q U b).image c'))).card ≤ 13 := by
    simpa only [c', retainedRecolor_spoke_image, retainedRecolor_fixedAt_image, union_assoc] using hunion
  have hresult : ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c' e.val := by
    by_cases hsmall : ((spokeEdges G p q U).image c' ∪
        (T ∪ ((fixedAt G p q U a).image c' ∩ (fixedAt G p q U b).image c'))).card ≤ 12
    · obtain ⟨color,hcolor,_⟩ := overlap_three_large_union_host_extension G p q a b U hU
        hpq hn hab haU hbU hdegree hdp hdq hNp hNq c' hc' T hT' hD' hsmall
      exact ⟨color,hcolor⟩
    · obtain ⟨color,hcolor,_⟩ := seven_union_host_dispatch G p q a b U hU hpq hn hab haU hbU
        hdegree hdp hdq hNp hNq c' hc' T hT' (by omega) (by omega)
      exact ⟨color,hcolor⟩
  obtain ⟨color,hcolor⟩ := hresult
  exact ⟨color,fun e he => (hcolor e he).trans (hfixed e.val he)⟩

/-- Every exact K2,3 retained coloring extends, changing only the at-most-six
actual spokes. All conflict relations are those of the original host. -/
theorem k23_retained_host_extension (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (c : Sym2 V → Fin 20) (hc : RetainedProper G p q c) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : G.edgeSet, e.val ∈ fixedEdges G p q U → color e = c e.val := by
  classical
  have hp : ∀ u ∈ U, G.Adj p u := fun u hu => (hNp u).mpr (Or.inl hu)
  have hq : ∀ u ∈ U, G.Adj q u := fun u hu => (hNq u).mpr (Or.inl hu)
  have hpa : G.Adj p a := (hNp a).mpr (Or.inr rfl)
  let Q := (spokeEdges G p q U).image c
  let D := (fixedAt G p q U a).image c ∩ (fixedAt G p q U b).image c
  have hDle : D.card ≤ 3 := (card_le_card inter_subset_left).trans
    (fixedAt_colors_card_le_three_of_adj_left G p q U a hdegree hpa c)
  by_cases hDsmall : D.card ≤ 2
  · exact overlap_at_most_two_host_extension G p q a b U hU hpq hn hab haU hbU hdegree
      hdp hdq hNp hNq c hc hDsmall
  have hD : D.card = 3 := by omega
  let T : Finset (Fin 20) := univ.filter
    (fun color => ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c)
  have hT : ∀ color, color ∈ T ↔ ∀ u ∈ U, color ∈ (rowSeen G p q U u).image c := by
    intro color
    simp only [T, mem_filter, mem_univ, true_and]
  have hcommon : ∀ u ∈ U, T ⊆ (rowSeen G p q U u).image c :=
    fun u hu color ht => (hT color).mp ht u hu
  have hTle : T.card ≤ 6 := (card_le_card (hcommon (cellRow3 U hU 0) (cellRow3_mem U hU 0))).trans
    (row_colors_card_le_six_of_common G p q U _ hpq hdegree (cellRow3_mem U hU 0)
      (hp _ (cellRow3_mem U hU 0)) (hq _ (cellRow3_mem U hU 0)) c)
  by_cases hsix : T.card = 6
  · exact six_common_host_extension G p q a b U hU hpq hn hab haU hbU hdegree hdp hdq
      hNp hNq c hc T hsix hcommon
  have hTfive : T.card ≤ 5 := by omega
  by_cases hlarge : (Q ∪ (T ∪ D)).card ≤ 12
  · obtain ⟨color,hcolor,_⟩ := overlap_three_large_union_host_extension G p q a b U hU hpq hn
      hab haU hbU hdegree hdp hdq hNp hNq c hc T hT hD hlarge
    exact ⟨color,hcolor⟩
  by_cases hseven : (Q ∪ (T ∪ D)).card = 13
  · obtain ⟨color,hcolor,_⟩ := seven_union_host_dispatch G p q a b U hU hpq hn hab haU hbU
      hdegree hdp hdq hNp hNq c hc T hT (by change 2 ≤ D.card; omega) hseven
    exact ⟨color,hcolor⟩
  have hQ : Q.card ≤ 6 := card_image_le.trans
    (spokeEdges_card_le_six_of_common G p q U hU hpq hdegree hp hq)
  have h1 := card_union_le Q T
  have h2 := card_union_le (Q ∪ T) D
  have hunion : (Q ∪ T ∪ D).card = 6 + 5 + 3 := by
    rw [union_assoc] at h2
    rw [union_assoc]
    omega
  obtain ⟨_,hTc,_,_,_,hTD⟩ := three_set_card_saturation Q T D 6 5 3 hQ hTfive hDle hunion
  exact five_common_overlap_three_host_extension G p q a b U hU hpq hn hab haU hbU
    hdegree hdp hdq hNp hNq c hc T hTc hT hD hTD

/-- A strong coloring after induced vertex deletion transfers to the retained
host relation, then extends with every fixed input color preserved. -/
theorem twenty_color_k23_extension_from_induce (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b)
    (g : (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Coloring (Fin 20)) :
    ∃ color : (strongConflict G).Coloring (Fin 20),
      ∀ e : (G.induce {v | v ≠ p ∧ v ≠ q}).edgeSet,
        ((SimpleGraph.Embedding.induce (G := G) {v | v ≠ p ∧ v ≠ q}).mapEdgeSet e).val ∈
          fixedEdges G p q U →
        color ((SimpleGraph.Embedding.induce (G := G) {v | v ≠ p ∧ v ≠ q}).mapEdgeSet e) = g e := by
  obtain ⟨c,hc,hagree⟩ := retainedProper_from_induced_coloring G p q g
  obtain ⟨color,hcolor⟩ := k23_retained_host_extension G p q a b U hU hpq hn hab haU hbU
    hdegree hdp hdq hNp hNq c hc
  exact ⟨color,fun e he => (hcolor _ he).trans (hagree e)⟩

/-- The exact K2,3 configuration is reducible for strong twenty-colorability. -/
theorem twenty_color_k23_vertex_deletion (p q a b : V) (U : Finset V) (hU : U.card = 3)
    (hpq : p ≠ q) (hn : ¬G.Adj p q) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hdegree : G.maxDegree ≤ 4) (hdp : G.degree p = 4) (hdq : G.degree q = 4)
    (hNp : ∀ v, G.Adj p v ↔ v ∈ U ∨ v = a)
    (hNq : ∀ v, G.Adj q v ↔ v ∈ U ∨ v = b) :
    (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Colorable 20 →
      (strongConflict G).Colorable 20 := by
  rintro ⟨g⟩
  obtain ⟨color,_⟩ := twenty_color_k23_extension_from_induce G p q a b U hU hpq hn hab haU hbU
    hdegree hdp hdq hNp hNq g
  exact ⟨color⟩


end K23Reduction
end Part64

open StructuralAttack

open scoped Classical in
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ p q a b : Fin n, ∀ U : Finset (Fin n),
    U.card = 3 → p ≠ q → ¬ G.Adj p q → a ≠ b → a ∉ U → b ∉ U →
    G.maxDegree ≤ 4 → G.degree p = 4 → G.degree q = 4 →
    (∀ v, G.Adj p v ↔ v ∈ U ∨ v = a) →
    (∀ v, G.Adj q v ↔ v ∈ U ∨ v = b) →
    (strongConflict (G.induce {v | v ≠ p ∧ v ≠ q})).Colorable 20 →
      (strongConflict G).Colorable 20

/-- The explicit degree-four exact K2,3 configuration is reducible for strong
 twenty-colorability; this is a partial deletion lemma for the root problem. -/
theorem proof : statement := by
  classical
  intro n G p q a b U hU hpq hn hab haU hbU hdegree hdp hdq hNp hNq
  exact K23Reduction.twenty_color_k23_vertex_deletion G p q a b U hU hpq hn hab haU hbU
    hdegree hdp hdq hNp hNq

#print axioms proof

end Submissions.Erdos149K23Deletion.Savcab

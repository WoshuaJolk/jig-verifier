import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.SetTheory.Cardinal.Finite

/-!
Uncompiled draft of the exact Jig #399 S19 statement.
The small inlined path-closing helper is from our locally checked S20 source, SHA-256
465a643a8d833064a44f615f6975c52d9e017ac330768753032503294403b3aa.
No Submissions or canonical admitted module is imported.

The four-cycle constructor below is copied from am00lya's S3 proof,
artifact 31afcd6a-e56b-47ec-9cf5-fec4fcf2216f, source SHA-256
7e6da73006f8016e2b893c461d76fe50afeadfb9d83db2f74b4a11eff197d7d6.
S19's closed-neighborhood argument was previously posted by ~qf9gr3.
The quotient-degree and walk-lifting proofs below implement the argument
in closed-neighborhood-plan.md. No successful check of this full draft
is claimed; the separately saved foundation snapshot was checked locally.
-/

namespace Erdos64.NontriangularContraction

open scoped Sym2

variable {V : Type*} {G : SimpleGraph V} {u v : V} [DecidableEq V]

/-- Close a path avoiding both endpoints through their joining edge. -/
theorem close_opposite_path {x y : V} (huv : G.Adj u v)
    (d : G.Walk x y) (hd : d.IsPath)
    (hud : u ∉ d.support) (hvd : v ∉ d.support)
    (hux : G.Adj u x) (hvy : G.Adj v y) :
    ∃ e : G.Walk v v, e.IsCycle ∧ e.length = d.length + 3 ∧
      s(u, v) ∈ e.edgeSet := by
  let r : G.Walk u v := SimpleGraph.Walk.cons hux (d.concat hvy.symm)
  have hrpath : r.IsPath := (hd.concat hvd hvy.symm).cons (by
    simp [hud, huv.ne])
  have hedge : s(v, u) ∉ r.edges := by
    intro he
    simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_concat,
      List.concat_eq_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at he
    rcases he with he | he | he
    · rcases Sym2.eq_iff.mp he with h | h
      · exact huv.ne h.1.symm
      · apply hvd
        simpa only [h.1] using d.start_mem_support
    · exact hvd (d.fst_mem_support_of_mem_edges he)
    · rcases Sym2.eq_iff.mp he with h | h
      · exact huv.ne h.2
      · apply hud
        simpa only [h.2] using d.end_mem_support
  let e : G.Walk v v := SimpleGraph.Walk.cons huv.symm r
  refine ⟨e, (SimpleGraph.Walk.cons_isCycle_iff r huv.symm).mpr
    ⟨hrpath, hedge⟩, ?_, ?_⟩
  · simp [e, r, Nat.add_assoc]
  · simp [e, Sym2.eq_swap]

end Erdos64.NontriangularContraction

namespace Erdos64.ClosedNeighborhoodContraction

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≠ 4

theorem four_cycle_of_common {x y a b : V}
    (hxy : x ≠ y) (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hya : G.Adj y a) (hyb : G.Adj y b) :
    ∃ (c : G.Walk x x), c.IsCycle ∧ c.length = 4 := by
  refine ⟨Walk.cons hxa (Walk.cons hya.symm (Walk.cons hyb (Walk.cons hxb.symm Walk.nil))),
    ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    have h1 := hxa.ne
    have h2 := hxb.ne
    have h3 := hya.ne
    have h4 := hyb.ne
    constructor
    · rw [Walk.isPath_def]
      simp [List.nodup_cons, hab, h4, hxy.symm, h1.symm, h2.symm, h3.symm]
    · simp [Walk.edges_cons, hab, hxy, h1, h2, h1.symm, h3.symm]
  · simp

/-- Distinct vertices cannot share two different neighbors. -/
theorem common_neighbor_unique (h4 : NoFourCycle G) {x y a b : V}
    (hxy : x ≠ y) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hya : G.Adj y a) (hyb : G.Adj y b) : a = b := by
  by_contra hab
  obtain ⟨c, hc, hlen⟩ := four_cycle_of_common hxy hab hxa hxb hya hyb
  exact h4 x c hc hlen

/-- The graph induced by a neighborhood has maximum degree one. -/
theorem neighbor_internal_unique (h4 : NoFourCycle G) {v a b c : V}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : G.Adj a b) (hac : G.Adj a c) : b = c :=
  common_neighbor_unique h4 hva.ne hvb hvc hab hac

/-- Every leaf has an external neighbor, including when it lies in a triangle. -/
theorem external_neighbor [Fintype V] [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {v a : V} (hva : G.Adj v a)
    (hdeg : 3 ≤ G.degree a) :
    ∃ x : V, G.Adj a x ∧ ¬ G.Adj v x ∧ x ≠ v := by
  classical
  have hv : v ∈ G.neighborFinset a := by simpa using hva.symm
  have hcard : 1 < ((G.neighborFinset a).erase v).card := by
    rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨hxv, hxa⟩ := Finset.mem_erase.mp hx
  obtain ⟨hyv, hya⟩ := Finset.mem_erase.mp hy
  have hax : G.Adj a x := (G.mem_neighborFinset a x).mp hxa
  have hay : G.Adj a y := (G.mem_neighborFinset a y).mp hya
  by_cases hvx : G.Adj v x
  · by_cases hvy : G.Adj v y
    · exact (hxy (common_neighbor_unique h4 hva.ne hvx hvy hax hay)).elim
    · exact ⟨y, hay, hvy, hyv⟩
  · exact ⟨x, hax, hvx, hxv⟩

/-- Distinct leaves cannot use the same external neighbor. -/
theorem external_neighbor_unique_leaf (h4 : NoFourCycle G) {v x a b : V}
    (hxv : x ≠ v) (hva : G.Adj v a) (hvb : G.Adj v b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b :=
  common_neighbor_unique h4 hxv.symm hva hvb hxa hxb

/-- Vertices surviving the contraction: the center and its nonneighbors. -/
abbrev Survivors (G : SimpleGraph V) (v : V) := {x : V // ¬ G.Adj v x}

def center (G : SimpleGraph V) (v : V) : Survivors G v := ⟨v, G.irrefl⟩

def collapse (G : SimpleGraph V) [DecidableRel G.Adj] (v x : V) : Survivors G v :=
  if hx : G.Adj v x then center G v else ⟨x, hx⟩

def quotient (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    SimpleGraph (Survivors G v) := G.map (collapse G v)

@[simp] theorem collapse_of_adj [DecidableRel G.Adj] {v x : V} (hx : G.Adj v x) :
    collapse G v x = center G v := by simp [collapse, hx]

@[simp] theorem collapse_of_not_adj [DecidableRel G.Adj] {v x : V}
    (hx : ¬ G.Adj v x) : collapse G v x = ⟨x, hx⟩ := by simp [collapse, hx]

@[simp] theorem collapse_center [DecidableRel G.Adj] (v : V) :
    collapse G v v = center G v := by simp [collapse, center]

theorem collapse_surjective [DecidableRel G.Adj] (v : V) :
    Function.Surjective (collapse G v) := by
  rintro ⟨x, hx⟩
  exact ⟨x, collapse_of_not_adj hx⟩

theorem survivor_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : Fintype.card (Survivors G v) = n - G.degree v := by
  change Fintype.card {x : Fin n // ¬ G.Adj v x} = _
  rw [Fintype.card_subtype_compl]
  change Fintype.card (Fin n) - Fintype.card (G.neighborSet v) = _
  rw [Fintype.card_fin, G.card_neighborSet_eq_degree]

theorem survivor_card_pos [Fintype V] [DecidableRel G.Adj] (v : V) :
    0 < Fintype.card (Survivors G v) :=
  Fintype.card_pos_iff.mpr ⟨center G v⟩

theorem survivor_card_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (hdeg : 3 ≤ G.degree v) : Fintype.card (Survivors G v) < n := by
  rw [survivor_card]
  have hn := v.isLt
  omega

/-- Reuse the S20 path-closing lemma after adjoining the second leaf.
The resulting cycle goes through the original center and gains two edges
relative to the quotient cycle whose outside path is `d`. -/
theorem cycle_through_center_of_distinct_leaves [DecidableEq V] {v a b x y : V}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    (d : G.Walk x y) (hd : d.IsPath)
    (hvd : v ∉ d.support) (had : a ∉ d.support) (hbd : b ∉ d.support)
    (hax : G.Adj a x) (hby : G.Adj b y) :
    ∃ c : G.Walk v v, c.IsCycle ∧ c.length = d.length + 4 ∧ v ∈ c.support := by
  let p : G.Walk x b := d.concat hby.symm
  have hp : p.IsPath := hd.concat hbd hby.symm
  have hap : a ∉ p.support := by simp [p, had, hab]
  have hvp : v ∉ p.support := by simp [p, hvd, hvb.ne]
  obtain ⟨c, hc, hlen, _⟩ := Erdos64.NontriangularContraction.close_opposite_path
    hva.symm p hp hap hvp hax hvb
  refine ⟨c, hc, ?_, c.start_mem_support⟩
  simpa [p, Nat.add_assoc] using hlen

end Erdos64.ClosedNeighborhoodContraction

namespace Erdos64.ClosedNeighborhoodContraction

open scoped Sym2

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
variable (v : V)

theorem collapse_eq_center {a : V} :
    collapse G v a = center G v ↔ a = v ∨ G.Adj v a := by
  by_cases ha : G.Adj v a
  · simp [collapse, ha]
  · simp [collapse, ha, center]

theorem eq_of_collapse_eq_away {a : V} {x : Survivors G v}
    (hx : x.1 ≠ v) (ha : collapse G v a = x) : a = x.1 := by
  by_cases hna : G.Adj v a
  · have he : v = x.1 := by
      simpa [collapse, hna, center] using congrArg Subtype.val ha
    exact (hx he.symm).elim
  · simpa [collapse, hna] using congrArg Subtype.val ha

theorem quotient_adj_iff (x y : Survivors G v) :
    (quotient G v).Adj x y ↔ x ≠ y ∧ ∃ a b : V,
      G.Adj a b ∧ collapse G v a = x ∧ collapse G v b = y :=
  SimpleGraph.map_adj' _ _ _ _

theorem quotient_adj_iff_away (x y : Survivors G v)
    (hx : x.1 ≠ v) (hy : y.1 ≠ v) :
    (quotient G v).Adj x y ↔ G.Adj x.1 y.1 := by
  constructor
  · rw [quotient_adj_iff]
    rintro ⟨_, a, b, hab, ha, hb⟩
    simpa only [eq_of_collapse_eq_away v hx ha,
      eq_of_collapse_eq_away v hy hb] using hab
  · intro hxy
    rw [quotient_adj_iff]
    exact ⟨(fun he => hxy.ne (congrArg Subtype.val he)), x.1, y.1,
      hxy, collapse_of_not_adj x.2, collapse_of_not_adj y.2⟩

theorem leaf_origin_of_center_adj {x : Survivors G v}
    (h : (quotient G v).Adj (center G v) x) :
    ∃ a : V, G.Adj v a ∧ G.Adj a x.1 := by
  have hx : x.1 ≠ v := by
    intro he
    exact h.ne (Subtype.ext he.symm)
  rw [quotient_adj_iff] at h
  obtain ⟨_, a, b, hab, ha, hb⟩ := h
  have hb' : b = x.1 := eq_of_collapse_eq_away v hx hb
  subst b
  rcases (collapse_eq_center v).mp ha with rfl | hva
  · exact (x.2 hab).elim
  · exact ⟨a, hva, hab⟩

theorem degree_le_quotient_of_away [Fintype V] (h4 : NoFourCycle G)
    (x : Survivors G v) (hx : x.1 ≠ v) :
    G.degree x.1 ≤ @SimpleGraph.degree _ (quotient G v) x (Fintype.ofFinite _) := by
  classical
  let f := collapse G v
  letI : Fintype ((quotient G v).neighborSet x) := Fintype.ofFinite _
  have hfx : f x.1 = x := collapse_of_not_adj x.2
  have hedge_ne : ∀ z : G.neighborSet x.1, f x.1 ≠ f z.1 := by
    intro z he
    have hz : z.1 = x.1 := eq_of_collapse_eq_away v hx (he.symm.trans hfx)
    exact z.2.ne hz.symm
  let phi : G.neighborSet x.1 → (quotient G v).neighborSet x :=
    fun z => ⟨f z.1, by
      change (G.map f).Adj x (f z.1)
      simpa only [hfx] using SimpleGraph.map_adj_apply' z.2 (hedge_ne z)⟩
  have hphi : Function.Injective phi := by
    intro z₁ z₂ he
    have hf : f z₁.1 = f z₂.1 := congrArg Subtype.val he
    by_cases hm : f z₁.1 = center G v
    · have hm₂ : f z₂.1 = center G v := hf.symm.trans hm
      have hn₁ := (collapse_eq_center v).mp hm
      have hn₂ := (collapse_eq_center v).mp hm₂
      rcases hn₁ with hn₁ | hn₁
      · exact (x.2 (by simpa only [hn₁] using z₁.2.symm)).elim
      rcases hn₂ with hn₂ | hn₂
      · exact (x.2 (by simpa only [hn₂] using z₂.2.symm)).elim
      exact Subtype.ext (common_neighbor_unique h4 hx.symm hn₁ hn₂ z₁.2 z₂.2)
    · have haway : (f z₁.1).1 ≠ v := by
        intro hv
        exact hm (Subtype.ext hv)
      have hz₁ : z₁.1 = (f z₁.1).1 := eq_of_collapse_eq_away v haway rfl
      have hz₂ : z₂.1 = (f z₁.1).1 := eq_of_collapse_eq_away v haway hf.symm
      exact Subtype.ext (hz₁.trans hz₂.symm)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective phi hphi

theorem degree_le_quotient_center [Fintype V] (h4 : NoFourCycle G)
    (hmin : ∀ x : V, 3 ≤ G.degree x) :
    G.degree v ≤
      @SimpleGraph.degree _ (quotient G v) (center G v) (Fintype.ofFinite _) := by
  classical
  have hex : ∀ a : G.neighborSet v, ∃ x : V,
      G.Adj a.1 x ∧ ¬ G.Adj v x ∧ x ≠ v :=
    fun a => external_neighbor h4 a.2 (hmin a.1)
  choose ext hext using hex
  letI : Fintype ((quotient G v).neighborSet (center G v)) := Fintype.ofFinite _
  let phi : G.neighborSet v → (quotient G v).neighborSet (center G v) :=
    fun a => ⟨⟨ext a, (hext a).2.1⟩, by
      change (quotient G v).Adj (center G v) ⟨ext a, (hext a).2.1⟩
      rw [quotient_adj_iff]
      refine ⟨?_, a.1, ext a, (hext a).1, collapse_of_adj a.2,
        collapse_of_not_adj (hext a).2.1⟩
      intro he
      exact (hext a).2.2 (congrArg Subtype.val he).symm⟩
  have hphi : Function.Injective phi := by
    intro a b he
    have hextab : ext a = ext b := congrArg
      (fun z : (quotient G v).neighborSet (center G v) => z.1.1) he
    apply Subtype.ext
    apply external_neighbor_unique_leaf h4 (hext a).2.2 a.2 b.2
      (hext a).1.symm
    simpa only [hextab] using (hext b).1.symm
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective phi hphi

theorem quotient_min_degree_three [Fintype V] (h4 : NoFourCycle G)
    (hmin : ∀ x : V, 3 ≤ G.degree x) (x : Survivors G v) :
    3 ≤ @SimpleGraph.degree _ (quotient G v) x (Fintype.ofFinite _) := by
  by_cases hx : x.1 = v
  · have he : x = center G v := Subtype.ext hx
    subst x
    exact (hmin v).trans (degree_le_quotient_center v h4 hmin)
  · exact (hmin x.1).trans (degree_le_quotient_of_away v h4 x hx)

theorem quotient_min_natCard_three [Fintype V] (h4 : NoFourCycle G)
    (hmin : ∀ x : V, 3 ≤ G.degree x) (x : Survivors G v) :
    3 ≤ Nat.card ((quotient G v).neighborSet x) := by
  have hm := quotient_min_degree_three v h4 hmin x
  rw [← @SimpleGraph.card_neighborSet_eq_degree _ _ _ (Fintype.ofFinite _)] at hm
  rw [← @Nat.card_eq_fintype_card _ (Fintype.ofFinite _)] at hm
  exact hm

def awaySet : Set (Survivors G v) := {x | x.1 ≠ v}

def awayEmbedding :
    ((quotient G v).induce (awaySet (G := G) v)) ↪g G where
  toFun x := x.1.1
  inj' _ _ he := Subtype.ext (Subtype.ext he)
  map_rel_iff' := by
    intro x y
    exact (quotient_adj_iff_away v x.1 y.1 x.2 y.2).symm

theorem center_not_mem_awayMapped_support
    {x y : awaySet (G := G) v}
    (p : ((quotient G v).induce (awaySet (G := G) v)).Walk x y) :
    v ∉ (p.map (awayEmbedding (G := G) v).toHom).support := by
  intro hv
  have hv' : v ∈ List.map (awayEmbedding (G := G) v).toHom p.support := by
    simpa only [SimpleGraph.Walk.support_map] using hv
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hv'
  exact z.2 (by simpa [awayEmbedding] using hz)

theorem leaf_not_mem_awayMapped_support {a : V} (hva : G.Adj v a)
    {x y : awaySet (G := G) v}
    (p : ((quotient G v).induce (awaySet (G := G) v)).Walk x y) :
    a ∉ (p.map (awayEmbedding (G := G) v).toHom).support := by
  intro ha
  have ha' : a ∈ List.map (awayEmbedding (G := G) v).toHom p.support := by
    simpa only [SimpleGraph.Walk.support_map] using ha
  obtain ⟨z, _, hz⟩ := List.mem_map.mp ha'
  have heq : z.1.1 = a := by simpa [awayEmbedding] using hz
  apply z.1.2
  simpa only [heq] using hva

def liftAwayWalk {x y : Survivors G v}
    (p : (quotient G v).Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ awaySet (G := G) v) : G.Walk x.1 y.1 :=
  (p.induce (awaySet (G := G) v) hp).map (awayEmbedding (G := G) v).toHom

@[simp] theorem liftAwayWalk_length {x y : Survivors G v}
    (p : (quotient G v).Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ awaySet (G := G) v) :
    (liftAwayWalk v p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      change (liftAwayWalk v p _).length + 1 = p.length + 1
      exact congrArg (· + 1) (ih _)

theorem liftAwayWalk_isPath {x y : Survivors G v}
    (p : (quotient G v).Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ awaySet (G := G) v)
    (hpath : p.IsPath) : (liftAwayWalk v p hp).IsPath := by
  unfold liftAwayWalk
  have hi : (p.induce (awaySet (G := G) v) hp).IsPath := by
    rw [SimpleGraph.Walk.isPath_def] at hpath ⊢
    rw [SimpleGraph.Walk.support_induce]
    apply List.Nodup.of_map Subtype.val
    rw [List.attachWith_map_subtype_val]
    exact hpath
  exact hi.map (awayEmbedding (G := G) v).injective

theorem cycle_lifts_of_center_not_mem {x : Survivors G v}
    (c : (quotient G v).Walk x x) (hc : c.IsCycle)
    (hm : center G v ∉ c.support) :
    ∃ d : G.Walk x.1 x.1, d.IsCycle ∧ d.length = c.length := by
  have hp : ∀ z ∈ c.support, z ∈ awaySet (G := G) v := by
    intro z hz hzv
    apply hm
    have heq : z = center G v := Subtype.ext hzv
    simpa only [heq] using hz
  let ci := c.induce (awaySet (G := G) v) hp
  have hci : ci.IsCycle := by
    have hmap : (ci.map (SimpleGraph.Embedding.induce
        (G := quotient G v) (awaySet (G := G) v)).toHom).IsCycle := by
      convert hc using 1 <;> simp [ci]
    exact SimpleGraph.Walk.IsCycle.of_map hmap
  let d := ci.map (awayEmbedding (G := G) v).toHom
  refine ⟨d, hci.map (awayEmbedding (G := G) v).injective, ?_⟩
  exact liftAwayWalk_length v c hp

theorem cycle_lifts_of_based_at_center
    (c : (quotient G v).Walk (center G v) (center G v)) (hc : c.IsCycle) :
    ∃ w : V, ∃ d : G.Walk w w, d.IsCycle ∧
      (d.length = c.length ∨ (d.length = c.length + 2 ∧ v ∈ d.support)) := by
  cases c with
  | nil => exact (hc.not_nil (by simp)).elim
  | @cons _ x _ h p =>
    have hpnon : ¬p.Nil := SimpleGraph.Walk.not_nil_of_isCycle_cons hc
    have hpc := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc
    let q := p.dropLast
    let y := p.penultimate
    have hlast : (quotient G v).Adj y (center G v) := p.adj_penultimate hpnon
    have hmnot : center G v ∉ q.support := by
      have hn := hpc.1.support_nodup
      rw [← p.support_dropLast_concat hpnon] at hn
      have hd := (List.nodup_append.mp hn).2.2
      intro hm
      exact hd (center G v) (by simpa [q] using hm) (center G v) (by simp) rfl
    have hqaway : ∀ z ∈ q.support, z ∈ awaySet (G := G) v := by
      intro z hz hzv
      apply hmnot
      have heq : z = center G v := Subtype.ext hzv
      simpa [heq] using hz
    obtain ⟨a, hva, hax⟩ := leaf_origin_of_center_adj v h
    obtain ⟨b, hvb, hby⟩ := leaf_origin_of_center_adj v hlast.symm
    let d := liftAwayWalk v q hqaway
    have hdpath : d.IsPath := liftAwayWalk_isPath v q hqaway hpc.1.dropLast
    have hvd : v ∉ d.support := center_not_mem_awayMapped_support v
      (q.induce (awaySet (G := G) v) hqaway)
    have had : a ∉ d.support := leaf_not_mem_awayMapped_support v hva
      (q.induce (awaySet (G := G) v) hqaway)
    have hbd : b ∉ d.support := leaf_not_mem_awayMapped_support v hvb
      (q.induce (awaySet (G := G) v) hqaway)
    by_cases hab : a = b
    · subst b
      let r : G.Walk x.1 a := d.concat hby.symm
      have hrpath : r.IsPath := hdpath.concat had hby.symm
      have hedge : s(a, x.1) ∉ r.edges := by
        intro he
        simp [r, Sym2.eq_iff] at he
        rcases he with he | he
        · exact had (d.fst_mem_support_of_mem_edges he)
        · have hlastmem : s(y, center G v) ∈ p.edges :=
            p.mk_penultimate_end_mem_edges hpnon
          apply hpc.2
          rcases he with he | he
          · exact (hby.ne he.1).elim
          · have hxy : x = y := Subtype.ext he
            simpa only [hxy, Sym2.eq_swap] using hlastmem
      let e : G.Walk a a := SimpleGraph.Walk.cons hax r
      refine ⟨a, e, (SimpleGraph.Walk.cons_isCycle_iff r hax).mpr
        ⟨hrpath, hedge⟩, Or.inl ?_⟩
      simp [e, r, d, liftAwayWalk_length]
      exact SimpleGraph.Walk.length_dropLast_add_one hpnon
    · obtain ⟨e, he, helen, hevmem⟩ := cycle_through_center_of_distinct_leaves
        hva hvb hab d hdpath hvd had hbd hax hby
      refine ⟨v, e, he, Or.inr ⟨?_, hevmem⟩⟩
      have hdlen : d.length = p.dropLast.length := liftAwayWalk_length v q hqaway
      have hplen := SimpleGraph.Walk.length_dropLast_add_one hpnon
      simp only [SimpleGraph.Walk.length_cons]
      omega

theorem quotient_cycle_lifts {x : Survivors G v}
    (c : (quotient G v).Walk x x) (hc : c.IsCycle) :
    ∃ w : V, ∃ d : G.Walk w w, d.IsCycle ∧
      (d.length = c.length ∨ (d.length = c.length + 2 ∧ v ∈ d.support)) := by
  by_cases hm : center G v ∈ c.support
  · obtain ⟨w, d, hd, hlen⟩ := cycle_lifts_of_based_at_center v
      (c.rotate (center G v) hm) (hc.rotate _)
    exact ⟨w, d, hd, by simpa using hlen⟩
  · obtain ⟨d, hd, hlen⟩ := cycle_lifts_of_center_not_mem v c hc hm
    exact ⟨x.1, d, hd, Or.inl hlen⟩

noncomputable def canonicalQuotient [Fintype V] :
    SimpleGraph (Fin (Fintype.card (Survivors G v))) :=
  (quotient G v).map (Fintype.equivFin (Survivors G v))

noncomputable def quotientIso [Fintype V] :
    quotient G v ≃g canonicalQuotient (G := G) v :=
  SimpleGraph.Iso.map (Fintype.equivFin (Survivors G v)) _

theorem cycle_maps_from_canonical [Fintype V]
    {x : Fin (Fintype.card (Survivors G v))}
    (c : (canonicalQuotient (G := G) v).Walk x x) (hc : c.IsCycle) :
    ∃ y : Survivors G v, ∃ d : (quotient G v).Walk y y,
      d.IsCycle ∧ d.length = c.length := by
  let d := c.map (quotientIso (G := G) v).symm.toHom
  exact ⟨(quotientIso (G := G) v).symm x, d,
    hc.map (quotientIso (G := G) v).symm.injective,
    SimpleGraph.Walk.length_map _ c⟩

end Erdos64.ClosedNeighborhoodContraction

namespace Submissions.ErdosGyarfasClosedNeighborhoodCycles.ClosedNeighborhoodContraction

open Erdos64.ClosedNeighborhoodContraction

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ),
    c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsOrderMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    IsCex H → n ≤ m

/-- Every vertex of a minimum-order counterexample lies on a cycle whose
length is two more than a power of two. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsOrderMinCex G → ∀ v : Fin n,
      ∃ (w : Fin n) (c : G.Walk w w) (k : ℕ),
        c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k + 2 ∧ v ∈ c.support

theorem target : statement := by
  intro n G inst hmin v
  classical
  have h4 : NoFourCycle G := by
    intro w c hc hlen
    apply hmin.1.2.2
    exact ⟨w, c, 2, hc, by decide, by simpa using hlen⟩
  let H := canonicalQuotient (G := G) v
  have hsmall : Fintype.card (Survivors G v) < n :=
    survivor_card_lt G v (hmin.1.2.1 v)
  have hpos : 0 < Fintype.card (Survivors G v) := survivor_card_pos (G := G) v
  have hHmin : ∀ y : Fin (Fintype.card (Survivors G v)), 3 ≤ H.degree y := by
    intro y
    let x := (Fintype.equivFin (Survivors G v)).symm y
    have hm := quotient_min_natCard_three v h4 hmin.1.2.1 x
    have hm0 : 3 ≤ (quotient G v).degree x := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      exact hm
    have hy : (Fintype.equivFin (Survivors G v)) x = y := by simp [x]
    rw [← hy]
    have heq : (canonicalQuotient (G := G) v).degree
          ((Fintype.equivFin (Survivors G v)) x) = (quotient G v).degree x := by
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr ((quotientIso (G := G) v).mapNeighborSet x).symm
    change 3 ≤ (canonicalQuotient (G := G) v).degree _
    omega
  have hpH : HasPow2Cycle H := by
    by_contra hno
    have hHcex : IsCex H := ⟨hpos, hHmin, hno⟩
    have hle := hmin.2 (Fintype.card (Survivors G v)) H hHcex
    exact (Nat.not_le_of_lt hsmall) hle
  obtain ⟨y, c, k, hc, hk, hlen⟩ := hpH
  obtain ⟨x, d, hd, hdlen⟩ := cycle_maps_from_canonical v c hc
  obtain ⟨w, q, hq, hqcases⟩ := quotient_cycle_lifts v d hd
  rcases hqcases with hsame | ⟨hlonger, hvq⟩
  · exact (hmin.1.2.2 ⟨w, q, k, hq, hk, by omega⟩).elim
  · exact ⟨w, q, k, hq, hk, by omega, hvq⟩

#print axioms target

end Submissions.ErdosGyarfasClosedNeighborhoodCycles.ClosedNeighborhoodContraction

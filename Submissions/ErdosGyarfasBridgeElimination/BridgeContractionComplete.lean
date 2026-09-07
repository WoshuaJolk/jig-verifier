import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
Kernel-checked infrastructure for the bridge-contraction proof in
`BridgeEliminationStatement.lean`.
-/

namespace Erdos64.BridgeContraction

open scoped Sym2

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Endpoints of a bridge have no common neighbour. -/
theorem no_common_neighbor (hbridge : G.IsBridge s(u, v)) :
    ¬ ∃ z, G.Adj u z ∧ G.Adj v z := by
  rintro ⟨z, huz, hvz⟩
  have huv : u ≠ v := by
    intro h
    subst v
    simp [SimpleGraph.isBridge_iff] at hbridge
  rw [SimpleGraph.isBridge_iff] at hbridge
  apply hbridge
  let p : G.Walk u v := .cons huz (.cons hvz.symm .nil)
  refine ⟨p.toDeleteEdge s(u, v) ?_⟩
  simp [p, huv, huz.ne, hvz.ne]

section Contract

variable [DecidableEq V] (hne : u ≠ v)

/-- Collapse `v` onto `u`, with codomain literally the vertices other than
`v`. -/
def contractMap (x : V) : {y : V // y ≠ v} :=
  if h : x = v then ⟨u, hne⟩ else ⟨x, h⟩

@[simp] theorem contractMap_v : contractMap hne v = ⟨u, hne⟩ := by
  simp [contractMap]

@[simp] theorem contractMap_of_ne {x : V} (hx : x ≠ v) :
    contractMap hne x = ⟨x, hx⟩ := by
  simp [contractMap, hx]

@[simp] theorem contractMap_u : contractMap hne u = ⟨u, hne⟩ :=
  contractMap_of_ne hne hne

theorem contractMap_surjective : Function.Surjective (contractMap hne) := by
  rintro ⟨x, hx⟩
  exact ⟨x, contractMap_of_ne hne hx⟩

theorem contractMap_eq_iff {x y : V} :
    contractMap hne x = contractMap hne y ↔
      x = y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  by_cases hx : x = v <;> by_cases hy : y = v
  · simp [hx, hy]
  · subst x
    simp [contractMap, hy, Ne.symm hy, hne, Ne.symm hne, eq_comm]
  · subst y
    simp [contractMap, hx, Ne.symm hx, hne, Ne.symm hne, eq_comm]
  · simp [contractMap, hx, hy, Ne.symm hx, Ne.symm hy, eq_comm]

theorem eq_of_contractMap_eq_away {a : V} {x : {z : V // z ≠ v}}
    (hx : x.1 ≠ u) (ha : contractMap hne a = x) : a = x.1 := by
  have hfx : contractMap hne x.1 = x := contractMap_of_ne hne x.2
  have h : contractMap hne a = contractMap hne x.1 := ha.trans hfx.symm
  rw [contractMap_eq_iff hne] at h
  rcases h with h | h | h
  · exact h
  · exact False.elim (x.2 h.2)
  · exact False.elim (hx h.2)

/-- The simple graph obtained by contracting `uv`; `SimpleGraph.map`
automatically discards the collapsed loop. -/
def contraction : SimpleGraph {y : V // y ≠ v} :=
  G.map (contractMap hne)

theorem contraction_adj_iff (x y : {z : V // z ≠ v}) :
    (contraction (G := G) hne).Adj x y ↔
      x ≠ y ∧ ∃ a b : V,
        G.Adj a b ∧ contractMap hne a = x ∧ contractMap hne b = y :=
  SimpleGraph.map_adj' _ _ _ _

/-- Off the merged vertex, contraction changes no adjacency. -/
theorem contraction_adj_iff_away
    (x y : {z : V // z ≠ v}) (hx : x.1 ≠ u) (hy : y.1 ≠ u) :
    (contraction (G := G) hne).Adj x y ↔ G.Adj x.1 y.1 := by
  constructor
  · rw [contraction_adj_iff]
    rintro ⟨_, a, b, hab, ha, hb⟩
    simpa only [eq_of_contractMap_eq_away hne hx ha,
      eq_of_contractMap_eq_away hne hy hb] using hab
  · intro hxy
    rw [contraction_adj_iff]
    refine ⟨(fun h => hxy.ne (congrArg Subtype.val h)), x.1, y.1, hxy, ?_, ?_⟩
    · exact contractMap_of_ne hne x.2
    · exact contractMap_of_ne hne y.2

def awaySet : Set {z : V // z ≠ v} := {x | x.1 ≠ u}

/-- Away from the merged vertex, the contracted graph embeds back into the
original graph by forgetting subtype wrappers. -/
def awayEmbedding :
    ((contraction (G := G) hne).induce (awaySet (u := u) (v := v))) ↪g G where
  toFun x := x.1.1
  inj' _ _ h := Subtype.ext (Subtype.ext h)
  map_rel_iff' := by
    intro x y
    exact (contraction_adj_iff_away hne x.1 y.1 x.2 y.2).symm

theorem u_not_mem_awayMapped_support
    {x y : awaySet (u := u) (v := v)}
    (p : ((contraction (G := G) hne).induce
      (awaySet (u := u) (v := v))).Walk x y) :
    u ∉ (p.map (awayEmbedding (G := G) hne).toHom).support := by
  intro hu
  have hu' : u ∈ List.map (awayEmbedding (G := G) hne).toHom p.support := by
    simpa only [SimpleGraph.Walk.support_map] using hu
  obtain ⟨z, hz, hz'⟩ := List.mem_map.mp hu'
  exact z.2 (by simpa [awayEmbedding] using hz')

theorem v_not_mem_awayMapped_support
    {x y : awaySet (u := u) (v := v)}
    (p : ((contraction (G := G) hne).induce
      (awaySet (u := u) (v := v))).Walk x y) :
    v ∉ (p.map (awayEmbedding (G := G) hne).toHom).support := by
  intro hv
  have hv' : v ∈ List.map (awayEmbedding (G := G) hne).toHom p.support := by
    simpa only [SimpleGraph.Walk.support_map] using hv
  obtain ⟨z, hz, hz'⟩ := List.mem_map.mp hv'
  exact z.1.2 (by simpa [awayEmbedding] using hz')

/-- A walk avoiding the merged vertex lifts unchanged to the original graph. -/
def liftAwayWalk {x y : {z : V // z ≠ v}}
    (p : (contraction (G := G) hne).Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ awaySet (u := u) (v := v)) :
    G.Walk x.1 y.1 :=
  (p.induce (awaySet (u := u) (v := v)) hp).map (awayEmbedding (G := G) hne).toHom

@[simp] theorem liftAwayWalk_length {x y : {z : V // z ≠ v}}
    (p : (contraction (G := G) hne).Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ awaySet (u := u) (v := v)) :
    (liftAwayWalk (G := G) hne p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      change (liftAwayWalk (G := G) hne p _).length + 1 = p.length + 1
      exact congrArg (· + 1) (ih _)

theorem liftAwayWalk_isPath {x y : {z : V // z ≠ v}}
    (p : (contraction (G := G) hne).Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ awaySet (u := u) (v := v))
    (hpath : p.IsPath) : (liftAwayWalk (G := G) hne p hp).IsPath := by
  unfold liftAwayWalk
  have hi : (p.induce (awaySet (u := u) (v := v)) hp).IsPath := by
    rw [SimpleGraph.Walk.isPath_def] at hpath ⊢
    rw [SimpleGraph.Walk.support_induce]
    apply List.Nodup.of_map Subtype.val
    rw [List.attachWith_map_subtype_val]
    exact hpath
  exact hi.map (awayEmbedding (G := G) hne).injective

/-- Every contracted cycle avoiding the merged vertex lifts to an original
cycle of exactly the same length. -/
theorem cycle_lifts_of_merged_not_mem {x : {z : V // z ≠ v}}
    (c : (contraction (G := G) hne).Walk x x) (hc : c.IsCycle)
    (hm : (⟨u, hne⟩ : {z : V // z ≠ v}) ∉ c.support) :
    ∃ d : G.Walk x.1 x.1, d.IsCycle ∧ d.length = c.length := by
  have hp : ∀ z ∈ c.support, z ∈ awaySet (u := u) (v := v) := by
    intro z hz hzu
    apply hm
    have heq : z = (⟨u, hne⟩ : {z : V // z ≠ v}) := Subtype.ext hzu
    simpa only [heq] using hz
  let ci := c.induce (awaySet (u := u) (v := v)) hp
  have hci : ci.IsCycle := by
    have hmap :
        (ci.map (SimpleGraph.Embedding.induce
          (G := contraction (G := G) hne)
          (awaySet (u := u) (v := v))).toHom).IsCycle := by
      convert hc using 1 <;> simp [ci]
    exact SimpleGraph.Walk.IsCycle.of_map hmap
  let d := ci.map (awayEmbedding (G := G) hne).toHom
  refine ⟨d, hci.map (awayEmbedding (G := G) hne).injective, ?_⟩
  exact liftAwayWalk_length (G := G) hne c hp

/-- Every edge at the merged vertex originated at one of the two contracted
endpoints. -/
theorem endpoint_adj_of_contraction_merged_adj {x : {z : V // z ≠ v}}
    (h : (contraction (G := G) hne).Adj ⟨u, hne⟩ x) :
    G.Adj u x.1 ∨ G.Adj v x.1 := by
  rw [contraction_adj_iff] at h
  rcases h with ⟨hmx, a, b, hab, ha, hb⟩
  have hx : x.1 ≠ u := by
    intro hx
    apply hmx
    exact Subtype.ext hx.symm
  have hb' : b = x.1 := eq_of_contractMap_eq_away hne hx hb
  subst b
  have hfa : contractMap hne a = contractMap hne u := by
    simpa only [contractMap_u hne] using ha
  rw [contractMap_eq_iff hne] at hfa
  rcases hfa with hfa | hfa | hfa
  · exact Or.inl (hfa ▸ hab)
  · exact Or.inl (hfa.1 ▸ hab)
  · exact Or.inr (hfa.1 ▸ hab)

theorem endpoint_adj_exclusive (hbridge : G.IsBridge s(u, v))
    {x : {z : V // z ≠ v}}
    (h : (contraction (G := G) hne).Adj ⟨u, hne⟩ x) :
    (G.Adj u x.1 ∨ G.Adj v x.1) ∧ ¬(G.Adj u x.1 ∧ G.Adj v x.1) := by
  exact ⟨endpoint_adj_of_contraction_merged_adj hne h,
    fun hx => no_common_neighbor hbridge ⟨x.1, hx⟩⟩

/-- A path through vertices away from the merger cannot enter the merged
vertex on the `u` side and leave on the `v` side: that would give a
`u`--`v` walk avoiding the bridge. -/
theorem endpoint_origins_same (hbridge : G.IsBridge s(u, v))
    {x y : {z : V // z ≠ v}}
    (hx : x.1 ≠ u) (hy : y.1 ≠ u)
    (q : (contraction (G := G) hne).Walk x y)
    (hqaway : ∀ z ∈ q.support, z ∈ awaySet (u := u) (v := v))
    (hmx : (contraction (G := G) hne).Adj ⟨u, hne⟩ x)
    (hmy : (contraction (G := G) hne).Adj y ⟨u, hne⟩) :
    (G.Adj u x.1 ∧ G.Adj u y.1) ∨ (G.Adj v x.1 ∧ G.Adj v y.1) := by
  have ox := endpoint_adj_exclusive hne hbridge hmx
  have oy := endpoint_adj_exclusive hne hbridge hmy.symm
  let d := liftAwayWalk (G := G) hne q hqaway
  have hud : u ∉ d.support := by
    exact u_not_mem_awayMapped_support (G := G) hne
      (q.induce (awaySet (u := u) (v := v)) hqaway)
  have hvd : v ∉ d.support := by
    exact v_not_mem_awayMapped_support (G := G) hne
      (q.induce (awaySet (u := u) (v := v)) hqaway)
  rcases ox.1 with hux | hvx <;> rcases oy.1 with huy | hvy
  · exact Or.inl ⟨hux, huy⟩
  · exfalso
    let p : G.Walk u v := SimpleGraph.Walk.cons hux (d.concat hvy.symm)
    have he : s(u, v) ∈ p.edges :=
      (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hbridge) p
    simp [p, Sym2.eq_iff] at he
    rcases he with he | he | he
    · rcases he with he | he <;> aesop
    · exact hud (d.fst_mem_support_of_mem_edges he)
    · rcases he with he | he <;> aesop
  · exfalso
    let p : G.Walk v u := SimpleGraph.Walk.cons hvx (d.concat huy.symm)
    have he : s(v, u) ∈ p.edges :=
      (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp
        (by simpa only [Sym2.eq_swap] using hbridge)) p
    simp [p, Sym2.eq_iff] at he
    rcases he with he | he | he
    · rcases he with he | he <;> aesop
    · exact hvd (d.fst_mem_support_of_mem_edges he)
    · rcases he with he | he <;> aesop
  · exact Or.inr ⟨hvx, hvy⟩

/-- A contracted cycle based at the merged vertex lifts with unchanged length. -/
theorem cycle_lifts_of_based_at_merged (hbridge : G.IsBridge s(u, v))
    (c : (contraction (G := G) hne).Walk ⟨u, hne⟩ ⟨u, hne⟩)
    (hc : c.IsCycle) :
    ∃ z : V, ∃ d : G.Walk z z, d.IsCycle ∧ d.length = c.length := by
  cases c with
  | nil => exact (hc.not_nil (by simp)).elim
  | @cons _ x _ h p =>
    have hpnon : ¬p.Nil := SimpleGraph.Walk.not_nil_of_isCycle_cons hc
    have hpc := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc
    let q := p.dropLast
    let y := p.penultimate
    have hlast : (contraction (G := G) hne).Adj y ⟨u, hne⟩ := p.adj_penultimate hpnon
    have hx : x.1 ≠ u := by
      intro he
      exact h.ne (Subtype.ext he.symm)
    have hy : y.1 ≠ u := by
      intro he
      exact hlast.ne (Subtype.ext he)
    have hmnot : (⟨u, hne⟩ : {z : V // z ≠ v}) ∉ q.support := by
      have hn := hpc.1.support_nodup
      rw [← p.support_dropLast_concat hpnon] at hn
      have hd := (List.nodup_append.mp hn).2.2
      intro hm
      exact hd ⟨u, hne⟩ (by simpa [q] using hm) ⟨u, hne⟩ (by simp) rfl
    have hqaway : ∀ z ∈ q.support, z ∈ awaySet (u := u) (v := v) := by
      intro z hz hzu
      apply hmnot
      have heq : z = (⟨u, hne⟩ : {z : V // z ≠ v}) := Subtype.ext hzu
      simpa [heq] using hz
    have horig := endpoint_origins_same (G := G) hne hbridge hx hy q hqaway h hlast
    let d := liftAwayWalk (G := G) hne q hqaway
    have hdpath : d.IsPath := liftAwayWalk_isPath (G := G) hne q hqaway hpc.1.dropLast
    have hud : u ∉ d.support := by
      exact u_not_mem_awayMapped_support (G := G) hne
        (q.induce (awaySet (u := u) (v := v)) hqaway)
    have hvd : v ∉ d.support := by
      exact v_not_mem_awayMapped_support (G := G) hne
        (q.induce (awaySet (u := u) (v := v)) hqaway)
    rcases horig with ⟨hux, huy⟩ | ⟨hvx, hvy⟩
    · let r : G.Walk x.1 u := d.concat huy.symm
      have hrpath : r.IsPath := hdpath.concat hud huy.symm
      have hedge : s(u, x.1) ∉ r.edges := by
        intro he
        simp [r, Sym2.eq_iff] at he
        rcases he with he | he
        · exact hud (d.fst_mem_support_of_mem_edges he)
        · have hlastmem : s(y, (⟨u, hne⟩ : {z : V // z ≠ v})) ∈ p.edges := by
            exact p.mk_penultimate_end_mem_edges hpnon
          apply hpc.2
          rcases he with he | he
          · exact (hy he.1.symm).elim
          · have hxy : x = y := Subtype.ext he
            simpa only [hxy, Sym2.eq_swap] using hlastmem
      let e : G.Walk u u := SimpleGraph.Walk.cons hux r
      refine ⟨u, e, (SimpleGraph.Walk.cons_isCycle_iff r hux).mpr ⟨hrpath, hedge⟩, ?_⟩
      simp [e, r, d, liftAwayWalk_length]
      exact SimpleGraph.Walk.length_dropLast_add_one hpnon

    · let r : G.Walk x.1 v := d.concat hvy.symm
      have hrpath : r.IsPath := hdpath.concat hvd hvy.symm
      have hedge : s(v, x.1) ∉ r.edges := by
        intro he
        simp [r, Sym2.eq_iff] at he
        rcases he with he | he
        · exact hvd (d.fst_mem_support_of_mem_edges he)
        · have hlastmem : s(y, (⟨u, hne⟩ : {z : V // z ≠ v})) ∈ p.edges := by
            exact p.mk_penultimate_end_mem_edges hpnon
          apply hpc.2
          rcases he with he | he
          · exact (x.2 he.2).elim
          · have hxy : x = y := Subtype.ext he
            simpa only [hxy, Sym2.eq_swap] using hlastmem
      let e : G.Walk v v := SimpleGraph.Walk.cons hvx r
      refine ⟨v, e, (SimpleGraph.Walk.cons_isCycle_iff r hvx).mpr ⟨hrpath, hedge⟩, ?_⟩
      simp [e, r, d, liftAwayWalk_length]
      exact SimpleGraph.Walk.length_dropLast_add_one hpnon

/-- Every cycle of the bridge contraction lifts to an original cycle of the
same length, including cycles passing through the merged vertex. -/
theorem contraction_cycle_lifts (hbridge : G.IsBridge s(u, v))
    {x : {z : V // z ≠ v}}
    (c : (contraction (G := G) hne).Walk x x) (hc : c.IsCycle) :
    ∃ z : V, ∃ d : G.Walk z z, d.IsCycle ∧ d.length = c.length := by
  by_cases hm : (⟨u, hne⟩ : {z : V // z ≠ v}) ∈ c.support
  · obtain ⟨z, d, hd, hlen⟩ := cycle_lifts_of_based_at_merged
      (G := G) hne hbridge (c.rotate ⟨u, hne⟩ hm) (hc.rotate _)
    exact ⟨z, d, hd, by simpa using hlen⟩
  · obtain ⟨d, hd, hlen⟩ := cycle_lifts_of_merged_not_mem (G := G) hne c hc hm
    exact ⟨x.1, d, hd, hlen⟩

/-- Contracting one vertex of `Fin n` leaves exactly `n-1` vertices. -/
theorem card_contraction_vertices {n : ℕ} (v : Fin n) :
    Fintype.card {x : Fin n // x ≠ v} = n - 1 := by
  simp

/-- Away from the merged vertex, contraction does not lower degree.  The key
point is that identifying two distinct neighbours would make the original
vertex a common neighbour of the bridge endpoints. -/
theorem degree_le_contraction_of_ne [Fintype V] [DecidableRel G.Adj]
    (hbridge : G.IsBridge s(u, v)) (x : {z : V // z ≠ v})
    (hx : x.1 ≠ u) :
    G.degree x.1 ≤
      @SimpleGraph.degree _ (contraction (G := G) hne) x (Fintype.ofFinite _) := by
  classical
  let f := contractMap hne
  letI : Fintype ((contraction (G := G) hne).neighborSet x) := Fintype.ofFinite _
  have hfx : f x.1 = x := contractMap_of_ne hne x.2
  have hedge_ne : ∀ z : G.neighborSet x.1, f x.1 ≠ f z.1 := by
    intro z heq
    rw [contractMap_eq_iff hne] at heq
    rcases heq with h | h | h
    · exact z.2.ne h
    · exact hx h.1
    · exact x.2 h.1
  let phi : G.neighborSet x.1 → (contraction (G := G) hne).neighborSet x :=
    fun z => ⟨f z.1, by
      change (G.map f).Adj x (f z.1)
      simpa only [hfx] using SimpleGraph.map_adj_apply' z.2 (hedge_ne z)⟩
  have hphi : Function.Injective phi := by
    intro z₁ z₂ hz
    have hf : f z₁.1 = f z₂.1 := congrArg Subtype.val hz
    rw [contractMap_eq_iff hne] at hf
    rcases hf with hf | hf | hf
    · exact Subtype.ext hf
    · exfalso
      apply no_common_neighbor hbridge
      refine ⟨x.1, ?_, ?_⟩
      · simpa only [hf.1] using z₁.2.symm
      · simpa only [hf.2] using z₂.2.symm
    · exfalso
      apply no_common_neighbor hbridge
      refine ⟨x.1, ?_, ?_⟩
      · simpa only [hf.2] using z₂.2.symm
      · simpa only [hf.1] using z₁.2.symm
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective phi hphi

/-- At the merged vertex the neighbours from the two bridge endpoints remain
disjoint, except that the contracted endpoints themselves are discarded. -/
theorem merged_degree_lower_bound [Fintype V] [DecidableRel G.Adj]
    (huv : G.Adj u v) (hbridge : G.IsBridge s(u, v)) :
    G.degree u - 1 + (G.degree v - 1) ≤
      @SimpleGraph.degree _ (contraction (G := G) hne) ⟨u, hne⟩ (Fintype.ofFinite _) := by
  classical
  let f := contractMap hne
  let H := contraction (G := G) hne
  let U := {z : G.neighborSet u // z.1 ≠ v}
  let W := {z : G.neighborSet v // z.1 ≠ u}
  letI : Fintype (H.neighborSet ⟨u, hne⟩) := Fintype.ofFinite _
  have hu_edge_ne : ∀ z : U, f u ≠ f z.1.1 := by
    intro z heq
    rw [contractMap_eq_iff hne] at heq
    rcases heq with h | h | h
    · exact z.1.2.ne h
    · exact z.2 h.2
    · exact hne h.1
  have hv_edge_ne : ∀ z : W, f v ≠ f z.1.1 := by
    intro z heq
    rw [contractMap_eq_iff hne] at heq
    rcases heq with h | h | h
    · exact z.1.2.ne h
    · exact (Ne.symm hne) h.1
    · exact z.2 h.2
  let phi : U ⊕ W → H.neighborSet ⟨u, hne⟩
    | .inl z => ⟨f z.1.1, show H.Adj ⟨u, hne⟩ (f z.1.1) from by
        simpa only [H, contraction, f, contractMap_u hne] using
          SimpleGraph.map_adj_apply' z.1.2 (hu_edge_ne z)⟩
    | .inr z => ⟨f z.1.1, show H.Adj ⟨u, hne⟩ (f z.1.1) from by
        simpa only [H, contraction, f, contractMap_v hne] using
          SimpleGraph.map_adj_apply' z.1.2 (hv_edge_ne z)⟩
  have hphi : Function.Injective phi := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · apply congrArg Sum.inl
      apply Subtype.ext
      apply Subtype.ext
      have hf : f a.1.1 = f b.1.1 := congrArg Subtype.val hab
      rw [contractMap_eq_iff hne] at hf
      rcases hf with hf | hf | hf
      · exact hf
      · exact False.elim (b.2 hf.2)
      · exact False.elim (a.2 hf.1)
    · exfalso
      have hf : f a.1.1 = f b.1.1 := congrArg Subtype.val hab
      rw [contractMap_eq_iff hne] at hf
      rcases hf with hf | hf | hf
      · apply no_common_neighbor hbridge
        exact ⟨a.1.1, a.1.2, hf ▸ b.1.2⟩
      · exact a.1.2.ne hf.1.symm
      · exact a.2 hf.1
    · exfalso
      have hf : f a.1.1 = f b.1.1 := congrArg Subtype.val hab
      rw [contractMap_eq_iff hne] at hf
      rcases hf with hf | hf | hf
      · apply no_common_neighbor hbridge
        exact ⟨a.1.1, hf ▸ b.1.2, a.1.2⟩
      · exact a.2 hf.1
      · exact a.1.2.ne hf.1.symm
    · apply congrArg Sum.inr
      apply Subtype.ext
      apply Subtype.ext
      have hf : f a.1.1 = f b.1.1 := congrArg Subtype.val hab
      rw [contractMap_eq_iff hne] at hf
      rcases hf with hf | hf | hf
      · exact hf
      · exact False.elim (a.2 hf.1)
      · exact False.elim (b.2 hf.2)
  have hcard := Fintype.card_le_of_injective phi hphi
  have hU : Fintype.card U = G.degree u - 1 := by
    have hp : Fintype.card {z : G.neighborSet u // z.1 = v} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨⟨v, huv⟩, rfl⟩, ?_⟩
      intro z
      apply Subtype.ext
      exact Subtype.ext z.2
    rw [show Fintype.card U = Fintype.card {z : G.neighborSet u // ¬z.1 = v} by rfl]
    rw [Fintype.card_subtype_compl, hp, SimpleGraph.card_neighborSet_eq_degree]
  have hW : Fintype.card W = G.degree v - 1 := by
    have hp : Fintype.card {z : G.neighborSet v // z.1 = u} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨⟨u, huv.symm⟩, rfl⟩, ?_⟩
      intro z
      apply Subtype.ext
      exact Subtype.ext z.2
    rw [show Fintype.card W = Fintype.card {z : G.neighborSet v // ¬z.1 = u} by rfl]
    rw [Fintype.card_subtype_compl, hp, SimpleGraph.card_neighborSet_eq_degree]
  simpa only [Fintype.card_sum, hU, hW, SimpleGraph.card_neighborSet_eq_degree] using hcard

/-- Edge contraction preserves the minimum-degree-three condition. -/
theorem contraction_min_degree_three [Fintype V] [DecidableRel G.Adj]
    (huv : G.Adj u v) (hbridge : G.IsBridge s(u, v))
    (hmin : ∀ x : V, 3 ≤ G.degree x) :
    ∀ x : {z : V // z ≠ v},
      3 ≤ @SimpleGraph.degree _ (contraction (G := G) hne) x (Fintype.ofFinite _) := by
  intro x
  by_cases hx : x.1 = u
  · have hx' : x = ⟨u, hne⟩ := Subtype.ext hx
    subst x
    have hm := merged_degree_lower_bound (G := G) hne huv hbridge
    have hu := hmin u
    have hv := hmin v
    omega
  · exact (hmin x.1).trans (degree_le_contraction_of_ne (G := G) hne hbridge x hx)

/-- Instance-independent form of the contraction minimum-degree bound. -/
theorem contraction_min_natCard_three [Fintype V] [DecidableRel G.Adj]
    (huv : G.Adj u v) (hbridge : G.IsBridge s(u, v))
    (hmin : ∀ x : V, 3 ≤ G.degree x) :
    ∀ x : {z : V // z ≠ v},
      3 ≤ Nat.card ((contraction (G := G) hne).neighborSet x) := by
  intro x
  have hm := contraction_min_degree_three (G := G) hne huv hbridge hmin x
  rw [← @SimpleGraph.card_neighborSet_eq_degree _ _ _ (Fintype.ofFinite _)] at hm
  rw [← @Nat.card_eq_fintype_card _ (Fintype.ofFinite _)] at hm
  exact hm

section Relabel

variable [Fintype V]

/-- Canonical finite relabeling of the contracted graph. -/
noncomputable def canonicalContraction :
    SimpleGraph (Fin (Fintype.card {z : V // z ≠ v})) :=
  (contraction (G := G) hne).map (Fintype.equivFin {z : V // z ≠ v})

noncomputable def contractionIso :
    contraction (G := G) hne ≃g canonicalContraction (G := G) hne :=
  SimpleGraph.Iso.map (Fintype.equivFin {z : V // z ≠ v}) _

/-- Relabeling preserves every vertex degree. -/
theorem canonicalContraction_degree (x : {z : V // z ≠ v}) :
    @SimpleGraph.degree _ (canonicalContraction (G := G) hne)
        ((Fintype.equivFin {z : V // z ≠ v}) x) (Fintype.ofFinite _) =
      @SimpleGraph.degree _ (contraction (G := G) hne) x (Fintype.ofFinite _) := by
  classical
  letI : Fintype ((canonicalContraction (G := G) hne).neighborSet
      ((Fintype.equivFin {z : V // z ≠ v}) x)) := Fintype.ofFinite _
  letI : Fintype ((contraction (G := G) hne).neighborSet x) := Fintype.ofFinite _
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr ((contractionIso (G := G) hne).mapNeighborSet x).symm

/-- A cycle maps through the canonical relabeling with unchanged length. -/
theorem cycle_maps_to_canonical {x : {z : V // z ≠ v}}
    (c : (contraction (G := G) hne).Walk x x) (hc : c.IsCycle) :
    ∃ d : (canonicalContraction (G := G) hne).Walk
        ((Fintype.equivFin {z : V // z ≠ v}) x)
        ((Fintype.equivFin {z : V // z ≠ v}) x),
      d.IsCycle ∧ d.length = c.length := by
  let d := c.map (contractionIso (G := G) hne).toHom
  exact ⟨d, hc.map (contractionIso (G := G) hne).injective,
    SimpleGraph.Walk.length_map _ c⟩

/-- A canonical cycle pulls back to the raw contraction unchanged. -/
theorem cycle_maps_from_canonical
    {x : Fin (Fintype.card {z : V // z ≠ v})}
    (c : (canonicalContraction (G := G) hne).Walk x x) (hc : c.IsCycle) :
    ∃ y : {z : V // z ≠ v}, ∃ d : (contraction (G := G) hne).Walk y y,
      d.IsCycle ∧ d.length = c.length := by
  let d := c.map (contractionIso (G := G) hne).symm.toHom
  exact ⟨(contractionIso (G := G) hne).symm x, d,
    hc.map (contractionIso (G := G) hne).symm.injective,
    SimpleGraph.Walk.length_map _ c⟩

end Relabel

end Contract

end Erdos64.BridgeContraction

/-! Standalone Jig submission for canonical statement 17. -/
namespace Submissions.ErdosGyarfasBridgeElimination.BridgeContractionComplete

open Erdos64.BridgeContraction

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ),
    c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsOrderMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    IsCex H → n ≤ m

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsOrderMinCex G → ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

theorem target : statement := by
  intro n G inst hmin e he hbridge
  classical
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := G.mem_edgeSet.mp he
    have hne : u ≠ v := huv.ne
    let H := canonicalContraction (G := G) hne
    have hcard : Fintype.card {z : Fin n // z ≠ v} = n - 1 := card_contraction_vertices v
    have hn4 : 4 ≤ n := by
      let x : Fin n := ⟨0, hmin.1.1⟩
      have hd := hmin.1.2.1 x
      have hlt := G.degree_lt_card_verts x
      have hlt' : G.degree x < n := by simpa using hlt
      omega
    have hH : IsCex H := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [H, hcard] using (show 0 < n - 1 from by omega)
      · intro y
        let x := (Fintype.equivFin {z : Fin n // z ≠ v}).symm y
        have hm := contraction_min_natCard_three (G := G) hne huv hbridge hmin.1.2.1 x
        have hm0 : 3 ≤ (contraction (G := G) hne).degree x := by
          rw [← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card]
          exact hm
        have hy : (Fintype.equivFin {z : Fin n // z ≠ v}) x = y := by simp [x]
        rw [← hy]
        have heq : (canonicalContraction (G := G) hne).degree
              ((Fintype.equivFin {z : Fin n // z ≠ v}) x) =
            (contraction (G := G) hne).degree x := by
          rw [← SimpleGraph.card_neighborSet_eq_degree,
            ← SimpleGraph.card_neighborSet_eq_degree]
          exact Fintype.card_congr ((contractionIso (G := G) hne).mapNeighborSet x).symm
        change 3 ≤ (canonicalContraction (G := G) hne).degree _
        omega
      · intro hp
        rcases hp with ⟨y, c, k, hc, hk, hlen⟩
        obtain ⟨x, d, hd, hdc⟩ := cycle_maps_from_canonical (G := G) hne c hc
        obtain ⟨z, q, hq, hqlen⟩ := contraction_cycle_lifts (G := G) hne hbridge d hd
        apply hmin.1.2.2
        exact ⟨z, q, k, hq, hk, by omega⟩
    have hle := hmin.2 (Fintype.card {z : Fin n // z ≠ v}) H hH
    rw [hcard] at hle
    omega

#print axioms target

end Submissions.ErdosGyarfasBridgeElimination.BridgeContractionComplete

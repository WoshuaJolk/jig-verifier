import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Submissions.J4P399PairSuppression.Proof

/-! Exact two-edge cycle lifting. The graph construction and binary linear
algebra used to supply this model are separate paper obligations. -/
namespace PairSuppressionLift
open SimpleGraph
variable {U V : Type*} {K : SimpleGraph U} {G : SimpleGraph V}

structure Model (K : SimpleGraph U) (G : SimpleGraph V) where
  vertex : U → V
  injective : Function.Injective vertex
  middle : K.Dart → V
  first : ∀ d, G.Adj (vertex d.fst) (middle d)
  second : ∀ d, G.Adj (middle d) (vertex d.snd)
  fresh : ∀ d u, middle d ≠ vertex u
  unique : ∀ d e, middle d = middle e → d.edge = e.edge

def Within (M : Model K G) {u v : U} (p : K.Walk u v)
    (q : G.Walk (M.vertex u) (M.vertex v)) : Prop :=
  ∀ z ∈ q.support, (∃ w ∈ p.support, M.vertex w = z) ∨
    ∃ d ∈ p.darts, M.middle d = z

theorem lift_path (M : Model K G) {u v : U} (p : K.Walk u v) (hp : p.IsPath) :
    ∃ q : G.Walk (M.vertex u) (M.vertex v),
      q.IsPath ∧ q.length = 2*p.length ∧ Within M p q := by
  induction p with
  | nil =>
    refine ⟨.nil, .nil, rfl, ?_⟩
    intro z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact Or.inl ⟨_, by simp, rfl⟩
  | @cons u x v h p ih =>
    let d : K.Dart := ⟨(u,x),h⟩
    have hd : d ∈ (Walk.cons h p).darts := by simp [d]
    have hu : u ∉ p.support := ((Walk.cons_isPath_iff h p).mp hp).2
    obtain ⟨q,hq,hlen,hw⟩ := ih hp.of_cons
    have hfu : M.vertex u ∉ q.support := by
      intro hm
      rcases hw _ hm with ⟨w,hw,he⟩ | ⟨e,he,heq⟩
      · exact hu (M.injective he ▸ hw)
      · exact M.fresh e u heq
    have hmd : M.middle d ∉ q.support := by
      intro hm
      rcases hw _ hm with ⟨w,hw,he⟩ | ⟨e,he,heq⟩
      · exact M.fresh d w he.symm
      · have hed := M.unique e d heq
        have hem : d.edge ∈ p.edges := by
          rw [← hed]
          exact List.mem_map.mpr ⟨e,he,rfl⟩
        exact hu (p.fst_mem_support_of_mem_edges hem)
    refine ⟨Walk.cons (M.first d) (Walk.cons (M.second d) q), ?_, ?_, ?_⟩
    · apply (hq.cons hmd).cons
      simpa only [Walk.support_cons, List.mem_cons, not_or] using
        And.intro (M.fresh d u).symm hfu
    · simp only [Walk.length_cons,hlen]
      omega
    · intro z hz
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact Or.inl ⟨u,by simp,rfl⟩
      · exact Or.inr ⟨d,hd,rfl⟩
      · rcases hw z hz with ⟨w,hw,he⟩ | ⟨e,he,heq⟩
        · exact Or.inl ⟨w,List.mem_cons_of_mem u hw,he⟩
        · exact Or.inr ⟨e,List.mem_cons_of_mem d he,heq⟩

theorem close_doubled_path (M : Model K G) {u v : U}
    (p : K.Walk v u) (hp : p.IsPath) (h : K.Adj u v)
    (he : s(u,v) ∉ p.edges) (hl : 1 < p.length) :
    ∃ c : G.Walk (M.vertex u) (M.vertex u),
      c.IsCycle ∧ c.length = 2*(p.length+1) := by
  let d : K.Dart := ⟨(u,v),h⟩
  obtain ⟨q,hq,hlen,hw⟩ := lift_path M p hp
  have hm : M.middle d ∉ q.support := by
    intro hh
    rcases hw _ hh with ⟨w,hw,heq⟩ | ⟨e,he',heq⟩
    · exact M.fresh d w heq.symm
    · have hed := M.unique e d heq
      apply he
      change d.edge ∈ p.edges
      rw [← hed]
      exact List.mem_map.mpr ⟨e,he',rfl⟩
  let tail := Walk.cons (M.second d) q
  have ht : tail.IsPath := hq.cons hm
  have htl : tail.length = 2*p.length+1 := by simp [tail,hlen]
  have hne : s(M.vertex u,M.middle d) ∉ tail.edges := by
    intro hem
    have hem' : s(M.middle d,M.vertex u) ∈ tail.edges := by
      simpa only [Sym2.eq_swap] using hem
    have h1 := ht.length_eq_one_of_mem_edges hem'
    omega
  refine ⟨Walk.cons (M.first d) tail,
    (Walk.cons_isCycle_iff tail (M.first d)).mpr ⟨ht,hne⟩, ?_⟩
  simp only [Walk.length_cons,htl]
  omega

theorem double_cycle (M : Model K G) {u : U} (c : K.Walk u u) (hc : c.IsCycle) :
    ∃ d : G.Walk (M.vertex u) (M.vertex u),
      d.IsCycle ∧ d.length = 2*c.length := by
  cases c with
  | nil => simp at hc
  | @cons _ v _ h p =>
    obtain ⟨hp,he⟩ := (Walk.cons_isCycle_iff p h).mp hc
    have hl := hc.three_le_length
    have hpl : 1 < p.length := by
      simp only [Walk.length_cons] at hl
      omega
    simpa only [Walk.length_cons] using close_doubled_path M p hp h he hpl

theorem zero_defect_smaller (s t n : Nat) (hs : 0 < s)
    (hdeg : 3*s = 2*t) (hcard : s+t ≤ n) : s < n := by omega

/-- A selected row has one or three supported neighbors. Pair all but one;
the two-copy cubic repair has fewer vertices than the original graph. -/
theorem one_defect_smaller (s t n h : Nat) (hs : 0 < s)
    (hh : h=1 ∨ h=3) (hhs : h ≤ s)
    (hdeg : 3*s = 2*t+h) (hcard : s+t+1 ≤ n) : 2*s < n := by
  rcases hh with rfl | rfl <;> omega

end PairSuppressionLift

open SimpleGraph

theorem proof :
  ∀ (U V : Type) (K : SimpleGraph U) (G : SimpleGraph V)
    (vertex : U → V) (middle : K.Dart → V),
    Function.Injective vertex →
    (∀ d, G.Adj (vertex d.fst) (middle d)) →
    (∀ d, G.Adj (middle d) (vertex d.snd)) →
    (∀ d u, middle d ≠ vertex u) →
    (∀ d e, middle d = middle e → d.edge = e.edge) →
    ∀ (u : U) (c : K.Walk u u), c.IsCycle →
      ∃ d : G.Walk (vertex u) (vertex u), d.IsCycle ∧ d.length = 2 * c.length := by
  intro U V K G vertex middle hi hf hs hfr hu u c hc
  exact PairSuppressionLift.double_cycle
    ⟨vertex, hi, middle, hf, hs, hfr, hu⟩ c hc

end Submissions.J4P399PairSuppression.Proof

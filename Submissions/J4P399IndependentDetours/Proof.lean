import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Submissions.J4P399IndependentDetours.Proof

/- Actual graph interpolation by independent triangle detours. The quotient
   base-cycle construction and component-count identities are separate. -/
namespace IndependentDetours
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def Compatible {u v : V} (p : G.Walk u v) (eligible : G.Dart → Bool)
    (tip : G.Dart → V) : Prop :=
  (∀ d ∈ p.darts, eligible d = true → G.Adj d.fst (tip d) ∧ G.Adj (tip d) d.snd) ∧
  (∀ d ∈ p.darts, eligible d = true → tip d ∉ p.support) ∧
  (∀ d ∈ p.darts, eligible d = true → ∀ e ∈ p.darts, eligible e = true →
    tip d = tip e → d = e)

def Within {u v x y : V} (p : G.Walk u v) (q : G.Walk x y)
    (eligible : G.Dart → Bool) (tip : G.Dart → V) : Prop :=
  ∀ z ∈ q.support, z ∈ p.support ∨ ∃ d ∈ p.darts, eligible d = true ∧ tip d = z

theorem stretch_path {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (eligible : G.Dart → Bool) (tip : G.Dart → V) (h : Compatible p eligible tip)
    (k : Nat) (hk : k ≤ (p.darts.filter eligible).length) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length = p.length + k ∧ Within p q eligible tip := by
  induction p generalizing k with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact ⟨.nil, .nil, rfl, fun _ hz => Or.inl hz⟩
  | @cons u x v huv p ih =>
    let d : G.Dart := ⟨(u,x), huv⟩
    have hd : d ∈ (Walk.cons huv p).darts := by simp [d]
    have emb : ∀ e ∈ p.darts, e ∈ (Walk.cons huv p).darts :=
      fun e he => List.mem_cons_of_mem d he
    have htail : Compatible p eligible tip := by
      refine ⟨fun e he hel => h.1 e (emb e he) hel, ?_, ?_⟩
      · intro e he hel hmem
        exact h.2.1 e (emb e he) hel (List.mem_cons_of_mem u hmem)
      · intro e he hel f hf hfl heq
        exact h.2.2 e (emb e he) hel f (emb f hf) hfl heq
    have hu : u ∉ p.support := (Walk.cons_isPath_iff huv p).mp hp |>.2
    have hp' : p.IsPath := hp.of_cons
    have fresh_u : ∀ q : G.Walk x v, Within p q eligible tip → u ∉ q.support := by
      intro q hq hmem
      rcases hq u hmem with hbase | ⟨e, he, hel, htip⟩
      · exact hu hbase
      · exact h.2.1 e (emb e he) hel (by simp [htip])
    by_cases hk0 : k = 0
    · subst k
      exact ⟨.cons huv p, hp, by simp, fun _ hz => Or.inl hz⟩
    by_cases hel : eligible d = true
    · have hkt : k-1 ≤ (p.darts.filter eligible).length := by
        have hk' : k ≤ ((d :: p.darts).filter eligible).length := hk
        have hcount : ((d :: p.darts).filter eligible).length =
            (p.darts.filter eligible).length + 1 := by simp [hel]
        omega
      obtain ⟨q, hq, hlen, hwithin⟩ := ih hp' htail (k-1) hkt
      have hz : tip d ∉ q.support := by
        intro hmem
        rcases hwithin (tip d) hmem with hbase | ⟨e, he, heL, htip⟩
        · exact h.2.1 d hd hel (List.mem_cons_of_mem u hbase)
        · have hed : e = d := h.2.2 e (emb e he) heL d hd hel htip
          have hnodup := Walk.darts_nodup_of_support_nodup hp.support_nodup
          have hnot : d ∉ p.darts := (List.nodup_cons.mp hnodup).1
          exact hnot (hed ▸ he)
      have hadj := h.1 d hd hel
      have hqu : u ∉ q.support := fresh_u q hwithin
      have hzu : u ≠ tip d := by
        intro heq
        exact h.2.1 d hd hel (by simp [← heq])
      refine ⟨Walk.cons hadj.1 (Walk.cons hadj.2 q),
        (hq.cons hz).cons (by simpa [Walk.support_cons] using And.intro hzu hqu), ?_, ?_⟩
      · simp only [Walk.length_cons, hlen]
        omega
      · intro z hzq
        simp only [Walk.support_cons, List.mem_cons] at hzq
        rcases hzq with rfl | rfl | hzq
        · exact Or.inl (by simp)
        · exact Or.inr ⟨d, hd, hel, rfl⟩
        · rcases hwithin z hzq with hb | ⟨e, he, heL, het⟩
          · exact Or.inl (List.mem_cons_of_mem u hb)
          · exact Or.inr ⟨e, emb e he, heL, het⟩
    · have hkt : k ≤ (p.darts.filter eligible).length := by
        have hk' : k ≤ ((d :: p.darts).filter eligible).length := hk
        simpa [hel] using hk'
      obtain ⟨q, hq, hlen, hwithin⟩ := ih hp' htail k hkt
      refine ⟨Walk.cons huv q, hq.cons (fresh_u q hwithin), by simp only [Walk.length_cons, hlen]; omega, ?_⟩
      intro z hzq
      simp only [Walk.support_cons, List.mem_cons] at hzq
      rcases hzq with rfl | hzq
      · exact Or.inl (by simp)
      · rcases hwithin z hzq with hb | ⟨e, he, heL, het⟩
        · exact Or.inl (List.mem_cons_of_mem u hb)
        · exact Or.inr ⟨e, emb e he, heL, het⟩

theorem cycle_interval {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hclose : G.Adj v u) (hplen : 1 < p.length)
    (eligible : G.Dart → Bool) (tip : G.Dart → V) (h : Compatible p eligible tip)
    (k : Nat) (hk : k ≤ (p.darts.filter eligible).length) :
    ∃ c : G.Walk v v, c.IsCycle ∧ c.length = p.length + 1 + k ∧
      Within p c eligible tip := by
  obtain ⟨q, hq, hlen, hwithin⟩ := stretch_path p hp eligible tip h k hk
  have hnot : s(v,u) ∉ q.edges := by
    intro he
    have he' : s(u,v) ∈ q.edges := by simpa only [Sym2.eq_swap] using he
    have := hq.length_eq_one_of_mem_edges he'
    omega
  refine ⟨Walk.cons hclose q, (Walk.cons_isCycle_iff q hclose).mpr ⟨hq, hnot⟩, ?_, ?_⟩
  · simp only [Walk.length_cons, hlen]
    omega
  · intro z hz
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inl p.end_mem_support
    · exact hwithin z hz

end IndependentDetours

open SimpleGraph IndependentDetours

theorem proof :
  ∀ (V : Type) (G : SimpleGraph V) (u v : V) (p : G.Walk u v),
    p.IsPath → G.Adj v u → 1 < p.length →
    ∀ (eligible : G.Dart → Bool) (tip : G.Dart → V),
    Compatible p eligible tip → ∀ k : Nat,
    k ≤ (p.darts.filter eligible).length →
    ∃ c : G.Walk v v, c.IsCycle ∧ c.length = p.length + 1 + k ∧
      Within p c eligible tip := by
  intro V G u v p hp hclose hplen eligible tip h k hk
  exact IndependentDetours.cycle_interval p hp hclose hplen eligible tip h k hk

end Submissions.J4P399IndependentDetours.Proof

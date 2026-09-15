import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Submissions.J5P399PowerPathNonHelly.Proof

/- A finite obstruction to replacing minimum degree three by average degree
three. The graph has degree-two vertices and is not a root counterexample.
The recursive decision procedure is related to actual simple paths below. -/
namespace AverageDegreeControl
open SimpleGraph

def pathCheck {V : Type*} [DecidableEq V] (ns : V → List V) (target : V) :
    Nat → V → List V → Bool
  | 0, v, allowed => decide (v = target ∧ v ∈ allowed)
  | n+1, v, allowed => decide (v ∈ allowed) &&
      (ns v).any (fun w => pathCheck ns target n w (allowed.filter (fun x => decide (x ≠ v))))

theorem pathCheck_complete {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (ns : V → List V)
    (hns : ∀ u v, G.Adj u v → v ∈ ns u) {u v : V}
    (p : G.Walk u v) : p.IsPath → ∀ allowed,
    (∀ x ∈ p.support, x ∈ allowed) →
    pathCheck ns v p.length u allowed = true := by
  induction p with
  | nil =>
    intro hp allowed hs
    simp only [Walk.length_nil, pathCheck, decide_eq_true_eq]
    exact ⟨True.intro, hs _ (by simp)⟩
  | @cons a b c hab q ih =>
    intro hp allowed hs
    have hn : a ∉ q.support ∧ q.support.Nodup := by
      simpa only [Walk.support_cons, List.nodup_cons] using hp.support_nodup
    have hq : q.IsPath := Walk.IsPath.mk' hn.2
    have ha : a ∈ allowed := hs a (by simp)
    have hf : ∀ x ∈ q.support,
        x ∈ allowed.filter (fun x => decide (x ≠ a)) := by
      intro x hx
      apply List.mem_filter.mpr
      refine ⟨hs x (by simp [Walk.support_cons, hx]), ?_⟩
      simp only [decide_eq_true_eq]
      intro he
      exact hn.1 (he ▸ hx)
    simp only [Walk.length_cons, pathCheck, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨ha, List.any_eq_true.mpr ⟨b, hns a b hab, ih hq _ hf⟩⟩

def neighbors (v : Fin 18) : List (Fin 18) :=
  match v.val with
  | 0 => [1,2,3,4,12]
  | 1 => [0,2,7,13,14]
  | 2 => [0,1,8,9,17]
  | 3 => [0,4,5]
  | 4 => [0,3,6]
  | 5 => [3,7]
  | 6 => [4,7]
  | 7 => [1,5,6]
  | 8 => [2,9,10]
  | 9 => [2,8,11]
  | 10 => [8,12]
  | 11 => [9,12]
  | 12 => [0,10,11]
  | 13 => [1,14,15]
  | 14 => [1,13,16]
  | 15 => [13,17]
  | 16 => [14,17]
  | _ => [2,15,16]

def graph : SimpleGraph (Fin 18) := SimpleGraph.fromRel (fun u v => v ∈ neighbors u)
instance : DecidableRel graph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∈ neighbors _ ∨ _ ∈ neighbors _)))

theorem adjacency : ∀ u v : Fin 18, graph.Adj u v ↔ v ∈ neighbors u := by decide
theorem edge_count : graph.edgeFinset.card = 27 := by decide
theorem average_three : 2 * graph.edgeFinset.card = 3 * Fintype.card (Fin 18) := by decide
theorem minimum_two : ∀ v : Fin 18, 2 ≤ graph.degree v := by decide
theorem degree_two_exists : graph.degree 5 = 2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem checked_four : ∀ u v : Fin 18, graph.Adj u v →
    pathCheck neighbors u 3 v (List.finRange 18) = false := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem checked_eight : ∀ u v : Fin 18, graph.Adj u v →
    pathCheck neighbors u 7 v (List.finRange 18) = false := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem checked_sixteen : ∀ u v : Fin 18, graph.Adj u v →
    pathCheck neighbors u 15 v (List.finRange 18) = false := by decide

theorem no_cycle_of_check (n : Nat)
    (hcheck : ∀ u v : Fin 18, graph.Adj u v →
      pathCheck neighbors u n v (List.finRange 18) = false)
    (u : Fin 18) (p : graph.Walk u u) (hp : p.IsCycle) : p.length ≠ n+1 := by
  intro he
  cases p with
  | nil => simp at he
  | cons hab q =>
    have hq : q.IsPath := (q.cons_isCycle_iff hab).mp hp |>.1
    have hlen : q.length = n := by simpa only [Walk.length_cons, Nat.add_right_cancel_iff] using he
    have hy := pathCheck_complete graph neighbors (fun a b h => (adjacency a b).mp h)
      q hq (List.finRange 18) (by simp)
    rw [hlen, hcheck _ _ hab] at hy
    cases hy

theorem no_power (u : Fin 18) (p : graph.Walk u u) (hp : p.IsCycle)
    (k : Nat) (hk : 2 ≤ k) : p.length ≠ 2^k := by
  intro he
  have ht : p.length-1 < 18 := by
    simpa [Walk.length_tail] using hp.isPath_tail.length_lt
  have hb : k < 5 := by
    by_contra hn
    have hpow : (2:Nat)^5 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    change 32 ≤ 2^k at hpow
    omega
  have cases_k : k=2 ∨ k=3 ∨ k=4 := by omega
  rcases cases_k with rfl | rfl | rfl
  · exact no_cycle_of_check 3 checked_four u p hp (by simpa using he)
  · exact no_cycle_of_check 7 checked_eight u p hp (by simpa using he)
  · exact no_cycle_of_check 15 checked_sixteen u p hp (by simpa using he)

theorem average_degree_strengthening_fails :
    2 * graph.edgeFinset.card = 3 * Fintype.card (Fin 18) ∧
    (∀ v : Fin 18, 2 ≤ graph.degree v) ∧
    (∀ u (p : graph.Walk u u), p.IsCycle → ∀ k : Nat, 2 ≤ k → p.length ≠ 2^k) :=
  ⟨average_three, minimum_two, no_power⟩

end AverageDegreeControl


/- A subdivision of K5 minus one edge. Minimum degree TWO, with cubic
terminals. Six actual terminal paths of length eight intersect internally
pairwise but have no common internal vertex. There is no power cycle.
This diagnoses a Helly shortcut; it is not a root counterexample. -/
namespace PowerPathHellyControl
open SimpleGraph
open AverageDegreeControl (pathCheck pathCheck_complete)

def neighbors (v : Fin 20) : List (Fin 20) :=
  match v.val with
  | 0 => [5,7,9]
  | 1 => [11,12,13]
  | 2 => [6,11,14,18]
  | 3 => [8,12,15,16]
  | 4 => [10,13,17,19]
  | 5 => [0,6]
  | 6 => [2,5]
  | 7 => [0,8]
  | 8 => [3,7]
  | 9 => [0,10]
  | 10 => [4,9]
  | 11 => [1,2]
  | 12 => [1,3]
  | 13 => [1,4]
  | 14 => [2,15]
  | 15 => [3,14]
  | 16 => [3,17]
  | 17 => [4,16]
  | 18 => [2,19]
  | _ => [4,18]

def graph : SimpleGraph (Fin 20) := SimpleGraph.fromRel (fun u v => v ∈ neighbors u)
instance : DecidableRel graph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∈ neighbors _ ∨ _ ∈ neighbors _)))

theorem adjacency : ∀ u v : Fin 20, graph.Adj u v ↔ v ∈ neighbors u := by decide
theorem degrees : (∀ v : Fin 20, 2 ≤ graph.degree v) ∧
    graph.degree 0 = 3 ∧ graph.degree 1 = 3 ∧ graph.degree 5 = 2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem checked_four : ∀ u v : Fin 20, graph.Adj u v →
    pathCheck neighbors u 3 v (List.finRange 20) = false := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem checked_eight : ∀ u v : Fin 20, graph.Adj u v →
    pathCheck neighbors u 7 v (List.finRange 20) = false := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem checked_sixteen : ∀ u v : Fin 20, graph.Adj u v →
    pathCheck neighbors u 15 v (List.finRange 20) = false := by decide

theorem no_cycle_of_check (n : Nat)
    (hcheck : ∀ u v : Fin 20, graph.Adj u v →
      pathCheck neighbors u n v (List.finRange 20) = false)
    (u : Fin 20) (p : graph.Walk u u) (hp : p.IsCycle) : p.length ≠ n+1 := by
  intro he
  cases p with
  | nil => simp at he
  | cons hab q =>
    have hq : q.IsPath := (q.cons_isCycle_iff hab).mp hp |>.1
    have hlen : q.length = n := by simpa only [Walk.length_cons, Nat.add_right_cancel_iff] using he
    have hy := pathCheck_complete graph neighbors (fun a b h => (adjacency a b).mp h)
      q hq (List.finRange 20) (by simp)
    rw [hlen, hcheck _ _ hab] at hy
    cases hy

theorem no_power (u : Fin 20) (p : graph.Walk u u) (hp : p.IsCycle)
    (k : Nat) (hk : 2 ≤ k) : p.length ≠ 2^k := by
  intro he
  have ht : p.length-1 < 20 := by
    simpa [Walk.length_tail] using hp.isPath_tail.length_lt
  have hb : k < 5 := by
    by_contra hn
    have hpow : (2:Nat)^5 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    change 32 ≤ 2^k at hpow
    omega
  have cases_k : k=2 ∨ k=3 ∨ k=4 := by omega
  rcases cases_k with rfl | rfl | rfl
  · exact no_cycle_of_check 3 checked_four u p hp (by simpa using he)
  · exact no_cycle_of_check 7 checked_eight u p hp (by simpa using he)
  · exact no_cycle_of_check 15 checked_sixteen u p hp (by simpa using he)

def witness (i : Fin 6) : List (Fin 20) :=
  match i.val with
  | 0 => [0,5,6,2,14,15,3,12,1]
  | 1 => [0,5,6,2,18,19,4,13,1]
  | 2 => [0,7,8,3,15,14,2,11,1]
  | 3 => [0,7,8,3,16,17,4,13,1]
  | 4 => [0,9,10,4,17,16,3,12,1]
  | _ => [0,9,10,4,19,18,2,11,1]

def Valid (i : Fin 6) : Prop :=
  let xs := witness i
  xs.head?=some 0 ∧ xs.getLast?=some 1 ∧ xs.Nodup ∧
  xs.IsChain graph.Adj ∧ xs.length=9
instance (i : Fin 6) : Decidable (Valid i) := by unfold Valid; infer_instance

theorem certificates : ∀ i : Fin 6, Valid i := by decide
theorem pairwise_intersections : ∀ i j : Fin 6, i≠j →
    ∃ x : Fin 20, x≠0 ∧ x≠1 ∧ x∈witness i ∧ x∈witness j := by decide
theorem no_common_internal : ¬ ∃ x : Fin 20, x≠0 ∧ x≠1 ∧
    ∀ i : Fin 6, x∈witness i := by decide

theorem realize (i : Fin 6) : ∃ p : graph.Walk 0 1,
    p.IsPath ∧ p.length=8 ∧ p.support=witness i := by
  rcases certificates i with ⟨hh,ht,hnd,hchain,hlen⟩
  let xs := witness i
  have hn : xs≠[] := by
    intro hz
    have hz' : witness i=[] := hz
    simp [hz'] at hh
  have hhead : xs.head hn=0 := (List.head_eq_iff_head?_eq_some _).mpr hh
  have hlast : xs.getLast hn=1 := (List.getLast_eq_iff_getLast?_eq_some _).mpr ht
  let p : graph.Walk 0 1 := (Walk.ofSupport xs hn hchain).copy hhead hlast
  refine ⟨p,?_,?_,?_⟩
  · apply Walk.IsPath.mk'; simpa [p,xs] using hnd
  · simp only [p,Walk.length_copy,Walk.length_ofSupport]
    change xs.length=9 at hlen
    omega
  · simp [p,xs]

theorem actual_non_helly_paths : ∃ ps : Fin 6 → graph.Walk 0 1,
    (∀ i, (ps i).IsPath ∧ (ps i).length=8) ∧
    (∀ i j, i≠j → ∃ x : Fin 20,
      x≠0 ∧ x≠1 ∧ x∈(ps i).support ∧ x∈(ps j).support) ∧
    (¬ ∃ x : Fin 20, x≠0 ∧ x≠1 ∧ ∀ i, x∈(ps i).support) := by
  classical
  let ps := fun i => (realize i).choose
  have hs (i) : (ps i).support=witness i := (realize i).choose_spec.2.2
  refine ⟨ps,fun i => ⟨(realize i).choose_spec.1,(realize i).choose_spec.2.1⟩,?_,?_⟩
  · intro i j hij
    simpa only [hs] using pairwise_intersections i j hij
  · simpa only [hs] using no_common_internal

/-- Literal countercontrol: cubic endpoints do not imply the proposed
Helly property. Minimum degree three throughout remains an open target. -/
theorem endpoint_degree_three_is_insufficient :
    graph.degree 0=3 ∧ graph.degree 1=3 ∧ graph.degree 5=2 ∧
    (∀ u (p : graph.Walk u u), p.IsCycle → ∀ k : Nat, 2≤k → p.length≠2^k) ∧
    (∃ ps : Fin 6 → graph.Walk 0 1,
      (∀ i, (ps i).IsPath ∧ (ps i).length=8) ∧
      (∀ i j, i≠j → ∃ x : Fin 20,
        x≠0 ∧ x≠1 ∧ x∈(ps i).support ∧ x∈(ps j).support) ∧
      (¬ ∃ x : Fin 20, x≠0 ∧ x≠1 ∧ ∀ i, x∈(ps i).support)) :=
  ⟨degrees.2.1,degrees.2.2.1,degrees.2.2.2,no_power,actual_non_helly_paths⟩

end PowerPathHellyControl

open PowerPathHellyControl

theorem solves :
  graph.degree 0=3 ∧ graph.degree 1=3 ∧ graph.degree 5=2 ∧
    (∀ u (p : graph.Walk u u), p.IsCycle → ∀ k : Nat, 2≤k → p.length≠2^k) ∧
    (∃ ps : Fin 6 → graph.Walk 0 1,
      (∀ i, (ps i).IsPath ∧ (ps i).length=8) ∧
      (∀ i j, i≠j → ∃ x : Fin 20,
        x≠0 ∧ x≠1 ∧ x∈(ps i).support ∧ x∈(ps j).support) ∧
      (¬ ∃ x : Fin 20, x≠0 ∧ x≠1 ∧ ∀ i, x∈(ps i).support)) :=
  endpoint_degree_three_is_insufficient

end Submissions.J5P399PowerPathNonHelly.Proof

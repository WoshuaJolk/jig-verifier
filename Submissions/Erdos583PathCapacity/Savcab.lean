import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Submissions.Erdos583PathCapacity.Savcab

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V, p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b → ∃! p : List V, p ∈ paths ∧ PathUses p a b

def edgeList {V : Type} : List V → List (Sym2 V)
  | [] => []
  | [_] => []
  | a :: b :: r => s(a,b) :: edgeList (b :: r)

theorem edgeList_length {V : Type} (p : List V) :
    (edgeList p).length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => rfl
    | cons b r => simpa [edgeList] using congrArg Nat.succ ih

theorem uses_mem_edgeList {V : Type} {p : List V} {a b : V}
    (h : PathUses p a b) : s(a,b) ∈ edgeList p := by
  obtain ⟨l, r, h | h⟩ := h
  · subst p
    induction l with
    | nil => simp [edgeList]
    | cons c l ih =>
      cases l with
      | nil => simp [edgeList]
      | cons d l => exact List.mem_cons_of_mem _ ih
  · subst p
    have hab : s(a,b) = s(b,a) := Sym2.eq_swap
    rw [hab]
    induction l with
    | nil => simp [edgeList]
    | cons c l ih =>
      cases l with
      | nil => simp [edgeList]
      | cons d l => exact List.mem_cons_of_mem _ ih

open scoped BigOperators

theorem capacity {n : ℕ} (G : SimpleGraph (Fin n))
    (paths : Finset (List (Fin n))) (h : IsPathDecomposition G paths) :
    Nat.card G.edgeSet ≤ paths.card * (n - 1) := by
  classical
  have cover : G.edgeFinset ⊆ paths.biUnion (fun p => (edgeList p).toFinset) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      obtain ⟨p, hp, _⟩ := h.2 hab
      exact Finset.mem_biUnion.mpr ⟨p, hp.1, List.mem_toFinset.mpr (uses_mem_edgeList hp.2)⟩
  calc
    Nat.card G.edgeSet = G.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, G.edgeFinset_card]
    _ ≤ (paths.biUnion (fun p => (edgeList p).toFinset)).card := Finset.card_le_card cover
    _ ≤ ∑ p ∈ paths, (edgeList p).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ paths, (n - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        (edgeList p).toFinset.card ≤ (edgeList p).length := List.toFinset_card_le _
        _ = p.length - 1 := edgeList_length p
        _ ≤ n - 1 := Nat.sub_le_sub_right (by simpa using (h.1 p hp).1.length_le_card) 1
    _ = paths.card * (n - 1) := by simp

theorem dense_odd_lower {k : ℕ} (G : SimpleGraph (Fin (2 * k + 1)))
    (paths : Finset (List (Fin (2 * k + 1))))
    (hdense : 2 * k * k < Nat.card G.edgeSet)
    (h : IsPathDecomposition G paths) : k + 1 ≤ paths.card := by
  have cap := capacity G paths h
  have he : 2 * k + 1 - 1 = 2 * k := by omega
  rw [he] at cap
  by_contra hn
  have hn' : paths.card ≤ k := by omega
  have hm := Nat.mul_le_mul_right (2 * k) hn'
  nlinarith

theorem odd_clique_lower {k : ℕ} (hk : 1 ≤ k)
    (paths : Finset (List (Fin (2 * k + 1))))
    (h : IsPathDecomposition (⊤ : SimpleGraph (Fin (2 * k + 1))) paths) :
    k + 1 ≤ paths.card := by
  have cap := capacity (⊤ : SimpleGraph (Fin (2 * k + 1))) paths h
  have edges : Nat.card (⊤ : SimpleGraph (Fin (2 * k + 1))).edgeSet = (2 * k + 1) * k := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.choose_two_right]
    have he : 2 * k + 1 - 1 = 2 * k := by omega
    rw [he, ← Nat.mul_assoc, Nat.mul_right_comm _ 2 k, Nat.mul_div_cancel _ (by decide)]
  rw [edges] at cap
  have he : 2 * k + 1 - 1 = 2 * k := by omega
  rw [he] at cap
  by_contra hn
  have hn' : paths.card ≤ k := by omega
  have hm := Nat.mul_le_mul_right (2 * k) hn'
  nlinarith

theorem proof :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (paths : Finset (List (Fin n))),
      IsPathDecomposition G paths → Nat.card G.edgeSet ≤ paths.card * (n - 1)) ∧
    (∀ (k : ℕ) (G : SimpleGraph (Fin (2 * k + 1)))
      (paths : Finset (List (Fin (2 * k + 1)))),
      2 * k * k < Nat.card G.edgeSet → IsPathDecomposition G paths → k + 1 ≤ paths.card) ∧
    (∀ (k : ℕ), 1 ≤ k → ∀ paths : Finset (List (Fin (2 * k + 1))),
      IsPathDecomposition (⊤ : SimpleGraph (Fin (2 * k + 1))) paths → k + 1 ≤ paths.card) := by
  exact ⟨fun _ G paths h => capacity G paths h,
    fun _ G paths hd h => dense_odd_lower G paths hd h,
    fun _ hk paths h => odd_clique_lower hk paths h⟩

end Submissions.Erdos583PathCapacity.Savcab

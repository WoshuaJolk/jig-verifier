import Mathlib

namespace Submissions.Erdos583PathGraphDecomposition.SchmitzAndrewProof

/-- Path-decomposition machinery, transcribed independently (this file imports
no `Statements.*` module). -/
def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V, p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b → ∃! p : List V, p ∈ paths ∧ PathUses p a b

theorem pathUses_symm {α : Type} {L : List α} {a b : α} (h : PathUses L a b) :
    PathUses L b a := by
  obtain ⟨l, r, h⟩ := h
  exact ⟨l, r, h.symm⟩

theorem finRange_getElem_eq {n : ℕ} (a : Fin n) (h : a.val < (List.finRange n).length) :
    (List.finRange n)[a.val]'h = a := by
  simp [List.getElem_finRange]

/-- Two provably-equal indices into the same list pick out the same element,
regardless of which (proof-irrelevant) bound witnesses membership. -/
theorem getElem_eq_of_index_eq {α : Type} (L : List α) {i j : ℕ} (h : i = j)
    (hi : i < L.length) (hj : j < L.length) : L[i]'hi = L[j]'hj := by
  subst h; rfl

/-- The `PathUses` witness at a Gallai-adjacent pair inside the standard
increasing enumeration of `Fin (n+1)`. Proved directly by a `take`/`drop`
split rather than by transporting a generic index lemma, so no rewrite ever
has to generalize across the (omega-derived) bound proofs. -/
theorem pathUses_of_adj {n : ℕ} {a b : Fin (n + 1)} (h : a.val + 1 = b.val) :
    PathUses (List.finRange (n + 1)) a b := by
  set L := List.finRange (n + 1) with hLdef
  have hlen1 : a.val < L.length := by simp [hLdef]; omega
  have hlen2 : a.val + 1 < L.length := by simp [hLdef]; omega
  have e1 : L[a.val]'hlen1 = a := finRange_getElem_eq a hlen1
  have e2 : L[a.val + 1]'hlen2 = b := by
    rw [getElem_eq_of_index_eq L h hlen2 (by simp [hLdef]; omega)]
    exact finRange_getElem_eq b (by simp only [List.length_finRange]; omega)
  have hd1 : L.drop a.val = L[a.val]'hlen1 :: L.drop (a.val + 1) :=
    List.drop_eq_getElem_cons hlen1
  have hd2 : L.drop (a.val + 1) = L[a.val + 1]'hlen2 :: L.drop (a.val + 2) :=
    List.drop_eq_getElem_cons hlen2
  refine ⟨L.take a.val, L.drop (a.val + 2), Or.inl ?_⟩
  calc
    L = L.take a.val ++ L.drop a.val := (List.take_append_drop _ _).symm
    _ = L.take a.val ++ (L[a.val]'hlen1 :: L.drop (a.val + 1)) := by rw [hd1]
    _ = L.take a.val ++ (a :: L.drop (a.val + 1)) := by rw [e1]
    _ = L.take a.val ++ (a :: L[a.val + 1]'hlen2 :: L.drop (a.val + 2)) := by rw [hd2]
    _ = L.take a.val ++ (a :: b :: L.drop (a.val + 2)) := by rw [e2]

theorem target (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).Connected →
    ∃ paths : Finset (List (Fin (n + 1))),
      paths.card ≤ ((n + 1) + 1) / 2 ∧
      IsPathDecomposition (SimpleGraph.pathGraph (n + 1)) paths := by
  intro _
  classical
  set L : List (Fin (n + 1)) := List.finRange (n + 1) with hLdef
  have hnodup : L.Nodup := List.nodup_finRange (n + 1)
  have hchain : L.IsChain (SimpleGraph.pathGraph (n + 1)).Adj := by
    have hofFn : L = List.ofFn (id : Fin (n + 1) → Fin (n + 1)) := by
      rw [hLdef, List.ofFn_id]
    rw [hofFn, List.isChain_ofFn]
    intro i hi
    simp [SimpleGraph.pathGraph_adj]
  refine ⟨{L}, ?_, ?_, ?_⟩
  · rw [Finset.card_singleton]
    omega
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨hnodup, hchain⟩
  · intro a b hab
    refine ⟨L, ⟨Finset.mem_singleton_self L, ?_⟩, ?_⟩
    · rcases SimpleGraph.pathGraph_adj.mp hab with h1 | h1
      · exact pathUses_of_adj h1
      · exact pathUses_symm (pathUses_of_adj h1)
    · rintro p ⟨hp, -⟩
      exact Finset.mem_singleton.mp hp

end Submissions.Erdos583PathGraphDecomposition.SchmitzAndrewProof

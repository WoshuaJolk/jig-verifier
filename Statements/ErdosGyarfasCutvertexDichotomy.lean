import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

/-!
Jig-ready canonical proposition for the cutvertex dichotomy in a
lexicographically minimum Erdős--Gyárfás counterexample.

Mathlib does not currently expose named cutvertex/2-connected predicates, so
this file defines them directly by connectivity after vertex deletion.
`cycle_space_attack.md` contains the graph-theoretic proof.
-/

namespace Statements.ErdosGyarfasCutvertexDichotomy

open scoped Sym2

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ),
    c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

def withoutVertex {V : Type} (G : SimpleGraph V) (v : V) :
    SimpleGraph {w : V // w ≠ v} :=
  G.induce {w | w ≠ v}

def IsCutVertex {V : Type} (G : SimpleGraph V) (v : V) : Prop :=
  G.Connected ∧ ¬(withoutVertex G v).Preconnected

def IsTwoConnected {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v : V, (withoutVertex G v).Preconnected

def restoreSet {V : Type} {v : V} (A : Set {w : V // w ≠ v}) : Set V :=
  {w | w = v ∨ ∃ h : w ≠ v, (⟨w, h⟩ : {z : V // z ≠ v}) ∈ A}

def restoredBlock {V : Type} (G : SimpleGraph V) {v : V}
    (A : Set {w : V // w ≠ v}) : SimpleGraph (restoreSet A) :=
  G.induce (restoreSet A)

/-- In the non-2-connected case, `A,B` are exactly the two components after
deleting `v`; this is encoded by their partition and the iff characterizing
reachability in the vertex-deleted graph. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    (∀ e ∈ G.edgeSet, ¬G.IsBridge e) →
    IsTwoConnected G ∨
      ∃ (v : Fin n) (A B : Set {w : Fin n // w ≠ v}),
        A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Set.univ ∧
        (∀ x y : {w : Fin n // w ≠ v},
          (withoutVertex G v).Reachable x y ↔
            (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)) ∧
        G.degree v = 4 ∧
        2 * Set.ncard A + 1 = n ∧ 2 * Set.ncard B + 1 = n ∧
        Set.ncard (restoredBlock G A).edgeSet =
          Set.ncard (restoredBlock G B).edgeSet ∧
        IsTwoConnected (restoredBlock G A) ∧
        IsTwoConnected (restoredBlock G B) ∧
        (∀ w : Fin n, IsCutVertex G w → w = v)

theorem target : statement := by
  sorry

end Statements.ErdosGyarfasCutvertexDichotomy

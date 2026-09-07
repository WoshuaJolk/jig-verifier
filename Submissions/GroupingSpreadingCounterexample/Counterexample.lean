import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
An exact eight-vertex counterexample to the universal one-factorization assertion
GroupingSpreadingCrossFirst. The following definitions and originalStatement are
copied unchanged from that canonical statement, except for its local name.
No claim is made against the existential grouping statement.
-/
namespace Submissions.GroupingSpreadingCounterexample.Counterexample

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The circulant on `ZMod m` with symmetric connection set `S`. -/
def circulant (m : ℕ) (S : Finset (ZMod m)) : SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w => (w - v) ∈ S

/-- Connection set of the connected `k`-regular seed. -/
def degSet (m k : ℕ) : Finset (ZMod m) :=
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (i : ZMod m)) ∪
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (-(i : ZMod m))) ∪
  (if k % 2 = 1 then {((m / 2 : ℕ) : ZMod m)} else ∅)

/-- A one-factor as an involution on `ZMod m` with no fixed points (perfect matching). -/
abbrev IsOneFactor {m : ℕ} (F : ZMod m → ZMod m) : Prop :=
  (∀ v, F (F v) = v) ∧ (∀ v, F v ≠ v)

/-- Class complement: the seed together with every factor not assigned to class `j`. -/
def classCompl {m n : ℕ} (k : ℕ) (F : Fin n → ZMod m → ZMod m) (g : Fin n → ℕ) (j : ℕ) :
    SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w =>
    (circulant m (degSet m k)).Adj v w ∨ ∃ t : Fin n, g t ≠ j ∧ F t v = w

/-- The canonical proposition.

For even `m`, `2 ≤ k`, `2 * k < m`, and class degrees `e j ≥ 1` summing to `m - 1 - k` with no
class taking every factor, every 1-factorization of the seed complement admits an assignment of its
factors to the classes — the cross-first spreading assignment — such that each class complement
stays connected after deleting fewer than `m - 1 - e j` vertices. -/
abbrev originalStatement : Prop :=
  ∀ m k q : ℕ, 2 ≤ k → 2 * k < m → m % 2 = 0 → ∀ e : Fin q → ℕ,
    (∀ j, 1 ≤ e j) →
    (∑ j, e j) + 1 + k = m →
    (∀ j, e j + 1 < m - k) →
    ∀ n : ℕ, n = m - 1 - k →
    ∀ F : Fin n → ZMod m → ZMod m,
      (∀ t, IsOneFactor (F t)) →
      (∀ t v, ¬ (circulant m (degSet m k)).Adj v (F t v)) →
      (∀ v w, v ≠ w → ¬ (circulant m (degSet m k)).Adj v w → ∃! t, F t v = w) →
      ∃ g : Fin n → ℕ,
        (∀ j : Fin q, (Finset.univ.filter fun t => g t = (j : ℕ)).card = e j) ∧
        (∀ j : Fin q, ∀ X : Finset (ZMod m),
          X.card + 1 + e j < m →
          ((classCompl k F g (j : ℕ)).induce {v : ZMod m | v ∉ X}).Connected)


/-- A genuine one-factorization of the complement of the degree-three seed on eight vertices. -/
def factors : Fin 4 → ZMod 8 → ZMod 8 :=
  ![![6, 3, 4, 1, 2, 7, 0, 5],
    ![2, 7, 0, 5, 6, 3, 4, 1],
    ![3, 6, 5, 0, 7, 2, 1, 4],
    ![5, 4, 7, 6, 1, 0, 3, 2]]

/-- Complements of the three four-cycle bicliques in factor pairs 01, 02, 12. -/
def cuts : Fin 3 → Finset (ZMod 8) :=
  ![{1, 3, 5, 7}, {2, 4, 5, 7}, {1, 4, 6, 7}]

theorem cuts_card : ∀ r, (cuts r).card = 4 := by decide

theorem factor_hypotheses :
    (∀ t, IsOneFactor (factors t)) ∧
    (∀ t v, ¬ (circulant 8 (degSet 8 3)).Adj v (factors t v)) ∧
    (∀ v w : ZMod 8, v ≠ w → ¬ (circulant 8 (degSet 8 3)).Adj v w →
      ∃! t, factors t v = w) := by
  unfold IsOneFactor circulant ExistsUnique
  decide

instance (g : Fin 4 → ℕ) (j : ℕ) : DecidableRel (classCompl 3 factors g j).Adj := by
  unfold classCompl circulant
  infer_instance

/-- One side of each exhibited biclique; zero is always on this side. -/
def firstSides : Fin 3 → Finset (ZMod 8) := ![{0, 4}, {0, 1}, {0, 5}]

def opposite : Fin 3 → ZMod 8 := ![2, 3, 2]

theorem sides_nonempty : ∀ r : Fin 3,
    (0 : ZMod 8) ∉ cuts r ∧ opposite r ∉ cuts r ∧
    (0 : ZMod 8) ∈ firstSides r ∧ opposite r ∉ firstSides r := by decide

/-- Every admissible finite label pattern has one of the three explicit separating cuts.
The certificate checks only finite adjacency, not an enumeration of walks. -/
theorem finite_certificate :
    ∀ g : Fin 4 → Fin 3,
      (∀ j : Fin 2, (Finset.univ.filter fun t => (g t).val = j.val).card = 2) →
      ∃ j : Fin 2, ∃ r : Fin 3, ∀ v w : ZMod 8,
        v ∉ cuts r → w ∉ cuts r →
        (classCompl 3 factors (fun t => (g t).val) j.val).Adj v w →
        (v ∈ firstSides r ↔ w ∈ firstSides r) := by decide

/-- Adjacency preserving a predicate forces every walk to preserve it. -/
theorem walk_preserves {V : Type*} {G : SimpleGraph V} (P : V → Prop)
    (hP : ∀ a b, G.Adj a b → (P a ↔ P b))
    {a b : V} (p : G.Walk a b) : P a ↔ P b := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (hP _ _ h).trans ih

/-- All natural-number labels outside 0 and 1 have the same effect on both class complements. -/
def compress (g : Fin 4 → ℕ) (t : Fin 4) : Fin 3 :=
  if g t = 0 then 0 else if g t = 1 then 1 else 2

theorem compress_eq (g : Fin 4 → ℕ) (t : Fin 4) (j : Fin 2) :
    (compress g t).val = j.val ↔ g t = j.val := by
  fin_cases j <;> by_cases h0 : g t = 0 <;> by_cases h1 : g t = 1 <;>
    simp_all [compress]

theorem compress_graph (g : Fin 4 → ℕ) (j : Fin 2) :
    classCompl 3 factors (fun t => (compress g t).val) j.val =
      classCompl 3 factors g j.val := by
  ext v w
  simp only [classCompl, SimpleGraph.fromRel_adj, ne_eq, compress_eq]

/-- The exact canonical universal statement is false. -/
theorem proof : ¬ originalStatement := by
  intro h
  obtain ⟨g, hg, hc⟩ := h 8 3 2 (by decide) (by decide) (by decide)
    (fun _ => 2) (by decide) (by decide) (by decide) 4 rfl factors
    factor_hypotheses.1 factor_hypotheses.2.1 factor_hypotheses.2.2
  have hg' : ∀ j : Fin 2,
      (Finset.univ.filter fun t => (compress g t).val = j.val).card = 2 := by
    intro j
    simpa only [compress_eq] using hg j
  obtain ⟨j, r, hr⟩ := finite_certificate (compress g) hg'
  rw [compress_graph] at hr
  have hconn := hc j (cuts r) (by rw [cuts_card]; decide)
  let a : {v : ZMod 8 | v ∉ cuts r} := ⟨0, (sides_nonempty r).1⟩
  let b : {v : ZMod 8 | v ∉ cuts r} := ⟨opposite r, (sides_nonempty r).2.1⟩
  obtain ⟨p⟩ := hconn a b
  have hinv := walk_preserves (fun v : {v : ZMod 8 | v ∉ cuts r} =>
    v.val ∈ firstSides r) (fun v w h => hr v.val w.val v.property w.property h) p
  exact (sides_nonempty r).2.2.2 (hinv.mp (sides_nonempty r).2.2.1)

end Submissions.GroupingSpreadingCounterexample.Counterexample

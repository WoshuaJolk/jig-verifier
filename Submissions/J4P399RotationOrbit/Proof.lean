import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Submissions.J4P399RotationOrbit.Proof

/-! A finite counterexample to an EVERY-fixed-endpoint-orbit selection rule.
The graph is cubic and has an actual C4. The certified orbit consists of
Hamilton paths, but every endpoint fan with one or two chords avoids dyadic lengths.
This is not a counterexample to the Erdos--Gyarfas conjecture. -/
namespace RotationOrbitCounterexample

open SimpleGraph

abbrev V := Fin 10

def edges : List (V × V) :=
  [(0,1),(0,4),(0,9),(1,2),(1,6),(2,3),(2,8),(3,4),
   (3,9),(4,5),(5,6),(5,7),(6,7),(7,8),(8,9)]

def G : SimpleGraph V := SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)

instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun u v => (u,v) ∈ edges)).Adj)

def states : List (List V) :=
  [[7,8,9,0,1,2,3,4,5,6],
   [4,3,2,1,0,9,8,7,5,6],
   [5,4,3,2,1,0,9,8,7,6],
   [1,2,3,4,0,9,8,7,5,6],
   [8,9,0,1,2,3,4,5,7,6],
   [5,7,8,9,0,4,3,2,1,6],
   [1,0,9,8,2,3,4,5,7,6],
   [0,9,8,7,5,4,3,2,1,6],
   [7,5,4,3,2,8,9,0,1,6],
   [2,3,4,5,7,8,9,0,1,6]]

def state (s : Fin 10) : List V := states.getD s.val []
def rotate (p : List V) (i : Fin 10) : List V :=
  (p.take i.val).reverse ++ p.drop i.val
def Legal (p : List V) (i : Fin 10) : Prop :=
  2 ≤ i.val ∧ G.Adj (p.getD 0 0) (p.getD i.val 0)

instance (p : List V) (i : Fin 10) : Decidable (Legal p i) :=
  inferInstanceAs (Decidable (2 ≤ i.val ∧ G.Adj (p.getD 0 0) (p.getD i.val 0)))

theorem cubic : ∀ v : V, G.degree v = 3 := by decide

theorem state_valid : ∀ s : Fin 10,
    (state s).Nodup ∧ (state s).length = 10 ∧
    (state s).IsChain G.Adj ∧ (state s).getLast? = some 6 := by decide

theorem state_closed : ∀ s i : Fin 10, Legal (state s) i →
    ∃ t : Fin 10, rotate (state s) i = state t := by decide

theorem state_one_avoids : ∀ s i : Fin 10, Legal (state s) i →
    i.val + 1 ≠ 4 ∧ i.val + 1 ≠ 8 := by decide

theorem state_two_avoids : ∀ s i j : Fin 10,
    Legal (state s) i → Legal (state s) j → i.val < j.val →
    j.val - i.val + 2 ≠ 4 ∧ j.val - i.val + 2 ≠ 8 := by decide

inductive Reach : List V → Prop
  | seed : Reach (state 0)
  | step {p : List V} (hp : Reach p) (i : Fin 10) (hi : Legal p i) :
      Reach (rotate p i)

theorem reachable_state {p : List V} (hp : Reach p) :
    ∃ s : Fin 10, p = state s := by
  induction hp with
  | seed => exact ⟨0, rfl⟩
  | @step p hp i hi ih =>
    rcases ih with ⟨s, rfl⟩
    exact state_closed s i hi

theorem reachable_valid {p : List V} (hp : Reach p) :
    p.Nodup ∧ p.length = 10 ∧ p.IsChain G.Adj ∧ p.getLast? = some 6 := by
  rcases reachable_state hp with ⟨s, rfl⟩
  exact state_valid s

theorem state_ne_nil (s : Fin 10) : state s ≠ [] := by
  have h := (state_valid s).2.1
  intro he
  simp [he] at h

def stateWalk (s : Fin 10) :=
  Walk.ofSupport (G := G) (state s) (state_ne_nil s) (state_valid s).2.2.1

theorem stateWalk_isPath (s : Fin 10) : (stateWalk s).IsPath := by
  rw [Walk.isPath_def]
  simpa only [stateWalk, Walk.support_ofSupport] using (state_valid s).1

theorem stateWalk_length (s : Fin 10) : (stateWalk s).length = 9 := by
  simp only [stateWalk, Walk.length_ofSupport, (state_valid s).2.1]

theorem stateWalk_longest (s : Fin 10) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) : p.length ≤ (stateWalk s).length := by
  have h : p.length < 10 := by simpa using hp.length_lt
  rw [stateWalk_length]
  omega

theorem no_small_power (n : ℕ) (hn : n ≤ 10) (h4 : n ≠ 4) (h8 : n ≠ 8) :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k := by
  rintro ⟨k, hk, rfl⟩
  by_cases hlarge : 4 ≤ k
  · have h16 : 16 ≤ 2 ^ k := Nat.pow_le_pow_right (n := 2) (i := 4) (by decide) hlarge
    omega
  · have : k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl <;> contradiction

theorem reachable_one_no_power {p : List V} (hp : Reach p)
    (i : Fin 10) (hi : Legal p i) :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ i.val + 1 = 2 ^ k := by
  rcases reachable_state hp with ⟨s, rfl⟩
  have h := state_one_avoids s i hi
  exact no_small_power (i.val + 1) (by omega) h.1 h.2

theorem reachable_two_no_power {p : List V} (hp : Reach p)
    (i j : Fin 10) (hi : Legal p i) (hj : Legal p j) (hij : i.val < j.val) :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ j.val - i.val + 2 = 2 ^ k := by
  rcases reachable_state hp with ⟨s, rfl⟩
  have h := state_two_avoids s i j hi hj hij
  have hi2 := hi.1
  exact no_small_power (j.val - i.val + 2) (by omega) h.1 h.2

def square : G.Walk (8 : V) 8 :=
  .cons (show G.Adj (8 : V) 2 by decide)
    (.cons (show G.Adj (2 : V) 3 by decide)
      (.cons (show G.Adj (3 : V) 9 by decide)
        (.cons (show G.Adj (9 : V) 8 by decide) .nil)))

theorem square_isCycle : square.IsCycle := by
  unfold square
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.isPath_def]
    decide
  · decide
theorem square_length : square.length = 4 := rfl


end RotationOrbitCounterexample

open RotationOrbitCounterexample

theorem proof :
  (∀ v : V, G.degree v = 3) ∧
  (∀ s : Fin 10, (state s).Nodup ∧ (state s).length = 10 ∧
    (state s).IsChain G.Adj ∧ (state s).getLast? = some 6) ∧
  (∀ s i : Fin 10, Legal (state s) i → ∃ t : Fin 10, rotate (state s) i = state t) ∧
  (∀ s i : Fin 10, Legal (state s) i →
    ¬ ∃ k : Nat, 2 ≤ k ∧ i.val + 1 = 2 ^ k) ∧
  (∀ s i j : Fin 10, Legal (state s) i → Legal (state s) j → i.val < j.val →
    ¬ ∃ k : Nat, 2 ≤ k ∧ j.val - i.val + 2 = 2 ^ k) ∧
  (∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4) := by
  refine ⟨cubic, state_valid, state_closed, ?_, ?_, ?_⟩
  · intro s i hi
    have h := state_one_avoids s i hi
    exact no_small_power (i.val + 1) (by omega) h.1 h.2
  · intro s i j hi hj hij
    have h := state_two_avoids s i j hi hj hij
    have hi2 := hi.1
    exact no_small_power (j.val - i.val + 2) (by omega) h.1 h.2
  · exact ⟨8, square, square_isCycle, square_length⟩

end Submissions.J4P399RotationOrbit.Proof

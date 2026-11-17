import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

namespace Submissions.Erdos1111TriangleFreeC2.WagonTriangleFree

def ProperColoring {V C : Type} (G : SimpleGraph V) (color : V → C) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → color v ≠ color w

def Colorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ color : V → Fin k, ProperColoring G color

def ChromaticAtLeast {V : Type} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ k : ℕ, k < d → ¬Colorable G k

def ChromaticAtLeastOn {V : Type} (G : SimpleGraph V)
    (A : Finset V) (c : ℕ) : Prop :=
  ChromaticAtLeast (G.induce (A : Set V)) c

def Anticomplete {V : Type} (G : SimpleGraph V)
    (A B : Finset V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b

/-- The two endpoints of an edge induce a graph that is not `k`-colourable for `k < 2`. -/
theorem edge_chromaticAtLeastOn_two {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {a b : V} (hab : G.Adj a b) : ChromaticAtLeastOn G ({a, b} : Finset V) 2 := by
  intro k hk
  rintro ⟨color, hcol⟩
  have ha : a ∈ (({a, b} : Finset V) : Set V) := by simp
  have hb : b ∈ (({a, b} : Finset V) : Set V) := by simp
  have hadj : (G.induce (({a, b} : Finset V) : Set V)).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
    simpa using hab
  have hne := hcol hadj
  apply hne
  have h1 : (color ⟨a, ha⟩ : ℕ) < k := (color ⟨a, ha⟩).isLt
  have h2 : (color ⟨b, hb⟩ : ℕ) < k := (color ⟨b, hb⟩).isLt
  apply Fin.ext
  omega

/-- Wagon's argument at clique number two: a triangle-free graph that is not 3-colourable
contains an induced `2K₂`. The threshold is `d = 4`. -/
theorem proof :
    ∃ d : ℕ, 1 ≤ d ∧
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
        ChromaticAtLeast G d →
        G.CliqueFree 3 →
        ∃ A B : Finset (Fin n),
          Anticomplete G A B ∧
          ChromaticAtLeastOn G A 2 ∧
          ChromaticAtLeastOn G B 2 := by
  classical
  refine ⟨4, by norm_num, ?_⟩
  intro n G hchi hfree
  have h3 : ¬Colorable G 3 := hchi 3 (by norm_num)
  -- there is an edge, otherwise a constant colouring is proper
  have hedge : ∃ a b : Fin n, G.Adj a b := by
    by_contra h
    push_neg at h
    exact h3 ⟨fun _ => 0, fun v w hvw => absurd hvw (h v w)⟩
  obtain ⟨a, b, hab⟩ := hedge
  -- colour by: neighbour of a / neighbour of b / the rest
  let color : Fin n → Fin 3 := fun v =>
    if G.Adj a v then 0 else if G.Adj b v then 1 else 2
  have hnot : ¬ProperColoring G color := fun h => h3 ⟨color, h⟩
  unfold ProperColoring at hnot
  push_neg at hnot
  obtain ⟨v, w, hvw, hc⟩ := hnot
  have tri : ∀ x y z : Fin n, G.Adj x y → G.Adj x z → G.Adj y z → False := by
    intro x y z hxy hxz hyz
    exact hfree {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  by_cases hav : G.Adj a v
  · by_cases haw : G.Adj a w
    · exact (tri a v w hav haw hvw).elim
    · exfalso
      by_cases hbw : G.Adj b w <;> simp [color, hav, haw, hbw] at hc
  · by_cases hbv : G.Adj b v
    · by_cases haw : G.Adj a w
      · exfalso; simp [color, hav, hbv, haw] at hc
      · by_cases hbw : G.Adj b w
        · exact (tri b v w hbv hbw hvw).elim
        · exfalso; simp [color, hav, hbv, haw, hbw] at hc
    · by_cases haw : G.Adj a w
      · exfalso; simp [color, hav, hbv, haw] at hc
      · by_cases hbw : G.Adj b w
        · exfalso; simp [color, hav, hbv, haw, hbw] at hc
        · -- v, w are adjacent and neither sees a or b: an induced 2K₂
          refine ⟨{a, b}, {v, w}, ⟨?_, ?_⟩, edge_chromaticAtLeastOn_two G hab,
            edge_chromaticAtLeastOn_two G hvw⟩
          · rw [Finset.disjoint_left]
            intro x hx hx'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
            rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
            · exact hbv hab.symm
            · exact hbw hab.symm
            · exact hav hab
            · exact haw hab
          · intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> assumption

end Submissions.Erdos1111TriangleFreeC2.WagonTriangleFree

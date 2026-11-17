import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

namespace Submissions.Erdos1111TriangleFreeC2Sharp.FiveCycle

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

/-- The 5-cycle on `Fin 5`. -/
def C5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun i j : Fin 5 => j = i + 1

instance : DecidableRel C5.Adj := by
  unfold C5; infer_instance

/-- A vertex set whose induced graph is not 1-colourable contains an edge. -/
theorem exists_edge_of_chromaticAtLeastOn_two {V : Type} (G : SimpleGraph V) (A : Finset V)
    (h : ChromaticAtLeastOn G A 2) : ∃ a ∈ A, ∃ b ∈ A, G.Adj a b := by
  by_contra hno
  push_neg at hno
  apply h 1 (by norm_num)
  refine ⟨fun _ => 0, ?_⟩
  intro v w hvw
  exact absurd (by simpa using hvw) (hno v.1 (by exact_mod_cast v.2) w.1 (by exact_mod_cast w.2))

theorem c5_no_two_colouring :
    ∀ color : Fin 5 → Fin 2, ∃ v w, C5.Adj v w ∧ color v = color w := by
  intro color
  have key : ∀ c0 c1 c2 c3 c4 : Fin 2,
      c0 = c1 ∨ c1 = c2 ∨ c2 = c3 ∨ c3 = c4 ∨ c4 = c0 := by decide
  rcases key (color 0) (color 1) (color 2) (color 3) (color 4) with h | h | h | h | h
  · exact ⟨0, 1, by decide, h⟩
  · exact ⟨1, 2, by decide, h⟩
  · exact ⟨2, 3, by decide, h⟩
  · exact ⟨3, 4, by decide, h⟩
  · exact ⟨4, 0, by decide, h⟩

theorem c5_no_induced_2K2 :
    ∀ a b c d : Fin 5, C5.Adj a b → C5.Adj c d →
      ¬(a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
        ¬C5.Adj a c ∧ ¬C5.Adj a d ∧ ¬C5.Adj b c ∧ ¬C5.Adj b d) := by
  decide

theorem c5_triangle_free :
    ∀ a b c : Fin 5, ¬(C5.Adj a b ∧ C5.Adj a c ∧ C5.Adj b c) := by
  decide

theorem proof :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      ChromaticAtLeast G 3 ∧
      G.CliqueFree 3 ∧
      ¬∃ A B : Finset (Fin n),
          Anticomplete G A B ∧
          ChromaticAtLeastOn G A 2 ∧
          ChromaticAtLeastOn G B 2 := by
  refine ⟨5, C5, ?_, ?_, ?_⟩
  · intro k hk
    rintro ⟨color, hcol⟩
    have hk2 : k ≤ 2 := by omega
    obtain ⟨v, w, hvw, hc⟩ := c5_no_two_colouring (fun x => Fin.castLE hk2 (color x))
    exact hcol hvw (Fin.castLE_injective hk2 hc)
  · intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact c5_triangle_free a b c ⟨hab, hac, hbc⟩
  · rintro ⟨A, B, ⟨hdisj, hanti⟩, hA, hB⟩
    obtain ⟨a, ha, b, hb, hab⟩ := exists_edge_of_chromaticAtLeastOn_two C5 A hA
    obtain ⟨c, hc, d, hd, hcd⟩ := exists_edge_of_chromaticAtLeastOn_two C5 B hB
    have hne : ∀ x ∈ A, ∀ y ∈ B, x ≠ y := fun x hx y hy hxy =>
      Finset.disjoint_left.mp hdisj hx (hxy ▸ hy)
    exact c5_no_induced_2K2 a b c d hab hcd
      ⟨hne a ha c hc, hne a ha d hd, hne b hb c hc, hne b hb d hd,
        hanti a ha c hc, hanti a ha d hd, hanti b hb c hc, hanti b hb d hd⟩

end Submissions.Erdos1111TriangleFreeC2Sharp.FiveCycle

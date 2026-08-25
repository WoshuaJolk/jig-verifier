import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

namespace Submissions.Erdos1111OneColorBoundary.Direct

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

theorem chromaticAtLeast_one_of_nonempty {V : Type} [Nonempty V]
    (G : SimpleGraph V) :
    ChromaticAtLeast G 1 := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  rintro ⟨color, _⟩
  exact Fin.elim0 (color v)

theorem proof :
    ∀ t : ℕ, 1 ≤ t → ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ChromaticAtLeast G t →
      G.CliqueFree t →
      ∃ A B : Finset (Fin n),
        Anticomplete G A B ∧
        ChromaticAtLeastOn G A 1 ∧
        ChromaticAtLeastOn G B 1 := by
  classical
  intro t ht n G hchi hfree
  have htn : t ≤ n := by
    by_contra h
    have hnt : n < t := Nat.lt_of_not_ge h
    apply hchi n hnt
    exact ⟨id, fun _ _ hadj => hadj.ne⟩
  have hnon : ∃ a b : Fin n, a ≠ b ∧ ¬G.Adj a b := by
    by_contra h
    push_neg at h
    let e : Fin t ↪ Fin n := ⟨Fin.castLE htn, Fin.castLE_injective htn⟩
    let S : Finset (Fin n) := Finset.univ.map e
    apply hfree S
    constructor
    · intro a ha b hb hab
      exact h a b hab
    · simp [S]
  rcases hnon with ⟨a, b, hab, hnab⟩
  let A : Finset (Fin n) := {a}
  let B : Finset (Fin n) := {b}
  refine ⟨A, B, ?_, ?_, ?_⟩
  · simp [Anticomplete, A, B, hab, hnab]
  · letI : Nonempty A := ⟨⟨a, by simp [A]⟩⟩
    apply chromaticAtLeast_one_of_nonempty
  · letI : Nonempty B := ⟨⟨b, by simp [B]⟩⟩
    apply chromaticAtLeast_one_of_nonempty

end Submissions.Erdos1111OneColorBoundary.Direct

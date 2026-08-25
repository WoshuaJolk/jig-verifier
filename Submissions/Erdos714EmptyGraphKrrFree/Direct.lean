import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Submissions.Erdos714EmptyGraphKrrFree.Direct

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

def ContainsKrr {n : ℕ} (E : Finset (Fin n × Fin n)) (r : ℕ) : Prop :=
  ∃ A B : Finset (Fin n),
    A.card = r ∧ B.card = r ∧ Disjoint A B ∧
      ∀ a ∈ A, ∀ b ∈ B, edge a b ∈ E

theorem proof :
    ∀ n r : ℕ, 0 < r →
      ¬ ContainsKrr (n := n) ∅ r := by
  intro n r hr
  rintro ⟨A, B, hA, hB, hdisj, hcross⟩
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  simpa using hcross a ha b hb

end Submissions.Erdos714EmptyGraphKrrFree.Direct

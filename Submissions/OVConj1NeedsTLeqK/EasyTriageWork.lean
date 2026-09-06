import Mathlib

namespace Submissions.OVConj1NeedsTLeqK.EasyTriageWork
open Finset

def kInter {k m n : ℕ} (A : Fin k → Fin m → Finset (Fin n)) (f : Fin k → Fin m) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => ∀ j : Fin k, x ∈ A j (f j))

def OVHyp (k t m n : ℕ) (A : Fin k → Fin m → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin m, (Even (kInter A f).card ↔ t ≤ (image f univ).card)

theorem proof :
  ∀ C : ℕ, ∃ (n m : ℕ) (A : Fin 3 → Fin m → Finset (Fin n)),
    OVHyp 3 4 m n A ∧ ¬ (m ^ (3 / 2) ≤ C * n) := by
  intro C
  refine ⟨1, C + 1, fun _ _ => univ, ?_, ?_⟩
  · intro f
    have hcard : (image f univ).card ≤ 3 := by
      simpa using (card_image_le (s := (univ : Finset (Fin 3))) (f := f))
    simp only [kInter, mem_univ, implies_true, filter_true, card_univ,
      Fintype.card_fin, Nat.not_even_one, false_iff]
    omega
  · simp

end Submissions.OVConj1NeedsTLeqK.EasyTriageWork

import Mathlib.Data.ZMod.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

/-!
Standard interval-to-group reduction; no novelty or exponent improvement is claimed.
The helper definitions and proofs below are reused verbatim from the local
IntervalBridge.lean, SHA-256
5e297102be8012618acf80ce17606fe593599fcde5c50e11463469b8bbcf4905.
The only addition is their explicit combined theorem and submission wrapper.
Literal reduction into ZMod preserves interval Sidon sets when M > 2*N.
The following IsSidon definition is copied byte-for-byte from the canonical
problem 41 root source saved in problem41.json; no root analysis imports.
This bridge supplies hypotheses for a finite-group energy lemma. It makes
no claim of an improved asymptotic bound.
-/

namespace IntervalBridge

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

open scoped Fin.NatCast

/-- Reduction modulo M is injective on natural numbers below M. -/
theorem natCast_injective_below {M a b : ℕ} (ha : a < M) (hb : b < M)
    (h : (a : ZMod M) = (b : ZMod M)) : a = b := by
  cases M with
  | zero => omega
  | succ m =>
      change (a : Fin (m + 1)) = (b : Fin (m + 1)) at h
      have hv := congrArg Fin.val h
      simpa only [Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv

/-- The image has exactly the original number of elements. -/
theorem card_image_natCast {A : Finset ℕ} {N M : ℕ}
    (hAN : A ⊆ Finset.Icc 1 N) (hM : N < M) :
    (A.image (fun a : ℕ => (a : ZMod M))).card = A.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact natCast_injective_below
    (lt_of_le_of_lt (Finset.mem_Icc.mp (hAN ha)).2 hM)
    (lt_of_le_of_lt (Finset.mem_Icc.mp (hAN hb)).2 hM) hab

/-- The exact sum-uniqueness hypothesis used by SignedSidonEnergy on ZMod M. -/
theorem sidon_image_natCast {A : Finset ℕ} {N M : ℕ}
    (hA : IsSidon A) (hAN : A ⊆ Finset.Icc 1 N) (hM : 2 * N < M) :
    ∀ a ∈ A.image (fun a : ℕ => (a : ZMod M)),
    ∀ b ∈ A.image (fun a : ℕ => (a : ZMod M)),
    ∀ c ∈ A.image (fun a : ℕ => (a : ZMod M)),
    ∀ d ∈ A.image (fun a : ℕ => (a : ZMod M)),
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  intro a ha b hb c hc d hd habcd
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
  have hbound : ∀ x ∈ A, x ≤ N := fun x hx => (Finset.mem_Icc.mp (hAN hx)).2
  have hab : a' + b' < M := by have := hbound a' ha'; have := hbound b' hb'; omega
  have hcd : c' + d' < M := by have := hbound c' hc'; have := hbound d' hd'; omega
  have hs : a' + b' = c' + d' :=
    natCast_injective_below hab hcd (by simpa only [Nat.cast_add] using habcd)
  rcases hA ha' hb' hc' hd' hs with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact Or.inl ⟨congrArg (fun x : ℕ => (x : ZMod M)) hac,
      congrArg (fun x : ℕ => (x : ZMod M)) hbd⟩
  · exact Or.inr ⟨congrArg (fun x : ℕ => (x : ZMod M)) had,
      congrArg (fun x : ℕ => (x : ZMod M)) hbc⟩

/-- Standard interval-to-group reduction, preserving cardinality and all
unordered two-sum uniqueness, including repeated summands. -/
theorem card_and_sidon_image_natCast {A : Finset ℕ} {N M : ℕ}
    (hA : IsSidon A) (hAN : A ⊆ Finset.Icc 1 N) (hM : 2 * N < M) :
    (A.image (fun a : ℕ => (a : ZMod M))).card = A.card ∧
      (∀ a ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ b ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ c ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ d ∈ A.image (fun a : ℕ => (a : ZMod M)),
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  constructor
  · exact card_image_natCast hAN (by omega)
  · exact sidon_image_natCast hA hAN hM

end IntervalBridge

namespace Submissions.Erdos30IntervalReduction.Savcab

theorem proof :
    ∀ (N M : ℕ) (A : Finset ℕ),
    IntervalBridge.IsSidon A → A ⊆ Finset.Icc 1 N → 2 * N < M →
    (A.image (fun a : ℕ => (a : ZMod M))).card = A.card ∧
      (∀ a ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ b ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ c ∈ A.image (fun a : ℕ => (a : ZMod M)),
      ∀ d ∈ A.image (fun a : ℕ => (a : ZMod M)),
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  intro N M A hA hAN hM
  exact IntervalBridge.card_and_sidon_image_natCast hA hAN hM

end Submissions.Erdos30IntervalReduction.Savcab

#print axioms Submissions.Erdos30IntervalReduction.Savcab.proof

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval

namespace Statements.Erdos530SidonStripDomination

def IsSidon (S : Finset ℤ) : Prop :=
  ∀ ⦃a b c d : ℤ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

abbrev statement : Prop :=
  ∀ A : Finset ℤ, IsSidon A → ∀ (L : ℕ) (M : ℤ), 2 * L ≤ M →
    ((A ×ˢ Finset.Ico 0 (L : ℤ)).image (fun a => M * a.1 + a.2)).card = A.card * L ∧
    ∀ T : Finset ℤ, T ⊆ Finset.Ico 0 ((A.card * L : ℕ) : ℤ) → IsSidon T →
      ∃ S : Finset ℤ,
        S ⊆ (A ×ˢ Finset.Ico 0 (L : ℤ)).image (fun a => M * a.1 + a.2) ∧
        IsSidon S ∧ S.card = T.card

theorem target : statement := sorry

end Statements.Erdos530SidonStripDomination

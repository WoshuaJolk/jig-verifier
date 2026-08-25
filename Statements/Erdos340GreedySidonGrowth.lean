import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

open Filter Function Set
open scoped Pointwise Real

namespace Statements.Erdos340GreedySidonGrowth

/-- A set whose unordered pairwise sums are unique. -/
def IsSidon (A : Set ℕ) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Set

theorem IsSidon.insert {A : Set ℕ} {m : ℕ} (hA : IsSidon A) :
    IsSidon (A ∪ {m}) ↔
      (m ∈ A ∨ ∀ᵉ (a ∈ A) (b ∈ A), m + m ≠ a + b ∧ ∀ c ∈ A, m + a ≠ b + c) := by
  by_cases h_mem : m ∈ A
  · exact ⟨fun _ ↦ .inl h_mem, fun _ ↦ by rwa [union_singleton, insert_eq_of_mem h_mem]⟩
  refine ⟨fun h ↦ .inr fun a ha b hb ↦ ⟨fun hc ↦ ?_, fun c hc h_contr ↦ ?_⟩, fun hm ↦ ?_⟩
  · exact h m (by simp) a (by simp [ha]) m (by simp) b (by simp [hb]) hc
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · exact h m (by simp) b (by simp [hb]) a (by simp [ha]) c (by simp [hc]) h_contr
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · intro i₁ hi₁
    rcases hi₁ with (hi₁ | hi₁)
    · intro j₁ hj₁
      rcases hj₁ with (hj₁ | hj₁)
      · intro i₂ hi₂
        rcases hi₂ with (hi₂ | hi₂)
        · intro j₂ hj₂
          rcases hj₂ with (hj₂ | hj₂)
          · exact fun h ↦ hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
          · simp_all
            exact fun h ↦ by
              cases (hm j₁ hj₁ i₁ hi₁).2 i₂ hi₂ (add_comm j₁ m ▸ h.symm)
        · simp_all
          exact fun a ha h ↦ by
            cases (hm i₁ hi₁ j₁ hj₁).2 a ha (add_comm i₁ m ▸ h)
      · simp_all
        refine ⟨fun b hb h ↦ .inr <| by simp_all [add_comm], fun b hb ↦ ⟨fun h ↦ ?_, ?_⟩⟩
        · cases (hm i₁ hi₁ b hb).1 h.symm
        · exact fun c hc h ↦ by cases ((hm c hc i₁ hi₁).2 b hb) h.symm
    · simp_all
      exact fun _ _ _ _ _ ↦ by simp_all [add_comm]

end Set

namespace Finset

instance (A : Finset ℕ) : Decidable (IsSidon (A : Set ℕ)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

theorem IsSidon.insert_ge_max' {A : Finset ℕ} (h : A.Nonempty)
    (hA : IsSidon (A : Set ℕ)) {s : ℕ} (hs : 2 * A.max' h + 1 ≤ s) :
    IsSidon (A ∪ {s}) := by
  have h₁ {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
      a + b < 2 * A.max' h + 1 + c := by
    linarith [A.le_max' _ ha, A.le_max' _ hb]
  have hnot : s ∉ A := by
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ h |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  exact (Set.IsSidon.insert hA).2 <| by
    simpa [hnot] using fun a ha b hb ↦
      ⟨by linarith [A.le_max' _ ha, A.le_max' _ hb],
        fun c hc ↦ by linarith [h₁ hc hb ha]⟩

theorem IsSidon.exists_insert_ge {A : Finset ℕ} (h : A.Nonempty)
    (hA : IsSidon (A : Set ℕ)) (s : ℕ) :
    ∃ m ≥ s, m ∉ A ∧ IsSidon (A ∪ {m}) := by
  refine ⟨if s ≥ 2 * A.max' h + 1 then s else 2 * A.max' h + 1, ?_, ?_, ?_⟩
  · split_ifs <;> omega
  · split_ifs <;>
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ h |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  · split_ifs with hs
    · exact insert_ge_max' h hA hs
    · exact insert_ge_max' h hA le_rfl

def greedySidon.go (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ)} :=
  if h : A.Nonempty then
    have hex : ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
      simpa [and_assoc] using Finset.IsSidon.exists_insert_ge h hA m
    ⟨Nat.find hex, Nat.find_spec hex⟩
  else ⟨m, by simp_all [IsSidon]⟩

def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon (A : Set ℕ)} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A.1 ∪ {s'.1}, s'.2.2.2⟩, s'.1)

def greedySidon (n : ℕ) : ℕ :=
  greedySidon.aux n |>.2

end Finset

/-- Erdős Problem 340: the greedy Sidon counting function has every
square-root exponent loss. -/
abbrev statement : Prop :=
  ∀ ε > (0 : ℝ),
    (fun n : ℕ ↦ √(n : ℝ) / (n : ℝ) ^ ε) =O[atTop]
      (fun n : ℕ ↦ ((Set.range Finset.greedySidon ∩ Set.Icc 1 n).ncard : ℝ))

theorem target : statement := sorry

end Statements.Erdos340GreedySidonGrowth

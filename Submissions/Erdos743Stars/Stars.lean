import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos743Stars.Stars

def IsPacking {n : ℕ}
    (T : (i : Fin (n - 1)) → SimpleGraph (Fin (i.val + 2)))
    (f : (i : Fin (n - 1)) → Fin (i.val + 2) ↪ Fin n) : Prop :=
  ∀ u v : Fin n, u ≠ v →
    ∃! i : Fin (n - 1),
      ∃ a b : Fin (i.val + 2), (T i).Adj a b ∧
        ((f i a = u ∧ f i b = v) ∨ (f i a = v ∧ f i b = u))

def last {n : ℕ} (i : Fin (n - 1)) : Fin (i.val + 2) := ⟨i.val + 1, by omega⟩

def embed {n : ℕ} (i : Fin (n - 1)) (c : Fin (i.val + 2)) :
    Fin (i.val + 2) ↪ Fin n where
  toFun a := ⟨(Equiv.swap c (last i) a).val, by
    have := (Equiv.swap c (last i) a).isLt
    have := i.isLt
    omega⟩
  inj' := by
    intro a b h
    apply (Equiv.swap c (last i)).injective
    exact Fin.ext (congrArg (fun x : Fin n ↦ x.val) h)

@[simp] theorem embed_center {n : ℕ} (i : Fin (n - 1)) (c : Fin (i.val + 2)) :
    (embed i c c).val = i.val + 1 := by simp [embed, last]

theorem embed_bound {n : ℕ} (i : Fin (n - 1)) (c a : Fin (i.val + 2)) :
    (embed i c a).val < i.val + 2 := (Equiv.swap c (last i) a).isLt

theorem edge_height {n : ℕ} (i : Fin (n - 1)) (c a b : Fin (i.val + 2))
    (h : (SimpleGraph.starGraph c).Adj a b) :
    max (embed i c a).val (embed i c b).val = i.val + 1 := by
  have ha := embed_bound i c a
  have hb := embed_bound i c b
  rcases (SimpleGraph.starGraph_adj.mp h).2 with rfl | rfl <;>
    simp only [embed_center] at * <;> omega

theorem ordered_edge {n : ℕ} (c : (i : Fin (n - 1)) → Fin (i.val + 2))
    (u v : Fin n) (huv : u.val < v.val) :
    ∃! i : Fin (n - 1),
      ∃ a b : Fin (i.val + 2), (SimpleGraph.starGraph (c i)).Adj a b ∧
        ((embed i (c i) a = u ∧ embed i (c i) b = v) ∨
         (embed i (c i) a = v ∧ embed i (c i) b = u)) := by
  let i : Fin (n - 1) := ⟨v.val - 1, by have := v.isLt; omega⟩
  have hi : i.val + 1 = v.val := by dsimp [i]; omega
  let a₀ : Fin (i.val + 2) := ⟨u.val, by omega⟩
  let a := Equiv.swap (c i) (last i) a₀
  have ha : embed i (c i) a = u := by
    apply Fin.ext
    change (Equiv.swap (c i) (last i) (Equiv.swap (c i) (last i) a₀)).val = u.val
    simp [a₀]
  have hb : embed i (c i) (c i) = v := Fin.ext (by simpa using hi)
  refine ⟨i, ⟨a, c i, ?_, Or.inl ⟨ha, hb⟩⟩, ?_⟩
  · apply SimpleGraph.starGraph_adj.mpr
    refine ⟨?_, Or.inr rfl⟩
    intro hac
    have : u = v := ha.symm.trans ((congrArg (embed i (c i)) hac).trans hb)
    have := congrArg Fin.val this
    omega
  · rintro j ⟨x, y, hxy, hmaps⟩
    have h := edge_height j (c j) x y hxy
    rcases hmaps with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      rw [hx, hy] at h <;> apply Fin.ext <;> omega

/-- Exact packing for arbitrary orders and arbitrary labeled star centers. -/
theorem proof : ∀ n : ℕ, 2 ≤ n →
    ∀ T : (i : Fin (n - 1)) → SimpleGraph (Fin (i.val + 2)),
      (∀ i, ∃ c, T i = SimpleGraph.starGraph c) →
      ∃ f : (i : Fin (n - 1)) → Fin (i.val + 2) ↪ Fin n, IsPacking T f := by
  classical
  intro n _ T hT
  choose c hc using hT
  refine ⟨fun i ↦ embed i (c i), ?_⟩
  intro u v huv
  have hne : u.val ≠ v.val := fun h ↦ huv (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · simpa only [hc] using ordered_edge c u v h
  · obtain ⟨i, hi, hu⟩ := ordered_edge c v u h
    refine ⟨i, ?_, ?_⟩
    · obtain ⟨a, b, hab, hm⟩ := hi
      exact ⟨a, b, by simpa only [hc] using hab, hm.symm⟩
    · rintro j ⟨a, b, hab, hm⟩
      exact hu j ⟨a, b, by simpa only [hc] using hab, hm.symm⟩

end Submissions.Erdos743Stars.Stars

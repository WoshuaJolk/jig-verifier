import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

namespace Submissions.E810WedgeBound.WedgeBound

open Finset

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

def allEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun e => e.1 < e.2

def EveryC4Rainbow {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Prop :=
  ∀ v : Fin 4 → Fin n, Function.Injective v →
    (∀ i : Fin 4, edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩) ∈ E) →
    Function.Injective
      (fun i : Fin 4 => color (edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩)))

def monochromaticWedges {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t => t.2.1 < t.2.2 ∧
    edge t.1 t.2.1 ∈ E ∧ edge t.1 t.2.2 ∈ E ∧
      color (edge t.1 t.2.1) = color (edge t.1 t.2.2)

theorem edge_comm {n : ℕ} (u v : Fin n) : edge u v = edge v u := by
  unfold edge
  split_ifs <;> simp_all <;> omega

theorem endpoints_ne {n : ℕ} {E : Finset (Fin n × Fin n)}
    (hE : E ⊆ allEdges n) {u v : Fin n} (h : edge u v ∈ E) : u ≠ v := by
  intro huv
  subst v
  have hh := hE h
  simp [allEdges, edge] at hh

theorem unique_center {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) {x w y z : Fin n}
    (hyz : y ≠ z) (hxy : edge x y ∈ E) (hxz : edge x z ∈ E)
    (hwy : edge w y ∈ E) (hwz : edge w z ∈ E)
    (hc : color (edge x y) = color (edge x z)) : x = w := by
  by_contra hxw
  have hxy' := endpoints_ne hE hxy
  have hxz' := endpoints_ne hE hxz
  have hwy' := endpoints_ne hE hwy
  have hwz' := endpoints_ne hE hwz
  let v : Fin 4 → Fin n := fun i =>
    if i = 0 then y else if i = 1 then x else if i = 2 then z else w
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have he : ∀ i : Fin 4, edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩) ∈ E := by
    intro i
    fin_cases i <;> simp_all [v, edge_comm]
  have hi := hrain v hv he
  have heq : color (edge (v 0) (v 1)) = color (edge (v 1) (v 2)) := by
    simpa [v, edge_comm] using hc
  have h01 : (0 : Fin 4) = 1 := hi (by simpa using heq)
  exact (by decide : (0 : Fin 4) ≠ 1) h01

theorem proof (n : ℕ) (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) :
    (monochromaticWedges E color).card ≤ (allEdges n).card := by
  apply Finset.card_le_card_of_injOn (fun t : Fin n × Fin n × Fin n => t.2)
  · intro t ht
    have h := (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h.1⟩
  · intro t ht s hs hts
    rcases t with ⟨x, y, z⟩
    rcases s with ⟨w, y', z'⟩
    simp only [Prod.mk.injEq] at hts
    rcases hts with ⟨rfl, rfl⟩
    have ht' := (Finset.mem_filter.mp ht).2
    have hs' := (Finset.mem_filter.mp hs).2
    have hxw := unique_center hE hrain (ne_of_lt ht'.1)
      ht'.2.1 ht'.2.2.1 hs'.2.1 hs'.2.2.1 ht'.2.2.2
    exact congrArg (fun a => (a, y, z)) hxw

end Submissions.E810WedgeBound.WedgeBound

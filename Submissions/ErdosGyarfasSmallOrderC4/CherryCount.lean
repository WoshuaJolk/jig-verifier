import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-! T1 (small order): every graph on `Fin n` with `0 < n ≤ 7` and minimum degree at least `3`
contains a 4-cycle. Proof by double counting "cherries" (paths of length 2). -/

namespace Submissions.ErdosGyarfasSmallOrderC4.CherryCount

open SimpleGraph Finset

/-- Two distinct vertices with two distinct common neighbours yield a 4-cycle. -/
theorem four_cycle_of_common {V : Type*} {G : SimpleGraph V} {x y a b : V}
    (hxy : x ≠ y) (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hya : G.Adj y a) (hyb : G.Adj y b) :
    ∃ (c : G.Walk x x), c.IsCycle ∧ c.length = 4 := by
  refine ⟨Walk.cons hxa (Walk.cons hya.symm (Walk.cons hyb (Walk.cons hxb.symm Walk.nil))),
    ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    have h1 := hxa.ne
    have h2 := hxb.ne
    have h3 := hya.ne
    have h4 := hyb.ne
    constructor
    · rw [Walk.isPath_def]
      simp [List.nodup_cons, hab, h4, hxy.symm, h1.symm, h2.symm, h3.symm]
    · simp [Walk.edges_cons, hab, hxy, h1, h2, h1.symm, h3.symm]
  · simp

/-- Arithmetic: for `0 < n ≤ 7`, `3 n < C(n,2)` is impossible. -/
theorem arith_lt (n : ℕ) (h1 : 0 < n) (h2 : n ≤ 7) (h : 3 * n < n.choose 2) : False := by
  rw [Nat.choose_two_right] at h
  interval_cases n <;> omega

/-- Arithmetic: for `0 < n ≤ 7`, `3 n ≤ C(n,2)` forces `n = 7`. -/
theorem arith_le (n : ℕ) (h1 : 0 < n) (h2 : n ≤ 7) (h : 3 * n ≤ n.choose 2) : n = 7 := by
  rw [Nat.choose_two_right] at h
  interval_cases n <;> omega

theorem proof : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < n → n ≤ 7 → (∀ v : Fin n, 3 ≤ G.degree v) →
      ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length = 4 := by
  intro n G _ hn hn7 hdeg
  by_contra hno
  -- (i) two distinct vertices have at most one common neighbour
  have hcommon : ∀ x y a b : Fin n, x ≠ y → a ≠ b → G.Adj x a → G.Adj x b →
      G.Adj y a → G.Adj y b → False := by
    intro x y a b hxy hab hxa hxb hya hyb
    obtain ⟨c, hc, hl⟩ := four_cycle_of_common hxy hab hxa hxb hya hyb
    exact hno ⟨x, c, hc, hl⟩
  -- (ii) the cherry set
  set C : Finset (Σ _ : Fin n, Finset (Fin n)) :=
    univ.sigma (fun v => (G.neighborFinset v).powersetCard 2) with hC
  have hcard : C.card = ∑ v, (G.degree v).choose 2 := by
    rw [hC, card_sigma]
    refine sum_congr rfl ?_
    intro v _
    rw [card_powersetCard, card_neighborFinset_eq_degree]
  -- (iii) the pair map is injective on cherries
  have hinj : Set.InjOn (fun p : (Σ _ : Fin n, Finset (Fin n)) => p.2) (C : Set _) := by
    rintro ⟨v, s⟩ hv ⟨v', s'⟩ hv' heq
    simp only at heq
    subst heq
    simp only [hC, coe_sigma, Set.mem_sigma_iff, coe_univ, Set.mem_univ, true_and, mem_coe,
      mem_powersetCard] at hv hv'
    obtain ⟨hsv, hs2⟩ := hv
    obtain ⟨hsv', _⟩ := hv'
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs2
    by_cases hvv : v = v'
    · subst hvv; rfl
    · exfalso
      have ha : a ∈ G.neighborFinset v := hsv (by simp)
      have hb : b ∈ G.neighborFinset v := hsv (by simp)
      have ha' : a ∈ G.neighborFinset v' := hsv' (by simp)
      have hb' : b ∈ G.neighborFinset v' := hsv' (by simp)
      rw [mem_neighborFinset] at ha hb ha' hb'
      exact hcommon v v' a b hvv hab ha hb ha' hb'
  have hmaps : Set.MapsTo (fun p : (Σ _ : Fin n, Finset (Fin n)) => p.2) (C : Set _)
      ((univ : Finset (Fin n)).powersetCard 2 : Set _) := by
    rintro ⟨v, s⟩ hv
    simp only [hC, coe_sigma, Set.mem_sigma_iff, coe_univ, Set.mem_univ, true_and, mem_coe,
      mem_powersetCard] at hv
    simp only [mem_coe, mem_powersetCard, subset_univ, true_and]
    exact hv.2
  have hle : C.card ≤ ((univ : Finset (Fin n)).powersetCard 2).card :=
    card_le_card_of_injOn _ hmaps hinj
  rw [hcard, card_powersetCard, card_univ, Fintype.card_fin] at hle
  -- lower bound: each vertex contributes at least C(3,2) = 3 cherries
  have hterm : ∀ v ∈ (univ : Finset (Fin n)), 3 ≤ (G.degree v).choose 2 := by
    intro v _
    have h32 : Nat.choose 3 2 = 3 := by decide
    have := Nat.choose_le_choose 2 (hdeg v)
    rwa [h32] at this
  have hlow : ∑ _v : Fin n, 3 ≤ ∑ v, (G.degree v).choose 2 := sum_le_sum hterm
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlow
  -- (iv) all degrees are exactly 3
  have hall : ∀ v, G.degree v = 3 := by
    intro v
    by_contra hne
    have h4 : 4 ≤ G.degree v := by have := hdeg v; omega
    have hlt : ∑ _v : Fin n, 3 < ∑ v, (G.degree v).choose 2 := by
      apply sum_lt_sum hterm
      refine ⟨v, mem_univ _, ?_⟩
      have h42 : Nat.choose 4 2 = 6 := by decide
      have := Nat.choose_le_choose 2 h4
      rw [h42] at this
      omega
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    exact arith_lt n hn hn7 (by omega)
  have hn7' : n = 7 := arith_le n hn hn7 (by omega)
  -- parity: the degree sum is odd
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hall, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

end Submissions.ErdosGyarfasSmallOrderC4.CherryCount

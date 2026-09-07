import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
Formalization of the finite case of Liam Price / GPT-5.5 Pro,
"A Linear Intersection Bound", April 27, 2026.
Public proof: https://www.overleaf.com/read/bhnhxhswnjht#52529b
The present proof simplifies the initial coloring construction using uniformity.
-/

namespace Submissions.Erdos836LinearEdgeIntersection.PricePort

open Finset

abbrev Hypergraph (N : ℕ) := Finset (Finset (Fin N))
def IsUniform {N : ℕ} (r : ℕ) (G : Hypergraph N) : Prop :=
  ∀ e ∈ G, e.card = r

def IsIntersecting {N : ℕ} (G : Hypergraph N) : Prop :=
  ∀ e ∈ G, ∀ f ∈ G, (e ∩ f).Nonempty

def HasProperColoring {N : ℕ} (k : ℕ) (G : Hypergraph N) : Prop :=
  ∃ color : Fin N → Fin k, ∀ e ∈ G,
    ∃ x ∈ e, ∃ y ∈ e, color x ≠ color y

def HasChromaticNumberThree {N : ℕ} (G : Hypergraph N) : Prop :=
  HasProperColoring 3 G ∧ ¬ HasProperColoring 2 G

/-- Vertices in B are blue and all others are red. -/
def Proper {N : ℕ} (G : Hypergraph N) (B : Finset (Fin N)) : Prop :=
  ∀ e ∈ G, (e ∩ B).Nonempty ∧ (e \ B).Nonempty

lemma coloring_of_proper {N : ℕ} {G : Hypergraph N} {B : Finset (Fin N)}
    (h : Proper G B) : HasProperColoring 2 G := by
  classical
  refine ⟨fun x => if x ∈ B then 1 else 0, ?_⟩
  intro e he
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h e he
  refine ⟨x, (mem_inter.mp hx).1, y, (mem_sdiff.mp hy).1, ?_⟩
  simp [(mem_inter.mp hx).2, (mem_sdiff.mp hy).2]

lemma exists_edge {N : ℕ} {G : Hypergraph N}
    (hn : ¬ HasProperColoring 2 G) : G.Nonempty := by
  by_contra h
  apply hn
  exact ⟨fun _ => 0, by simp [not_nonempty_iff_eq_empty.mp h]⟩

lemma initial_coloring {N r : ℕ} {G : Hypergraph N} (hu : IsUniform r G)
    (hi : IsIntersecting G) {A : Finset (Fin N)} (hA : A ∈ G) :
    Disjoint A (univ \ A) ∧ Proper (G.erase A) (univ \ A) := by
  classical
  refine ⟨disjoint_sdiff_self_right, ?_⟩
  intro e he
  obtain ⟨hne, heG⟩ := mem_erase.mp he
  constructor
  · have hnot : ¬ e ⊆ A := by
      intro hsub
      exact hne (eq_of_subset_of_card_le hsub (by rw [hu A hA, hu e heG]))
    obtain ⟨x, hx, hxA⟩ := not_subset.mp hnot
    exact ⟨x, by simp [hx, hxA]⟩
  · obtain ⟨x, hx⟩ := hi e heG A hA
    exact ⟨x, by simpa using hx⟩

lemma minimal_blue {N r : ℕ} {G : Hypergraph N} (hu : IsUniform r G)
    (hi : IsIntersecting G) {A : Finset (Fin N)} (hA : A ∈ G) :
    ∃ B : Finset (Fin N), Disjoint A B ∧ Proper (G.erase A) B ∧
      ∀ C : Finset (Fin N), Disjoint A C → Proper (G.erase A) C → B.card ≤ C.card := by
  classical
  let choices : Finset (Finset (Fin N)) :=
    univ.filter fun B => Disjoint A B ∧ Proper (G.erase A) B
  have hne : choices.Nonempty := ⟨univ \ A, by simp [choices, initial_coloring hu hi hA]⟩
  obtain ⟨B, hB, hmin⟩ := choices.exists_min_image card hne
  have hb := (mem_filter.mp hB).2
  exact ⟨B, hb.1, hb.2, fun C hd hp => hmin C (by simp [choices, hd, hp])⟩

/-- Flipping a red vertex of A creates an edge whose unique red vertex was x. -/
lemma red_flip {N r : ℕ} {G : Hypergraph N} (hu : IsUniform r G)
    (hr : 2 ≤ r) (hn : ¬ HasProperColoring 2 G)
    {A B : Finset (Fin N)} (hA : A ∈ G) (hd : Disjoint A B)
    (hp : Proper (G.erase A) B) {x : Fin N} (hx : x ∈ A) :
    ∃ F ∈ G, F ≠ A ∧ F \ B = {x} := by
  classical
  have hxb : x ∉ B := disjoint_left.mp hd hx
  have hnot : ¬ Proper G (insert x B) := fun h => hn (coloring_of_proper h)
  simp only [Proper, not_forall] at hnot
  obtain ⟨F, hF, hbad⟩ := hnot
  have hmono : ¬(F ∩ insert x B).Nonempty ∨ ¬(F \ insert x B).Nonempty := not_and_or.mp hbad
  have hFA : F ≠ A := by
    intro heq
    subst F
    apply hbad
    constructor
    · exact ⟨x, mem_inter.mpr ⟨hx, mem_insert_self _ _⟩⟩
    · have hcard : 0 < (A.erase x).card := by rw [card_erase_of_mem hx, hu A hA]; omega
      obtain ⟨y, hy⟩ := card_pos.mp hcard
      obtain ⟨hyx, hyA⟩ := mem_erase.mp hy
      exact ⟨y, by simp [hyA, hyx, disjoint_left.mp hd hyA]⟩
  have hprop := hp F (mem_erase.mpr ⟨hFA,hF⟩)
  have hred : F ⊆ insert x B := by
    rcases hmono with hb | hr
    · obtain ⟨b, hbmem⟩ := hprop.1
      obtain ⟨hbF, hbB⟩ := mem_inter.mp hbmem
      exact False.elim (hb ⟨b, by simp [hbF,hbB]⟩)
    · exact sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hr)
  refine ⟨F,hF,hFA, ?_⟩
  apply Subset.antisymm
  · intro y hy
    have hy' := mem_sdiff.mp hy
    have := mem_insert.mp (hred hy'.1)
    simp only [mem_singleton]
    exact this.resolve_right hy'.2
  · obtain ⟨y, hy⟩ := hprop.2
    have hy' := mem_sdiff.mp hy
    have hyx : y = x := (mem_insert.mp (hred hy'.1)).resolve_right hy'.2
    simpa [hyx] using singleton_subset_iff.mpr hy

/-- Minimality forces a red edge when any blue vertex is turned red. -/
lemma blue_flip {N : ℕ} {G : Hypergraph N} {A B : Finset (Fin N)}
    (hd : Disjoint A B) (hp : Proper (G.erase A) B)
    (hmin : ∀ C : Finset (Fin N), Disjoint A C → Proper (G.erase A) C → B.card ≤ C.card)
    {b : Fin N} (hb : b ∈ B) :
    ∃ E ∈ G, E ≠ A ∧ E ∩ B = {b} := by
  classical
  have hnot : ¬ Proper (G.erase A) (B.erase b) := by
    intro h
    have := hmin (B.erase b) (hd.mono_right (erase_subset _ _)) h
    rw [card_erase_of_mem hb] at this
    have := card_pos.mpr ⟨b,hb⟩
    omega
  simp only [Proper, not_forall] at hnot
  obtain ⟨E, hE, hbad⟩ := hnot
  have hprop := hp E hE
  have hblue : E ∩ B ⊆ {b} := by
    have hempty : ¬ (E ∩ B.erase b).Nonempty := by
      intro h
      apply hbad
      exact ⟨h, hprop.2.mono (sdiff_subset_sdiff_right E (erase_subset _ _))⟩
    intro z hz
    have hz' := mem_inter.mp hz
    by_contra hzb
    apply hempty
    exact ⟨z, mem_inter.mpr ⟨hz'.1, mem_erase.mpr ⟨by simpa using hzb,hz'.2⟩⟩⟩
  refine ⟨E, (mem_erase.mp hE).2, (mem_erase.mp hE).1, ?_⟩
  exact (subset_singleton_iff.mp hblue).resolve_left hprop.1.ne_empty

/-- A universal upper bound on pairwise intersections controls the edge size. -/
lemma size_le_twice_intersection_add_one {N r t : ℕ} {G : Hypergraph N}
    (hr : 2 ≤ r) (hu : IsUniform r G) (hi : IsIntersecting G)
    (hn : ¬ HasProperColoring 2 G)
    (ht : ∀ e ∈ G, ∀ f ∈ G, e ≠ f → (e ∩ f).card ≤ t) : r ≤ 2*t+1 := by
  classical
  obtain ⟨A,hA⟩ := exists_edge hn
  obtain ⟨B, hd,hp,hmin⟩ := minimal_blue hu hi hA
  have hANE : A.Nonempty := card_pos.mp (by rw [hu A hA]; omega)
  letI : Nonempty A := hANE.to_subtype
  choose F hFG hFA hred using fun x : A => red_flip hu hr hn hA hd hp x.property
  have hxF (x : A) : x.val ∈ F x := by
    have h := mem_sdiff.mp ((hred x).symm ▸ mem_singleton_self x.val)
    exact h.1
  have hfred (x : A) (z : Fin N) (hz : z ∈ F x) (hzB : z ∉ B) : z = x.val := by
    have : z ∈ F x \ B := mem_sdiff.mpr ⟨hz,hzB⟩
    rwa [hred x, mem_singleton] at this
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply hfred y x.val
    · rw [← hxy]; exact hxF x
    · exact disjoint_left.mp hd x.property
  have hdegree (b : Fin N) (hb : b ∈ B) :
      r - t ≤ (univ.filter fun y : A => b ∈ F y).card := by
    obtain ⟨E,hE,hEA,hEB⟩ := blue_flip hd hp hmin hb
    have hother : (univ.filter fun y : A => b ∉ F y).card ≤ (E ∩ A).card := by
      apply card_le_card_of_injOn (fun y : A => y.val)
      · intro y hy
        have hyb : b ∉ F y := (mem_filter.mp hy).2
        obtain ⟨z,hz⟩ := hi E hE (F y) (hFG y)
        obtain ⟨hzE,hzF⟩ := mem_inter.mp hz
        have hzB : z ∉ B := by
          intro hzB
          have hzb : z = b := by
            have hz' : z ∈ E ∩ B := mem_inter.mpr ⟨hzE,hzB⟩
            rwa [hEB, mem_singleton] at hz'
          exact hyb (hzb ▸ hzF)
        have hzy := hfred y z hzF hzB
        exact mem_inter.mpr ⟨by simpa only [hzy] using hzE, y.property⟩
      · exact fun x _ y _ h => Subtype.ext h
    have hcount :
        (univ.filter fun y : A => b ∈ F y).card +
          (univ.filter fun y : A => b ∉ F y).card = r := by
      rw [card_filter_add_card_filter_not]
      simpa using hu A hA
    have htE := ht E hE A hA hEA
    omega
  let x : A := Classical.choice inferInstance
  let P : Finset (Fin N) := F x ∩ B
  have hP : P.card = r-1 := by
    have h := card_inter_add_card_sdiff (F x) B
    rw [hred x, card_singleton, hu (F x) (hFG x)] at h
    dsimp [P]
    omega
  have hdouble :
      (∑ y : A, (P.filter fun b => b ∈ F y).card) =
        ∑ b ∈ P, (univ.filter fun y : A => b ∈ F y).card := by
    exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun y : A => fun b : Fin N => b ∈ F y)
  have hlower : P.card*(r-t) ≤ ∑ b ∈ P, (univ.filter fun y : A => b ∈ F y).card := by
    calc
      P.card*(r-t) = ∑ _b ∈ P, (r-t) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun b hb => hdegree b (mem_inter.mp hb).2
  have hdiag : (P.filter fun b => b ∈ F x).card = P.card := by
    congr 1
    apply filter_eq_self.mpr
    intro b hb
    exact (mem_inter.mp hb).1
  have hupper : (∑ y : A, (P.filter fun b => b ∈ F y).card) ≤ P.card+(r-1)*t := by
    rw [← sum_erase_add _ _ (mem_univ x), hdiag]
    have hbound : (∑ y ∈ (univ.erase x), (P.filter fun b => b ∈ F y).card) ≤ (r-1)*t := by
      calc
        _ ≤ ∑ _y ∈ (univ.erase x), t := by
          apply sum_le_sum
          intro y hy
          have hyx := (mem_erase.mp hy).1
          calc
            (P.filter fun b => b ∈ F y).card ≤ (F x ∩ F y).card := by
              apply card_le_card
              intro b hb
              obtain ⟨hbP,hby⟩ := mem_filter.mp hb
              exact mem_inter.mpr ⟨(mem_inter.mp hbP).1,hby⟩
            _ ≤ t := ht (F x) (hFG x) (F y) (hFG y) (fun h => hyx (hFinj h).symm)
        _ = (r-1)*t := by simp [card_erase_of_mem (mem_univ x), hu A hA, mul_comm]
    omega
  rw [← hdouble, hP] at hlower
  rw [hP] at hupper
  have hrt : r-t ≤ t+1 := by
    by_contra hh
    have hh' : t+1 < r-t := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left hh' (by omega : 0 < r-1)
    nlinarith
  omega

/-- Complete Jig p266 root. The universal constant 1/3 follows from the sharper integer bound. -/
theorem proof :
    ∃ c : ℝ, 0 < c ∧
      ∀ r : ℕ, 2 ≤ r → ∀ N : ℕ, ∀ G : Hypergraph N,
        IsUniform r G → IsIntersecting G → HasChromaticNumberThree G →
          ∃ e ∈ G, ∃ f ∈ G, e ≠ f ∧ c*r ≤ (e ∩ f).card := by
  classical
  refine ⟨1/3, by norm_num, ?_⟩
  intro r hr N G hu hi hc
  by_contra hnot
  have hbound : ∀ e ∈ G, ∀ f ∈ G, e ≠ f → (e ∩ f).card ≤ (r-1)/3 := by
    intro e he f hf hne
    have hsmall : ¬ (1/3 : ℝ)*r ≤ (e ∩ f).card := fun h => hnot ⟨e,he,f,hf,hne,h⟩
    have hreal : (3 : ℝ)*(e ∩ f).card < r := by linarith
    have hnat : 3*(e ∩ f).card < r := by exact_mod_cast hreal
    omega
  have := size_le_twice_intersection_add_one hr hu hi hc.2 hbound
  omega

end Submissions.Erdos836LinearEdgeIntersection.PricePort

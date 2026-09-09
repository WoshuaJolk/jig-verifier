import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs

/- Repeated global sums on a single valuation-layer path give distinct unordered endpoint products. -/

open scoped Pointwise

namespace Submissions.Erdos52SameSumPathProducts.Path

theorem padicValNat_mul_from_defs (p a b : ℕ) (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  apply ENat.natCast_inj.mp
  rw [ENat.natCast_add,
    padicValNat_eq_emultiplicity_of_ne_one hp.ne_one (Nat.mul_ne_zero ha hb),
    padicValNat_eq_emultiplicity_of_ne_one hp.ne_one ha,
    padicValNat_eq_emultiplicity_of_ne_one hp.ne_one hb]
  exact emultiplicity_mul hp.prime

theorem triangular_valuation_ordered_product_injective {m : ℕ}
    (p b γ : Fin m → ℕ) (hp : ∀ i, (p i).Prime) (hb : ∀ i, 0 < b i)
    (hdiag : ∀ i, γ i < padicValNat (p i) (b i))
    (htri : ∀ i j, i < j → padicValNat (p i) (b j) = γ i)
    (i j k l : Fin m) (hij : i ≤ j) (hkl : k ≤ l)
    (hprod : b i * b j = b k * b l) : i = k ∧ j = l := by
  have hinj : Function.Injective b := by
    intro u v huv
    rcases lt_trichotomy u v with huv' | huv' | hvu'
    · have h := hdiag u
      rw [huv, htri u v huv'] at h
      exact (Nat.lt_irrefl _ h).elim
    · exact huv'
    · have h := hdiag v
      rw [← huv, htri v u hvu'] at h
      exact (Nat.lt_irrefl _ h).elim
  have hfirst (i j k l : Fin m) (hij : i ≤ j) (hkl : k ≤ l) (hik : i < k) :
      padicValNat (p i) (b k * b l) < padicValNat (p i) (b i * b j) := by
    have hj : γ i ≤ padicValNat (p i) (b j) := by
      rcases eq_or_lt_of_le hij with hij | hij
      · subst j
        exact (hdiag i).le
      · exact le_of_eq (htri i j hij).symm
    rw [padicValNat_mul_from_defs (p i) (b k) (b l) (hp i)
        (ne_of_gt (hb k)) (ne_of_gt (hb l)),
      padicValNat_mul_from_defs (p i) (b i) (b j) (hp i)
        (ne_of_gt (hb i)) (ne_of_gt (hb j)),
      htri i k hik, htri i l (lt_of_lt_of_le hik hkl)]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right (hdiag i) (γ i))
      (Nat.add_le_add_left hj _)
  have hmin : i = k := by
    rcases lt_trichotomy i k with hik | hik | hki
    · have h := hfirst i j k l hij hkl hik
      rw [hprod] at h
      exact (Nat.lt_irrefl _ h).elim
    · exact hik
    · have h := hfirst k l i j hkl hij hki
      rw [hprod] at h
      exact (Nat.lt_irrefl _ h).elim
  subst k
  exact ⟨rfl, hinj (mul_left_cancel₀ (ne_of_gt (hb i)) hprod)⟩

theorem product_card_of_ordered_product_injective {m : ℕ} (b : Fin m → ℕ)
    (hinj : ∀ i j k l : Fin m, i ≤ j → k ≤ l →
      b i * b j = b k * b l → i = k ∧ j = l) :
    ((Finset.univ.image b) * (Finset.univ.image b)).card = m + m.choose 2 := by
  classical
  let U : Finset (Fin m) := Finset.univ
  let T : Finset (Fin m × Fin m) := (U ×ˢ U).filter fun q => q.1 ≤ q.2
  let L : Finset (Fin m × Fin m) := (U ×ˢ U).filter fun q => q.1 < q.2
  let B : Finset ℕ := Finset.univ.image b
  let f : Fin m × Fin m → ℕ := fun q => b q.1 * b q.2
  have hTmem (q : Fin m × Fin m) : q ∈ T ↔ q.1 ≤ q.2 := by
    simp [T, U]
  have hsplit : T = U.diag ∪ L := by
    ext q
    simp [T, L, U, le_iff_eq_or_lt]
  have hdisj : Disjoint U.diag L := by
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    exact (ne_of_lt (Finset.mem_filter.mp hq').2) (Finset.mem_diag.mp hq).2
  have hLcard : L.card = U.card.choose 2 :=
    Finset.card_product_filter_lt (s := U)
  have hTcard : T.card = m + m.choose 2 := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.diag_card, hLcard]
    simp [U]
  have hf : Set.InjOn f T := by
    intro u hu v hv hprod
    have h := hinj u.1 u.2 v.1 v.2 ((hTmem u).mp hu) ((hTmem v).mp hv) hprod
    exact Prod.ext h.1 h.2
  have himage : T.image f = B * B := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mul_mem_mul
        (Finset.mem_image_of_mem b (Finset.mem_univ i))
        (Finset.mem_image_of_mem b (Finset.mem_univ j))
    · intro hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      rcases le_total i j with hij | hji
      · exact Finset.mem_image.mpr ⟨(i, j), (hTmem (i, j)).mpr hij, rfl⟩
      · exact Finset.mem_image.mpr ⟨(j, i), (hTmem (j, i)).mpr hji, mul_comm _ _⟩
  change (B * B).card = m + m.choose 2
  rw [← himage, Finset.card_image_of_injOn hf]
  exact hTcard

theorem triangular_valuation_product_card {m : ℕ} (p b γ : Fin m → ℕ)
    (hp : ∀ i, (p i).Prime) (hb : ∀ i, 0 < b i)
    (hdiag : ∀ i, γ i < padicValNat (p i) (b i))
    (htri : ∀ i j, i < j → padicValNat (p i) (b j) = γ i) :
    ((Finset.univ.image b) * (Finset.univ.image b)).card = m + m.choose 2 :=
  product_card_of_ordered_product_injective b
    (triangular_valuation_ordered_product_injective p b γ hp hb hdiag htri)

end Submissions.Erdos52SameSumPathProducts.Path


namespace Submissions.Erdos52SameSumPathProducts.Path

theorem common_sum_layer_le_low {p a b c d γ : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsum : a + b = c + d)
    (hsplit : padicValNat p a < padicValNat p b)
    (hclayer : padicValNat p c = γ) (hdlayer : padicValNat p d = γ) :
    γ ≤ padicValNat p a := by
  by_contra h
  have hγ : padicValNat p a + 1 ≤ γ := Nat.succ_le_of_lt (lt_of_not_ge h)
  have hbdiv : p ^ (padicValNat p a + 1) ∣ b :=
    (Nat.pow_dvd_iff_le_padicValNat hp.ne_one (ne_of_gt hb)).mpr hsplit
  have hcdiv : p ^ (padicValNat p a + 1) ∣ c :=
    (Nat.pow_dvd_iff_le_padicValNat hp.ne_one (ne_of_gt hc)).mpr (by simpa [hclayer] using hγ)
  have hddiv : p ^ (padicValNat p a + 1) ∣ d :=
    (Nat.pow_dvd_iff_le_padicValNat hp.ne_one (ne_of_gt hd)).mpr (by simpa [hdlayer] using hγ)
  have hsdiv : p ^ (padicValNat p a + 1) ∣ a + b := hsum.symm ▸ dvd_add hcdiv hddiv
  have hadiv : p ^ (padicValNat p a + 1) ∣ a := (Nat.dvd_add_iff_left hbdiv).mpr hsdiv
  exact Nat.not_succ_le_self _
    ((Nat.pow_dvd_iff_le_padicValNat hp.ne_one (ne_of_gt ha)).mp hadiv)

end Submissions.Erdos52SameSumPathProducts.Path
open scoped Pointwise

namespace Submissions.Erdos52SameSumPathProducts.Path

theorem proof :
    ∀ (m S : ℕ) (A : Finset ℕ) (p a b γ : Fin m → ℕ),
      (∀ i, (p i).Prime) →
      (∀ i, 0 < a i ∧ 0 < b i) →
      (∀ i, a i ∈ A ∧ b i ∈ A) →
      (∀ i, a i + b i = S) →
      (∀ i, padicValNat (p i) (a i) < padicValNat (p i) (b i)) →
      (∀ i j, i < j →
        padicValNat (p i) (a j) = γ i ∧ padicValNat (p i) (b j) = γ i) →
      ((Finset.univ.image b) * (Finset.univ.image b)).card = m + m.choose 2 ∧
      m + m.choose 2 ≤ (A * A).card := by
  classical
  intro m S A p a b γ hp hab hmem hsum hsplit hlater
  let δ : Fin m → ℕ := fun i => min (γ i) (padicValNat (p i) (a i))
  have hdiag (i : Fin m) : δ i < padicValNat (p i) (b i) :=
    lt_of_le_of_lt (min_le_right _ _) (hsplit i)
  have htri (i j : Fin m) (hij : i < j) : padicValNat (p i) (b j) = δ i := by
    have hγ := common_sum_layer_le_low (hp i) (hab i).1 (hab i).2
      (hab j).1 (hab j).2 ((hsum i).trans (hsum j).symm) (hsplit i)
      (hlater i j hij).1 (hlater i j hij).2
    exact (hlater i j hij).2.trans (min_eq_left hγ).symm
  have hcard := triangular_valuation_product_card p b δ hp (fun i => (hab i).2)
    hdiag htri
  refine ⟨hcard, ?_⟩
  have hsub : Finset.univ.image b ⊆ A := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hmem i).2
  rw [← hcard]
  exact Finset.card_le_card (Finset.mul_subset_mul hsub hsub)

end Submissions.Erdos52SameSumPathProducts.Path

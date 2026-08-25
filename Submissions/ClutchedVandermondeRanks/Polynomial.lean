import Mathlib

namespace Submissions.ClutchedVandermondeRanks.Polynomial

open Matrix

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

lemma clutch_kminus1_independent {k n : ℕ} (hk : 2 ≤ k)
    (tau : ℂ) (z : Fin n → ℂ) (hz : Function.Injective z)
    (hnz : ∀ i, z i ≠ 0) (f : Fin (k - 1) → Fin n)
    (hf : Function.Injective f) :
    LinearIndependent ℂ (fun i => clutch k tau (z (f i))) := by
  let D : (Fin k → ℂ) →ₗ[ℂ] (Fin (k - 1) → ℂ) :=
    LinearMap.pi (fun q => LinearMap.proj (R := ℂ)
      (⟨q.val + 1, by omega⟩ : Fin k))
  let A : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ :=
    fun i q => z (f i) ^ (q.val + 1)
  have hA : A = Matrix.diagonal (fun i => z (f i)) *
      Matrix.vandermonde (z ∘ f) := by
    ext i q
    simp [A, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vandermonde_apply,
      pow_succ']
  have hdet : A.det ≠ 0 := by
    rw [hA, Matrix.det_mul, Matrix.det_diagonal]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hnz (f i))
    · exact Matrix.det_vandermonde_ne_zero_iff.mpr (hz.comp hf)
  have hrows : LinearIndependent ℂ (fun i => A i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  apply LinearIndependent.of_comp D
  have hDA : (fun i => D (clutch k tau (z (f i)))) = fun i => A i := by
    funext i q
    simp [D, A, clutch]
  change LinearIndependent ℂ (fun i => D (clutch k tau (z (f i))))
  rw [hDA]
  exact hrows

lemma clutch_kplus1_spanning {k n : ℕ} (hk : 2 ≤ k)
    (tau : ℂ) (z : Fin n → ℂ) (hz : Function.Injective z)
    (f : Fin (k + 1) → Fin n) (hf : Function.Injective f) :
    Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) = ⊤ := by
  classical
  by_contra htop
  have hlt : Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) < ⊤ :=
    lt_top_iff_ne_top.mpr htop
  obtain ⟨phi, hphi, hker⟩ :=
    (Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i)))).exists_le_ker_of_lt_top hlt
  let b : Module.Basis (Fin k) ℂ (Fin k → ℂ) := Pi.basisFun ℂ (Fin k)
  let term : Fin k → _root_.Polynomial ℂ := fun q =>
    Polynomial.C (phi (b q)) *
      if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
      else Polynomial.X ^ q.val
  let P : _root_.Polynomial ℂ := ∑ q, term q
  have hphi_clutch (w : ℂ) :
      phi (clutch k tau w) = ∑ q, clutch k tau w q * phi (b q) := by
    conv_lhs => rw [← b.sum_repr (clutch k tau w)]
    simp [b, Pi.basisFun_repr]
  have hPeval (w : ℂ) : P.eval w = phi (clutch k tau w) := by
    rw [hphi_clutch]
    change Polynomial.eval w (∑ q, term q) = _
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [term, Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hq0 : q.val = 0
    · rw [if_pos hq0]
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [show clutch k tau w q = 1 + tau * w ^ k by simp [clutch, hq0]]
      ring
    · rw [if_neg hq0]
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      rw [show clutch k tau w q = w ^ q.val by simp [clutch, hq0]]
      ring
  have hPdeg : P.natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    simp only [term]
    by_cases hq0 : q.val = 0
    · rw [if_pos hq0]
      calc
        (Polynomial.C (phi (b q)) *
            (1 + Polynomial.C tau * Polynomial.X ^ k)).natDegree
            ≤ (Polynomial.C (phi (b q))).natDegree +
              (1 + Polynomial.C tau * Polynomial.X ^ k).natDegree :=
                Polynomial.natDegree_mul_le
        _ ≤ 0 + k := by
          apply Nat.add_le_add
          · simp
          · apply Polynomial.natDegree_add_le_of_degree_le
            · simp
            · exact Polynomial.natDegree_mul_le.trans (by simp)
        _ = k := Nat.zero_add k
    · rw [if_neg hq0]
      calc
        (Polynomial.C (phi (b q)) * Polynomial.X ^ q.val).natDegree
            ≤ (Polynomial.C (phi (b q))).natDegree +
              (Polynomial.X ^ q.val).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + q.val := by simp
        _ ≤ k := by omega
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (hz.comp hf)
    · intro i
      rw [hPeval]
      apply LinearMap.mem_ker.mp
      apply hker
      exact Submodule.subset_span (Set.mem_range_self i)
    · simpa using Nat.lt_succ_of_le hPdeg
  apply hphi
  apply b.ext
  intro q
  have hcoeff : P.coeff q.val = phi (b q) := by
    change (∑ s, term s).coeff q.val = phi (b q)
    rw [Polynomial.finsetSum_coeff]
    calc
      ∑ s, (term s).coeff q.val = (term q).coeff q.val := by
        apply Finset.sum_eq_single q
        · intro s hs hsq
          have hsqval : s.val ≠ q.val := fun h => hsq (Fin.ext h)
          by_cases hs0 : s.val = 0
          · have hq0 : q.val ≠ 0 := fun h => hsq (Fin.ext (hs0.trans h.symm))
            have hqk : q.val ≠ k := Nat.ne_of_lt q.isLt
            change (Polynomial.C (phi (b s)) *
              (if s.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
                else Polynomial.X ^ s.val)).coeff q.val = 0
            rw [if_pos hs0, Polynomial.coeff_C_mul, Polynomial.coeff_add,
              Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow]
            simp [hq0, hqk]
          · change (Polynomial.C (phi (b s)) *
              (if s.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
                else Polynomial.X ^ s.val)).coeff q.val = 0
            rw [if_neg hs0, Polynomial.coeff_C_mul_X_pow]
            simp [Ne.symm hsqval]
        · simp
      _ = phi (b q) := by
        by_cases hq0 : q.val = 0
        · have hk0 : k ≠ 0 := by omega
          change (Polynomial.C (phi (b q)) *
            (if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
              else Polynomial.X ^ q.val)).coeff q.val = phi (b q)
          rw [if_pos hq0, Polynomial.coeff_C_mul, Polynomial.coeff_add,
            Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow]
          simp [hq0, hk0, Ne.symm hk0]
        · change (Polynomial.C (phi (b q)) *
            (if q.val = 0 then 1 + Polynomial.C tau * Polynomial.X ^ k
              else Polynomial.X ^ q.val)).coeff q.val = phi (b q)
          rw [if_neg hq0, Polynomial.coeff_C_mul_X_pow]
          simp
  rw [hPzero] at hcoeff
  simpa using hcoeff.symm

theorem proof :
  ∀ (k n : ℕ), 2 ≤ k → ∀ (tau : ℂ) (z : Fin n → ℂ),
    Function.Injective z →
      ((∀ (_hnz : ∀ i, z i ≠ 0) (f : Fin (k - 1) → Fin n),
          Function.Injective f →
            LinearIndependent ℂ (fun i => clutch k tau (z (f i)))) ∧
       (∀ (f : Fin (k + 1) → Fin n), Function.Injective f →
          Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) = ⊤)) := by
  intro k n hk tau z hz
  constructor
  · intro hnz f hf
    exact clutch_kminus1_independent hk tau z hz hnz f hf
  · intro f hf
    exact clutch_kplus1_spanning hk tau z hz f hf

end Submissions.ClutchedVandermondeRanks.Polynomial

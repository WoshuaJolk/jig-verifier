-- Port of the existing Erdős 1131 Lean disproof by GitHub user seanm27lol.
-- Source: https://github.com/seanm27lol/erdos-1131-lean/tree/31574acf09ae50430c08da92288800fe7d26c7fd
-- Original commit dated 2026-07-23; licensed under Apache-2.0.
-- No novelty is claimed for the disproof, comparison family, or upstream formalization.
-- MODIFICATIONS: explicit Mathlib imports and compatibility changes for Jig's pin;
-- combination into this namespace, with one section per original module;
-- canonical product/integral/infimum/index-shift bridge and final proof declaration.
-- This generated file preserves comments from the current audited local port.
-- Regenerate with p345/assemble-port.py after reviewing changes to its inputs.
-- The complete upstream LICENSE follows.
-- 
--                                  Apache License
--                            Version 2.0, January 2004
--                         http://www.apache.org/licenses/
-- 
--    TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION
-- 
--    1. Definitions.
-- 
--       "License" shall mean the terms and conditions for use, reproduction,
--       and distribution as defined by Sections 1 through 9 of this document.
-- 
--       "Licensor" shall mean the copyright owner or entity authorized by
--       the copyright owner that is granting the License.
-- 
--       "Legal Entity" shall mean the union of the acting entity and all
--       other entities that control, are controlled by, or are under common
--       control with that entity. For the purposes of this definition,
--       "control" means (i) the power, direct or indirect, to cause the
--       direction or management of such entity, whether by contract or
--       otherwise, or (ii) ownership of fifty percent (50%) or more of the
--       outstanding shares, or (iii) beneficial ownership of such entity.
-- 
--       "You" (or "Your") shall mean an individual or Legal Entity
--       exercising permissions granted by this License.
-- 
--       "Source" form shall mean the preferred form for making modifications,
--       including but not limited to software source code, documentation
--       source, and configuration files.
-- 
--       "Object" form shall mean any form resulting from mechanical
--       transformation or translation of a Source form, including but
--       not limited to compiled object code, generated documentation,
--       and conversions to other media types.
-- 
--       "Work" shall mean the work of authorship, whether in Source or
--       Object form, made available under the License, as indicated by a
--       copyright notice that is included in or attached to the work
--       (an example is provided in the Appendix below).
-- 
--       "Derivative Works" shall mean any work, whether in Source or Object
--       form, that is based on (or derived from) the Work and for which the
--       editorial revisions, annotations, elaborations, or other modifications
--       represent, as a whole, an original work of authorship. For the purposes
--       of this License, Derivative Works shall not include works that remain
--       separable from, or merely link (or bind by name) to the interfaces of,
--       the Work and Derivative Works thereof.
-- 
--       "Contribution" shall mean any work of authorship, including
--       the original version of the Work and any modifications or additions
--       to that Work or Derivative Works thereof, that is intentionally
--       submitted to Licensor for inclusion in the Work by the copyright owner
--       or by an individual or Legal Entity authorized to submit on behalf of
--       the copyright owner. For the purposes of this definition, "submitted"
--       means any form of electronic, verbal, or written communication sent
--       to the Licensor or its representatives, including but not limited to
--       communication on electronic mailing lists, source code control systems,
--       and issue tracking systems that are managed by, or on behalf of, the
--       Licensor for the purpose of discussing and improving the Work, but
--       excluding communication that is conspicuously marked or otherwise
--       designated in writing by the copyright owner as "Not a Contribution."
-- 
--       "Contributor" shall mean Licensor and any individual or Legal Entity
--       on behalf of whom a Contribution has been received and subsequently
--       incorporated within the Work.
-- 
--    2. Grant of Copyright License. Subject to the terms and conditions of
--       this License, each Contributor hereby grants to You a perpetual,
--       worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--       copyright license to reproduce, prepare Derivative Works of,
--       publicly display, publicly perform, sublicense, and distribute the
--       Work and such Derivative Works in Source or Object form.
-- 
--    3. Grant of Patent License. Subject to the terms and conditions of
--       this License, each Contributor hereby grants to You a perpetual,
--       worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--       (except as stated in this section) patent license to make, have made,
--       use, offer to sell, sell, import, and otherwise transfer the Work,
--       where such license applies only to those patent claims licensable
--       by such Contributor that are necessarily infringed by their
--       Contribution(s) alone or by combination of their Contribution(s)
--       with the Work to which such Contribution(s) was submitted. If You
--       institute patent litigation against any entity (including a
--       cross-claim or counterclaim in a lawsuit) alleging that the Work
--       or a Contribution incorporated within the Work constitutes direct
--       or contributory patent infringement, then any patent licenses
--       granted to You under this License for that Work shall terminate
--       as of the date such litigation is filed.
-- 
--    4. Redistribution. You may reproduce and distribute copies of the
--       Work or Derivative Works thereof in any medium, with or without
--       modifications, and in Source or Object form, provided that You
--       meet the following conditions:
-- 
--       (a) You must give any other recipients of the Work or
--           Derivative Works a copy of this License; and
-- 
--       (b) You must cause any modified files to carry prominent notices
--           stating that You changed the files; and
-- 
--       (c) You must retain, in the Source form of any Derivative Works
--           that You distribute, all copyright, patent, trademark, and
--           attribution notices from the Source form of the Work,
--           excluding those notices that do not pertain to any part of
--           the Derivative Works; and
-- 
--       (d) If the Work includes a "NOTICE" text file as part of its
--           distribution, then any Derivative Works that You distribute must
--           include a readable copy of the attribution notices contained
--           within such NOTICE file, excluding those notices that do not
--           pertain to any part of the Derivative Works, in at least one
--           of the following places: within a NOTICE text file distributed
--           as part of the Derivative Works; within the Source form or
--           documentation, if provided along with the Derivative Works; or,
--           within a display generated by the Derivative Works, if and
--           wherever such third-party notices normally appear. The contents
--           of the NOTICE file are for informational purposes only and
--           do not modify the License. You may add Your own attribution
--           notices within Derivative Works, alongside or as an addendum to
--           the NOTICE text from the Work, provided that such additional
--           attribution notices cannot be construed as modifying the License.
-- 
--       You may add Your own copyright statement to Your modifications and
--       may provide additional or different license terms and conditions
--       for use, reproduction, or distribution of Your modifications, or for
--       any such Derivative Works as a whole, provided Your use, reproduction,
--       and distribution of the Work otherwise complies with the conditions
--       stated in this License.
-- 
--    5. Submission of Contributions. Unless You explicitly state otherwise,
--       any Contribution intentionally submitted for inclusion in the Work
--       by You to the Licensor shall be under the terms and conditions of
--       this License, without any additional terms or conditions.
--       Notwithstanding the above, nothing herein shall supersede or modify
--       the terms of any separate license agreement you may have executed
--       with Licensor regarding such Contributions.
-- 
--    6. Trademarks. This License does not grant permission to use the trade
--       names, trademarks, service marks, or product names of the Licensor,
--       except as required for reasonable and customary use in describing the
--       origin of the Work and reproducing the content of the NOTICE file.
-- 
--    7. Disclaimer of Warranty. Unless required by applicable law or
--       agreed to in writing, Licensor provides the Work (and each
--       Contributor provides its Contributions) on an "AS IS" BASIS,
--       WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
--       implied, including, without limitation, any warranties or conditions
--       of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
--       PARTICULAR PURPOSE. You are solely responsible for determining the
--       appropriateness of using or redistributing the Work and assume any
--       risks associated with Your exercise of permissions under this License.
-- 
--    8. Limitation of Liability. In no event and under no legal theory,
--       whether in tort (including negligence), contract, or otherwise,
--       unless required by applicable law (such as deliberate and grossly
--       negligent acts) or agreed to in writing, shall any Contributor be
--       liable to You for damages, including any direct, indirect, special,
--       incidental, or consequential damages of any character arising as a
--       result of this License or out of the use or inability to use the
--       Work (including but not limited to damages for loss of goodwill,
--       work stoppage, computer failure or malfunction, or any and all other
--       commercial damages or losses), even if such Contributor has been
--       advised of the possibility of such damages.
-- 
--    9. Accepting Warranty or Additional Liability. While redistributing
--       the Work or Derivative Works thereof, You may choose to offer, and
--       charge a fee for, acceptance of support, warranty, indemnity, or other
--       liability obligations and/or rights consistent with this License.
--       However, in accepting such obligations, You may act only on Your own
--       behalf and on Your sole responsibility, not on behalf of any other
--       Contributor, and only if You agree to indemnify, defend, and hold each
--       Contributor harmless for any liability incurred by, or claims asserted
--       against, such Contributor by reason of your accepting any such warranty
--       or additional liability.
-- 
--    END OF TERMS AND CONDITIONS

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Topology.Algebra.Order.LiminfLimsup

-- Port/Imports.lean input SHA-256 26fd0327061a9127d4f0adb6f58e01503c3d63a5a07aa63eee349fba7f913f12
namespace Submissions.Erdos1131AsymptoticRefutation.ChebyshevPort

-- Original: Erdos1131/Definitions.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/Definitions.lean; SHA-256 e1be42fa3696ba8703f074278584e8d07674149086af521afc581bc23f67026b
section PortDefinitions

                   

/-!
# Definitions and elementary facts for Erdős Problem 1131

The node configuration is represented by an embedding `Fin n ↪ ℝ`, so
pairwise distinctness is part of the type.  The extremal value is an infimum;
no attainment is assumed.
-/

open scoped BigOperators Interval
open Filter Set

namespace Erdos1131

def Admissible {n : ℕ} (x : Fin n ↪ ℝ) : Prop :=
  ∀ k, x k ∈ Set.Icc (-1 : ℝ) 1

noncomputable def functional {n : ℕ} (x : Fin n ↪ ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    ∑ k : Fin n,
      ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2

def values (n : ℕ) : Set ℝ :=
  {y | ∃ x : Fin n ↪ ℝ, Admissible x ∧ functional x = y}

noncomputable def M (n : ℕ) : ℝ :=
  sInf (values n)

noncomputable def scaledDefect (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (2 - M (n + 1))

/-- A canonical admissible configuration, used only to show nonemptiness. -/
noncomputable def canonicalNodes (n : ℕ) : Fin n ↪ ℝ where
  toFun k := (k : ℝ) / (n + 1 : ℕ)
  inj' := by
    intro i j hij
    apply Fin.ext
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    exact_mod_cast (div_left_inj' hn).mp hij

theorem canonicalNodes_admissible (n : ℕ) : Admissible (canonicalNodes n) := by
  intro k
  constructor
  · change (-1 : ℝ) ≤ (k : ℝ) / (n + 1 : ℕ)
    have : 0 ≤ (k : ℝ) / (n + 1 : ℕ) := by positivity
    linarith
  · change (k : ℝ) / (n + 1 : ℕ) ≤ 1
    apply div_le_one_of_le₀
    · exact_mod_cast (Nat.le_of_lt (k.isLt.trans (Nat.lt_succ_self n)))
    · positivity

theorem values_nonempty (n : ℕ) : (values n).Nonempty :=
  ⟨functional (canonicalNodes n), canonicalNodes n, canonicalNodes_admissible n, rfl⟩

theorem functional_nonneg {n : ℕ} (x : Fin n ↪ ℝ) : 0 ≤ functional x := by
  apply intervalIntegral.integral_nonneg_of_forall
  · norm_num
  · intro t
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem values_bddBelow (n : ℕ) : BddBelow (values n) :=
  ⟨0, by
    rintro y ⟨x, -, rfl⟩
    exact functional_nonneg x⟩

theorem M_nonneg (n : ℕ) : 0 ≤ M n :=
  le_csInf (values_nonempty n) fun _ hy ↦
    let ⟨x, _, hxy⟩ := hy
    hxy ▸ functional_nonneg x

theorem M_le_functional {n : ℕ} (x : Fin n ↪ ℝ) (hx : Admissible x) :
    M n ≤ functional x :=
  csInf_le (values_bddBelow n) ⟨x, hx, rfl⟩

theorem basis_intervalIntegrable {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    IntervalIntegrable
      (fun t : ℝ ↦ (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t)
      MeasureTheory.volume (-1) 1 :=
  (Polynomial.continuous _).intervalIntegrable _ _

theorem sum_sq_intervalIntegrable {n : ℕ} (x : Fin n ↪ ℝ) :
    IntervalIntegrable
      (fun t : ℝ ↦
        ∑ k : Fin n,
          ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2)
      MeasureTheory.volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem basis_eval_self {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval (x k) = 1 := by
  simpa using Lagrange.eval_basis_self x.injective.injOn (Finset.mem_univ k)

theorem basis_eval_of_ne {n : ℕ} (x : Fin n ↪ ℝ) {j k : Fin n} (hjk : j ≠ k) :
    (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval (x j) = 0 := by
  exact Lagrange.eval_basis_of_ne (Ne.symm hjk) (Finset.mem_univ j)

theorem basis_eq_product {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    Lagrange.basis Finset.univ (x : Fin n → ℝ) k =
      ∏ i ∈ (Finset.univ.erase k),
        Polynomial.C ((x k - x i)⁻¹) * (Polynomial.X - Polynomial.C (x i)) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor]

theorem basis_eval_eq_product {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) (t : ℝ) :
    (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t =
      ∏ i ∈ (Finset.univ.erase k), (t - x i) / (x k - x i) := by
  rw [basis_eq_product]
  simp only [Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, div_eq_inv_mul]

theorem node_sub_ne_zero {n : ℕ} (x : Fin n ↪ ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    x i - x j ≠ 0 :=
  sub_ne_zero.mpr (x.injective.ne hij)

theorem lagrange_denominator_ne_zero {n : ℕ} (x : Fin n ↪ ℝ) (k : Fin n) :
    ∏ i ∈ Finset.univ.erase k, (x k - x i) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact node_sub_ne_zero x (Finset.ne_of_mem_erase hi).symm

theorem sq_eq_abs_sq (a : ℝ) : a ^ 2 = |a| ^ 2 := by
  rw [sq_abs]

def permuteNodes {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n) : Fin n ↪ ℝ :=
  e.toEmbedding.trans x

@[simp]
theorem permuteNodes_apply {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n) (k : Fin n) :
    permuteNodes x e k = x (e k) :=
  rfl

theorem admissible_permuteNodes {n : ℕ} {x : Fin n ↪ ℝ} (e : Fin n ≃ Fin n)
    (hx : Admissible x) : Admissible (permuteNodes x e) :=
  fun k ↦ hx (e k)

theorem basis_permuteNodes {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n)
    (k : Fin n) :
    Lagrange.basis Finset.univ (permuteNodes x e : Fin n → ℝ) k =
      Lagrange.basis Finset.univ (x : Fin n → ℝ) (e k) := by
  simp only [Lagrange.basis, permuteNodes_apply]
  apply Finset.prod_equiv e
  · intro i
    simp
  · intro i hi
    rfl

theorem functional_permuteNodes {n : ℕ} (x : Fin n ↪ ℝ) (e : Fin n ≃ Fin n) :
    functional (permuteNodes x e) = functional x := by
  unfold functional
  congr 1
  funext t
  simp_rw [basis_permuteNodes]
  exact e.sum_comp (fun k : Fin n ↦
    ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2)

theorem M_one : M 1 = 2 := by
  have hvalues : values 1 = {2} := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      simp [functional]
      norm_num
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨canonicalNodes 1, canonicalNodes_admissible 1, by
        simp [functional]
        norm_num⟩
  rw [M, hvalues, csInf_singleton]

end Erdos1131

end PortDefinitions

-- Original: Erdos1131/DisproofBridge.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/DisproofBridge.lean; SHA-256 39b0c42da62b1a956396d4cabdebe67dffc3a1fe6b6c4cdca5fb1c6480a43065
section PortDisproofBridge

                       

/-!
# From an explicit comparison family to the disproof

This file contains no asymptotic orthogonal-polynomial input.  It isolates the
order-theoretic step saying that an eventual admissible comparison family with
scaled defect at least `106 / 105` rules out convergence to `1`.
-/

open Filter Set

namespace Erdos1131

theorem scaledDefect_ge_of_comparison
    {N : ℕ} (x : Fin (N + 1) ↪ ℝ) (hx : Admissible x)
    (hcomparison :
      (106 : ℝ) / 105 ≤
        ((N + 1 : ℕ) : ℝ) * (2 - functional x)) :
    (106 : ℝ) / 105 ≤ scaledDefect N := by
  rw [scaledDefect]
  calc
    (106 : ℝ) / 105
        ≤ ((N + 1 : ℕ) : ℝ) * (2 - functional x) := hcomparison
    _ ≤ ((N + 1 : ℕ) : ℝ) * (2 - M (N + 1)) := by
      gcongr
      exact M_le_functional x hx

theorem not_erdos_1131_of_eventual_comparison
    (hcomparison :
      ∀ᶠ N : ℕ in atTop,
        ∃ x : Fin (N + 1) ↪ ℝ,
          Admissible x ∧
            (106 : ℝ) / 105 ≤
              ((N + 1 : ℕ) : ℝ) * (2 - functional x)) :
    ¬ Tendsto scaledDefect atTop (nhds 1) := by
  intro hlimit
  have hupper : ∀ᶠ N : ℕ in atTop, scaledDefect N < (211 : ℝ) / 210 :=
    (tendsto_order.1 hlimit).2 _ (by norm_num)
  rw [eventually_atTop] at hcomparison hupper
  obtain ⟨N₁, hcomparison⟩ := hcomparison
  obtain ⟨N₂, hupper⟩ := hupper
  let N := max N₁ N₂
  have hN := hcomparison N (le_max_left _ _)
  have hNupper := hupper N (le_max_right _ _)
  obtain ⟨x, hx, hscaled⟩ := hN
  have hlower := scaledDefect_ge_of_comparison x hx hscaled
  norm_num at hlower hNupper
  linarith

end Erdos1131

end PortDisproofBridge

-- Original: Erdos1131/AsymptoticConclusion.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/AsymptoticConclusion.lean; SHA-256 8464403022fba6f4e53caf1c8be508e24523873f120de2ac59431c827120616b
section PortAsymptoticConclusion

                          

/-!
# The explicit finite estimate implies the asymptotic contradiction

This file isolates the final elementary calculation.  The analytic and matrix
parts of the proof only need to supply the displayed upper bound on the
functional of an admissible comparison family.
-/

namespace Erdos1131

theorem scaled_comparison_of_functional_le
    {N : ℕ} (hN : 24780 ≤ N) (x : Fin (N + 1) ↪ ℝ)
    (hfunctional :
      functional x ≤
        2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2) :
    (106 : ℝ) / 105 ≤
      ((N + 1 : ℕ) : ℝ) * (2 - functional x) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNrLarge : (24780 : ℝ) ≤ N := by exact_mod_cast hN
  have hdefect :
      107 / (105 * (N : ℝ)) - 118 / (N : ℝ) ^ 2 ≤
        2 - functional x := by
    linarith
  have harithmetic :
      (106 : ℝ) / 105 ≤
        ((N + 1 : ℕ) : ℝ) *
          (107 / (105 * (N : ℝ)) - 118 / (N : ℝ) ^ 2) := by
    rw [show (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 by norm_num]
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hNrLarge) (le_of_lt hNr)]
  calc
    (106 : ℝ) / 105
        ≤ ((N + 1 : ℕ) : ℝ) *
            (107 / (105 * (N : ℝ)) - 118 / (N : ℝ) ^ 2) :=
      harithmetic
    _ ≤ ((N + 1 : ℕ) : ℝ) * (2 - functional x) := by
      gcongr

end Erdos1131

end PortAsymptoticConclusion

-- Original: Erdos1131/ChebyshevBound.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/ChebyshevBound.lean; SHA-256 91b784e6116d3f7deaef3a558da7c900fcca40fa961b6b5842f846eadd65e4cb
section PortChebyshevBound

                   

/-!
# The finite Chebyshev comparison estimate

This file contains the purely finite matrix estimate used by the Chebyshev
comparison family for Erdős Problem 1131.  The construction and enumeration of
the roots of `T_{N+1} - (1 / 6) T_{N-1}` is deliberately kept separate.

The central matrices below are indexed by the Chebyshev degrees `0, ..., N`.
`chebH` is the Lebesgue Gram matrix of these polynomials, `chebK` is the
bounded part of the evaluation Gram matrix, and `chebDInv` is the inverse of
its diagonal part.
-/

open scoped BigOperators

namespace Erdos1131.ChebyshevBound

noncomputable section

/-- The even Chebyshev moment `∫ T_{2r}` divided by two. -/
def chebMoment (r : ℕ) : ℝ :=
  1 / (1 - 4 * (r : ℝ) ^ 2)

/-- Two natural numbers have the same parity. -/
def SameParity (j k : ℕ) : Prop :=
  j % 2 = k % 2

instance (j k : ℕ) : Decidable (SameParity j k) :=
  inferInstanceAs (Decidable (j % 2 = k % 2))

/-- The Lebesgue Gram matrix of `T_0, ..., T_N`, written in closed form. -/
def chebH (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun j k =>
    if SameParity j.val k.val then
      chebMoment ((j.val + k.val) / 2) + chebMoment (j.val.dist k.val / 2)
    else 0

/-- The bounded part of the evaluation Gram matrix for
`T_{N+1} - (1/6) T_{N-1}`. -/
def chebK (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun j k =>
    if SameParity j.val k.val then
      (((1 / 6 : ℝ) ^ ((j.val + k.val) / 2) +
        (1 / 6 : ℝ) ^ (j.val.dist k.val / 2)) / 2)
    else 0

/-- The inverse of the diagonal matrix whose entries are
`2, 1, ..., 1, 7/6`.  The definitions at `0` and `N` overlap only when
`N = 0`; all comparison estimates assume `6 ≤ N`. -/
def chebDInvEntry (N i : ℕ) : ℝ :=
  if i = 0 then 1 / 2 else if i = N then 6 / 7 else 1

def chebDInv (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal fun i => chebDInvEntry N i

/-- Relative perturbation in the factorization
`R = (N/2) D (1 + chebY N)`. -/
def chebY (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (2 / (N : ℝ)) • (chebDInv N * chebK N)

/-- The inverse relative factor. -/
def chebZ (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (1 + chebY N)⁻¹

/-- The exact second-order remainder after expanding the relative inverse. -/
def chebInverseRemainder (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  chebY N * chebY N * chebZ N * ((2 / (N : ℝ)) • chebDInv N)

/-- Absolute row sum.  We use this elementary quantity instead of invoking
operator-norm or spectral machinery. -/
def absRowSum {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (i : m) : ℝ :=
  ∑ j, |A i j|

/-- Every absolute row sum of `A` is at most `c`. -/
def RowBound {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (c : ℝ) : Prop :=
  ∀ i, absRowSum A i ≤ c

/-- Maximum absolute row sum for a nonempty finite row index type. -/
def maxAbsRowSum {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (absRowSum A)

theorem le_maxAbsRowSum {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) (i : m) :
    absRowSum A i ≤ maxAbsRowSum A :=
  Finset.le_sup' (absRowSum A) (Finset.mem_univ i)

theorem rowBound_maxAbsRowSum
    {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) :
    RowBound A (maxAbsRowSum A) :=
  le_maxAbsRowSum A

theorem maxAbsRowSum_le_iff
    {m n : Type*} [Fintype m] [Nonempty m] [Fintype n]
    (A : Matrix m n ℝ) (c : ℝ) :
    maxAbsRowSum A ≤ c ↔ RowBound A c := by
  rw [maxAbsRowSum, Finset.sup'_le_iff]
  simp only [Finset.mem_univ, forall_const, RowBound]

theorem abs_chebMoment_le_one (r : ℕ) :
    |chebMoment r| ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    norm_num [chebMoment]
  · have hr_nat : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hr_real : (1 : ℝ) ≤ r := by exact_mod_cast hr_nat
    have hneg : 1 - 4 * (r : ℝ) ^ 2 ≤ 0 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
    have habs : 1 ≤ |1 - 4 * (r : ℝ) ^ 2| := by
      rw [abs_of_nonpos hneg]
      nlinarith [sq_nonneg ((r : ℝ) - 1)]
    rw [chebMoment, one_div, abs_inv]
    exact inv_le_one_of_one_le₀ habs

@[simp]
theorem chebMoment_zero : chebMoment 0 = 1 := by
  norm_num [chebMoment]

theorem chebMoment_succ (m : ℕ) :
    chebMoment (m + 1) =
      -(1 : ℝ) / ((2 * m + 1) * (2 * m + 3)) := by
  unfold chebMoment
  push_cast
  rw [show 1 - 4 * ((m : ℝ) + 1) ^ 2 =
      -((2 * m + 1) * (2 * m + 3)) by ring]
  simp only [one_div, inv_neg, neg_div]

/-- The elementary telescoping identity
`Σ_{r=1}^m (1 - 4r²)⁻¹ = -m/(2m+1)`. -/
theorem sum_chebMoment_succ (m : ℕ) :
    Finset.sum (Finset.range m) (fun r => chebMoment (r + 1)) =
      -(m : ℝ) / (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      rw [chebMoment_succ]
      push_cast
      have h₁ : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
      have h₂ : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
      field_simp
      ring

theorem abs_chebH_entry_le_two (N : ℕ) (i j : Fin (N + 1)) :
    |chebH N i j| ≤ 2 := by
  rw [chebH]
  split_ifs
  · calc
      |chebMoment ((i.val + j.val) / 2) +
          chebMoment (i.val.dist j.val / 2)| ≤
          |chebMoment ((i.val + j.val) / 2)| +
            |chebMoment (i.val.dist j.val / 2)| := abs_add_le _ _
      _ ≤ 1 + 1 :=
        add_le_add (abs_chebMoment_le_one _) (abs_chebMoment_le_one _)
      _ = 2 := by norm_num
  · norm_num

theorem chebH_diag (N : ℕ) (i : Fin (N + 1)) :
    chebH N i i = 1 + chebMoment i.val := by
  have hii : (i.val + i.val) / 2 = i.val := by
    rw [← Nat.two_mul i.val, Nat.mul_div_cancel_left]
    norm_num
  rw [chebH, if_pos (show SameParity i.val i.val from rfl)]
  rw [hii, Nat.dist_self, Nat.zero_div, chebMoment_zero, add_comm]

theorem trace_chebH_mul_chebDInv_eq_sum (N : ℕ) :
    Matrix.trace (chebH N * chebDInv N) =
      ∑ i : Fin (N + 1),
        (1 + chebMoment i.val) * chebDInvEntry N i.val := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  change (chebH N * chebDInv N) i i =
    (1 + chebMoment i.val) * chebDInvEntry N i.val
  rw [Matrix.mul_apply, chebDInv]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [chebH_diag]

theorem chebDInvEntry_fin_eq
    {N : ℕ} (hN : 0 < N) (i : Fin (N + 1)) :
    chebDInvEntry N i.val =
      1 - (if i = 0 then 1 / 2 else 0) -
        (if i = Fin.last N then 1 / 7 else 0) := by
  by_cases hi0 : i = 0
  · subst i
    simp [chebDInvEntry, hN.ne']
    norm_num
  · by_cases hiN : i = Fin.last N
    · subst i
      simp [chebDInvEntry, hN.ne']
      norm_num
    · have hival0 : i.val ≠ 0 := by
        intro h
        apply hi0
        exact Fin.ext h
      have hivalN : i.val ≠ N := by
        intro h
        apply hiN
        exact Fin.ext h
      simp [chebDInvEntry, hi0, hiN, hival0, hivalN]

theorem sum_mul_chebDInvEntry
    {N : ℕ} (hN : 0 < N) (f : Fin (N + 1) → ℝ) :
    (∑ i, f i * chebDInvEntry N i.val) =
      (∑ i, f i) - f 0 / 2 - f (Fin.last N) / 7 := by
  classical
  simp_rw [chebDInvEntry_fin_eq hN]
  calc
    (∑ i, f i *
        (1 - (if i = 0 then 1 / 2 else 0) -
          (if i = Fin.last N then 1 / 7 else 0))) =
        ∑ i, (f i - (if i = 0 then f i / 2 else 0) -
          (if i = Fin.last N then f i / 7 else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> ring
    _ = (∑ i, f i) - f 0 / 2 - f (Fin.last N) / 7 := by
      simp only [Finset.sum_sub_distrib]
      simp

theorem sum_chebMoment_fin (N : ℕ) :
    (∑ i : Fin (N + 1), chebMoment i.val) =
      1 - (N : ℝ) / (2 * N + 1) := by
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_range_succ',
    sum_chebMoment_succ, chebMoment_zero]
  ring

theorem trace_chebH_mul_chebDInv_exact
    {N : ℕ} (hN : 0 < N) :
    Matrix.trace (chebH N * chebDInv N) =
      (N : ℝ) + 5 / 14 + 1 / (2 * (2 * N + 1)) -
        chebMoment N / 7 := by
  rw [trace_chebH_mul_chebDInv_eq_sum,
    sum_mul_chebDInvEntry hN, Fin.last]
  rw [show (∑ i : Fin (N + 1), (1 + chebMoment i.val)) =
      (N + 1 : ℝ) + ∑ i : Fin (N + 1), chebMoment i.val by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring,
    sum_chebMoment_fin]
  simp only [Fin.val_zero, chebMoment_zero]
  have hden : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem trace_chebH_mul_chebDInv_le
    {N : ℕ} (hN : 0 < N) :
    Matrix.trace (chebH N * chebDInv N) ≤
      (N : ℝ) + 5 / 14 + 1 / N := by
  rw [trace_chebH_mul_chebDInv_exact hN]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hden : (0 : ℝ) < 4 * (N : ℝ) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have ha :
      (1 : ℝ) / (2 * (2 * N + 1)) ≤ 1 / (4 * N) := by
    apply (div_le_div_iff₀
      (by positivity : (0 : ℝ) < 2 * (2 * N + 1))
      (by positivity : (0 : ℝ) < 4 * N)).2
    nlinarith
  have hb :
      (1 : ℝ) / (4 * (N : ℝ) ^ 2 - 1) / 7 ≤ 1 / (7 * N) := by
    rw [div_div]
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) hNpos)
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hinv : 0 ≤ (1 : ℝ) / N := by positivity
  unfold chebMoment
  rw [show (1 : ℝ) - 4 * (N : ℝ) ^ 2 =
    -(4 * (N : ℝ) ^ 2 - 1) by ring, div_neg, neg_div,
    sub_neg_eq_add]
  have herr :
      (1 : ℝ) / (2 * (2 * N + 1)) +
          1 / (4 * (N : ℝ) ^ 2 - 1) / 7 ≤ 1 / N := by
    calc
      (1 : ℝ) / (2 * (2 * N + 1)) +
          1 / (4 * (N : ℝ) ^ 2 - 1) / 7 ≤
          1 / (4 * N) + 1 / (7 * N) := add_le_add ha hb
      _ ≤ 1 / N := by
        ring_nf at *
        nlinarith
  linarith

/-- A finite subseries of the geometric series with ratio `1/6`. -/
theorem sum_one_sixth_pow_le
    {α : Type*} (s : Finset α) (e : α → ℕ)
    (he : Set.InjOn e s) :
    (∑ x ∈ s, (1 / 6 : ℝ) ^ e x) ≤ 6 / 5 := by
  classical
  rw [← Finset.sum_image he]
  calc
    (∑ r ∈ s.image e, (1 / 6 : ℝ) ^ r) ≤
        ∑' r : ℕ, (1 / 6 : ℝ) ^ r := by
      exact (summable_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 6 : ℝ)‖ < 1)).sum_le_tsum _
          (fun _ _ => by positivity)
    _ = 6 / 5 := by
      rw [tsum_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 6 : ℝ)‖ < 1)]
      norm_num

def sameParityIndices (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun j => SameParity i.val j.val

def sameParityLeftIndices (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun j =>
    SameParity i.val j.val ∧ j.val ≤ i.val

def sameParityRightIndices (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun j =>
    SameParity i.val j.val ∧ i.val < j.val

theorem injOn_dist_div_two_left
    {N : ℕ} (i : Fin (N + 1)) :
    Set.InjOn (fun j : Fin (N + 1) => i.val.dist j.val / 2)
      (sameParityLeftIndices N i) := by
  intro a ha c hc heq
  rw [Finset.mem_coe] at ha hc
  simp only [sameParityLeftIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hc
  apply Fin.ext
  unfold SameParity at ha hc
  dsimp at heq
  rw [Nat.dist_comm i.val a.val, Nat.dist_eq_sub_of_le ha.2,
    Nat.dist_comm i.val c.val, Nat.dist_eq_sub_of_le hc.2] at heq
  omega

theorem injOn_dist_div_two_sub_one_right
    {N : ℕ} (i : Fin (N + 1)) :
    Set.InjOn (fun j : Fin (N + 1) => i.val.dist j.val / 2 - 1)
      (sameParityRightIndices N i) := by
  intro a ha c hc heq
  rw [Finset.mem_coe] at ha hc
  simp only [sameParityRightIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hc
  apply Fin.ext
  unfold SameParity at ha hc
  dsimp at heq
  rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt ha.2),
    Nat.dist_eq_sub_of_le (Nat.le_of_lt hc.2)] at heq
  omega

theorem injOn_add_div_two
    {N : ℕ} (i : Fin (N + 1)) :
    Set.InjOn (fun j : Fin (N + 1) => (i.val + j.val) / 2)
      (sameParityIndices N i) := by
  intro a ha c hc heq
  rw [Finset.mem_coe] at ha hc
  simp only [sameParityIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hc
  apply Fin.ext
  unfold SameParity at ha hc
  dsimp at heq
  have hea : (i.val + a.val) % 2 = 0 := by omega
  have hec : (i.val + c.val) % 2 = 0 := by omega
  have hda : ((i.val + a.val) / 2) * 2 = i.val + a.val := by omega
  have hdc : ((i.val + c.val) / 2) * 2 = i.val + c.val := by omega
  omega

theorem sum_dist_div_two_left_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityLeftIndices N i,
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) ≤ 6 / 5 :=
  sum_one_sixth_pow_le _ _ (injOn_dist_div_two_left i)

theorem sum_add_div_two_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityIndices N i,
      (1 / 6 : ℝ) ^ ((i.val + j.val) / 2)) ≤ 6 / 5 :=
  sum_one_sixth_pow_le _ _ (injOn_add_div_two i)

theorem sum_dist_div_two_right_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityRightIndices N i,
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) ≤ 1 / 5 := by
  have hshift :
      (∑ j ∈ sameParityRightIndices N i,
        (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) =
      (1 / 6 : ℝ) *
        ∑ j ∈ sameParityRightIndices N i,
          (1 / 6 : ℝ) ^ (i.val.dist j.val / 2 - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := hj
    simp only [sameParityRightIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj'
    have hdist : 1 ≤ i.val.dist j.val / 2 := by
      rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hj'.2)]
      unfold SameParity at hj'
      omega
    have hexp :
        i.val.dist j.val / 2 =
          (i.val.dist j.val / 2 - 1) + 1 := by omega
    calc
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2) =
          (1 / 6 : ℝ) ^ ((i.val.dist j.val / 2 - 1) + 1) := by
            exact congrArg (fun e : ℕ => (1 / 6 : ℝ) ^ e) hexp
      _ = (1 / 6 : ℝ) *
          (1 / 6 : ℝ) ^ (i.val.dist j.val / 2 - 1) := by
            rw [pow_succ]
            ring
  rw [hshift]
  have hgeom := sum_one_sixth_pow_le
    (sameParityRightIndices N i)
    (fun j : Fin (N + 1) => i.val.dist j.val / 2 - 1)
    (injOn_dist_div_two_sub_one_right i)
  calc
    (1 / 6 : ℝ) *
        ∑ j ∈ sameParityRightIndices N i,
          (1 / 6 : ℝ) ^ (i.val.dist j.val / 2 - 1) ≤
        (1 / 6 : ℝ) * (6 / 5) := by gcongr
    _ = 1 / 5 := by norm_num

theorem sum_dist_div_two_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityIndices N i,
      (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) ≤ 7 / 5 := by
  have hleft :
      (sameParityIndices N i).filter (fun j => j.val ≤ i.val) =
        sameParityLeftIndices N i := by
    ext j
    simp only [sameParityIndices, sameParityLeftIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
  have hright :
      (sameParityIndices N i).filter (fun j => ¬j.val ≤ i.val) =
        sameParityRightIndices N i := by
    ext j
    simp only [sameParityIndices, sameParityRightIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, hj⟩
      exact ⟨hp, Nat.lt_of_not_ge hj⟩
    · rintro ⟨hp, hj⟩
      exact ⟨hp, Nat.not_le_of_lt hj⟩
  rw [← Finset.sum_filter_add_sum_filter_not
      (sameParityIndices N i) (fun j => j.val ≤ i.val)
      (fun j => (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)),
    hleft, hright]
  linarith [sum_dist_div_two_left_le i, sum_dist_div_two_right_le i]

theorem chebK_nonneg (N : ℕ) (i j : Fin (N + 1)) :
    0 ≤ chebK N i j := by
  rw [chebK]
  split_ifs
  · positivity
  · norm_num

theorem rowBound_chebK (N : ℕ) :
    RowBound (chebK N) (13 / 10) := by
  intro i
  have hsum :
      absRowSum (chebK N) i =
        ∑ j ∈ sameParityIndices N i,
          (((1 / 6 : ℝ) ^ ((i.val + j.val) / 2) +
            (1 / 6 : ℝ) ^ (i.val.dist j.val / 2)) / 2) := by
    rw [absRowSum]
    simp_rw [abs_of_nonneg (chebK_nonneg N i _)]
    simp only [sameParityIndices, Finset.sum_filter, chebK]
  rw [hsum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  calc
    ((∑ x ∈ sameParityIndices N i,
        (1 / 6 : ℝ) ^ ((i.val + x.val) / 2)) +
      ∑ x ∈ sameParityIndices N i,
        (1 / 6 : ℝ) ^ (i.val.dist x.val / 2)) / 2 ≤
        ((6 / 5 : ℝ) + 7 / 5) / 2 := by
          exact div_le_div_of_nonneg_right
            (add_le_add (sum_add_div_two_le i) (sum_dist_div_two_le i))
            (by norm_num)
    _ = 13 / 10 := by norm_num

theorem absRowSum_nonneg {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (i : m) :
    0 ≤ absRowSum A i :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem absRowSum_smul {m n : Type*} [Fintype n]
    (a : ℝ) (A : Matrix m n ℝ) (i : m) :
    absRowSum (a • A) i = |a| * absRowSum A i := by
  classical
  simp only [absRowSum, Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem rowBound_smul {m n : Type*} [Fintype n]
    {A : Matrix m n ℝ} {c : ℝ} (hA : RowBound A c) (a : ℝ) :
    RowBound (a • A) (|a| * c) := by
  intro i
  rw [absRowSum_smul]
  exact mul_le_mul_of_nonneg_left (hA i) (abs_nonneg a)

theorem absRowSum_add_le {m n : Type*} [Fintype n]
    (A B : Matrix m n ℝ) (i : m) :
    absRowSum (A + B) i ≤ absRowSum A i + absRowSum B i := by
  classical
  simp only [absRowSum, Matrix.add_apply]
  calc
    ∑ j, |A i j + B i j| ≤ ∑ j, (|A i j| + |B i j|) :=
      Finset.sum_le_sum fun _ _ => abs_add_le _ _
    _ = _ := Finset.sum_add_distrib

theorem rowBound_add {m n : Type*} [Fintype n]
    {A B : Matrix m n ℝ} {c d : ℝ}
    (hA : RowBound A c) (hB : RowBound B d) :
    RowBound (A + B) (c + d) := by
  intro i
  exact (absRowSum_add_le A B i).trans (add_le_add (hA i) (hB i))

theorem absRowSum_mul_le {m n p : Type*} [Fintype n] [Fintype p]
    (A : Matrix m n ℝ) (B : Matrix n p ℝ) (i : m) :
    absRowSum (A * B) i ≤
      ∑ k, |A i k| * absRowSum B k := by
  classical
  simp only [absRowSum, Matrix.mul_apply]
  calc
    ∑ j, |∑ k, A i k * B k j| ≤
        ∑ j, ∑ k, |A i k * B k j| := by
      gcongr with j
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, ∑ j, |A i k * B k j| := Finset.sum_comm
    _ = ∑ k, |A i k| * ∑ j, |B k j| := by
      congr 1
      funext k
      simp only [abs_mul, Finset.mul_sum]

theorem rowBound_mul {m n p : Type*} [Fintype n] [Fintype p]
    {A : Matrix m n ℝ} {B : Matrix n p ℝ} {c d : ℝ}
    (hA : RowBound A c) (hB : RowBound B d) (hd : 0 ≤ d) :
    RowBound (A * B) (c * d) := by
  intro i
  refine (absRowSum_mul_le A B i).trans ?_
  calc
    ∑ k, |A i k| * absRowSum B k ≤ ∑ k, |A i k| * d := by
      gcongr with k
      exact hB k
    _ = absRowSum A i * d := by
      simp only [absRowSum, Finset.sum_mul]
    _ ≤ c * d := mul_le_mul_of_nonneg_right (hA i) hd

theorem rowBound_one {n : Type*} [Fintype n] [DecidableEq n] :
    RowBound (1 : Matrix n n ℝ) 1 := by
  intro i
  rw [absRowSum]
  simp only [Matrix.one_apply, abs_ite, abs_one, abs_zero]
  exact le_of_eq <| by
    simp

theorem absRowSum_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (f : n → ℝ) (i : n) :
    absRowSum (Matrix.diagonal f) i = |f i| := by
  rw [absRowSum]
  simp only [Matrix.diagonal_apply, abs_ite, abs_zero]
  simp

theorem abs_chebDInvEntry_le_one {N i : ℕ} :
    |chebDInvEntry N i| ≤ 1 := by
  rw [chebDInvEntry]
  split_ifs <;> norm_num

theorem rowBound_chebDInv (N : ℕ) :
    RowBound (chebDInv N) 1 := by
  intro i
  rw [chebDInv, absRowSum_diagonal]
  exact abs_chebDInvEntry_le_one

theorem rowBound_chebY_of_rowBound_chebK
    {N : ℕ} (hN : 0 < N)
    (hK : RowBound (chebK N) (13 / 10)) :
    RowBound (chebY N) (13 / (5 * N)) := by
  have hprod : RowBound (chebDInv N * chebK N) (1 * (13 / 10)) :=
    rowBound_mul (rowBound_chebDInv N) hK (by norm_num)
  have hsmul := rowBound_smul hprod (2 / (N : ℝ))
  rw [chebY]
  convert hsmul using 1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_of_pos (div_pos (by norm_num) hNr)]
  field_simp
  ring

/-- Elementary finite inverse bound.  It is stated from the identity
`Z = 1 - Y Z`, so it does not depend on a particular matrix-inverse API. -/
theorem rowBound_of_eq_one_sub_mul
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    (Y Z : Matrix n n ℝ) {q : ℝ}
    (hY : RowBound Y q) (hq1 : q < 1)
    (hZ : Z = 1 - Y * Z) :
    RowBound Z (1 / (1 - q)) := by
  let M := maxAbsRowSum Z
  have hM0 : 0 ≤ M := (absRowSum_nonneg Z (Classical.choice inferInstance)).trans
    (le_maxAbsRowSum Z (Classical.choice inferInstance))
  have hZM : RowBound Z M := rowBound_maxAbsRowSum Z
  have hYZ : RowBound (Y * Z) (q * M) :=
    rowBound_mul hY hZM hM0
  have hnegYZ : RowBound (-(Y * Z)) (q * M) := by
    intro i
    simpa only [absRowSum, Matrix.neg_apply, abs_neg] using hYZ i
  have hRhs : RowBound (1 - Y * Z) (1 + q * M) := by
    simpa only [sub_eq_add_neg] using rowBound_add rowBound_one hnegYZ
  have hMle : M ≤ 1 + q * M := by
    rw [maxAbsRowSum_le_iff]
    simpa only [← hZ] using hRhs
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hMdiv : M ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  exact fun i => (hZM i).trans hMdiv

theorem chebZ_eq_one_sub_mul
    {N : ℕ} (hunit : IsUnit (1 + chebY N).det) :
    chebZ N = 1 - chebY N * chebZ N := by
  have hmul : (1 + chebY N) * chebZ N = 1 := by
    rw [chebZ]
    exact (1 + chebY N).mul_nonsing_inv hunit
  have hadd : chebZ N + chebY N * chebZ N = 1 := by
    simpa only [Matrix.add_mul, Matrix.one_mul] using hmul
  exact eq_sub_of_add_eq hadd

theorem rowBound_chebZ_two
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (1 + chebY N).det) :
    RowBound (chebZ N) 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hY := rowBound_chebY_of_rowBound_chebK hNpos hK
  have hq : (13 : ℝ) / (5 * N) < 1 := by
    have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
    have hden : (0 : ℝ) < 5 * N := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith
  have hZ := rowBound_of_eq_one_sub_mul
    (chebY N) (chebZ N) hY hq (chebZ_eq_one_sub_mul hunit)
  intro i
  refine (hZ i).trans ?_
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < 1 - (13 : ℝ) / (5 * N) := sub_pos.mpr hq
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith

theorem rowBound_chebInverseRemainder
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (1 + chebY N).det) :
    RowBound (chebInverseRemainder N) (676 / (25 * (N : ℝ) ^ 3)) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hY := rowBound_chebY_of_rowBound_chebK hNpos hK
  have hZ := rowBound_chebZ_two hN hK hunit
  have hYY : RowBound (chebY N * chebY N)
      ((13 / (5 * N : ℝ)) * (13 / (5 * N : ℝ))) :=
    rowBound_mul hY hY (by positivity)
  have hYYZ : RowBound (chebY N * chebY N * chebZ N)
      (((13 / (5 * N : ℝ)) * (13 / (5 * N : ℝ))) * 2) :=
    rowBound_mul hYY hZ (by norm_num)
  have hscaledD :
      RowBound ((2 / (N : ℝ)) • chebDInv N) (2 / (N : ℝ)) := by
    have h := rowBound_smul (rowBound_chebDInv N) (2 / (N : ℝ))
    have hdiv : (0 : ℝ) < 2 / N := div_pos (by norm_num) hNr
    simpa only [abs_of_pos hdiv, mul_one] using h
  rw [chebInverseRemainder]
  convert rowBound_mul hYYZ hscaledD (le_of_lt (div_pos (by norm_num) hNr)) using 1
  field_simp
  ring

/-- A trace estimate that only uses entry bounds for the left factor and
absolute row sums for the right factor. -/
theorem abs_trace_mul_le_of_entry_le_rowBound
    {n : Type*} [Fintype n]
    (H E : Matrix n n ℝ) {h e : ℝ}
    (hH : ∀ i j, |H i j| ≤ h) (hE : RowBound E e)
    (hh : 0 ≤ h) :
    |Matrix.trace (H * E)| ≤ (Fintype.card n : ℝ) * h * e := by
  classical
  rw [Matrix.trace_mul_comm H E]
  rw [Matrix.trace]
  calc
    |∑ i, (E * H) i i| ≤ ∑ i, |(E * H) i i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, h * e := by
      gcongr with i
      rw [Matrix.mul_apply]
      calc
        |∑ j, E i j * H j i| ≤ ∑ j, |E i j * H j i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |E i j| * |H j i| := by simp only [abs_mul]
        _ ≤ ∑ j, |E i j| * h := by
          gcongr with j
          exact hH j i
        _ = absRowSum E i * h := by
          simp only [absRowSum, Finset.sum_mul]
        _ ≤ e * h := mul_le_mul_of_nonneg_right (hE i) hh
        _ = h * e := mul_comm _ _
    _ = (Fintype.card n : ℝ) * h * e := by
      simp [mul_assoc]

theorem abs_trace_chebH_inverseRemainder_le
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (1 + chebY N).det) :
    |Matrix.trace (chebH N * chebInverseRemainder N)| ≤
      64 / (N : ℝ) ^ 2 := by
  have hrow := rowBound_chebInverseRemainder hN hK hunit
  have htrace := abs_trace_mul_le_of_entry_le_rowBound
    (chebH N) (chebInverseRemainder N)
    (abs_chebH_entry_le_two N) hrow (by norm_num)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [Fintype.card_fin] at htrace
  refine htrace.trans ?_
  push_cast
  field_simp
  have hNr6 : (6 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

end

end Erdos1131.ChebyshevBound

end PortChebyshevBound

-- Original: Erdos1131/ChebyshevFamily.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/ChebyshevFamily.lean; SHA-256 5ad46898171d9bd182a24cf51504a3d94d740403d869da8a5a52c4209886770a
section PortChebyshevFamily

                       
                                                                             
                                          
                                                                 

/-!
# The explicit Chebyshev comparison nodes

For `n ≥ 2` and `b = 1/6`, the comparison nodes are the `n` real roots of

`Qₙ = Tₙ - b Tₙ₋₂`.

The alternating signs at the extrema `cos (kπ/n)` put one root in each
open interval between consecutive extrema.  This simultaneously proves
admissibility and excludes collisions.
-/

open scoped BigOperators Interval
open Set

namespace Erdos1131

open Polynomial Polynomial.Chebyshev Real

noncomputable def chebQ (n : ℕ) : ℝ[X] :=
  T ℝ (n : ℤ) -
    Polynomial.C ((1 : ℝ) / 6) * T ℝ ((n - 2 : ℕ) : ℤ)

theorem chebQ_eval (n : ℕ) (x : ℝ) :
    (chebQ n).eval x =
      (T ℝ (n : ℤ)).eval x -
        (1 : ℝ) / 6 * (T ℝ ((n - 2 : ℕ) : ℤ)).eval x := by
  simp [chebQ]

theorem degree_chebQ {n : ℕ} (hn : 2 ≤ n) : (chebQ n).degree = n := by
  rw [chebQ, degree_sub_eq_left_of_degree_lt]
  · exact degree_T ℝ n
  · calc
      (Polynomial.C ((1 : ℝ) / 6) * T ℝ ((n - 2 : ℕ) : ℤ)).degree
          = (T ℝ ((n - 2 : ℕ) : ℤ)).degree := by
              rw [degree_C_mul (by norm_num)]
      _ = (n - 2 : ℕ) := by
        simp only [degree_T, Int.natAbs_natCast]
      _ < (n : WithBot ℕ) := by
        exact_mod_cast Nat.sub_lt (by omega) (by omega)
      _ = (T ℝ n).degree := (degree_T ℝ n).symm

theorem chebQ_ne_zero {n : ℕ} (hn : 2 ≤ n) : chebQ n ≠ 0 := by
  rw [← degree_ne_bot, degree_chebQ hn]
  exact WithBot.coe_ne_bot

private theorem grid_angle_sub {n k : ℕ} (hn : 2 ≤ n) :
    ((n - 2 : ℕ) : ℝ) * ((k : ℝ) * π / n) =
      (k : ℝ) * π - 2 * ((k : ℝ) * π / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hn]
  field_simp

theorem chebQ_eval_grid {n k : ℕ} (hn : 2 ≤ n) :
    (chebQ n).eval (cos ((k : ℝ) * π / n)) =
      (-1 : ℝ) ^ k *
        (1 - (1 : ℝ) / 6 * cos (2 * ((k : ℝ) * π / n))) := by
  rw [chebQ_eval, T_real_cos, T_real_cos]
  norm_num only [Int.cast_natCast]
  rw [show (n : ℝ) * ((k : ℝ) * π / n) = (k : ℝ) * π by
    field_simp]
  rw [grid_angle_sub hn, cos_nat_mul_pi, cos_nat_mul_pi_sub]
  ring

theorem chebQ_grid_factor_pos {n k : ℕ} :
    0 < 1 - (1 : ℝ) / 6 * cos (2 * ((k : ℝ) * π / n)) := by
  have hcos := neg_one_le_cos (2 * ((k : ℝ) * π / n))
  have hcos' := cos_le_one (2 * ((k : ℝ) * π / n))
  nlinarith

theorem chebQ_eval_grid_ne_zero {n k : ℕ} (hn : 2 ≤ n) :
    (chebQ n).eval (cos ((k : ℝ) * π / n)) ≠ 0 := by
  rw [chebQ_eval_grid hn]
  exact mul_ne_zero (pow_ne_zero k (by norm_num)) (ne_of_gt chebQ_grid_factor_pos)

theorem chebQ_eval_grid_mul_next_neg {n k : ℕ} (hn : 2 ≤ n) :
    (chebQ n).eval (cos (((k + 1 : ℕ) : ℝ) * π / n)) *
        (chebQ n).eval (cos ((k : ℝ) * π / n)) < 0 := by
  rw [chebQ_eval_grid hn, chebQ_eval_grid hn, pow_succ]
  have hk := chebQ_grid_factor_pos (n := n) (k := k)
  have hk1 := chebQ_grid_factor_pos (n := n) (k := k + 1)
  have hs : (-1 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hsquare : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ k * -1 *
          (1 - 1 / 6 * cos (2 * (↑(k + 1) * π / ↑n))) *
          ((-1 : ℝ) ^ k *
            (1 - 1 / 6 * cos (2 * (↑k * π / ↑n))))
        = -(((-1 : ℝ) ^ k) ^ 2 *
            ((1 - 1 / 6 * cos (2 * (↑(k + 1) * π / ↑n))) *
              (1 - 1 / 6 * cos (2 * (↑k * π / ↑n))))) := by ring
    _ < 0 := by
      rw [hsquare]
      nlinarith [mul_pos hk1 hk]

private theorem grid_angle_mem {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    (k : ℝ) * π / n ∈ Set.Icc (0 : ℝ) π := by
  constructor
  · positivity
  · calc
      (k : ℝ) * π / n ≤ (n : ℝ) * π / n := by
        gcongr
      _ = π := by field_simp

theorem grid_cos_strictAnti {n i j : ℕ} (hn : 2 ≤ n) (hij : i < j) (hj : j ≤ n) :
    cos ((j : ℝ) * π / n) < cos ((i : ℝ) * π / n) := by
  apply cos_lt_cos_of_nonneg_of_le_pi
  · exact (grid_angle_mem hn (Nat.le_trans (Nat.le_of_lt hij) hj)).1
  · exact (grid_angle_mem hn hj).2
  · have hn0 : (0 : ℝ) < n := by positivity
    have hpi : (0 : ℝ) < π := pi_pos
    gcongr

theorem exists_chebQ_root_between {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    ∃ x : ℝ,
      x ∈ Set.Ioo
        (cos (((k.1 + 1 : ℕ) : ℝ) * π / n))
        (cos ((k.1 : ℝ) * π / n)) ∧
      (chebQ n).eval x = 0 := by
  let a := cos (((k.1 + 1 : ℕ) : ℝ) * π / n)
  let c := cos ((k.1 : ℝ) * π / n)
  have hac : a < c := by
    exact grid_cos_strictAnti hn (Nat.lt_succ_self k.1) (Nat.succ_le_of_lt k.2)
  have hsign :
      (chebQ n).eval a * (chebQ n).eval c < 0 := by
    simpa [a, c] using chebQ_eval_grid_mul_next_neg (n := n) (k := k.1) hn
  have hzero :
      (0 : ℝ) ∈ [[(chebQ n).eval a, (chebQ n).eval c]] := by
    rw [mem_uIcc]
    rcases (mul_neg_iff.mp hsign) with h | h
    · exact Or.inr ⟨h.2.le, h.1.le⟩
    · exact Or.inl ⟨h.1.le, h.2.le⟩
  have hiv :=
    intermediate_value_uIcc
      ((Polynomial.continuous (chebQ n)).continuousOn) hzero
  obtain ⟨x, hx, hqx⟩ := hiv
  refine ⟨x, ?_, hqx⟩
  rw [uIcc_of_le hac.le] at hx
  refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
  · intro hxa
    subst x
    exact (chebQ_eval_grid_ne_zero (n := n) (k := k.1 + 1) hn) hqx
  · intro hxc
    subst x
    exact (chebQ_eval_grid_ne_zero (n := n) (k := k.1) hn) hqx

noncomputable def chebNode {n : ℕ} (hn : 2 ≤ n) (k : Fin n) : ℝ :=
  Classical.choose (exists_chebQ_root_between hn k)

theorem chebNode_mem_interval {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    chebNode hn k ∈ Set.Ioo
      (cos (((k.1 + 1 : ℕ) : ℝ) * π / n))
      (cos ((k.1 : ℝ) * π / n)) :=
  (Classical.choose_spec (exists_chebQ_root_between hn k)).1

theorem chebNode_isRoot {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    (chebQ n).eval (chebNode hn k) = 0 :=
  (Classical.choose_spec (exists_chebQ_root_between hn k)).2

theorem chebNode_strictAnti {n : ℕ} (hn : 2 ≤ n) {i j : Fin n} (hij : i < j) :
    chebNode hn j < chebNode hn i := by
  have hi := chebNode_mem_interval hn i
  have hj := chebNode_mem_interval hn j
  have hij' : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hij
  have hcos :
      cos ((j.1 : ℝ) * π / n) ≤
        cos (((i.1 + 1 : ℕ) : ℝ) * π / n) := by
    rcases hij'.eq_or_lt with h | h
    · simp [h]
    · exact (grid_cos_strictAnti hn h (Nat.le_of_lt j.2)).le
  exact (hj.2.trans_le hcos).trans hi.1

noncomputable def chebNodes (n : ℕ) (hn : 2 ≤ n) : Fin n ↪ ℝ where
  toFun := chebNode hn
  inj' := by
    intro i j h
    apply Fin.ext
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have := chebNode_strictAnti hn hij
      linarith
    · have := chebNode_strictAnti hn hji
      linarith

@[simp]
theorem chebNodes_apply {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    chebNodes n hn k = chebNode hn k :=
  rfl

theorem chebNodes_admissible {n : ℕ} (hn : 2 ≤ n) :
    Admissible (chebNodes n hn) := by
  intro k
  have hk := chebNode_mem_interval hn k
  constructor
  · exact (neg_one_le_cos _).trans hk.1.le
  · exact hk.2.le.trans (cos_le_one _)

theorem chebNodes_isRoot {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    (chebQ n).eval (chebNodes n hn k) = 0 :=
  chebNode_isRoot hn k

end Erdos1131

end PortChebyshevFamily

-- Original: Erdos1131/ChebyshevFirstOrder.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/ChebyshevFirstOrder.lean; SHA-256 353c31759cd4a32882585bd1b5e29888c68a97fa57a657fdde952d58c2dcd491
section PortChebyshevFirstOrder

                          

/-!
# A first-order lower bound for the Chebyshev trace

This file gives an independent finite estimate for the first correction term.
The diagonal supplies `N / 2 + O(1)`.  Off the diagonal, the distance part is
summed geometrically and the Hankel part is absorbed into a uniform constant.
-/

open scoped BigOperators Matrix

namespace Erdos1131.ChebyshevFirstOrder

open ChebyshevBound

noncomputable section

private abbrev q : ℝ := 1 / 6

def sameParityOffDiag (N : ℕ) (i : Fin (N + 1)) :
    Finset (Fin (N + 1)) :=
  (sameParityIndices N i).erase i

lemma mem_sameParityOffDiag_iff
    {N : ℕ} {i j : Fin (N + 1)} :
    j ∈ sameParityOffDiag N i ↔
      SameParity i.val j.val ∧ j ≠ i := by
  simp [sameParityOffDiag, sameParityIndices, and_comm]

lemma dist_half_pos_of_mem_sameParityOffDiag
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    0 < i.val.dist j.val / 2 := by
  rw [mem_sameParityOffDiag_iff] at hj
  unfold SameParity at hj
  rcases le_total i.val j.val with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    have hne : i.val ≠ j.val := by
      intro h
      apply hj.2
      exact Fin.ext h.symm
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji]
    have hne : i.val ≠ j.val := by
      intro h
      apply hj.2
      exact Fin.ext h.symm
    omega

lemma dist_half_le_add_half_of_sameParity
    {a b : ℕ} (h : SameParity a b) :
    a.dist b / 2 ≤ (a + b) / 2 := by
  unfold SameParity at h
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    omega

lemma chebMoment_nonpos {r : ℕ} (hr : 1 ≤ r) :
    chebMoment r ≤ 0 := by
  unfold chebMoment
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : 1 - 4 * (r : ℝ) ^ 2 < 0 := by nlinarith
  exact div_nonpos_of_nonneg_of_nonpos (by norm_num) hden.le

lemma neg_chebMoment_le_third {r : ℕ} (hr : 1 ≤ r) :
    -chebMoment r ≤ (1 : ℝ) / 3 := by
  unfold chebMoment
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 4 * (r : ℝ) ^ 2 - 1 := by nlinarith
  rw [show -(1 / (1 - 4 * (r : ℝ) ^ 2)) =
      1 / (4 * (r : ℝ) ^ 2 - 1) by
        rw [show 1 - 4 * (r : ℝ) ^ 2 =
          -(4 * (r : ℝ) ^ 2 - 1) by ring]
        simp only [one_div, inv_neg, neg_neg]]
  apply (div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 3)).2
  nlinarith

lemma neg_chebMoment_le_fifteenth {r : ℕ} (hr : 2 ≤ r) :
    -chebMoment r ≤ (1 : ℝ) / 15 := by
  unfold chebMoment
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 4 * (r : ℝ) ^ 2 - 1 := by nlinarith
  rw [show -(1 / (1 - 4 * (r : ℝ) ^ 2)) =
      1 / (4 * (r : ℝ) ^ 2 - 1) by
        rw [show 1 - 4 * (r : ℝ) ^ 2 =
          -(4 * (r : ℝ) ^ 2 - 1) by ring]
        simp only [one_div, inv_neg, neg_neg]]
  apply (div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 15)).2
  nlinarith

lemma neg_chebMoment_le_thirtyFive {r : ℕ} (hr : 3 ≤ r) :
    -chebMoment r ≤ (1 : ℝ) / 35 := by
  unfold chebMoment
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 4 * (r : ℝ) ^ 2 - 1 := by nlinarith
  rw [show -(1 / (1 - 4 * (r : ℝ) ^ 2)) =
      1 / (4 * (r : ℝ) ^ 2 - 1) by
        rw [show 1 - 4 * (r : ℝ) ^ 2 =
          -(4 * (r : ℝ) ^ 2 - 1) by ring]
        simp only [one_div, inv_neg, neg_neg]]
  apply (div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 35)).2
  nlinarith

lemma chebH_offDiag_nonpos
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    chebH N i j ≤ 0 := by
  rw [chebH, if_pos (mem_sameParityOffDiag_iff.mp hj).1]
  apply add_nonpos
  · apply chebMoment_nonpos
    have hr := dist_half_pos_of_mem_sameParityOffDiag hj
    have hs := dist_half_le_add_half_of_sameParity
      (mem_sameParityOffDiag_iff.mp hj).1
    omega
  · exact chebMoment_nonpos
      (dist_half_pos_of_mem_sameParityOffDiag hj)

lemma neg_chebH_offDiag_le_twoThirds
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    -chebH N i j ≤ (2 : ℝ) / 3 := by
  rw [chebH, if_pos (mem_sameParityOffDiag_iff.mp hj).1]
  have hr := dist_half_pos_of_mem_sameParityOffDiag hj
  have hsle := dist_half_le_add_half_of_sameParity
    (mem_sameParityOffDiag_iff.mp hj).1
  have hs : 1 ≤ (i.val + j.val) / 2 := by omega
  linarith [neg_chebMoment_le_third hs,
    neg_chebMoment_le_third (show 1 ≤ i.val.dist j.val / 2 by omega)]

/-- A geometric estimate for the negative Chebyshev moments along any
injectively indexed positive set of distances. -/
lemma sum_neg_chebMoment_mul_pow_le
    {α : Type*}
    (s : Finset α) (e : α → ℕ)
    (hinj : Set.InjOn e s)
    (hpos : ∀ x ∈ s, 1 ≤ e x) :
    (∑ x ∈ s, (-chebMoment (e x)) * q ^ (e x)) ≤
      (13 : ℝ) / 225 := by
  classical
  have hcard :
      (s.filter fun x ↦ e x = 1).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
  have hone :
      (∑ x ∈ s.filter (fun x ↦ e x = 1),
          (-chebMoment (e x)) * q ^ (e x)) ≤
        (1 : ℝ) / 18 := by
    calc
      (∑ x ∈ s.filter (fun x ↦ e x = 1),
          (-chebMoment (e x)) * q ^ (e x)) =
          ∑ _x ∈ s.filter (fun x ↦ e x = 1), (1 : ℝ) / 18 := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Finset.mem_filter] at hx
            rw [hx.2]
            norm_num [chebMoment]
      _ = ((s.filter fun x ↦ e x = 1).card : ℝ) * (1 / 18) := by
        simp
      _ ≤ 1 / 18 := by
        have hcard_real :
            ((s.filter fun x ↦ e x = 1).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard
        nlinarith
  let t := s.filter fun x ↦ e x ≠ 1
  have ht_two : ∀ x ∈ t, 2 ≤ e x := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx)
    exact (show 1 ≤ e x from hpos x hx'.1).lt_of_ne hx'.2.symm
  have htinj : Set.InjOn (fun x ↦ e x - 2) t := by
    intro a ha b hb hab
    apply hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    have ha2 := ht_two a ha
    have hb2 := ht_two b hb
    change e a - 2 = e b - 2 at hab
    calc
      e a = e a - 2 + 2 := (Nat.sub_add_cancel ha2).symm
      _ = e b - 2 + 2 := by rw [hab]
      _ = e b := Nat.sub_add_cancel hb2
  have htailPow :
      (∑ x ∈ t, q ^ (e x)) ≤ (1 : ℝ) / 30 := by
    have hgeom :=
      sum_one_sixth_pow_le t (fun x ↦ e x - 2) htinj
    calc
      (∑ x ∈ t, q ^ (e x)) =
          q ^ 2 * ∑ x ∈ t, q ^ (e x - 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [← pow_add]
            congr 2
            exact (Nat.add_sub_of_le (ht_two x hx)).symm
      _ ≤ q ^ 2 * (6 / 5) := by
        gcongr
      _ = (1 : ℝ) / 30 := by norm_num
  have htail :
      (∑ x ∈ t, (-chebMoment (e x)) * q ^ (e x)) ≤
        (1 : ℝ) / 450 := by
    calc
      (∑ x ∈ t, (-chebMoment (e x)) * q ^ (e x)) ≤
          ∑ x ∈ t, ((1 : ℝ) / 15) * q ^ (e x) := by
            gcongr with x hx
            exact neg_chebMoment_le_fifteenth (ht_two x hx)
      _ = (1 / 15) * ∑ x ∈ t, q ^ (e x) := by
        rw [Finset.mul_sum]
      _ ≤ (1 / 15) * (1 / 30) := by
        gcongr
      _ = (1 : ℝ) / 450 := by norm_num
  rw [← Finset.sum_filter_add_sum_filter_not
    s (fun x ↦ e x = 1)
    (fun x ↦ (-chebMoment (e x)) * q ^ (e x))]
  change
    (∑ x ∈ s.filter (fun x ↦ e x = 1),
        (-chebMoment (e x)) * q ^ (e x)) +
      ∑ x ∈ t, (-chebMoment (e x)) * q ^ (e x) ≤ _
  linarith

lemma sum_dist_pow_offDiag_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityOffDiag N i,
      q ^ (i.val.dist j.val / 2)) ≤ (2 : ℝ) / 5 := by
  have hi : i ∈ sameParityIndices N i := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hsplit := Finset.sum_erase_add
    (sameParityIndices N i)
    (fun j ↦ q ^ (i.val.dist j.val / 2)) hi
  have hfull := sum_dist_div_two_le i
  have hsplit' :
      (∑ j ∈ sameParityOffDiag N i,
        q ^ (i.val.dist j.val / 2)) + 1 =
        ∑ j ∈ sameParityIndices N i,
          q ^ (i.val.dist j.val / 2) := by
    simpa [sameParityOffDiag] using hsplit
  linarith

/-- The distance-dependent negative moment contributes at most `26/225`
in any row before the factor `1/2` from `chebK`. -/
lemma sum_distance_moment_offDiag_le
    {N : ℕ} (i : Fin (N + 1)) :
    (∑ j ∈ sameParityOffDiag N i,
      (-chebMoment (i.val.dist j.val / 2)) *
        q ^ (i.val.dist j.val / 2)) ≤
      (26 : ℝ) / 225 := by
  let left :=
    (sameParityOffDiag N i).filter fun j ↦ j.val ≤ i.val
  let right :=
    (sameParityOffDiag N i).filter fun j ↦ ¬j.val ≤ i.val
  have hleft_inj :
      Set.InjOn (fun j : Fin (N + 1) ↦ i.val.dist j.val / 2) left := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [left, Finset.mem_filter] at ha hb
    apply Fin.ext
    change i.val.dist a.val / 2 = i.val.dist b.val / 2 at hab
    rw [Nat.dist_comm i.val a.val, Nat.dist_eq_sub_of_le ha.2,
      Nat.dist_comm i.val b.val, Nat.dist_eq_sub_of_le hb.2] at hab
    have hpa := (mem_sameParityOffDiag_iff.mp ha.1).1
    have hpb := (mem_sameParityOffDiag_iff.mp hb.1).1
    unfold SameParity at hpa hpb
    omega
  have hright_inj :
      Set.InjOn (fun j : Fin (N + 1) ↦ i.val.dist j.val / 2) right := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [right, Finset.mem_filter] at ha hb
    apply Fin.ext
    have hia : i.val ≤ a.val := Nat.le_of_not_ge ha.2
    have hib : i.val ≤ b.val := Nat.le_of_not_ge hb.2
    change i.val.dist a.val / 2 = i.val.dist b.val / 2 at hab
    rw [Nat.dist_eq_sub_of_le hia, Nat.dist_eq_sub_of_le hib] at hab
    have hpa := (mem_sameParityOffDiag_iff.mp ha.1).1
    have hpb := (mem_sameParityOffDiag_iff.mp hb.1).1
    unfold SameParity at hpa hpb
    omega
  have hleft :=
    sum_neg_chebMoment_mul_pow_le left
      (fun j ↦ i.val.dist j.val / 2) hleft_inj
      (fun j hj ↦ dist_half_pos_of_mem_sameParityOffDiag
        (Finset.mem_filter.mp hj).1)
  have hright :=
    sum_neg_chebMoment_mul_pow_le right
      (fun j ↦ i.val.dist j.val / 2) hright_inj
      (fun j hj ↦ dist_half_pos_of_mem_sameParityOffDiag
        (Finset.mem_filter.mp hj).1)
  rw [← Finset.sum_filter_add_sum_filter_not
    (sameParityOffDiag N i) (fun j ↦ j.val ≤ i.val)
    (fun j ↦ (-chebMoment (i.val.dist j.val / 2)) *
      q ^ (i.val.dist j.val / 2))]
  change
    (∑ j ∈ left,
      (-chebMoment (i.val.dist j.val / 2)) *
        q ^ (i.val.dist j.val / 2)) +
      ∑ j ∈ right,
        (-chebMoment (i.val.dist j.val / 2)) *
          q ^ (i.val.dist j.val / 2) ≤ _
  linarith

lemma sum_halfIndex_pow_le (N : ℕ) :
    (∑ i : Fin (N + 1), q ^ (i.val / 2)) ≤ (12 : ℝ) / 5 := by
  let evens :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ Even i.val
  let odds :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ ¬Even i.val
  have heven_inj :
      Set.InjOn (fun i : Fin (N + 1) ↦ i.val / 2) evens := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [evens, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply Fin.ext
    simp only [Nat.even_iff] at ha hb
    change a.val / 2 = b.val / 2 at hab
    omega
  have hodd_inj :
      Set.InjOn (fun i : Fin (N + 1) ↦ i.val / 2) odds := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [odds, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply Fin.ext
    have ha' : a.val % 2 = 1 :=
      Nat.odd_iff.mp (Nat.not_even_iff_odd.mp ha)
    have hb' : b.val % 2 = 1 :=
      Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hb)
    change a.val / 2 = b.val / 2 at hab
    omega
  have heven := sum_one_sixth_pow_le evens
    (fun i : Fin (N + 1) ↦ i.val / 2) heven_inj
  have hodd := sum_one_sixth_pow_le odds
    (fun i : Fin (N + 1) ↦ i.val / 2) hodd_inj
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (N + 1))) (fun i ↦ Even i.val)
    (fun i ↦ q ^ (i.val / 2))]
  change
    (∑ i ∈ evens, q ^ (i.val / 2)) +
      ∑ i ∈ odds, q ^ (i.val / 2) ≤ _
  linarith

/-- The Hankel geometric factor has uniformly bounded total mass. -/
lemma sum_hankel_pow_offDiag_le (N : ℕ) :
    (∑ i : Fin (N + 1), ∑ j ∈ sameParityOffDiag N i,
      q ^ ((i.val + j.val) / 2)) ≤ (144 : ℝ) / 25 := by
  have hhalf := sum_halfIndex_pow_le N
  have hhalf_nonneg :
      0 ≤ ∑ i : Fin (N + 1), q ^ (i.val / 2) :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  calc
    (∑ i : Fin (N + 1), ∑ j ∈ sameParityOffDiag N i,
        q ^ ((i.val + j.val) / 2)) ≤
        ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
          q ^ (i.val / 2) * q ^ (j.val / 2) := by
      gcongr with i
      calc
        (∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2)) ≤
            ∑ j ∈ sameParityOffDiag N i,
              q ^ (i.val / 2) * q ^ (j.val / 2) := by
          gcongr with j hj
          rw [← pow_add]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ ≤ ∑ j : Fin (N + 1),
              q ^ (i.val / 2) * q ^ (j.val / 2) := by
          exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ by positivity)
    _ = (∑ i : Fin (N + 1), q ^ (i.val / 2)) *
          ∑ j : Fin (N + 1), q ^ (j.val / 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ (144 : ℝ) / 25 := by nlinarith

lemma chebDInvEntry_nonneg (N i : ℕ) :
    0 ≤ chebDInvEntry N i := by
  unfold chebDInvEntry
  split_ifs <;> norm_num

lemma chebDInvEntry_le_one (N i : ℕ) :
    chebDInvEntry N i ≤ 1 := by
  unfold chebDInvEntry
  split_ifs <;> norm_num

lemma chebK_symmetric (N : ℕ) (i j : Fin (N + 1)) :
    chebK N i j = chebK N j i := by
  unfold chebK
  by_cases h : SameParity i.val j.val
  · rw [if_pos h, if_pos (show SameParity j.val i.val from h.symm),
      Nat.add_comm, Nat.dist_comm]
  · rw [if_neg h, if_neg (show ¬SameParity j.val i.val by
      exact fun h' ↦ h h'.symm)]

def traceTerm (N : ℕ) (i j : Fin (N + 1)) : ℝ :=
  chebH N i j * chebDInvEntry N j.val *
    chebK N j i * chebDInvEntry N i.val

lemma traceTerm_offDiag_ge_unweighted
    {N : ℕ} {i j : Fin (N + 1)}
    (hj : j ∈ sameParityOffDiag N i) :
    chebH N i j * chebK N i j ≤ traceTerm N i j := by
  have hH := chebH_offDiag_nonpos hj
  have hK := chebK_nonneg N i j
  have hdj0 := chebDInvEntry_nonneg N j.val
  have hdi0 := chebDInvEntry_nonneg N i.val
  have hdj1 := chebDInvEntry_le_one N j.val
  have hdi1 := chebDInvEntry_le_one N i.val
  have hw0 :
      0 ≤ chebDInvEntry N j.val * chebDInvEntry N i.val :=
    mul_nonneg hdj0 hdi0
  have hw1 :
      chebDInvEntry N j.val * chebDInvEntry N i.val ≤ 1 := by
    calc
      chebDInvEntry N j.val * chebDInvEntry N i.val ≤
          1 * chebDInvEntry N i.val :=
        mul_le_mul_of_nonneg_right hdj1 hdi0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hdi1 (by norm_num)
      _ = 1 := one_mul 1
  have hHK : chebH N i j * chebK N i j ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hH hK
  rw [traceTerm, chebK_symmetric N j i]
  calc
    chebH N i j * chebK N i j =
        (chebH N i j * chebK N i j) * 1 := by ring
    _ ≤ (chebH N i j * chebK N i j) *
          (chebDInvEntry N j.val * chebDInvEntry N i.val) :=
      mul_le_mul_of_nonpos_left hw1 hHK
    _ = chebH N i j * chebDInvEntry N j.val *
          chebK N i j * chebDInvEntry N i.val := by ring

lemma neg_chebH_mul_chebK_tail_row_le
    {N : ℕ} (i : Fin (N + 1)) (hi : 6 ≤ i.val) :
    (∑ j ∈ sameParityOffDiag N i,
      -(chebH N i j * chebK N i j)) ≤
      (1 : ℝ) / 15 +
        (1 / 3) *
          ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) := by
  have hdist := sum_distance_moment_offDiag_le i
  have hqdist := sum_dist_pow_offDiag_le i
  calc
    (∑ j ∈ sameParityOffDiag N i,
      -(chebH N i j * chebK N i j)) ≤
        ∑ j ∈ sameParityOffDiag N i,
          (1 / 2 : ℝ) *
            ((-chebMoment (i.val.dist j.val / 2)) *
                q ^ (i.val.dist j.val / 2) +
              (1 / 35) * q ^ (i.val.dist j.val / 2) +
              (2 / 3) * q ^ ((i.val + j.val) / 2)) := by
      gcongr with j hj
      have hp := (mem_sameParityOffDiag_iff.mp hj).1
      have hr := dist_half_pos_of_mem_sameParityOffDiag hj
      have hrs := dist_half_le_add_half_of_sameParity hp
      have hs : 3 ≤ (i.val + j.val) / 2 := by
        have : 3 ≤ i.val / 2 := by omega
        omega
      have has := neg_chebMoment_le_thirtyFive hs
      have har := neg_chebMoment_le_third (show 1 ≤ i.val.dist j.val / 2 by omega)
      have hqs : 0 ≤ q ^ ((i.val + j.val) / 2) := by positivity
      have hqr : 0 ≤ q ^ (i.val.dist j.val / 2) := by positivity
      rw [chebH, if_pos hp, chebK, if_pos hp]
      have h₁ :
          (-chebMoment ((i.val + j.val) / 2)) *
              q ^ (i.val.dist j.val / 2) ≤
            (1 / 35) * q ^ (i.val.dist j.val / 2) :=
        mul_le_mul_of_nonneg_right has hqr
      have h₂ :
          ((-chebMoment (i.val.dist j.val / 2)) +
              (-chebMoment ((i.val + j.val) / 2))) *
              q ^ ((i.val + j.val) / 2) ≤
            (2 / 3) * q ^ ((i.val + j.val) / 2) := by
        apply mul_le_mul_of_nonneg_right _ hqs
        linarith
      norm_num only [q]
      nlinarith
    _ = (1 / 2 : ℝ) *
          ((∑ j ∈ sameParityOffDiag N i,
              (-chebMoment (i.val.dist j.val / 2)) *
                q ^ (i.val.dist j.val / 2)) +
            (1 / 35) *
              ∑ j ∈ sameParityOffDiag N i,
                q ^ (i.val.dist j.val / 2) +
            (2 / 3) *
              ∑ j ∈ sameParityOffDiag N i,
                q ^ ((i.val + j.val) / 2)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) *
          ((26 / 225 : ℝ) + (1 / 35) * (2 / 5) +
            (2 / 3) *
              ∑ j ∈ sameParityOffDiag N i,
                q ^ ((i.val + j.val) / 2)) := by
      gcongr
    _ ≤ (1 : ℝ) / 15 +
        (1 / 3) *
          ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) := by
      have hq :
          0 ≤ ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) :=
        Finset.sum_nonneg fun _ _ ↦ by positivity
      nlinarith

lemma offDiagRow_ge_of_six_le
    {N : ℕ} (i : Fin (N + 1)) (hi : 6 ≤ i.val) :
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
      -(1 : ℝ) / 15 -
        (1 / 3) *
          ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) := by
  have hterm :
      ∑ j ∈ sameParityOffDiag N i,
          chebH N i j * chebK N i j ≤
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j := by
    gcongr with j hj
    exact traceTerm_offDiag_ge_unweighted hj
  have hneg := neg_chebH_mul_chebK_tail_row_le i hi
  have hneg' :
      -(∑ j ∈ sameParityOffDiag N i,
          chebH N i j * chebK N i j) ≤
        (1 : ℝ) / 15 +
          (1 / 3) *
            ∑ j ∈ sameParityOffDiag N i,
              q ^ ((i.val + j.val) / 2) := by
    simpa only [Finset.sum_neg_distrib] using hneg
  linarith

lemma offDiagRow_ge_of_lt_six
    {N : ℕ} (i : Fin (N + 1)) (_hi : i.val < 6) :
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
      -(13 : ℝ) / 15 := by
  have hKsum :
      (∑ j ∈ sameParityOffDiag N i, chebK N i j) ≤
        (13 : ℝ) / 10 := by
    calc
      (∑ j ∈ sameParityOffDiag N i, chebK N i j) ≤
          ∑ j : Fin (N + 1), chebK N i j :=
        Finset.sum_le_univ_sum_of_nonneg (chebK_nonneg N i)
      _ = absRowSum (chebK N) i := by
        rw [absRowSum]
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (chebK_nonneg N i j)]
      _ ≤ (13 : ℝ) / 10 := rowBound_chebK N i
  calc
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
        ∑ j ∈ sameParityOffDiag N i,
          (-(2 : ℝ) / 3) * chebK N i j := by
      gcongr with j hj
      calc
        (-(2 : ℝ) / 3) * chebK N i j ≤
            chebH N i j * chebK N i j := by
          apply mul_le_mul_of_nonneg_right _ (chebK_nonneg N i j)
          linarith [neg_chebH_offDiag_le_twoThirds hj]
        _ ≤ traceTerm N i j := traceTerm_offDiag_ge_unweighted hj
    _ = (-(2 : ℝ) / 3) *
          ∑ j ∈ sameParityOffDiag N i, chebK N i j := by
      rw [Finset.mul_sum]
    _ ≥ -(13 : ℝ) / 15 := by nlinarith

lemma total_offDiag_ge (N : ℕ) :
    (∑ i : Fin (N + 1),
      ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
      -((N + 1 : ℕ) : ℝ) / 15 - 26 / 5 - 48 / 25 := by
  let early :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ i.val < 6
  let late :=
    (Finset.univ : Finset (Fin (N + 1))).filter fun i ↦ ¬i.val < 6
  have hearly_card : early.card ≤ 6 := by
    have hcard := Finset.card_le_card_of_injOn
      (s := early) (t := Finset.range 6) (fun i : Fin (N + 1) ↦ i.val)
      (by
        intro i hi
        simp only [early, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and] at hi
        exact Finset.mem_range.mpr hi)
      (by
        intro a _ b _ hab
        exact Fin.ext hab)
    simpa using hcard
  have hearly :
      (∑ i ∈ early,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
        -(26 : ℝ) / 5 := by
    calc
      (∑ i ∈ early,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
          ∑ _i ∈ early, (-(13 : ℝ) / 15) := by
        gcongr with i hi
        exact offDiagRow_ge_of_lt_six i
          (Finset.mem_filter.mp hi).2
      _ = (early.card : ℝ) * (-(13 : ℝ) / 15) := by simp
      _ ≥ -(26 : ℝ) / 5 := by
        have hc : (early.card : ℝ) ≤ 6 := by exact_mod_cast hearly_card
        nlinarith
  have hlate_card : late.card ≤ N + 1 :=
    (Finset.card_filter_le _ _).trans_eq (by simp)
  have hlate_q :
      (∑ i ∈ late, ∑ j ∈ sameParityOffDiag N i,
        q ^ ((i.val + j.val) / 2)) ≤ (144 : ℝ) / 25 := by
    calc
      (∑ i ∈ late, ∑ j ∈ sameParityOffDiag N i,
        q ^ ((i.val + j.val) / 2)) ≤
          ∑ i : Fin (N + 1), ∑ j ∈ sameParityOffDiag N i,
            q ^ ((i.val + j.val) / 2) :=
        Finset.sum_le_univ_sum_of_nonneg
          (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity)
      _ ≤ (144 : ℝ) / 25 := sum_hankel_pow_offDiag_le N
  have hlate :
      (∑ i ∈ late,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
        -((N + 1 : ℕ) : ℝ) / 15 - 48 / 25 := by
    calc
      (∑ i ∈ late,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥
          ∑ i ∈ late,
            (-(1 : ℝ) / 15 -
              (1 / 3) *
                ∑ j ∈ sameParityOffDiag N i,
                  q ^ ((i.val + j.val) / 2)) := by
        gcongr with i hi
        apply offDiagRow_ge_of_six_le
        have := (Finset.mem_filter.mp hi).2
        omega
      _ = (late.card : ℝ) * (-(1 : ℝ) / 15) -
          (1 / 3) *
            ∑ i ∈ late, ∑ j ∈ sameParityOffDiag N i,
              q ^ ((i.val + j.val) / 2) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul, ← Finset.mul_sum]
      _ ≥ -((N + 1 : ℕ) : ℝ) / 15 - 48 / 25 := by
        have hc : (late.card : ℝ) ≤ (N + 1 : ℕ) := by
          exact_mod_cast hlate_card
        nlinarith
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (N + 1))) (fun i ↦ i.val < 6)
    (fun i ↦ ∑ j ∈ sameParityOffDiag N i, traceTerm N i j)]
  change
    (∑ i ∈ early,
      ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) +
      (∑ i ∈ late,
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j) ≥ _
  linarith

def interiorIndices (N : ℕ) : Finset (Fin (N + 1)) :=
  ((Finset.univ : Finset (Fin (N + 1))).erase 0).erase (Fin.last N)

lemma interiorIndices_card
    {N : ℕ} (hN : 0 < N) :
    (interiorIndices N).card = N - 1 := by
  have hlast :
      Fin.last N ∈
        (Finset.univ : Finset (Fin (N + 1))).erase 0 := by
    simp [Fin.last, hN.ne']
  rw [interiorIndices, Finset.card_erase_of_mem hlast,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (N + 1)))]
  simp

lemma mem_interiorIndices
    {N : ℕ} {i : Fin (N + 1)}
    (hi : i ∈ interiorIndices N) :
    0 < i.val ∧ i.val < N := by
  simp only [interiorIndices, Finset.mem_erase, Finset.mem_univ,
    and_true] at hi
  have hi0 : i.val ≠ 0 := by
    intro h
    apply hi.2
    exact Fin.ext h
  have hiN : i.val ≠ N := by
    intro h
    apply hi.1
    exact Fin.ext h
  omega

lemma sum_chebMoment_interior_ge
    {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ interiorIndices N, chebMoment i.val) ≥
      -(1 : ℝ) / 2 := by
  have hlast :
      Fin.last N ∈
        (Finset.univ : Finset (Fin (N + 1))).erase 0 := by
    simp [Fin.last, hN.ne']
  have hzero := Finset.sum_erase_add
    (Finset.univ : Finset (Fin (N + 1)))
    (fun i ↦ chebMoment i.val)
    (Finset.mem_univ (0 : Fin (N + 1)))
  have hlastSum := Finset.sum_erase_add
    ((Finset.univ : Finset (Fin (N + 1))).erase 0)
    (fun i ↦ chebMoment i.val) hlast
  have hfull := sum_chebMoment_fin N
  have hsum :
      (∑ i ∈ interiorIndices N, chebMoment i.val) =
        -(N : ℝ) / (2 * N + 1) - chebMoment N := by
    change
      (∑ i ∈
        ((Finset.univ : Finset (Fin (N + 1))).erase 0).erase
          (Fin.last N), chebMoment i.val) =
        -(N : ℝ) / (2 * N + 1) - chebMoment N
    simp only [Fin.val_zero, Fin.val_last] at hzero hlastSum
    rw [chebMoment_zero] at hzero
    have hzero' :
        (∑ x ∈ (Finset.univ : Finset (Fin (N + 1))).erase 0,
          chebMoment x.val) =
          (∑ x : Fin (N + 1), chebMoment x.val) - 1 :=
      eq_sub_of_add_eq hzero
    have hlast' :
        (∑ x ∈
          ((Finset.univ : Finset (Fin (N + 1))).erase 0).erase
            (Fin.last N), chebMoment x.val) =
          (∑ x ∈ (Finset.univ : Finset (Fin (N + 1))).erase 0,
            chebMoment x.val) - chebMoment N :=
      eq_sub_of_add_eq hlastSum
    rw [hlast', hzero', hfull]
    ring
  rw [hsum]
  have hmN : chebMoment N ≤ 0 := chebMoment_nonpos hN
  have hden : (0 : ℝ) < 2 * N + 1 := by positivity
  have hfrac : (N : ℝ) / (2 * N + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hnegfrac :
      -(1 : ℝ) / 2 ≤ -(N : ℝ) / (2 * N + 1) := by
    simpa only [neg_div] using neg_le_neg hfrac
  linarith

lemma chebK_diag (N : ℕ) (i : Fin (N + 1)) :
    chebK N i i = (q ^ i.val + 1) / 2 := by
  rw [chebK, if_pos (show SameParity i.val i.val from rfl),
    Nat.dist_self, Nat.zero_div]
  have hii : (i.val + i.val) / 2 = i.val := by omega
  rw [hii, pow_zero]

lemma traceTerm_diag_nonneg (N : ℕ) (i : Fin (N + 1)) :
    0 ≤ traceTerm N i i := by
  have hH : 0 ≤ chebH N i i := by
    rw [chebH_diag]
    by_cases hi : i.val = 0
    · rw [hi, chebMoment_zero]
      norm_num
    · have hi1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
      linarith [neg_chebMoment_le_third hi1]
  have hK := chebK_nonneg N i i
  have hd := chebDInvEntry_nonneg N i.val
  rw [traceTerm]
  positivity

lemma traceTerm_diag_ge
    {N : ℕ} {i : Fin (N + 1)}
    (hi : i ∈ interiorIndices N) :
    traceTerm N i i ≥ (1 + chebMoment i.val) / 2 := by
  have hi' := mem_interiorIndices hi
  have hi0 : i.val ≠ 0 := Nat.ne_of_gt hi'.1
  have hiN : i.val ≠ N := ne_of_lt hi'.2
  have hd : chebDInvEntry N i.val = 1 := by
    simp [chebDInvEntry, hi0, hiN]
  have hH : 0 ≤ 1 + chebMoment i.val := by
    linarith [neg_chebMoment_le_third hi'.1]
  have hK : (1 : ℝ) / 2 ≤ chebK N i i := by
    rw [chebK_diag]
    have : 0 ≤ q ^ i.val := by positivity
    linarith
  rw [traceTerm, hd, chebH_diag]
  simp only [mul_one]
  have hmul := mul_le_mul_of_nonneg_left hK hH
  nlinarith

lemma total_diag_ge
    {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin (N + 1), traceTerm N i i) ≥
      (N : ℝ) / 2 - 3 / 4 := by
  have hcard := interiorIndices_card hN
  have hmom := sum_chebMoment_interior_ge hN
  calc
    (∑ i : Fin (N + 1), traceTerm N i i) ≥
        ∑ i ∈ interiorIndices N, traceTerm N i i :=
      Finset.sum_le_univ_sum_of_nonneg (traceTerm_diag_nonneg N)
    _ ≥ ∑ i ∈ interiorIndices N,
        (1 + chebMoment i.val) / 2 := by
      gcongr with i hi
      exact traceTerm_diag_ge hi
    _ = ((interiorIndices N).card : ℝ) / 2 +
          (∑ i ∈ interiorIndices N, chebMoment i.val) / 2 := by
      simp only [add_div, Finset.sum_add_distrib, Finset.sum_div,
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≥ (N : ℝ) / 2 - 3 / 4 := by
      have hc : ((interiorIndices N).card : ℝ) = (N - 1 : ℕ) := by
        exact_mod_cast hcard
      rw [hc]
      have hNcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN]
        norm_num
      rw [hNcast]
      linarith

lemma chebDInv_mul_chebK_apply
    (N : ℕ) (j i : Fin (N + 1)) :
    (chebDInv N * chebK N) j i =
      chebDInvEntry N j.val * chebK N j i := by
  classical
  rw [chebDInv, Matrix.mul_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · simp

lemma chebDInv_mul_chebK_mul_chebDInv_apply
    (N : ℕ) (j i : Fin (N + 1)) :
    (chebDInv N * chebK N * chebDInv N) j i =
      chebDInvEntry N j.val * chebK N j i *
        chebDInvEntry N i.val := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [chebDInv_mul_chebK_apply]
    simp [chebDInv]
  · intro b _ hb
    simp [chebDInv, hb]
  · simp

lemma trace_eq_sum_traceTerm (N : ℕ) :
    Matrix.trace
      (chebH N * (chebDInv N * chebK N * chebDInv N)) =
        ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), traceTerm N i j := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  change
    (chebH N * (chebDInv N * chebK N * chebDInv N)) i i =
      ∑ j : Fin (N + 1), traceTerm N i j
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [traceTerm, chebDInv_mul_chebK_mul_chebDInv_apply]
  ring

lemma traceTerm_zero_of_not_sameParity
    {N : ℕ} {i j : Fin (N + 1)}
    (h : ¬SameParity i.val j.val) :
    traceTerm N i j = 0 := by
  rw [traceTerm, chebH, if_neg h]
  ring

lemma sum_traceTerm_row_eq_diag_add_offDiag
    (N : ℕ) (i : Fin (N + 1)) :
    (∑ j : Fin (N + 1), traceTerm N i j) =
      traceTerm N i i +
        ∑ j ∈ sameParityOffDiag N i, traceTerm N i j := by
  have hi : i ∈ sameParityIndices N i := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hrestrict :
      (∑ j ∈ sameParityIndices N i, traceTerm N i j) =
        ∑ j : Fin (N + 1), traceTerm N i j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply traceTerm_zero_of_not_sameParity
    simpa [sameParityIndices] using hj
  have herase := Finset.sum_erase_add
    (sameParityIndices N i) (fun j ↦ traceTerm N i j) hi
  change
    (∑ j ∈ sameParityOffDiag N i, traceTerm N i j) +
      traceTerm N i i =
        ∑ j ∈ sameParityIndices N i, traceTerm N i j at herase
  rw [← hrestrict] at *
  linarith

lemma trace_eq_diag_add_offDiag (N : ℕ) :
    Matrix.trace
      (chebH N * (chebDInv N * chebK N * chebDInv N)) =
        (∑ i : Fin (N + 1), traceTerm N i i) +
          ∑ i : Fin (N + 1),
            ∑ j ∈ sameParityOffDiag N i, traceTerm N i j := by
  rw [trace_eq_sum_traceTerm]
  simp_rw [sum_traceTerm_row_eq_diag_add_offDiag]
  exact Finset.sum_add_distrib

/-- The finite first-order trace bound needed in the Chebyshev comparison. -/
theorem trace_firstOrder_lower_bound
    {N : ℕ} (hN : 6 ≤ N) :
    (13 : ℝ) * (N : ℝ) / 30 - 13 ≤
      Matrix.trace
        (chebH N * (chebDInv N * chebK N * chebDInv N)) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hdiag := total_diag_ge hNpos
  have hoff := total_offDiag_ge N
  rw [trace_eq_diag_add_offDiag]
  push_cast at hoff
  linarith

end

end Erdos1131.ChebyshevFirstOrder

end PortChebyshevFirstOrder

-- Original: Erdos1131/ChebyshevResolvent.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/ChebyshevResolvent.lean; SHA-256 97c57fcfdaf7b6c0df7ba2fd0259939aa625ea1ee051278e95b32f646eaf151c
section PortChebyshevResolvent

                          

/-!
# Exact resolvent algebra for the Chebyshev comparison matrix

This file separates the non-asymptotic matrix identities from both the root
calculation and the numerical estimates.  The model Gram matrix is

`R_N = (N / 2) D_N + K_N`,

where `D_N = diag (2, 1, ..., 1, 7/6)`.  Factoring out its diagonal part gives
the relative perturbation `chebY`; the inverse is then expanded through second
order with the exact remainder already estimated in `ChebyshevBound`.
-/

open scoped BigOperators

namespace Erdos1131.ChebyshevResolvent

open ChebyshevBound

noncomputable section

def chebDEntry (N i : ℕ) : ℝ :=
  if i = 0 then 2 else if i = N then 7 / 6 else 1

def chebD (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal fun i => chebDEntry N i

def modelGram (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ((N : ℝ) / 2) • chebD N + chebK N

theorem chebDEntry_mul_chebDInvEntry
    {N : ℕ} (hN : 0 < N) (i : ℕ) :
    chebDEntry N i * chebDInvEntry N i = 1 := by
  by_cases hi0 : i = 0
  · simp [chebDEntry, chebDInvEntry, hi0]
  · by_cases hiN : i = N
    · subst i
      simp [chebDEntry, chebDInvEntry, hN.ne']
    · simp [chebDEntry, chebDInvEntry, hi0, hiN]

theorem chebD_mul_chebDInv
    {N : ℕ} (hN : 0 < N) :
    chebD N * chebDInv N = 1 := by
  rw [chebD, chebDInv, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [chebDEntry_mul_chebDInvEntry hN]
  · simp [hij]

theorem chebDInv_mul_chebD
    {N : ℕ} (hN : 0 < N) :
    chebDInv N * chebD N = 1 := by
  rw [chebD, chebDInv, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [mul_comm]
    exact chebDEntry_mul_chebDInvEntry hN i
  · simp [hij]

theorem modelGram_factor
    {N : ℕ} (hN : 0 < N) :
    modelGram N =
      (((N : ℝ) / 2) • chebD N) * (1 + chebY N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [modelGram, chebY, Matrix.mul_add, Matrix.mul_one]
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
    chebD_mul_chebDInv hN, Matrix.one_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem scaledChebD_mul_scaledChebDInv
    {N : ℕ} (hN : 0 < N) :
    (((N : ℝ) / 2) • chebD N) *
        ((2 / (N : ℝ)) • chebDInv N) = 1 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Matrix.smul_mul, Matrix.mul_smul, chebD_mul_chebDInv hN]
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> field_simp

theorem inv_scaledChebD
    {N : ℕ} (hN : 0 < N) :
    (((N : ℝ) / 2) • chebD N)⁻¹ =
      (2 / (N : ℝ)) • chebDInv N :=
  Matrix.inv_eq_right_inv (scaledChebD_mul_scaledChebDInv hN)

theorem isUnit_one_add_chebY_of_modelGram
    {N : ℕ} (hN : 0 < N)
    (hunit : IsUnit (modelGram N).det) :
    IsUnit (1 + chebY N).det := by
  have hne : (modelGram N).det ≠ 0 := by
    simpa only [isUnit_iff_ne_zero] using hunit
  rw [modelGram_factor hN, Matrix.det_mul] at hne
  have hright : (1 + chebY N).det ≠ 0 := fun h =>
    hne (by simp [h])
  simpa only [isUnit_iff_ne_zero] using hright

theorem chebZ_second_order
    {N : ℕ} (hunit : IsUnit (1 + chebY N).det) :
    chebZ N = 1 - chebY N +
      chebY N * chebY N * chebZ N := by
  have hfirst := chebZ_eq_one_sub_mul hunit
  calc
    chebZ N = 1 - chebY N * chebZ N := hfirst
    _ = 1 - chebY N * (1 - chebY N * chebZ N) := by
      exact congrArg (fun Z => 1 - chebY N * Z) hfirst
    _ = 1 - chebY N + chebY N * chebY N * chebZ N := by
      noncomm_ring

theorem inv_modelGram
    {N : ℕ} (hN : 0 < N) :
    (modelGram N)⁻¹ =
      chebZ N * ((2 / (N : ℝ)) • chebDInv N) := by
  rw [modelGram_factor hN, Matrix.mul_inv_rev, inv_scaledChebD hN, chebZ]

theorem chebY_mul_scaledChebDInv
    {N : ℕ} (hN : 0 < N) :
    chebY N * ((2 / (N : ℝ)) • chebDInv N) =
      (4 / (N : ℝ) ^ 2) •
        (chebDInv N * chebK N * chebDInv N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [chebY, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem inv_modelGram_second_order
    {N : ℕ} (hN : 0 < N)
    (hunit : IsUnit (modelGram N).det) :
    (modelGram N)⁻¹ =
      (2 / (N : ℝ)) • chebDInv N -
        (4 / (N : ℝ) ^ 2) •
          (chebDInv N * chebK N * chebDInv N) +
        chebInverseRemainder N := by
  have hunitY := isUnit_one_add_chebY_of_modelGram hN hunit
  rw [inv_modelGram hN, chebZ_second_order hunitY]
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
    chebY_mul_scaledChebDInv hN]
  simp only [chebInverseRemainder, Matrix.mul_assoc]

end

end Erdos1131.ChebyshevResolvent

end PortChebyshevResolvent

-- Original: Erdos1131/ChebyshevRootSums.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/ChebyshevRootSums.lean; SHA-256 38a98e972e765e8baf23f80102c3093a064cc611055f0f7761f349e67cf57652
section PortChebyshevRootSums

                           

/-!
# Root sums for the explicit Chebyshev comparison nodes

This file identifies the roots of `chebQ` with the chosen real nodes and
computes the Chebyshev moments of those roots.
-/

open scoped BigOperators

namespace Erdos1131

open Polynomial Polynomial.Chebyshev

private noncomputable def chebNodeMultiset {n : ℕ} (hn : 2 ≤ n) : Multiset ℝ :=
  Finset.univ.1.map (chebNodes n hn)

private theorem chebNodeMultiset_nodup {n : ℕ} (hn : 2 ≤ n) :
    (chebNodeMultiset hn).Nodup := by
  exact Finset.univ.2.map (chebNodes n hn).injective

private theorem chebNodeMultiset_le_roots {n : ℕ} (hn : 2 ≤ n) :
    chebNodeMultiset hn ≤ (chebQ n).roots := by
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : x ∈ chebNodeMultiset hn
  · have hcount_left : (chebNodeMultiset hn).count x = 1 :=
      Multiset.count_eq_one_of_mem (chebNodeMultiset_nodup hn) hx
    rw [hcount_left]
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx
    exact (Multiset.one_le_count_iff_mem.mpr
      ((Polynomial.mem_roots (chebQ_ne_zero hn)).mpr (chebNodes_isRoot hn k)))
  · simp [Multiset.count_eq_zero.mpr hx]

/-- The multiset of roots of `chebQ n` is exactly the multiset of the `n`
chosen comparison nodes. -/
theorem chebQ_roots_eq_nodes {n : ℕ} (hn : 2 ≤ n) :
    (chebQ n).roots = chebNodeMultiset hn := by
  symm
  apply Multiset.eq_of_le_of_card_le (chebNodeMultiset_le_roots hn)
  calc
    (chebQ n).roots.card ≤ (chebQ n).natDegree :=
      Polynomial.card_roots' (chebQ n)
    _ = n := by
      exact (Polynomial.degree_eq_iff_natDegree_eq (chebQ_ne_zero hn)).mp
        (degree_chebQ hn)
    _ = (chebNodeMultiset hn).card := by
      simp [chebNodeMultiset]

private theorem chebQ_splits {n : ℕ} (hn : 2 ≤ n) :
    (chebQ n).Splits := by
  rw [Polynomial.splits_iff_card_roots, chebQ_roots_eq_nodes hn]
  simp [chebNodeMultiset,
    (Polynomial.degree_eq_iff_natDegree_eq (chebQ_ne_zero hn)).mp (degree_chebQ hn)]

private theorem chebQ_leadingCoeff {n : ℕ} (hn : 2 ≤ n) :
    (chebQ n).leadingCoeff = (2 : ℝ) ^ (n - 1) := by
  rw [chebQ, Polynomial.leadingCoeff_sub_of_degree_lt]
  · simp
  · calc
      (Polynomial.C ((1 : ℝ) / 6) * T ℝ ((n - 2 : ℕ) : ℤ)).degree
          = (T ℝ ((n - 2 : ℕ) : ℤ)).degree := by
              rw [Polynomial.degree_C_mul (by norm_num)]
      _ = (n - 2 : ℕ) := by simp
      _ < (n : WithBot ℕ) := by
        exact_mod_cast Nat.sub_lt (by omega) (by omega)
      _ = (T ℝ (n : ℤ)).degree := (degree_T ℝ n).symm

/-- The reciprocal polynomial whose power sums encode the Chebyshev root
sums of `chebQ`. -/
private noncomputable def liftedChebQ (n : ℕ) : ℝ[X] :=
  Polynomial.X ^ (2 * n) -
    Polynomial.C ((1 : ℝ) / 6) * Polynomial.X ^ (2 * n - 2) -
      Polynomial.C ((1 : ℝ) / 6) * Polynomial.X ^ 2 + 1

/-- Product of the reciprocal quadratics attached to the comparison nodes. -/
private noncomputable def chebQuadraticProduct {n : ℕ} (hn : 2 ≤ n) : ℝ[X] :=
  ∏ i : Fin n,
    (Polynomial.X ^ 2 -
      Polynomial.C (2 * chebNodes n hn i) * Polynomial.X + 1)

private theorem T_eval_half_add_inv (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (T ℝ (m : ℤ)).eval ((t + t⁻¹) / 2) =
      (t ^ m + t⁻¹ ^ m) / 2 := by
  induction m using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num [T_one]
  | more m hm hm1 =>
      rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega, T_add_two,
        Polynomial.eval_sub, Polynomial.eval_mul]
      rw [← Polynomial.C_ofNat, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      change
        (2 * ((t + t⁻¹) / 2)) *
              (T ℝ ((m : ℤ) + 1)).eval ((t + t⁻¹) / 2) -
            (T ℝ (m : ℤ)).eval ((t + t⁻¹) / 2) =
          (t ^ (m + 2) + t⁻¹ ^ (m + 2)) / 2
      rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega, hm1, hm]
      simp only [inv_pow]
      field_simp [ht, pow_succ]
      ring

private theorem chebQuadraticProduct_eval_zero {n : ℕ} (hn : 2 ≤ n) :
    (chebQuadraticProduct hn).eval 0 = 1 := by
  simp [chebQuadraticProduct, Polynomial.eval_prod]

private theorem liftedChebQ_eval_zero {n : ℕ} (hn : 2 ≤ n) :
    (liftedChebQ n).eval 0 = 1 := by
  have htop : 2 * n ≠ 0 := by omega
  have hnext : 2 * n - 2 ≠ 0 := by omega
  simp [liftedChebQ, htop, hnext]

private theorem chebQ_eval_eq_prod_nodes {n : ℕ} (hn : 2 ≤ n) (y : ℝ) :
    (chebQ n).eval y =
      (2 : ℝ) ^ (n - 1) * ∏ i : Fin n, (y - chebNodes n hn i) := by
  rw [(chebQ_splits hn).eval_eq_prod_roots, chebQ_leadingCoeff hn,
    chebQ_roots_eq_nodes hn]
  simp [chebNodeMultiset, Function.comp_def,
    Finset.prod_eq_multiset_prod]

private theorem chebQuadraticProduct_eval_eq_chebQ
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ≠ 0) :
    (chebQuadraticProduct hn).eval t =
      2 * t ^ n * (chebQ n).eval ((t + t⁻¹) / 2) := by
  let y : ℝ := (t + t⁻¹) / 2
  have hfactor (i : Fin n) :
      t ^ 2 - (2 * chebNodes n hn i) * t + 1 =
        (2 * t) * (y - chebNodes n hn i) := by
    dsimp [y]
    field_simp [ht]
    ring
  rw [chebQ_eval_eq_prod_nodes hn]
  simp only [chebQuadraticProduct, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_pow]
  have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    nth_rw 1 [show n = (n - 1) + 1 by omega]
    rw [pow_add]
    ring
  rw [hpow]
  ring

private theorem pow_mul_inv_pow_eq_one {t : ℝ} (ht : t ≠ 0) (m : ℕ) :
    t ^ m * t⁻¹ ^ m = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]

private theorem pow_mul_inv_pow_sub_two {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : t ≠ 0) :
    t ^ n * t⁻¹ ^ (n - 2) = t ^ 2 := by
  nth_rw 1 [← Nat.sub_add_cancel hn]
  rw [pow_add]
  calc
    t ^ (n - 2) * t ^ 2 * t⁻¹ ^ (n - 2) =
        (t ^ (n - 2) * t⁻¹ ^ (n - 2)) * t ^ 2 := by ring
    _ = t ^ 2 := by rw [pow_mul_inv_pow_eq_one ht, one_mul]

private theorem pow_mul_pow_sub_two {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    t ^ n * t ^ (n - 2) = t ^ (2 * n - 2) := by
  rw [← pow_add]
  congr 1
  omega

private theorem chebQuadraticProduct_eval_ne_zero
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ≠ 0) :
    (chebQuadraticProduct hn).eval t = (liftedChebQ n).eval t := by
  rw [chebQuadraticProduct_eval_eq_chebQ hn ht, chebQ_eval,
    T_eval_half_add_inv n ht, T_eval_half_add_inv (n - 2) ht]
  simp only [liftedChebQ, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  have hsquare : t ^ n * t ^ n = t ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    2 * t ^ n * ((t ^ n + t⁻¹ ^ n) / 2 -
          1 / 6 * ((t ^ (n - 2) + t⁻¹ ^ (n - 2)) / 2)) =
        t ^ n * t ^ n + t ^ n * t⁻¹ ^ n -
          (1 / 6) * (t ^ n * t ^ (n - 2)) -
            (1 / 6) * (t ^ n * t⁻¹ ^ (n - 2)) := by ring
    _ = t ^ (2 * n) + 1 -
          (1 / 6) * t ^ (2 * n - 2) - (1 / 6) * t ^ 2 := by
      rw [hsquare, pow_mul_inv_pow_eq_one ht,
        pow_mul_pow_sub_two hn, pow_mul_inv_pow_sub_two hn ht]
    _ = t ^ (2 * n) - 1 / 6 * t ^ (2 * n - 2) -
          1 / 6 * t ^ 2 + 1 := by ring

/-- The reciprocal quadratic product is the sparse reciprocal polynomial
associated to `chebQ`. -/
private theorem chebQuadraticProduct_eq_liftedChebQ
    {n : ℕ} (hn : 2 ≤ n) :
    chebQuadraticProduct hn = liftedChebQ n := by
  apply Polynomial.funext
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [chebQuadraticProduct_eval_zero hn, liftedChebQ_eval_zero hn]
  · exact chebQuadraticProduct_eval_ne_zero hn ht

private noncomputable def complexQuadratic (x : ℝ) : ℂ[X] :=
  Polynomial.X ^ 2 -
    Polynomial.C (2 * (x : ℂ)) * Polynomial.X + Polynomial.C 1

private theorem complexQuadratic_eq_quadratic (x : ℝ) :
    complexQuadratic x =
      Polynomial.C (1 : ℂ) * Polynomial.X ^ 2 +
        Polynomial.C (-2 * (x : ℂ)) * Polynomial.X +
          Polynomial.C 1 := by
  simp [complexQuadratic]
  ring

private theorem complexQuadratic_natDegree (x : ℝ) :
    (complexQuadratic x).natDegree = 2 := by
  rw [complexQuadratic_eq_quadratic]
  exact Polynomial.natDegree_quadratic one_ne_zero

private theorem complexQuadratic_ne_zero (x : ℝ) :
    complexQuadratic x ≠ 0 := by
  intro h
  have := complexQuadratic_natDegree x
  simp [h] at this

private theorem complexQuadratic_leadingCoeff (x : ℝ) :
    (complexQuadratic x).leadingCoeff = 1 := by
  rw [complexQuadratic_eq_quadratic]
  exact Polynomial.leadingCoeff_quadratic one_ne_zero

private theorem complexQuadratic_roots_card (x : ℝ) :
    (complexQuadratic x).roots.card = 2 := by
  rw [← (IsAlgClosed.splits (complexQuadratic x)).natDegree_eq_card_roots,
    complexQuadratic_natDegree]

private noncomputable def quadraticRootPowerSum (x : ℝ) (m : ℕ) : ℂ :=
  ((complexQuadratic x).roots.map fun z ↦ z ^ m).sum

private theorem quadraticRootPowerSum_zero (x : ℝ) :
    quadraticRootPowerSum x 0 = 2 := by
  simp [quadraticRootPowerSum, complexQuadratic_roots_card]
  norm_num

private theorem complexQuadratic_nextCoeff (x : ℝ) :
    (complexQuadratic x).nextCoeff = -2 * (x : ℂ) := by
  rw [Polynomial.nextCoeff, complexQuadratic_natDegree,
    complexQuadratic_eq_quadratic]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  norm_num

private theorem quadraticRootPowerSum_one (x : ℝ) :
    quadraticRootPowerSum x 1 = 2 * (x : ℂ) := by
  have h := (IsAlgClosed.splits (complexQuadratic x)).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [complexQuadratic_nextCoeff, complexQuadratic_leadingCoeff] at h
  simpa [quadraticRootPowerSum] using (congrArg Neg.neg h).symm

private theorem complexQuadratic_root_recurrence (x : ℝ)
    {z : ℂ} (hz : z ∈ (complexQuadratic x).roots) (m : ℕ) :
    z ^ (m + 2) = 2 * (x : ℂ) * z ^ (m + 1) - z ^ m := by
  have hroot :=
    (Polynomial.mem_roots (complexQuadratic_ne_zero x)).mp hz
  simp only [Polynomial.IsRoot, complexQuadratic, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hroot
  calc
    z ^ (m + 2) = z ^ m * z ^ 2 := by
      rw [show m + 2 = m + 2 by rfl, pow_add]
    _ = z ^ m * (2 * (x : ℂ) * z - 1) := by
      congr 1
      linear_combination hroot
    _ = 2 * (x : ℂ) * z ^ (m + 1) - z ^ m := by
      rw [pow_succ]
      ring

private theorem quadraticRootPowerSum_add_two (x : ℝ) (m : ℕ) :
    quadraticRootPowerSum x (m + 2) =
      2 * (x : ℂ) * quadraticRootPowerSum x (m + 1) -
        quadraticRootPowerSum x m := by
  change
    ((complexQuadratic x).roots.map fun z ↦ z ^ (m + 2)).sum =
      2 * (x : ℂ) *
          ((complexQuadratic x).roots.map fun z ↦ z ^ (m + 1)).sum -
        ((complexQuadratic x).roots.map fun z ↦ z ^ m).sum
  rw [← Multiset.sum_map_mul_left, ← Multiset.sum_map_sub]
  congr 1
  exact Multiset.map_congr rfl fun z hz ↦
    complexQuadratic_root_recurrence x hz m

private theorem quadraticRootPowerSum_eq_two_mul_T (x : ℝ) (m : ℕ) :
    quadraticRootPowerSum x m =
      ((2 * (T ℝ (m : ℤ)).eval x : ℝ) : ℂ) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [quadraticRootPowerSum_zero, T_zero]
  | one => simp [quadraticRootPowerSum_one, T_one]
  | more m hm hm1 =>
      rw [quadraticRootPowerSum_add_two, hm, hm1,
        show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega, T_add_two,
        Polynomial.eval_sub, Polynomial.eval_mul]
      rw [← Polynomial.C_ofNat, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      push_cast
      ring

private noncomputable def complexLiftedChebQ (n : ℕ) : ℂ[X] :=
  (liftedChebQ n).map Complex.ofRealHom

private theorem complexLiftedChebQ_eq_prod_quadratic
    {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedChebQ n =
      ∏ i : Fin n, complexQuadratic (chebNodes n hn i) := by
  rw [complexLiftedChebQ, ← chebQuadraticProduct_eq_liftedChebQ hn,
    chebQuadraticProduct, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [complexQuadratic]

private theorem complexLiftedChebQ_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedChebQ n ≠ 0 := by
  rw [complexLiftedChebQ_eq_prod_quadratic hn]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ complexQuadratic_ne_zero _

private noncomputable def complexLiftedPowerSum (n m : ℕ) : ℂ :=
  ((complexLiftedChebQ n).roots.map fun z ↦ z ^ m).sum

private theorem complexLiftedPowerSum_eq_sum_quadratic
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    complexLiftedPowerSum n m =
      ∑ i : Fin n, quadraticRootPowerSum (chebNodes n hn i) m := by
  rw [complexLiftedPowerSum, complexLiftedChebQ_eq_prod_quadratic hn,
    Polynomial.roots_prod]
  · simp [quadraticRootPowerSum, Multiset.map_bind, List.sum_ofFn]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ complexQuadratic_ne_zero _

private theorem complexLiftedPowerSum_eq_two_mul_nodeSum
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    complexLiftedPowerSum n m =
      ((2 * ∑ i : Fin n, (T ℝ (m : ℤ)).eval (chebNodes n hn i) : ℝ) : ℂ) := by
  rw [complexLiftedPowerSum_eq_sum_quadratic hn]
  simp_rw [quadraticRootPowerSum_eq_two_mul_T]
  push_cast
  rw [Finset.mul_sum]

private noncomputable def rootPowerSum (p : ℂ[X]) (m : ℕ) : ℂ :=
  (p.roots.map fun z ↦ z ^ m).sum

private theorem rootPowerSum_newton_raw (p : ℂ[X]) {k : ℕ} (hk : 0 < k) :
    rootPowerSum p k =
      (-1 : ℂ) ^ (k + 1) * k * p.roots.esymm k -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          (-1 : ℂ) ^ a.1 * p.roots.esymm a.1 *
            rootPowerSum p a.2 := by
  let s := p.roots
  have h :=
    congrArg (MvPolynomial.aeval fun z : s ↦ (z : ℂ))
      (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ k hk)
  have he (j : ℕ) :
      MvPolynomial.eval (fun z : s ↦ (z : ℂ))
          (MvPolynomial.esymm s ℂ j) = p.roots.esymm j := by
    rw [← MvPolynomial.aeval_eq_eval]
    simpa [s] using
      (MvPolynomial.aeval_esymm_eq_multiset_esymm
        (σ := s) (R := ℂ) (S := ℂ) j (fun z : s ↦ (z : ℂ)))
  have hp (j : ℕ) :
      (∑ z : s, (z : ℂ) ^ j) = rootPowerSum p j := by
    rw [Finset.sum_eq_multiset_sum]
    change
      ((Finset.univ : Finset s).val.map fun z : s ↦ (z : ℂ) ^ j).sum =
        (p.roots.map fun z ↦ z ^ j).sum
    exact congrArg Multiset.sum (by simpa [s] using
      (Multiset.map_univ s fun z : ℂ ↦ z ^ j))
  simpa [MvPolynomial.psum, he, hp] using h

private theorem complexQuadratic_monic (x : ℝ) :
    (complexQuadratic x).Monic :=
  Polynomial.Monic.def.mpr (complexQuadratic_leadingCoeff x)

private theorem complexLiftedChebQ_monic {n : ℕ} (hn : 2 ≤ n) :
    (complexLiftedChebQ n).Monic := by
  rw [complexLiftedChebQ_eq_prod_quadratic hn]
  exact Polynomial.monic_prod_of_monic Finset.univ
    (fun i : Fin n ↦ complexQuadratic (chebNodes n hn i))
    (fun i _ ↦ complexQuadratic_monic _)

private theorem complexLiftedChebQ_natDegree {n : ℕ} (hn : 2 ≤ n) :
    (complexLiftedChebQ n).natDegree = 2 * n := by
  rw [complexLiftedChebQ_eq_prod_quadratic hn]
  calc
    (∏ i : Fin n,
        complexQuadratic (chebNodes n hn i)).natDegree =
        ∑ i ∈ Finset.univ,
          (complexQuadratic (chebNodes n hn i)).natDegree := by
      exact Polynomial.natDegree_prod_of_monic
        Finset.univ (fun i : Fin n ↦ complexQuadratic (chebNodes n hn i))
        (fun i (_ : i ∈ Finset.univ) ↦ complexQuadratic_monic
          (chebNodes n hn i))
    _ = 2 * n := by
      simp [complexQuadratic_natDegree, Nat.mul_comm]

private theorem complexLiftedChebQ_coeff (n k : ℕ) :
    (complexLiftedChebQ n).coeff k =
      (if k = 2 * n then 1 else 0) -
        (1 / 6 : ℂ) * (if k = 2 * n - 2 then 1 else 0) -
          (1 / 6 : ℂ) * (if k = 2 then 1 else 0) +
            (if k = 0 then 1 else 0) := by
  simp [complexLiftedChebQ, liftedChebQ,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one]

private theorem rootPowerSum_newton (p : ℂ[X]) (hp : p.Monic)
    {k : ℕ} (hk : 0 < k) (hkdeg : k ≤ p.natDegree) :
    rootPowerSum p k =
      -(k : ℂ) * p.coeff (p.natDegree - k) -
        ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
          p.coeff (p.natDegree - a.1) * rootPowerSum p a.2 := by
  have hv (j : ℕ) (hj : j ≤ p.natDegree) :
      (-1 : ℂ) ^ j * p.roots.esymm j =
        p.coeff (p.natDegree - j) := by
    have h := p.coeff_eq_esymm_roots_of_splits
      (IsAlgClosed.splits p) (k := p.natDegree - j)
        (Nat.sub_le _ _)
    rw [hp.leadingCoeff, Nat.sub_sub_self hj, one_mul] at h
    exact h.symm
  rw [rootPowerSum_newton_raw p hk]
  calc
    (-1 : ℂ) ^ (k + 1) * k * p.roots.esymm k -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1 : ℂ) ^ a.1 * p.roots.esymm a.1 *
              rootPowerSum p a.2 =
        -(k : ℂ) * ((-1 : ℂ) ^ k * p.roots.esymm k) -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            ((-1 : ℂ) ^ a.1 * p.roots.esymm a.1) *
              rootPowerSum p a.2 := by
      rw [pow_succ]
      ring
    _ = -(k : ℂ) * p.coeff (p.natDegree - k) -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            p.coeff (p.natDegree - a.1) *
              rootPowerSum p a.2 := by
      rw [hv k hkdeg]
      apply congrArg fun z ↦
        -(k : ℂ) * p.coeff (p.natDegree - k) - z
      apply Finset.sum_congr rfl
      intro a ha
      rw [hv a.1]
      have hai : a.1 ∈ Set.Ioo 0 k := (Finset.mem_filter.mp ha).2
      exact (le_trans (le_of_lt hai.2) hkdeg)

private theorem complexLiftedChebQ_coeff_from_top {n k : ℕ}
    (hk : 0 < k) (hkmax : k ≤ 2 * n - 2) :
    (complexLiftedChebQ n).coeff (2 * n - k) =
      -(1 / 6 : ℂ) * (if k = 2 then 1 else 0) -
        (1 / 6 : ℂ) * (if k = 2 * n - 2 then 1 else 0) := by
  have htop : 2 * n - k ≠ 2 * n := by omega
  have hnext : (2 * n - k = 2 * n - 2) ↔ k = 2 := by omega
  have htwo : (2 * n - k = 2) ↔ k = 2 * n - 2 := by omega
  have hzero : 2 * n - k ≠ 0 := by omega
  rw [complexLiftedChebQ_coeff]
  simp only [htop, hnext, htwo, hzero, if_false]
  split_ifs <;> ring

private theorem complexLiftedChebQ_coeff_inner {n j k : ℕ}
    (hj : 0 < j) (hjk : j < k) (hkmax : k ≤ 2 * n - 2) :
    (complexLiftedChebQ n).coeff (2 * n - j) =
      if j = 2 then -(1 / 6 : ℂ) else 0 := by
  have htop : 2 * n - j ≠ 2 * n := by omega
  have hnext : (2 * n - j = 2 * n - 2) ↔ j = 2 := by omega
  have htwo : 2 * n - j ≠ 2 := by omega
  have hzero : 2 * n - j ≠ 0 := by omega
  rw [complexLiftedChebQ_coeff]
  simp only [htop, hnext, htwo, hzero, if_false]
  split_ifs <;> ring

private theorem complexLiftedChebQ_newton_inner_sum {n k : ℕ}
    (hk : 3 ≤ k) (hkmax : k ≤ 2 * n - 2) :
    (∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (complexLiftedChebQ n).coeff (2 * n - a.1) *
          rootPowerSum (complexLiftedChebQ n) a.2) =
      -(1 / 6 : ℂ) * complexLiftedPowerSum n (k - 2) := by
  have hpair :
      (2, k - 2) ∈
        (Finset.antidiagonal k).filter (fun a ↦ a.1 ∈ Set.Ioo 0 k) := by
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo]
    omega
  rw [Finset.sum_eq_single_of_mem (2, k - 2) hpair]
  · rw [complexLiftedChebQ_coeff_inner (j := 2) (k := k)
      (by omega) (by omega) hkmax]
    simp [complexLiftedPowerSum, rootPowerSum]
  · intro a ha hne
    have ha' := Finset.mem_filter.mp ha
    have hjpos : 0 < a.1 := ha'.2.1
    have hjlt : a.1 < k := ha'.2.2
    rw [complexLiftedChebQ_coeff_inner hjpos hjlt hkmax]
    have hjne : a.1 ≠ 2 := by
      intro hj
      apply hne
      apply Prod.ext
      · exact hj
      · have hadi : a.1 + a.2 = k :=
          Finset.mem_antidiagonal.mp ha'.1
        omega
    simp [hjne]

private theorem complexLiftedPowerSum_recurrence {n k : ℕ}
    (hn : 2 ≤ n) (hk : 3 ≤ k) (hkmax : k ≤ 2 * n - 2) :
    complexLiftedPowerSum n k =
      (1 / 6 : ℂ) * complexLiftedPowerSum n (k - 2) +
        if k = 2 * n - 2 then (k : ℂ) * (1 / 6 : ℂ) else 0 := by
  have hkdeg : k ≤ (complexLiftedChebQ n).natDegree := by
    rw [complexLiftedChebQ_natDegree hn]
    omega
  change rootPowerSum (complexLiftedChebQ n) k = _
  rw [rootPowerSum_newton (complexLiftedChebQ n)
      (complexLiftedChebQ_monic hn) (by omega) hkdeg,
    complexLiftedChebQ_natDegree hn,
    complexLiftedChebQ_coeff_from_top (by omega) hkmax,
    complexLiftedChebQ_newton_inner_sum hk hkmax]
  have hk2 : k ≠ 2 := by omega
  have htop2 : 2 * n - 2 ≠ 2 := by omega
  by_cases htop : k = 2 * n - 2
  · simp [htop, htop2]
    ring
  · simp [hk2, htop]

private theorem complexLiftedChebQ_newton_inner_sum_small {n k : ℕ}
    (hk : 0 < k) (hksmall : k ≤ 2) (hkmax : k ≤ 2 * n - 2) :
    (∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (complexLiftedChebQ n).coeff (2 * n - a.1) *
          rootPowerSum (complexLiftedChebQ n) a.2) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  have hjpos : 0 < a.1 := ha'.2.1
  have hjlt : a.1 < k := ha'.2.2
  rw [complexLiftedChebQ_coeff_inner hjpos hjlt hkmax]
  have hjne : a.1 ≠ 2 := by omega
  simp [hjne]

private theorem complexLiftedPowerSum_one {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedPowerSum n 1 = 0 := by
  have hkmax : 1 ≤ 2 * n - 2 := by omega
  have hkdeg : 1 ≤ (complexLiftedChebQ n).natDegree := by
    rw [complexLiftedChebQ_natDegree hn]
    omega
  change rootPowerSum (complexLiftedChebQ n) 1 = 0
  rw [rootPowerSum_newton (complexLiftedChebQ n)
      (complexLiftedChebQ_monic hn) (by omega) hkdeg,
    complexLiftedChebQ_natDegree hn,
    complexLiftedChebQ_coeff_from_top (by omega) hkmax,
    complexLiftedChebQ_newton_inner_sum_small (by omega) (by omega) hkmax]
  norm_num
  omega

private theorem complexLiftedPowerSum_two {n : ℕ} (hn : 3 ≤ n) :
    complexLiftedPowerSum n 2 = 2 * (1 / 6 : ℂ) := by
  have hn2 : 2 ≤ n := by omega
  have hkmax : 2 ≤ 2 * n - 2 := by omega
  have hkdeg : 2 ≤ (complexLiftedChebQ n).natDegree := by
    rw [complexLiftedChebQ_natDegree hn2]
    omega
  change rootPowerSum (complexLiftedChebQ n) 2 = _
  rw [rootPowerSum_newton (complexLiftedChebQ n)
      (complexLiftedChebQ_monic hn2) (by omega) hkdeg,
    complexLiftedChebQ_natDegree hn2,
    complexLiftedChebQ_coeff_from_top (by omega) hkmax,
    complexLiftedChebQ_newton_inner_sum_small (by omega) (by omega) hkmax]
  have htop : 2 ≠ 2 * n - 2 := by omega
  simp [htop]

private theorem complexLiftedPowerSum_two_at_two :
    complexLiftedPowerSum 2 2 = 4 * (1 / 6 : ℂ) := by
  have hkdeg : 2 ≤ (complexLiftedChebQ 2).natDegree := by
    rw [complexLiftedChebQ_natDegree (by omega)]
    omega
  change rootPowerSum (complexLiftedChebQ 2) 2 = _
  rw [rootPowerSum_newton (complexLiftedChebQ 2)
      (complexLiftedChebQ_monic (by omega)) (by omega) hkdeg,
    complexLiftedChebQ_natDegree (by omega),
    complexLiftedChebQ_coeff_from_top (n := 2) (k := 2) (by omega) (by omega),
    complexLiftedChebQ_newton_inner_sum_small
      (n := 2) (k := 2) (by omega) (by omega) (by omega)]
  norm_num

private theorem complexLiftedPowerSum_of_odd {n m : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ 2 * n - 2) (hodd : Odd m) :
    complexLiftedPowerSum n m = 0 := by
  rcases hodd with ⟨r, rfl⟩
  induction r generalizing n with
  | zero =>
      simpa using complexLiftedPowerSum_one hn
  | succ r ih =>
      rw [complexLiftedPowerSum_recurrence hn (k := 2 * (r + 1) + 1)
        (by omega) hm]
      have htop : 2 * (r + 1) + 1 ≠ 2 * n - 2 := by omega
      rw [if_neg htop]
      rw [show 2 * (r + 1) + 1 - 2 = 2 * r + 1 by omega,
        ih hn (by omega)]
      ring

private theorem complexLiftedPowerSum_even_lt_top {n r : ℕ}
    (hn : 2 ≤ n) (hrpos : 0 < r) (hrmax : r ≤ n - 2) :
    complexLiftedPowerSum n (2 * r) = 2 * (1 / 6 : ℂ) ^ r := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
      by_cases hrzero : r = 0
      · subst r
        have hn3 : 3 ≤ n := by omega
        simpa using complexLiftedPowerSum_two hn3
      · rw [complexLiftedPowerSum_recurrence hn (k := 2 * (r + 1))
          (by omega) (by omega)]
        have htop : 2 * (r + 1) ≠ 2 * n - 2 := by omega
        rw [if_neg htop]
        rw [show 2 * (r + 1) - 2 = 2 * r by omega,
          ih hn (by omega) (by omega)]
        rw [pow_succ]
        ring

private theorem complexLiftedPowerSum_top {n : ℕ} (hn : 2 ≤ n) :
    complexLiftedPowerSum n (2 * n - 2) =
      2 * (1 / 6 : ℂ) ^ (n - 1) +
        (2 * n - 2 : ℕ) * (1 / 6 : ℂ) := by
  rcases eq_or_lt_of_le hn with rfl | hn3
  · rw [complexLiftedPowerSum_two_at_two]
    ring
  · rw [complexLiftedPowerSum_recurrence (by omega)
      (k := 2 * n - 2) (by omega) le_rfl, if_pos rfl]
    rw [show 2 * n - 2 - 2 = 2 * (n - 2) by omega,
      complexLiftedPowerSum_even_lt_top (by omega) (by omega) le_rfl]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring

/-- Every odd Chebyshev moment of the comparison nodes, through the last
moment below the degree of the reciprocal polynomial, vanishes. -/
theorem sum_chebNodes_T_of_odd {n m : ℕ} (hn : 2 ≤ n)
    (hm : m ≤ 2 * n - 2) (hodd : Odd m) :
    ∑ i : Fin n, (T ℝ (m : ℤ)).eval (chebNodes n hn i) = 0 := by
  have h := complexLiftedPowerSum_eq_two_mul_nodeSum hn m
  rw [complexLiftedPowerSum_of_odd hn hm hodd] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- The even Chebyshev moments strictly below the exceptional top moment. -/
theorem sum_chebNodes_T_even {n r : ℕ} (hn : 2 ≤ n)
    (hr : r ≤ n - 2) :
    ∑ i : Fin n, (T ℝ ((2 * r : ℕ) : ℤ)).eval (chebNodes n hn i) =
      if r = 0 then (n : ℝ) else ((1 : ℝ) / 6) ^ r := by
  by_cases hrzero : r = 0
  · subst r
    simp [T_zero]
  · rw [if_neg hrzero]
    have h := complexLiftedPowerSum_eq_two_mul_nodeSum hn (2 * r)
    rw [complexLiftedPowerSum_even_lt_top hn (Nat.pos_of_ne_zero hrzero) hr] at h
    apply Complex.ofReal_injective
    push_cast at h ⊢
    apply mul_left_cancel₀ (a := (2 : ℂ)) (by norm_num)
    exact h.symm

/-- The exceptional last even Chebyshev moment of the comparison nodes. -/
theorem sum_chebNodes_T_top {n : ℕ} (hn : 2 ≤ n) :
    ∑ i : Fin n,
        (T ℝ ((2 * (n - 1) : ℕ) : ℤ)).eval (chebNodes n hn i) =
      ((1 : ℝ) / 6) ^ (n - 1) + ((n - 1 : ℕ) : ℝ) / 6 := by
  rw [show 2 * (n - 1) = 2 * n - 2 by omega]
  have h := complexLiftedPowerSum_eq_two_mul_nodeSum hn (2 * n - 2)
  rw [complexLiftedPowerSum_top hn] at h
  have hnat :
      ((2 * n - 2 : ℕ) : ℂ) = 2 * ((n - 1 : ℕ) : ℂ) := by
    norm_cast
    omega
  apply Complex.ofReal_injective
  push_cast at h ⊢
  rw [hnat] at h
  apply mul_left_cancel₀ (a := (2 : ℂ)) (by norm_num)
  calc
    2 * ∑ x,
          (T ℂ ((2 * n - 2 : ℕ) : ℤ)).eval
            (chebNodes n hn x : ℂ) =
        2 * (1 / 6 : ℂ) ^ (n - 1) +
          (2 * ((n - 1 : ℕ) : ℂ)) * (1 / 6 : ℂ) := h.symm
    _ = 2 * ((1 / 6 : ℂ) ^ (n - 1) +
          ((n - 1 : ℕ) : ℂ) / 6) := by ring

end Erdos1131

end PortChebyshevRootSums

-- Original: Erdos1131/ChebyshevMoment.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/ChebyshevMoment.lean; SHA-256 00e93e971a0e50f9805c670750f5ea2017b285aa2821769b058e1da32d215408
section PortChebyshevMoment

                   

/-!
# Unweighted moments of Chebyshev polynomials

The comparison-family Gram matrix uses Lebesgue measure, rather than the
classical Chebyshev weight.  This file records the corresponding elementary
moment calculation.
-/

open scoped Interval
open Polynomial

namespace Erdos1131

namespace ChebyshevMoment

open Polynomial.Chebyshev

lemma U_sub_two_eq_two_mul_T (m : ℤ) :
    U ℝ m - U ℝ (m - 2) = 2 * T ℝ m := by
  have hT := T_eq_U_sub_X_mul_U (R := ℝ) m
  have hU := U_sub_two ℝ m
  linear_combination -2 * hT - hU

noncomputable def primitive (m : ℤ) : ℝ[X] :=
  (2 * ((m + 1 : ℤ) : ℝ))⁻¹ • T ℝ (m + 1) -
    (2 * ((m - 1 : ℤ) : ℝ))⁻¹ • T ℝ (m - 1)

lemma derivative_primitive (m : ℤ) (hm1 : m ≠ 1) (hmneg1 : m ≠ -1) :
    (primitive m).derivative = T ℝ m := by
  have hp : ((m + 1 : ℤ) : ℝ) ≠ 0 := by
    have : m + 1 ≠ 0 := by omega
    exact_mod_cast this
  have hm : ((m - 1 : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hm1
  rw [primitive, derivative_sub, derivative_smul, derivative_smul,
    T_derivative_eq_U, T_derivative_eq_U]
  have hfirst :
      (2 * ((m + 1 : ℤ) : ℝ))⁻¹ •
          ((m + 1 : ℤ) * U ℝ (m + 1 - 1)) =
        (2 : ℝ)⁻¹ • U ℝ m := by
    simp only [Int.add_sub_cancel]
    rw [← Polynomial.C_eq_intCast, ← Polynomial.smul_eq_C_mul, smul_smul]
    congr 1
    field_simp
  have hsecond :
      (2 * ((m - 1 : ℤ) : ℝ))⁻¹ •
          ((m - 1 : ℤ) * U ℝ (m - 1 - 1)) =
        (2 : ℝ)⁻¹ • U ℝ (m - 2) := by
    simp only [sub_sub]
    rw [← Polynomial.C_eq_intCast, ← Polynomial.smul_eq_C_mul, smul_smul]
    congr 1
    field_simp
  rw [hfirst, hsecond, ← smul_sub, U_sub_two_eq_two_mul_T]
  rw [← Polynomial.C_ofNat, ← Polynomial.smul_eq_C_mul, smul_smul]
  norm_num

lemma integral_eval_T_eq_primitive_sub
    (m : ℤ) (hm1 : m ≠ 1) (hmneg1 : m ≠ -1) :
    (∫ x in (-1 : ℝ)..1, (T ℝ m).eval x) =
      (primitive m).eval 1 - (primitive m).eval (-1) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x ↦ (primitive m).eval x)
    (f' := fun x ↦ (T ℝ m).eval x)
    (fun x _ ↦ by
      simpa only [derivative_primitive m hm1 hmneg1] using
        (primitive m).hasDerivAt x)
    ((by fun_prop : Continuous fun x : ℝ ↦ (T ℝ m).eval x).intervalIntegrable _ _)

lemma eval_primitive_one_sub_neg_one (m : ℤ) :
    (primitive m).eval 1 - (primitive m).eval (-1) =
      (2 * ((m + 1 : ℤ) : ℝ))⁻¹ *
          (1 - ((m + 1).negOnePow : ℝ)) -
        (2 * ((m - 1 : ℤ) : ℝ))⁻¹ *
          (1 - ((m - 1).negOnePow : ℝ)) := by
  simp only [primitive, eval_sub, eval_smul, T_eval_one, T_eval_neg_one,
    smul_eq_mul]
  ring

theorem integral_eval_T_nat_of_even (n : ℕ) (hn : Even n) :
    (∫ x in (-1 : ℝ)..1, (T ℝ (n : ℤ)).eval x) =
      2 / (1 - (n : ℝ) ^ 2) := by
  have hn_int : Even (n : ℤ) := (Int.even_coe_nat n).mpr hn
  have hn1 : (n : ℤ) ≠ 1 := by
    rintro h
    have : n = 1 := by exact_mod_cast h
    subst n
    norm_num at hn
  have hnneg1 : (n : ℤ) ≠ -1 := by omega
  have hn1_real : (n : ℝ) ≠ 1 := by exact_mod_cast hn1
  have hminus : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hn1_real
  have hsquare : 1 - (n : ℝ) ^ 2 ≠ 0 := by
    rw [show 1 - (n : ℝ) ^ 2 = (1 - n) * (1 + n) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr (ne_comm.mpr hn1_real))
      (by positivity)
  rw [integral_eval_T_eq_primitive_sub (n : ℤ) hn1 hnneg1,
    eval_primitive_one_sub_neg_one,
    Int.negOnePow_odd _ (hn_int.add_odd odd_one),
    Int.negOnePow_odd _ (hn_int.sub_odd odd_one)]
  push_cast
  field_simp [hminus, hsquare]
  ring

theorem integral_eval_T_nat_of_odd (n : ℕ) (hn : Odd n) :
    (∫ x in (-1 : ℝ)..1, (T ℝ (n : ℤ)).eval x) = 0 := by
  by_cases hn1 : n = 1
  · subst n
    simp [T_one]
  have hn_int : Odd (n : ℤ) := (Int.odd_coe_nat n).mpr hn
  have hn1_int : (n : ℤ) ≠ 1 := by exact_mod_cast hn1
  have hnneg1 : (n : ℤ) ≠ -1 := by omega
  rw [integral_eval_T_eq_primitive_sub (n : ℤ) hn1_int hnneg1,
    eval_primitive_one_sub_neg_one,
    Int.negOnePow_even _ (hn_int.add_odd odd_one),
    Int.negOnePow_even _ (hn_int.sub_odd odd_one)]
  norm_num

/-- The unweighted first Chebyshev moment on `[-1,1]`. -/
theorem integral_eval_T_nat (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (T ℝ (n : ℤ)).eval x) =
      if Even n then 2 / (1 - (n : ℝ) ^ 2) else 0 := by
  by_cases hn : Even n
  · rw [if_pos hn, integral_eval_T_nat_of_even n hn]
  · have hn' : Odd n := (Nat.not_even_iff_odd).mp hn
    rw [if_neg hn, integral_eval_T_nat_of_odd n hn']

private lemma eval_T_mul_T (j k : ℕ) (x : ℝ) :
    (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x =
      (2 : ℝ)⁻¹ *
        ((T ℝ ((j : ℤ) + (k : ℤ))).eval x +
          (T ℝ ((j : ℤ) - (k : ℤ))).eval x) := by
  have h := congrArg (Polynomial.eval x)
    (T_mul_T ℝ (j : ℤ) (k : ℤ))
  simp only [eval_mul, eval_ofNat, eval_add] at h
  linarith

/-- The product moment before simplifying the common parity condition. -/
theorem integral_eval_T_mul_T_nat_raw (j k : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x) =
      (2 : ℝ)⁻¹ *
        ((if Even (j + k) then
            2 / (1 - ((j + k : ℕ) : ℝ) ^ 2) else 0) +
          (if Even ((j : ℤ) - (k : ℤ)).natAbs then
            2 / (1 - (((j : ℤ) - (k : ℤ)).natAbs : ℝ) ^ 2) else 0)) := by
  have hsum :
      (∫ x in (-1 : ℝ)..1,
        (T ℝ ((j : ℤ) + (k : ℤ))).eval x) =
          if Even (j + k) then
            2 / (1 - ((j + k : ℕ) : ℝ) ^ 2) else 0 := by
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
      integral_eval_T_nat (j + k)
  have hdiff :
      (∫ x in (-1 : ℝ)..1,
        (T ℝ ((j : ℤ) - (k : ℤ))).eval x) =
          if Even ((j : ℤ) - (k : ℤ)).natAbs then
            2 / (1 - (((j : ℤ) - (k : ℤ)).natAbs : ℝ) ^ 2) else 0 := by
    rw [← T_natAbs ℝ ((j : ℤ) - (k : ℤ))]
    exact integral_eval_T_nat ((j : ℤ) - (k : ℤ)).natAbs
  rw [intervalIntegral.integral_congr (fun x _ ↦ eval_T_mul_T j k x)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add
    ((by fun_prop :
      Continuous fun x : ℝ ↦
        (T ℝ ((j : ℤ) + (k : ℤ))).eval x).intervalIntegrable _ _)
    ((by fun_prop :
      Continuous fun x : ℝ ↦
        (T ℝ ((j : ℤ) - (k : ℤ))).eval x).intervalIntegrable _ _)]
  rw [hsum, hdiff]

/-- The unweighted product moment of two Chebyshev polynomials on `[-1,1]`.
It vanishes in opposite parities; in the common-parity case this is the
closed form used for the Gram matrix. -/
theorem integral_eval_T_mul_T_nat (j k : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x) =
      if Even (j + k) then
        1 / (1 - ((j : ℝ) - (k : ℝ)) ^ 2) +
          1 / (1 - ((j : ℝ) + (k : ℝ)) ^ 2)
      else 0 := by
  have hparity :
      Even ((j : ℤ) - (k : ℤ)).natAbs ↔ Even (j + k) := by
    simp only [Int.natAbs_even, Int.even_sub, Int.even_coe_nat,
      Nat.even_add]
  have habs :
      (((j : ℤ) - (k : ℤ)).natAbs : ℝ) =
        |(j : ℝ) - (k : ℝ)| := by
    calc
      (((j : ℤ) - (k : ℤ)).natAbs : ℝ) =
          ((((j : ℤ) - (k : ℤ)).natAbs : ℤ) : ℝ) := by norm_num
      _ = ((|((j : ℤ) - (k : ℤ))| : ℤ) : ℝ) := by
        rw [Int.natCast_natAbs]
      _ = |((((j : ℤ) - (k : ℤ)) : ℤ) : ℝ)| := Int.cast_abs
      _ = |(j : ℝ) - (k : ℝ)| := by push_cast; rfl
  rw [integral_eval_T_mul_T_nat_raw]
  by_cases h : Even (j + k)
  · simp only [if_pos h, if_pos (hparity.mpr h)]
    rw [habs, sq_abs]
    push_cast
    ring
  · simp only [if_neg h, if_neg (mt hparity.mp h)]
    norm_num

end ChebyshevMoment

end Erdos1131

end PortChebyshevMoment

-- Original: Erdos1131/InterpolationTrace.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/InterpolationTrace.lean; SHA-256 6111e8b6af1ceaf85dd018390c12b2d2fb625760e350d7ed2b86cae2f976085d
section PortInterpolationTrace

                       
                           
                          

/-!
# Interpolation in the Chebyshev basis

This file connects the Lagrange functional to the finite Chebyshev matrices.
Rows of `chebEvalMatrix x` are nodes and columns are Chebyshev degrees.
-/

open scoped BigOperators Interval Matrix
open Polynomial

namespace Erdos1131

namespace InterpolationTrace

open Polynomial.Chebyshev

noncomputable section

/-- Evaluation of `T₀, ..., T_{n-1}` at the nodes `x`. -/
def chebEvalMatrix {n : ℕ} (x : Fin n ↪ ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (T ℝ (j.val : ℤ)).eval (x i)

/-- The actual (unweighted) integral Gram matrix of `T₀, ..., T_{n-1}`. -/
def integralGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    ∫ t in (-1 : ℝ)..1,
      (T ℝ (i.val : ℤ)).eval t * (T ℝ (j.val : ℤ)).eval t

/-- A coefficient vector interpreted in the Chebyshev basis. -/
def chebExpansion {n : ℕ} (c : Fin n → ℝ) : ℝ[X] :=
  ∑ j : Fin n, C (c j) * T ℝ (j.val : ℤ)

theorem chebEvalMatrix_det_ne_zero {n : ℕ} (x : Fin n ↪ ℝ) :
    (chebEvalMatrix x).det ≠ 0 := by
  let p : Fin n → ℝ[X] := fun j ↦ T ℝ (j.val : ℤ)
  have hdeg : ∀ j, (p j).natDegree ≤ j.val := by
    intro j
    simp [p]
  have hfactor :=
    Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
      (x : Fin n → ℝ) p hdeg
  have hvander :
      (Matrix.vandermonde (x : Fin n → ℝ)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr x.injective
  have hcoeff :
      (Matrix.of (fun (i j : Fin n) ↦ (p j).coeff i.val)).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular
      (Matrix.matrixOfPolynomials_blockTriangular p hdeg)]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simp only [Matrix.of_apply]
    have hjdeg : (p j).natDegree = j.val := by simp [p]
    rw [← hjdeg, coeff_natDegree]
    simp only [p, leadingCoeff_T]
    positivity
  have hdet := congrArg Matrix.det hfactor
  change (chebEvalMatrix x).det =
    (Matrix.vandermonde (x : Fin n → ℝ) *
      Matrix.of (fun (i j : Fin n) ↦ (p j).coeff i.val)).det at hdet
  rw [Matrix.det_mul] at hdet
  rw [hdet]
  exact mul_ne_zero hvander hcoeff

/-- Distinct nodes make the Chebyshev evaluation matrix invertible. -/
theorem chebEvalMatrix_isUnit_det {n : ℕ} (x : Fin n ↪ ℝ) :
    IsUnit (chebEvalMatrix x).det :=
  isUnit_iff_ne_zero.mpr (chebEvalMatrix_det_ne_zero x)

/-- Every finite Chebyshev expansion indexed by `Fin n` has degree `< n`. -/
theorem degree_chebExpansion_lt {n : ℕ} (c : Fin n → ℝ) :
    (chebExpansion c).degree < (n : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 ?_
  intro j _
  calc
    (C (c j) * T ℝ (j.val : ℤ)).degree
        ≤ (C (c j)).degree + (T ℝ (j.val : ℤ)).degree :=
      degree_mul_le _ _
    _ ≤ 0 + (j.val : WithBot ℕ) := by
      gcongr
      · exact degree_C_le
      · simp
    _ < (n : WithBot ℕ) := by
      simpa only [zero_add, Nat.cast_lt] using j.isLt

/-- The `k`th Lagrange polynomial has as its Chebyshev coefficients the
`k`th column of the inverse evaluation matrix. -/
theorem lagrange_basis_eq_chebExpansion {n : ℕ}
    (x : Fin n ↪ ℝ) (k : Fin n) :
    Lagrange.basis Finset.univ (x : Fin n → ℝ) k =
      chebExpansion (fun j ↦ (chebEvalMatrix x)⁻¹ j k) := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨k⟩
  have hbdeg :
      (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).degree <
        (n : WithBot ℕ) := by
    rw [Lagrange.degree_basis x.injective.injOn (Finset.mem_univ k)]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot,
      WithBot.coe_lt_coe]
    exact Nat.sub_lt hn zero_lt_one
  have hedeg :
      (chebExpansion (fun j ↦ (chebEvalMatrix x)⁻¹ j k)).degree <
        (n : WithBot ℕ) :=
    degree_chebExpansion_lt (fun j ↦ (chebEvalMatrix x)⁻¹ j k)
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    x.injective.injOn (by simpa using hbdeg) (by simpa using hedeg) ?_
  intro i _
  have hmul := Matrix.mul_nonsing_inv (chebEvalMatrix x)
    (chebEvalMatrix_isUnit_det x)
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i k) hmul
  change (chebEvalMatrix x * (chebEvalMatrix x)⁻¹) i k =
    (1 : Matrix (Fin n) (Fin n) ℝ) i k at hentry
  have hbasis :
      (Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval (x i) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i k := by
    simp only [Matrix.one_apply]
    by_cases hik : i = k
    · subst i
      rw [if_pos rfl, basis_eval_self]
    · rw [if_neg hik, basis_eval_of_ne x hik]
  rw [hbasis, ← hentry]
  simp only [Matrix.mul_apply, chebEvalMatrix, chebExpansion,
    eval_finsetSum, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Squaring removes the orientation in `Nat.dist`. -/
lemma natCast_dist_sq (a b : ℕ) :
    ((a.dist b : ℕ) : ℝ) ^ 2 = ((a : ℝ) - (b : ℝ)) ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab]
    ring
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba, Nat.cast_sub hba]

lemma even_add_iff_sameParity (a b : ℕ) :
    Even (a + b) ↔ ChebyshevBound.SameParity a b := by
  simp [ChebyshevBound.SameParity, Nat.even_iff]
  omega

lemma two_mul_half_add_of_sameParity {a b : ℕ}
    (h : ChebyshevBound.SameParity a b) :
    2 * ((a + b) / 2) = a + b := by
  apply Nat.two_mul_div_two_of_even
  exact (even_add_iff_sameParity a b).mpr h

lemma two_mul_half_dist_of_sameParity {a b : ℕ}
    (h : ChebyshevBound.SameParity a b) :
    2 * (a.dist b / 2) = a.dist b := by
  apply Nat.two_mul_div_two_of_even
  have heab : Even a ↔ Even b := by
    simp [ChebyshevBound.SameParity, Nat.even_iff] at h ⊢
    omega
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (Nat.even_sub hab).2 heab.symm
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    exact (Nat.even_sub hba).2 heab

/-- The integral definition of the Gram matrix agrees with the closed form
used by `ChebyshevBound`. -/
theorem integralGram_eq_chebH (N : ℕ) :
    integralGram (N + 1) = ChebyshevBound.chebH N := by
  ext i j
  rw [integralGram, ChebyshevMoment.integral_eval_T_mul_T_nat,
    ChebyshevBound.chebH]
  have hparity :=
    even_add_iff_sameParity i.val j.val
  by_cases hsame : ChebyshevBound.SameParity i.val j.val
  · simp only [if_pos hsame, if_pos (hparity.mpr hsame)]
    have hsum := two_mul_half_add_of_sameParity hsame
    have hdist := two_mul_half_dist_of_sameParity hsame
    have hsum_real :
        (2 : ℝ) * (((i.val + j.val) / 2 : ℕ) : ℝ) =
          (i.val : ℝ) + (j.val : ℝ) := by
      exact_mod_cast hsum
    have hdist_real :
        (2 : ℝ) * ((i.val.dist j.val / 2 : ℕ) : ℝ) =
          (i.val.dist j.val : ℕ) := by
      exact_mod_cast hdist
    unfold ChebyshevBound.chebMoment
    rw [show
      4 * (((i.val + j.val) / 2 : ℕ) : ℝ) ^ 2 =
        ((i.val : ℝ) + (j.val : ℝ)) ^ 2 by nlinarith,
      show
      4 * ((i.val.dist j.val / 2 : ℕ) : ℝ) ^ 2 =
        ((i.val : ℝ) - (j.val : ℝ)) ^ 2 by
          calc
            4 * ((i.val.dist j.val / 2 : ℕ) : ℝ) ^ 2 =
                ((i.val.dist j.val : ℕ) : ℝ) ^ 2 := by nlinarith
            _ = ((i.val : ℝ) - (j.val : ℝ)) ^ 2 :=
              natCast_dist_sq i.val j.val]
    ring
  · simp only [if_neg hsame, if_neg (mt hparity.mp hsame)]

/-- The integral of the square of a Chebyshev expansion is its Gram
quadratic form. -/
theorem integral_sq_chebExpansion {n : ℕ} (c : Fin n → ℝ) :
    (∫ t in (-1 : ℝ)..1, (chebExpansion c).eval t ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * integralGram n i j * c j := by
  have hpoint (t : ℝ) :
      (chebExpansion c).eval t ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          c i *
            ((T ℝ (i.val : ℤ)).eval t *
              (T ℝ (j.val : ℤ)).eval t) *
            c j := by
    simp only [chebExpansion, eval_finsetSum, eval_mul, eval_C, pow_two]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    (∫ t in (-1 : ℝ)..1, (chebExpansion c).eval t ^ 2) =
        ∫ t in (-1 : ℝ)..1,
          ∑ i : Fin n, ∑ j : Fin n,
            c i *
              ((T ℝ (i.val : ℤ)).eval t *
                (T ℝ (j.val : ℤ)).eval t) *
              c j :=
      intervalIntegral.integral_congr (fun t _ ↦ hpoint t)
    _ = ∑ i : Fin n,
          ∫ t in (-1 : ℝ)..1,
            ∑ j : Fin n,
              c i *
                ((T ℝ (i.val : ℤ)).eval t *
                  (T ℝ (j.val : ℤ)).eval t) *
                c j := by
      rw [intervalIntegral.integral_finsetSum]
      intro i _
      apply Continuous.intervalIntegrable
      fun_prop
    _ = ∑ i : Fin n, ∑ j : Fin n,
          ∫ t in (-1 : ℝ)..1,
            c i *
              ((T ℝ (i.val : ℤ)).eval t *
                (T ℝ (j.val : ℤ)).eval t) *
              c j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum]
      intro j _
      apply Continuous.intervalIntegrable
      fun_prop
    _ = ∑ i : Fin n, ∑ j : Fin n,
        c i * integralGram n i j * c j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul]
      rfl

/-- The Lagrange functional is the trace of the integral Gram matrix times
the inverse discrete Gram matrix. -/
theorem functional_eq_trace {n : ℕ} (x : Fin n ↪ ℝ) :
    functional x =
      Matrix.trace
        (integralGram n *
          (((chebEvalMatrix x)ᵀ * chebEvalMatrix x)⁻¹)) := by
  let A := chebEvalMatrix x
  let B := A⁻¹
  let H := integralGram n
  have hfunctional :
      functional x =
        ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          B i k * H i j * B j k := by
    unfold functional
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [lagrange_basis_eq_chebExpansion]
      simp_rw [integral_sq_chebExpansion]
      rfl
    · intro k _
      apply Continuous.intervalIntegrable
      fun_prop
  have htrace :
      Matrix.trace (Bᵀ * H * B) =
        ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          B i k * H i j * B j k := by
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro k _
    change (Bᵀ * H * B) k k =
      ∑ i : Fin n, ∑ j : Fin n, B i k * H i j * B j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  calc
    functional x =
        ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          B i k * H i j * B j k := hfunctional
    _ = Matrix.trace (Bᵀ * H * B) := htrace.symm
    _ = Matrix.trace (B * Bᵀ * H) :=
      Matrix.trace_mul_cycle Bᵀ H B
    _ = Matrix.trace (H * (B * Bᵀ)) := by
      rw [Matrix.trace_mul_comm (B * Bᵀ) H]
    _ = Matrix.trace
        (integralGram n *
          (((chebEvalMatrix x)ᵀ * chebEvalMatrix x)⁻¹)) := by
      dsimp only [H, B, A]
      rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]

end

end InterpolationTrace

end Erdos1131

end PortInterpolationTrace

-- Original: Erdos1131/ChebyshevGram.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/ChebyshevGram.lean; SHA-256 05f4ec14e40b27bda8f364b38d990307156d91eec4133c10d396361cc9f85184
section PortChebyshevGram

                             
                              
                              

/-!
# The discrete Gram matrix of the Chebyshev comparison nodes

This file identifies the evaluation Gram matrix of the explicit roots of
`T_(N+1) - (1/6) T_(N-1)` with the finite model matrix used by the
resolvent estimate.
-/

open scoped BigOperators Matrix

namespace Erdos1131.ChebyshevGram

open Polynomial Polynomial.Chebyshev
open ChebyshevBound ChebyshevResolvent InterpolationTrace

noncomputable section

/-- The product formula for two Chebyshev polynomials, with the difference
index expressed as a natural-number distance. -/
theorem two_mul_eval_T_mul_eval_T_nat
    (a b : ℕ) (x : ℝ) :
    2 * (T ℝ (a : ℤ)).eval x * (T ℝ (b : ℤ)).eval x =
      (T ℝ ((a + b : ℕ) : ℤ)).eval x +
        (T ℝ ((a.dist b : ℕ) : ℤ)).eval x := by
  rcases le_total b a with hba | hab
  · have h := congrArg (fun p : ℝ[X] => p.eval x)
      (T_mul_T ℝ (a : ℤ) (b : ℤ))
    have hsub : (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) := by
      exact (Nat.cast_sub hba).symm
    rw [hsub] at h
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    simpa only [eval_add, eval_mul, eval_ofNat, Nat.cast_add,
      mul_assoc] using h
  · have h := congrArg (fun p : ℝ[X] => p.eval x)
      (T_mul_T ℝ (b : ℤ) (a : ℤ))
    have hsub : (b : ℤ) - (a : ℤ) = ((b - a : ℕ) : ℤ) := by
      exact (Nat.cast_sub hab).symm
    rw [hsub] at h
    rw [Nat.dist_eq_sub_of_le hab]
    simpa only [eval_add, eval_mul, eval_ofNat, Nat.cast_add,
      mul_assoc, add_comm, mul_comm, add_left_comm, mul_left_comm] using h

/-- Entrywise reduction of the discrete Gram matrix to two Chebyshev root
sums.  This is the only polynomial-product calculation needed below. -/
theorem two_mul_chebEvalGram_apply
    {n : ℕ} (x : Fin n ↪ ℝ) (j k : Fin n) :
    2 * ((chebEvalMatrix x)ᵀ * chebEvalMatrix x) j k =
      (∑ i : Fin n,
          (T ℝ ((j.val + k.val : ℕ) : ℤ)).eval (x i)) +
        ∑ i : Fin n,
          (T ℝ ((j.val.dist k.val : ℕ) : ℤ)).eval (x i) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, chebEvalMatrix]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_assoc] using
    two_mul_eval_T_mul_eval_T_nat j.val k.val (x i)

/-- Opposite parity makes both the sum and the distance odd. -/
private theorem odd_add_of_not_sameParity
    {a b : ℕ} (h : ¬SameParity a b) :
    Odd (a + b) := by
  rw [Nat.odd_iff]
  unfold SameParity at h
  omega

private theorem odd_dist_of_not_sameParity
    {a b : ℕ} (h : ¬SameParity a b) :
    Odd (a.dist b) := by
  rw [Nat.odd_iff]
  unfold SameParity at h
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
    omega

/-- Abstract entrywise assembly of the model Gram matrix from the four root
sum formulas.  The hypotheses are arranged to match the public statements in
`ChebyshevRootSums`. -/
theorem evalGram_eq_modelGram_of_rootSums
    {N : ℕ} (hN : 6 ≤ N) (x : Fin (N + 1) ↪ ℝ)
    (hzero :
      (∑ i : Fin (N + 1), (T ℝ (0 : ℤ)).eval (x i)) =
        (N + 1 : ℕ))
    (hodd :
      ∀ m : ℕ, m ≤ 2 * N → Odd m →
        (∑ i : Fin (N + 1), (T ℝ (m : ℤ)).eval (x i)) = 0)
    (heven :
      ∀ r : ℕ, 1 ≤ r → r ≤ N - 1 →
        (∑ i : Fin (N + 1), (T ℝ ((2 * r : ℕ) : ℤ)).eval (x i)) =
          (1 / 6 : ℝ) ^ r)
    (htop :
      (∑ i : Fin (N + 1),
          (T ℝ ((2 * N : ℕ) : ℤ)).eval (x i)) =
        (1 / 6 : ℝ) ^ N + (N : ℝ) / 6) :
    (chebEvalMatrix x)ᵀ * chebEvalMatrix x = modelGram N := by
  ext j k
  have htwo := two_mul_chebEvalGram_apply x j k
  have hjN : j.val ≤ N := by omega
  have hkN : k.val ≤ N := by omega
  by_cases hpar : SameParity j.val k.val
  · have hsum_even : Even (j.val + k.val) :=
      (even_add_iff_sameParity j.val k.val).mpr hpar
    have hdist_even : Even (j.val.dist k.val) := by
      refine ⟨j.val.dist k.val / 2, ?_⟩
      have hhalf := two_mul_half_dist_of_sameParity hpar
      omega
    by_cases hjk : j = k
    · subst k
      by_cases hj0 : j.val = 0
      · have hsum0 : j.val + j.val = 0 := by omega
        have hdist0 : j.val.dist j.val = 0 := Nat.dist_self _
        rw [hsum0, hdist0] at htwo
        norm_num only [Nat.cast_zero] at htwo
        rw [hzero] at htwo
        simp only [modelGram, chebD, chebK, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
          if_pos hpar]
        simp [chebDEntry, hj0]
        norm_num at htwo ⊢
        linarith
      · by_cases hjNtop : j.val = N
        · have hsumtop : j.val + j.val = 2 * N := by omega
          have hhalfN : (N + N) / 2 = N := by omega
          have hN0 : N ≠ 0 := by omega
          have hdist0 : j.val.dist j.val = 0 := Nat.dist_self _
          rw [hsumtop, hdist0, htop] at htwo
          norm_num only [Nat.cast_zero] at htwo
          rw [hzero] at htwo
          simp only [modelGram, chebD, chebK, Matrix.add_apply,
            Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
            if_pos hpar]
          simp [chebDEntry, hjNtop, hN0, hhalfN]
          rw [one_div_pow] at htwo
          norm_num at htwo ⊢
          linarith
        · have hjpos : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hj0
          have hjbelow : j.val ≤ N - 1 := by omega
          have hhalf : (j.val + j.val) / 2 = j.val := by omega
          have hsum :
              j.val + j.val = 2 * j.val := by omega
          have hdist0 : j.val.dist j.val = 0 := Nat.dist_self _
          rw [hsum, hdist0, heven j.val hjpos hjbelow] at htwo
          norm_num only [Nat.cast_zero] at htwo
          rw [hzero] at htwo
          simp only [modelGram, chebD, chebK, Matrix.add_apply,
            Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
            if_pos hpar]
          simp [chebDEntry, hj0, hjNtop, hhalf]
          rw [one_div_pow] at htwo
          norm_num at htwo ⊢
          linarith
    · have hsum_pos : 1 ≤ (j.val + k.val) / 2 := by
        have hneval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
        have hhalf :=
          two_mul_half_add_of_sameParity hpar
        omega
      have hsum_below : (j.val + k.val) / 2 ≤ N - 1 := by
        have hhalf := two_mul_half_add_of_sameParity hpar
        have hnotTop : ¬(j.val = N ∧ k.val = N) := by
          rintro ⟨hj, hk⟩
          apply hjk
          exact Fin.ext (hj.trans hk.symm)
        omega
      have hdist_pos : 1 ≤ j.val.dist k.val / 2 := by
        have hhalf := two_mul_half_dist_of_sameParity hpar
        have hneval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
        have hdistne : j.val.dist k.val ≠ 0 := by
          intro hd
          rcases le_total j.val k.val with hjk' | hkj'
          · rw [Nat.dist_eq_sub_of_le hjk'] at hd
            omega
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj'] at hd
            omega
        omega
      have hdist_below : j.val.dist k.val / 2 ≤ N - 1 := by
        have hhalf := two_mul_half_dist_of_sameParity hpar
        have hdist_le : j.val.dist k.val ≤ N := by
          rcases le_total j.val k.val with hjk' | hkj'
          · rw [Nat.dist_eq_sub_of_le hjk']
            omega
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj']
            omega
        omega
      have hsum :
          j.val + k.val = 2 * ((j.val + k.val) / 2) :=
        (two_mul_half_add_of_sameParity hpar).symm
      have hdist :
          j.val.dist k.val = 2 * (j.val.dist k.val / 2) :=
        (two_mul_half_dist_of_sameParity hpar).symm
      rw [hsum, hdist,
        heven _ hsum_pos hsum_below,
        heven _ hdist_pos hdist_below] at htwo
      simp only [modelGram, chebD, chebK, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply, if_neg hjk, if_pos hpar]
      norm_num at htwo ⊢
      linarith
  · have hjk : j ≠ k := by
      intro h
      subst k
      exact hpar rfl
    have hsum_le : j.val + k.val ≤ 2 * N := by omega
    have hdist_le : j.val.dist k.val ≤ 2 * N := by
      rcases le_total j.val k.val with hjk' | hkj'
      · rw [Nat.dist_eq_sub_of_le hjk']
        omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj']
        omega
    rw [hodd _ hsum_le (odd_add_of_not_sameParity hpar),
      hodd _ hdist_le (odd_dist_of_not_sameParity hpar)] at htwo
    simp only [modelGram, chebD, chebK, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply, if_neg hjk, if_neg hpar]
    linarith

/-- The evaluation Gram matrix of the explicit comparison nodes is exactly
the model matrix used in the finite resolvent estimate. -/
theorem chebEvalGram_eq_modelGram
    {N : ℕ} (hN : 6 ≤ N) :
    let hn : 2 ≤ N + 1 := by omega
    (chebEvalMatrix (chebNodes (N + 1) hn))ᵀ *
        chebEvalMatrix (chebNodes (N + 1) hn) = modelGram N := by
  let hn : 2 ≤ N + 1 := by omega
  apply evalGram_eq_modelGram_of_rootSums hN
    (chebNodes (N + 1) hn)
  · simp [T_zero]
  · intro m hm hodd
    exact sum_chebNodes_T_of_odd hn (by omega) hodd
  · intro r hrpos hrmax
    have h := sum_chebNodes_T_even (n := N + 1) (r := r) hn (by omega)
    rw [if_neg (Nat.ne_of_gt hrpos)] at h
    exact h
  · have h := sum_chebNodes_T_top (n := N + 1) hn
    simpa [show N + 1 - 1 = N by omega] using h

/-- Invertibility of an evaluation Gram matrix transfers to `modelGram`
once the two matrices have been identified. -/
theorem modelGram_det_isUnit_of_evalGram_eq
    {N : ℕ} (x : Fin (N + 1) ↪ ℝ)
    (hgram :
      (chebEvalMatrix x)ᵀ * chebEvalMatrix x = modelGram N) :
    IsUnit (modelGram N).det := by
  rw [← hgram, Matrix.det_mul, Matrix.det_transpose]
  exact (chebEvalMatrix_isUnit_det x).mul
    (chebEvalMatrix_isUnit_det x)

/-- The model Gram matrix is nonsingular for the explicit nodes. -/
theorem modelGram_det_isUnit
    {N : ℕ} (hN : 6 ≤ N) :
    IsUnit (modelGram N).det := by
  let hn : 2 ≤ N + 1 := by omega
  apply modelGram_det_isUnit_of_evalGram_eq
    (chebNodes (N + 1) hn)
  exact chebEvalGram_eq_modelGram hN

/-- The interpolation functional is the model trace once the discrete Gram
identity is known. -/
theorem functional_eq_modelTrace_of_evalGram_eq
    {N : ℕ} (x : Fin (N + 1) ↪ ℝ)
    (hgram :
      (chebEvalMatrix x)ᵀ * chebEvalMatrix x = modelGram N) :
    functional x =
      Matrix.trace (chebH N * (modelGram N)⁻¹) := by
  rw [functional_eq_trace, integralGram_eq_chebH, hgram]

/-- Exact trace representation of the functional for the explicit comparison
nodes. -/
theorem functional_chebNodes_eq_modelTrace
    {N : ℕ} (hN : 6 ≤ N) :
    let hn : 2 ≤ N + 1 := by omega
    functional (chebNodes (N + 1) hn) =
      Matrix.trace (chebH N * (modelGram N)⁻¹) := by
  let hn : 2 ≤ N + 1 := by omega
  apply functional_eq_modelTrace_of_evalGram_eq
    (chebNodes (N + 1) hn)
  exact chebEvalGram_eq_modelGram hN

end

end Erdos1131.ChebyshevGram

end PortChebyshevGram

-- Original: Erdos1131/FiniteComparison.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/FiniteComparison.lean; SHA-256 4ee182e2391d9c9904ecda4dd556043d7149900909e1fc4f1208afad5b413c19
section PortFiniteComparison

                              

/-!
# The finite comparison inequality

The root and interpolation calculations reduce the analytic functional to the
trace of the inverse of `modelGram`.  This file combines the exact resolvent
identity with the three scalar estimates used in the final disproof.
-/

namespace Erdos1131.FiniteComparison

open ChebyshevBound ChebyshevResolvent

noncomputable section

theorem trace_modelGram_inv_decomposition
    {N : ℕ} (hN : 0 < N)
    (hunit : IsUnit (modelGram N).det) :
    Matrix.trace (chebH N * (modelGram N)⁻¹) =
      (2 / (N : ℝ)) *
          Matrix.trace (chebH N * chebDInv N) -
        (4 / (N : ℝ) ^ 2) *
          Matrix.trace
            (chebH N * (chebDInv N * chebK N * chebDInv N)) +
        Matrix.trace (chebH N * chebInverseRemainder N) := by
  rw [inv_modelGram_second_order hN hunit]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

/-- Once the bounded first-order trace has its elementary lower bound, the
comparison trace has the explicit estimate needed by the disproof. -/
theorem trace_modelGram_inv_le
    {N : ℕ} (hN : 6 ≤ N)
    (hK : RowBound (chebK N) (13 / 10))
    (hunit : IsUnit (modelGram N).det)
    (hfirstOrder :
      (13 : ℝ) * N / 30 - 13 ≤
        Matrix.trace
          (chebH N * (chebDInv N * chebK N * chebDInv N))) :
    Matrix.trace (chebH N * (modelGram N)⁻¹) ≤
      2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hA := trace_chebH_mul_chebDInv_le hNpos
  have hunitY := isUnit_one_add_chebY_of_modelGram hNpos hunit
  have hE := abs_trace_chebH_inverseRemainder_le hN hK hunitY
  have hE' :
      Matrix.trace (chebH N * chebInverseRemainder N) ≤
        64 / (N : ℝ) ^ 2 :=
    (le_abs_self _).trans hE
  rw [trace_modelGram_inv_decomposition hNpos hunit]
  calc
    (2 / (N : ℝ)) *
          Matrix.trace (chebH N * chebDInv N) -
        (4 / (N : ℝ) ^ 2) *
          Matrix.trace
            (chebH N * (chebDInv N * chebK N * chebDInv N)) +
        Matrix.trace (chebH N * chebInverseRemainder N)
        ≤ (2 / (N : ℝ)) *
              ((N : ℝ) + 5 / 14 + 1 / N) -
            (4 / (N : ℝ) ^ 2) *
              ((13 : ℝ) * N / 30 - 13) +
            64 / (N : ℝ) ^ 2 := by
      have htwo : 0 ≤ (2 : ℝ) / N := by positivity
      have hfour : 0 ≤ (4 : ℝ) / N ^ 2 := by positivity
      gcongr
    _ = 2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2 := by
      field_simp
      ring

end

end Erdos1131.FiniteComparison

end PortFiniteComparison

-- Original: Erdos1131/Main.lean at upstream commit 31574acf09ae50430c08da92288800fe7d26c7fd
-- Current port input: Port/Main.lean; SHA-256 581b50060dcdf2eb5981e5c9b5d0e7ceb682d29104c33af7f9f555dbc9aa70b3
section PortMain

                                
                               
                         
                            

/-!
# Erdős Problem 1131

The explicit roots of `T_(N+1) - (1/6) T_(N-1)` have interpolation
functional at most

`2 - 107 / (105 N) + 118 / N²`.

Consequently the scaled defect is eventually at least `106 / 105`, so it
cannot converge to `1`.
-/

namespace Erdos1131

open ChebyshevBound ChebyshevFirstOrder ChebyshevGram FiniteComparison
open Filter

noncomputable section

/-- The complete finite estimate for the explicit admissible Chebyshev
comparison family. -/
theorem functional_chebNodes_le
    {N : ℕ} (hN : 6 ≤ N) :
    let hn : 2 ≤ N + 1 := by omega
    functional (chebNodes (N + 1) hn) ≤
      2 - 107 / (105 * (N : ℝ)) + 118 / (N : ℝ) ^ 2 := by
  let hn : 2 ≤ N + 1 := by omega
  dsimp only
  rw [functional_chebNodes_eq_modelTrace hN]
  exact trace_modelGram_inv_le hN
    (rowBound_chebK N)
    (modelGram_det_isUnit hN)
    (trace_firstOrder_lower_bound hN)

/-- For every sufficiently large index, the explicit nodes certify the
strictly larger first-order defect `106 / 105`. -/
theorem eventual_cheb_comparison :
    ∀ᶠ N : ℕ in atTop,
      ∃ x : Fin (N + 1) ↪ ℝ,
        Admissible x ∧
          (106 : ℝ) / 105 ≤
            ((N + 1 : ℕ) : ℝ) * (2 - functional x) := by
  filter_upwards [eventually_ge_atTop 24780] with N hN
  let hn : 2 ≤ N + 1 := by omega
  refine ⟨chebNodes (N + 1) hn, chebNodes_admissible hn, ?_⟩
  apply scaled_comparison_of_functional_le hN
  exact functional_chebNodes_le (by omega)

/-- A stronger eventual lower bound on the scaled extremal defect. -/
theorem eventually_scaledDefect_ge :
    ∀ᶠ N : ℕ in atTop, (106 : ℝ) / 105 ≤ scaledDefect N := by
  filter_upwards [eventual_cheb_comparison] with N hN
  obtain ⟨x, hx, hcomparison⟩ := hN
  exact scaledDefect_ge_of_comparison x hx hcomparison

/-- Erdős Problem 1131, as stated, is false. -/
theorem not_erdos_1131 :
    ¬ Tendsto scaledDefect atTop (nhds 1) :=
  not_erdos_1131_of_eventual_comparison eventual_cheb_comparison

end

end Erdos1131

end PortMain

-- PortBridge.lean input SHA-256 af110bf203f161e31e39d24319bf9816a3a87a4c6fe7dabbdfe3a01571d4fcca
section CanonicalBridge

                

open Filter MeasureTheory
open scoped Topology

namespace Jig345Bridge

noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ)
    (k : Fin n) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (t - nodes i) / (nodes k - nodes i)

def Admissible {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Function.Injective nodes ∧
    ∀ k, nodes k ∈ Set.Icc (-1 : ℝ) 1

noncomputable def energy {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ t in Set.Icc (-1 : ℝ) 1,
    (∑ k : Fin n, (lagrangeBasis nodes k t) ^ 2) ∂volume

noncomputable def minimumEnergy (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ,
    Admissible nodes ∧ v = energy nodes}

abbrev statement : Prop :=
  Tendsto (fun n : ℕ => (n : ℝ) * (2 - minimumEnergy n)) atTop (𝓝 1)

theorem functional_eq_energy {n : ℕ} (nodes : Fin n ↪ ℝ) :
    Erdos1131.functional nodes = energy (nodes : Fin n → ℝ) := by
  unfold Erdos1131.functional energy
  simp_rw [Erdos1131.basis_eval_eq_product]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  rfl

theorem values_eq (n : ℕ) :
    Erdos1131.values n =
      {v : ℝ | ∃ nodes : Fin n → ℝ,
        Admissible nodes ∧ v = energy nodes} := by
  ext v
  constructor
  · rintro ⟨nodes, had, hv⟩
    refine ⟨nodes, ⟨nodes.injective, had⟩, ?_⟩
    rw [← functional_eq_energy]
    exact hv.symm
  · rintro ⟨nodes, ⟨hinj, had⟩, hv⟩
    let embedded : Fin n ↪ ℝ := ⟨nodes, hinj⟩
    refine ⟨embedded, had, ?_⟩
    rw [functional_eq_energy]
    exact hv.symm

theorem minimumEnergy_eq_M (n : ℕ) : minimumEnergy n = Erdos1131.M n := by
  unfold minimumEnergy Erdos1131.M
  rw [values_eq]

theorem not_statement : ¬ statement := by
  intro h
  apply Erdos1131.not_erdos_1131
  have hshift := (tendsto_add_atTop_iff_nat 1).2 h
  change Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
    (2 - Erdos1131.M (n + 1))) atTop (𝓝 1)
  simpa only [minimumEnergy_eq_M] using hshift

end Jig345Bridge

                                        

end CanonicalBridge

theorem proof : ¬ Jig345Bridge.statement := Jig345Bridge.not_statement

end Submissions.Erdos1131AsymptoticRefutation.ChebyshevPort

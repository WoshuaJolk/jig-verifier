/-
Ported 2026-09-07 from Kenta Kitamura, commit 9ae46727eef654665a51e8341961feb0127a2a44.
Based on Liam Price / GPT-5.5 Pro and Nat Sothanaphan proofs.
Changes: port to Lean4.33 and current pinned Mathlib; restrict source to lower-bound proof; add exact Jig root bridge.
Original license reproduced below.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
/-
Background:
This file formalizes work related to Erdos Problems #1039.  It is based on:

* a natural-language proof PDF by Liam Price, reportedly developed with GPT
  assistance:
    https://www.overleaf.com/project/69fba41e9e7830016040c90e

* the public Erdos Problems #1039 forum discussion:
    https://www.erdosproblems.com/forum/thread/1039

AI usage:
The code was created with assistance from Codex 5.5 using xhigh reasoning.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

-- Lean 4.29-compatible elaboration; proofs are still checked by the kernel.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators ENNReal

noncomputable section

namespace Submissions.Erdos1039LemniscateInradius.KitamuraPort

/--
`fval z w` is the monic polynomial value

  ∏ i, (w - z i)

when the roots are listed as `z : Fin n → ℂ`.

This avoids `Polynomial.roots` while we experiment with the estimate.
-/
def fval {n : ℕ} (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∏ i : Fin n, (w - z i)

/-- The lemniscate interior `{w : ‖f(w)‖ < 1}` for the root list `z`. -/
def lemniscate {n : ℕ} (z : Fin n → ℂ) : Set ℂ :=
  {w | ‖fval z w‖ < 1}

/--
The elementary rewriting behind the product bound:
`|f(w_j)|` is the product of the distances from `w_j` to all roots.
-/
lemma norm_fval_eq_prod {n : ℕ} (z : Fin n → ℂ) (w : ℂ) :
    ‖fval z w‖ = ∏ i : Fin n, ‖w - z i‖ := by
  simp [fval, norm_prod]

/-- The monic product `fval` vanishes at every listed root. -/
lemma fval_at_root {n : ℕ} (z : Fin n → ℂ) (j : Fin n) :
    fval z (z j) = 0 := by
  unfold fval
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

/--
The full product over values `f(w_j)`, rewritten as a matrix of distances.
-/
lemma prod_norm_fval_eq_prod_prod {n : ℕ} (z w : Fin n → ℂ) :
    (∏ j : Fin n, ‖fval z (w j)‖)
      = ∏ j : Fin n, ∏ i : Fin n, ‖w j - z i‖ := by
  simp [norm_fval_eq_prod]

/--
The part of the distance matrix with the diagonal factors removed.

For fixed `j`, the missing factor is the easy one `‖w j - z j‖`.
The remaining factors `‖w j - z i‖` with `i ≠ j` are where the real
content of the product bound lives.
-/
def offDiagProduct {n : ℕ} (z w : Fin n → ℂ) : ℝ :=
  ∏ j : Fin n, (Finset.univ.erase j).prod fun i => ‖w j - z i‖

/-- Ordered off-diagonal index pairs `(j, i)` with `i ≠ j`. -/
def offDiagPairs {n : ℕ} : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun p => p.2 ≠ p.1

/-- The ordered pairs above the diagonal: `(j, i)` with `j < i`. -/
def upperOffDiagPairs {n : ℕ} : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun p => p.1 < p.2

/-- The ordered pairs below the diagonal: `(j, i)` with `i < j`. -/
def lowerOffDiagPairs {n : ℕ} : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun p => p.2 < p.1

/--
The paired off-diagonal product: for every unordered pair of indices, keep the
two cross terms together.
-/
def pairedOffDiagProduct {n : ℕ} (z w : Fin n → ℂ) : ℝ :=
  (upperOffDiagPairs : Finset (Fin n × Fin n)).prod
    fun p => ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖

/--
For one point cloud, multiply the shifted mutual distances over unordered
pairs.  This is the product to which the PDF's separation estimate is applied.
-/
def separationProduct {n : ℕ} (x : Fin n → ℂ) (σ : ℝ) : ℝ :=
  (upperOffDiagPairs : Finset (Fin n × Fin n)).prod
    fun p => ‖x p.1 - x p.2‖ + σ

/--
The product obtained after pairing the off-diagonal factors and bounding each
pair by a `z`-distance term times a `w`-distance term.
-/
def pairedSeparationProduct {n : ℕ} (z w : Fin n → ℂ) (σ : ℝ) : ℝ :=
  (upperOffDiagPairs : Finset (Fin n × Fin n)).prod
    fun p => (‖z p.1 - z p.2‖ + σ) * (‖w p.1 - w p.2‖ + σ)

/--
The quadratic separation product from the PDF's Lemma 4:
`∏_{i<j} (‖x_i - x_j‖^2 + σ^2)`.
-/
def quadraticSeparationProduct {n : ℕ} (x : Fin n → ℂ) (σ : ℝ) : ℝ :=
  (upperOffDiagPairs : Finset (Fin n × Fin n)).prod
    fun p => ‖x p.1 - x p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)

/--
The ordered Blaschke-type product from PDF Lemma 3:
`∏_{i≠j} |1 - a x_i \overline{x_j}|`.

This is the analytic input used in PDF Lemma 4 before translating back to
ordinary Euclidean distances.
-/
def blaschkeOffDiagProduct {n : ℕ} (x : Fin n → ℂ) (a : ℝ) : ℝ :=
  (offDiagPairs : Finset (Fin n × Fin n)).prod
    fun p => ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖

/-- One ordered Blaschke off-diagonal factor. -/
def blaschkePairFactor {n : ℕ} (x : Fin n → ℂ) (a : ℝ)
    (p : Fin n × Fin n) : ℝ :=
  ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖

/--
The part of the ordered Blaschke product where at least one coordinate is the
chosen index `k`.
-/
def blaschkeIncidentPairProduct {n : ℕ} (x : Fin n → ℂ) (a : ℝ)
    (k : Fin n) : ℝ :=
  ((offDiagPairs : Finset (Fin n × Fin n)).filter
    (fun p => p.1 = k ∨ p.2 = k)).prod (blaschkePairFactor x a)

/--
The part of the ordered Blaschke product whose two coordinates are both
different from `k`.
-/
def blaschkeNonincidentProduct {n : ℕ} (x : Fin n → ℂ) (a : ℝ)
    (k : Fin n) : ℝ :=
  ((offDiagPairs : Finset (Fin n × Fin n)).filter
    (fun p => ¬ (p.1 = k ∨ p.2 = k))).prod (blaschkePairFactor x a)

/--
The same Blaschke-type product, but including the diagonal ordered pairs.

On the torus this full product is useful because the diagonal factors are
exactly `(1-a)^n`.  Away from the torus, the full product is not the right
object for a maximum-modulus reduction; the off-diagonal product above is the
one used in Lemma 4.
-/
def blaschkeFullProduct {n : ℕ} (x : Fin n → ℂ) (a : ℝ) : ℝ :=
  ((Finset.univ : Finset (Fin n)).diag ∪
      (Finset.univ : Finset (Fin n)).offDiag).prod
    fun p => ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖

/-- The full Blaschke-type product written as a product over all ordered pairs. -/
def blaschkeAllPairsProduct {n : ℕ} (x : Fin n → ℂ) (a : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n × Fin n)).prod
    fun p => ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖

/-- The diagonal part of the full Blaschke-type product. -/
def blaschkeDiagProduct {n : ℕ} (x : Fin n → ℂ) (a : ℝ) : ℝ :=
  ((Finset.univ : Finset (Fin n)).diag).prod
    fun p => ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖

/-- All listed points lie on the unit circle. -/
def onUnitCircle {n : ℕ} (x : Fin n → ℂ) : Prop :=
  ∀ i, ‖x i‖ = 1

/--
The logarithmic gap used in the torus proof of PDF Lemma 3:

`g(a) = n log(1-a^n) - Σ_{j,k} log |1-a ω_j \barω_k|`.
-/
def blaschkeLogGap (n : ℕ) (ω : Fin n → ℂ) (a : ℝ) : ℝ :=
  (n : ℝ) * Real.log (1 - a ^ n) -
    (Finset.univ : Finset (Fin n × Fin n)).sum
      (fun p => Real.log ‖1 - (a : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖)

/--
The expression that appears after the PDF differentiates `g` and multiplies by
the positive parameter:

`a g'(a) = Σ Re(1 / (1-aω_j\barω_k)) - n²/(1-a^n)`.

PDF Lemma 2 proves this quantity is nonnegative on the torus.
-/
def blaschkeDerivativeGap (n : ℕ) (ω : Fin n → ℂ) (a : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n × Fin n)).sum
      (fun p => ((1 : ℂ) /
        (1 - (a : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2))).re)
    - (n : ℝ) ^ (2 : ℕ) / (1 - a ^ n)

/-- The real Szego-kernel sum appearing in PDF Lemma 2. -/
def szegoKernelRealSum {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  (Finset.univ : Finset (Fin n × Fin n)).sum
    (fun p => ((1 : ℂ) /
      (1 - z p.1 * (starRingEnd ℂ) (z p.2))).re)

/-- The Blaschke-product defect `1 - |∏ z_i|²` from PDF Lemma 2. -/
def szegoKernelProductDefect {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  1 - ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ)

/--
The nonnegative power-series expansion of the Szego-kernel sum:
`∑_m |∑_i z_i^m|²`.
-/
def szegoKernelPowerNormSqSum {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∑' m : ℕ, Complex.normSq (∑ i : Fin n, z i ^ m)

/-- The constant `Λ = B(0) = (-1)^n ∏ z_i` for the finite Blaschke product. -/
def blaschkeLambda {n : ℕ} (z : Fin n → ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ∏ i : Fin n, z i

/-- A single disk Blaschke factor `(w-a)/(1-\bar a w)`. -/
def diskBlaschkeFactor (a w : ℂ) : ℂ :=
  (w - a) / (1 - (starRingEnd ℂ) a * w)

/-- The finite Blaschke product with zeros at the listed points. -/
def finiteBlaschkeProduct {n : ℕ} (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∏ i : Fin n, diskBlaschkeFactor (z i) w

/-- The defect function `1 - \bar Λ B(w)` used in PDF Lemma 2. -/
def szegoKernelDefectValue {n : ℕ} (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  1 - (starRingEnd ℂ) (blaschkeLambda z) * finiteBlaschkeProduct z w

/--
The right-hand side of the PDF's quadratic separation estimate:

`A^{n(n-1)} * (sinh(n α) / sinh α)^n`,
where `α = arsinh (σ / (2A))`.
-/
def quadraticSeparationBound (n : ℕ) (A σ : ℝ) : ℝ :=
  let α := Real.arsinh (σ / (2 * A))
  A ^ (n * (n - 1)) * (Real.sinh ((n : ℝ) * α) / Real.sinh α) ^ n

/-- In degree zero, the quadratic separation product is empty. -/
lemma quadraticSeparationProduct_zero
    (x : Fin 0 → ℂ) (σ : ℝ) :
    quadraticSeparationProduct x σ = 1 := by
  simp [quadraticSeparationProduct, upperOffDiagPairs]

/-- In degree zero, the PDF Lemma 4 right-hand side is also `1`. -/
lemma quadraticSeparationBound_zero
    (A σ : ℝ) :
    quadraticSeparationBound 0 A σ = 1 := by
  simp [quadraticSeparationBound]

/-- The PDF Lemma 4 estimate is proved directly in degree zero. -/
theorem quadraticSeparationProduct_bound_zero
    (x : Fin 0 → ℂ)
    {A σ : ℝ} :
    quadraticSeparationProduct x σ ≤ quadraticSeparationBound 0 A σ := by
  rw [quadraticSeparationProduct_zero, quadraticSeparationBound_zero]

/-- In degree one, there are no unordered pairs, so the product is empty. -/
lemma quadraticSeparationProduct_one
    (x : Fin 1 → ℂ) (σ : ℝ) :
    quadraticSeparationProduct x σ = 1 := by
  have hupper :
      (upperOffDiagPairs : Finset (Fin 1 × Fin 1)) = ∅ := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i
    fin_cases j
    simp [upperOffDiagPairs]
  simp [quadraticSeparationProduct, hupper]

/-- In degree one, the PDF Lemma 4 right-hand side simplifies to `1`. -/
lemma quadraticSeparationBound_one
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ) :
    quadraticSeparationBound 1 A σ = 1 := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  simp [quadraticSeparationBound, hA_ne, hσ_ne]

/-- The PDF Lemma 4 estimate is proved directly in degree one. -/
theorem quadraticSeparationProduct_bound_one
    (x : Fin 1 → ℂ)
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ) :
    quadraticSeparationProduct x σ ≤ quadraticSeparationBound 1 A σ := by
  rw [quadraticSeparationProduct_one, quadraticSeparationBound_one hA hσ]

/-- In degree two, there is exactly one unordered pair of indices. -/
lemma upperOffDiagPairs_two :
    (upperOffDiagPairs : Finset (Fin 2 × Fin 2)) = {((0 : Fin 2), (1 : Fin 2))} := by
  ext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [upperOffDiagPairs]

/-- In degree two, the quadratic separation product has one factor. -/
lemma quadraticSeparationProduct_two
    (x : Fin 2 → ℂ) (σ : ℝ) :
    quadraticSeparationProduct x σ =
      ‖x 0 - x 1‖ ^ (2 : ℕ) + σ ^ (2 : ℕ) := by
  simp [quadraticSeparationProduct, upperOffDiagPairs_two]

/--
In degree two, the PDF Lemma 4 right-hand side simplifies to
`(2A)^2 + σ^2`.
-/
lemma quadraticSeparationBound_two
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ) :
    quadraticSeparationBound 2 A σ = (2 * A) ^ (2 : ℕ) + σ ^ (2 : ℕ) := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hden_ne : 2 * A ≠ 0 := mul_ne_zero two_ne_zero hA_ne
  have harg_ne : σ / (2 * A) ≠ 0 := div_ne_zero hσ_ne hden_ne
  simp [quadraticSeparationBound, Real.sinh_two_mul, Real.sinh_arsinh,
    Real.cosh_arsinh]
  field_simp [harg_ne, hA_ne, hσ_ne]
  rw [Real.sq_sqrt]
  · field_simp [hA_ne]
  · positivity

/-- If two points lie in the disk of radius `A`, their distance is at most `2A`. -/
lemma norm_sub_le_two_mul_of_norm_le
    {x₀ x₁ : ℂ} {A : ℝ}
    (hx₀ : ‖x₀‖ ≤ A) (hx₁ : ‖x₁‖ ≤ A) :
    ‖x₀ - x₁‖ ≤ 2 * A := by
  calc
    ‖x₀ - x₁‖ = ‖x₀ + -x₁‖ := by rw [sub_eq_add_neg]
    _ ≤ ‖x₀‖ + ‖-x₁‖ := norm_add_le _ _
    _ = ‖x₀‖ + ‖x₁‖ := by simp
    _ ≤ A + A := add_le_add hx₀ hx₁
    _ = 2 * A := by ring

/-- The PDF Lemma 4 estimate is proved directly in degree two. -/
theorem quadraticSeparationProduct_bound_two
    (x : Fin 2 → ℂ)
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ)
    (hx : ∀ i, ‖x i‖ ≤ A) :
    quadraticSeparationProduct x σ ≤ quadraticSeparationBound 2 A σ := by
  rw [quadraticSeparationProduct_two, quadraticSeparationBound_two hA hσ]
  have hdist : ‖x 0 - x 1‖ ≤ 2 * A :=
    norm_sub_le_two_mul_of_norm_le (hx 0) (hx 1)
  have htwoA_nonneg : 0 ≤ 2 * A := (mul_pos two_pos hA).le
  have hdist_sq :
      ‖x 0 - x 1‖ ^ (2 : ℕ) ≤ (2 * A) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ (norm_nonneg _) htwoA_nonneg).2 hdist
  exact add_le_add hdist_sq (le_refl (σ ^ (2 : ℕ)))

/-- In degree three, there are exactly three unordered pairs of indices. -/
lemma upperOffDiagPairs_three :
    (upperOffDiagPairs : Finset (Fin 3 × Fin 3)) =
      {((0 : Fin 3), (1 : Fin 3)), ((0 : Fin 3), (2 : Fin 3)),
        ((1 : Fin 3), (2 : Fin 3))} := by
  ext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [upperOffDiagPairs]

/-- In degree three, the quadratic separation product has the three edge factors. -/
lemma quadraticSeparationProduct_three
    (x : Fin 3 → ℂ) (σ : ℝ) :
    quadraticSeparationProduct x σ =
      (‖x 0 - x 1‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) *
        (‖x 0 - x 2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) *
          (‖x 1 - x 2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) := by
  simp [quadraticSeparationProduct, upperOffDiagPairs_three, mul_assoc]

/-- In degree four, there are exactly six unordered pairs of indices. -/
lemma upperOffDiagPairs_four :
    (upperOffDiagPairs : Finset (Fin 4 × Fin 4)) =
      {((0 : Fin 4), (1 : Fin 4)), ((0 : Fin 4), (2 : Fin 4)),
        ((0 : Fin 4), (3 : Fin 4)), ((1 : Fin 4), (2 : Fin 4)),
        ((1 : Fin 4), (3 : Fin 4)), ((2 : Fin 4), (3 : Fin 4))} := by
  ext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [upperOffDiagPairs]

/-- In degree four, the quadratic separation product has the six edge factors. -/
lemma quadraticSeparationProduct_four
    (x : Fin 4 → ℂ) (σ : ℝ) :
    quadraticSeparationProduct x σ =
      (‖x 0 - x 1‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) *
        (‖x 0 - x 2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) *
          (‖x 0 - x 3‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) *
            (‖x 1 - x 2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) *
              (‖x 1 - x 3‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) *
                (‖x 2 - x 3‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) := by
  simp [quadraticSeparationProduct, upperOffDiagPairs_four, mul_assoc]

/-- In degree four, the paired off-diagonal product has six paired factors. -/
lemma pairedOffDiagProduct_four
    (z w : Fin 4 → ℂ) :
    pairedOffDiagProduct z w =
      (‖w 0 - z 1‖ * ‖w 1 - z 0‖) *
        (‖w 0 - z 2‖ * ‖w 2 - z 0‖) *
          (‖w 0 - z 3‖ * ‖w 3 - z 0‖) *
            (‖w 1 - z 2‖ * ‖w 2 - z 1‖) *
              (‖w 1 - z 3‖ * ‖w 3 - z 1‖) *
                (‖w 2 - z 3‖ * ‖w 3 - z 2‖) := by
  simp [pairedOffDiagProduct, upperOffDiagPairs_four, mul_assoc]

/-- A useful hyperbolic triple-angle quotient for the degree-three case. -/
lemma sinh_three_mul_div_sinh {α : ℝ} (hα : Real.sinh α ≠ 0) :
    Real.sinh (3 * α) / Real.sinh α = 3 + 4 * Real.sinh α ^ (2 : ℕ) := by
  rw [show (3 : ℝ) * α = 2 * α + α by ring]
  rw [Real.sinh_add, Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp [hα]
  rw [Real.cosh_sq]
  ring

/-- A useful hyperbolic quadruple-angle quotient for the degree-four case. -/
lemma sinh_four_mul_div_sinh {α : ℝ} (hα : Real.sinh α ≠ 0) :
    Real.sinh (4 * α) / Real.sinh α =
      4 * Real.cosh α * (1 + 2 * Real.sinh α ^ (2 : ℕ)) := by
  rw [show (4 : ℝ) * α = 2 * α + 2 * α by ring]
  rw [Real.sinh_add, Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp [hα]
  rw [Real.cosh_sq]
  ring

/--
The fourth power of the degree-four hyperbolic quotient, written without
square roots.  This is the shape needed to simplify the PDF Lemma 4 bound.
-/
lemma sinh_four_mul_div_sinh_pow_four {α : ℝ} (hα : Real.sinh α ≠ 0) :
    (Real.sinh (4 * α) / Real.sinh α) ^ (4 : ℕ) =
      (4 : ℝ) ^ (4 : ℕ)
        * (1 + Real.sinh α ^ (2 : ℕ)) ^ (2 : ℕ)
        * (1 + 2 * Real.sinh α ^ (2 : ℕ)) ^ (4 : ℕ) := by
  have hcosh4 :
      Real.cosh α ^ (4 : ℕ) =
        (1 + Real.sinh α ^ (2 : ℕ)) ^ (2 : ℕ) := by
    calc
      Real.cosh α ^ (4 : ℕ)
          = (Real.cosh α ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (1 + Real.sinh α ^ (2 : ℕ)) ^ (2 : ℕ) := by
          rw [Real.cosh_sq]
          ring
  rw [sinh_four_mul_div_sinh hα]
  rw [show (4 * Real.cosh α * (1 + 2 * Real.sinh α ^ (2 : ℕ))) ^ (4 : ℕ)
      = (4 : ℝ) ^ (4 : ℕ) * Real.cosh α ^ (4 : ℕ)
        * (1 + 2 * Real.sinh α ^ (2 : ℕ)) ^ (4 : ℕ) by ring]
  rw [hcosh4]

/--
In degree three, the PDF Lemma 4 right-hand side simplifies to
`(3A^2 + σ^2)^3`.
-/
lemma quadraticSeparationBound_three
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ) :
    quadraticSeparationBound 3 A σ =
      (3 * A ^ (2 : ℕ) + σ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hden_ne : 2 * A ≠ 0 := mul_ne_zero two_ne_zero hA_ne
  have harg_ne : σ / (2 * A) ≠ 0 := div_ne_zero hσ_ne hden_ne
  let α := Real.arsinh (σ / (2 * A))
  have hsinh_ne : Real.sinh α ≠ 0 := by
    dsimp [α]
    simpa [Real.sinh_arsinh] using harg_ne
  dsimp [quadraticSeparationBound]
  change A ^ (3 * (3 - 1)) * (Real.sinh ((3 : ℝ) * α) / Real.sinh α) ^ (3 : ℕ) =
    (3 * A ^ (2 : ℕ) + σ ^ (2 : ℕ)) ^ (3 : ℕ)
  norm_num
  rw [sinh_three_mul_div_sinh hsinh_ne]
  dsimp [α]
  rw [Real.sinh_arsinh]
  field_simp [hA_ne]
  ring

/--
In degree four, the PDF Lemma 4 right-hand side simplifies to the value
attained by a square on the circle of radius `A`:
two diagonal factors `4A² + σ²` and four side factors `2A² + σ²`.
-/
lemma quadraticSeparationBound_four
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ) :
    quadraticSeparationBound 4 A σ =
      (4 * A ^ (2 : ℕ) + σ ^ (2 : ℕ)) ^ (2 : ℕ)
        * (2 * A ^ (2 : ℕ) + σ ^ (2 : ℕ)) ^ (4 : ℕ) := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hden_ne : 2 * A ≠ 0 := mul_ne_zero two_ne_zero hA_ne
  have harg_ne : σ / (2 * A) ≠ 0 := div_ne_zero hσ_ne hden_ne
  let α := Real.arsinh (σ / (2 * A))
  have hsinh_ne : Real.sinh α ≠ 0 := by
    dsimp [α]
    simpa [Real.sinh_arsinh] using harg_ne
  dsimp [quadraticSeparationBound]
  change A ^ (4 * (4 - 1)) * (Real.sinh ((4 : ℝ) * α) / Real.sinh α) ^ (4 : ℕ) =
    (4 * A ^ (2 : ℕ) + σ ^ (2 : ℕ)) ^ (2 : ℕ)
      * (2 * A ^ (2 : ℕ) + σ ^ (2 : ℕ)) ^ (4 : ℕ)
  norm_num
  rw [sinh_four_mul_div_sinh_pow_four hsinh_ne]
  dsimp [α]
  rw [Real.sinh_arsinh]
  field_simp [hA_ne]
  ring

/--
For three complex points, the sum of squared edge lengths plus the squared
norm of the total sum equals three times the sum of squared norms.
-/
lemma three_pair_sq_sum_add_normSq_sum
    (a b c : ℂ) :
    ‖a - b‖ ^ (2 : ℕ) + ‖a - c‖ ^ (2 : ℕ) + ‖b - c‖ ^ (2 : ℕ)
        + Complex.normSq (a + b + c)
      = 3 * (‖a‖ ^ (2 : ℕ) + ‖b‖ ^ (2 : ℕ) + ‖c‖ ^ (2 : ℕ)) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_sub]
  rw [show a + b + c = (a + b) + c by ring]
  rw [Complex.normSq_add, Complex.normSq_add]
  simp
  ring

/-- If three points lie in the disk of radius `A`, their squared edge lengths sum to at most `9A^2`. -/
lemma three_pair_sq_sum_le_nine_mul
    {a b c : ℂ} {A : ℝ}
    (hA : 0 ≤ A)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A) (hc : ‖c‖ ≤ A) :
    ‖a - b‖ ^ (2 : ℕ) + ‖a - c‖ ^ (2 : ℕ) + ‖b - c‖ ^ (2 : ℕ)
      ≤ 9 * A ^ (2 : ℕ) := by
  have hsum_nonneg : 0 ≤ Complex.normSq (a + b + c) := Complex.normSq_nonneg _
  have hidentity := three_pair_sq_sum_add_normSq_sum a b c
  have hpair_le_norms :
      ‖a - b‖ ^ (2 : ℕ) + ‖a - c‖ ^ (2 : ℕ) + ‖b - c‖ ^ (2 : ℕ)
        ≤ 3 * (‖a‖ ^ (2 : ℕ) + ‖b‖ ^ (2 : ℕ) + ‖c‖ ^ (2 : ℕ)) := by
    nlinarith
  have ha_sq : ‖a‖ ^ (2 : ℕ) ≤ A ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) hA).2 ha
  have hb_sq : ‖b‖ ^ (2 : ℕ) ≤ A ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) hA).2 hb
  have hc_sq : ‖c‖ ^ (2 : ℕ) ≤ A ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) hA).2 hc
  nlinarith

/-- Three-variable AM-GM in the polynomial form needed for the degree-three case. -/
lemma three_nonneg_prod_le_cube_of_sum_le
    {a b c M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c ≤ 3 * M) :
    a * b * c ≤ M ^ (3 : ℕ) := by
  have hamgm : 27 * a * b * c ≤ (a + b + c) ^ (3 : ℕ) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
  have hsum_nonneg : 0 ≤ a + b + c := by positivity
  have hpow : (a + b + c) ^ (3 : ℕ) ≤ (3 * M) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hsum_nonneg hsum 3
  nlinarith

/-- The PDF Lemma 4 estimate is proved directly in degree three. -/
theorem quadraticSeparationProduct_bound_three
    (x : Fin 3 → ℂ)
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ)
    (hx : ∀ i, ‖x i‖ ≤ A) :
    quadraticSeparationProduct x σ ≤ quadraticSeparationBound 3 A σ := by
  rw [quadraticSeparationProduct_three, quadraticSeparationBound_three hA hσ]
  let a : ℝ := ‖x 0 - x 1‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)
  let b : ℝ := ‖x 0 - x 2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)
  let c : ℝ := ‖x 1 - x 2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)
  let M : ℝ := 3 * A ^ (2 : ℕ) + σ ^ (2 : ℕ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hdist_sum :
      ‖x 0 - x 1‖ ^ (2 : ℕ) + ‖x 0 - x 2‖ ^ (2 : ℕ) + ‖x 1 - x 2‖ ^ (2 : ℕ)
        ≤ 9 * A ^ (2 : ℕ) :=
    three_pair_sq_sum_le_nine_mul hA.le (hx 0) (hx 1) (hx 2)
  have hsum : a + b + c ≤ 3 * M := by
    dsimp [a, b, c, M]
    nlinarith
  have hprod : a * b * c ≤ M ^ (3 : ℕ) :=
    three_nonneg_prod_le_cube_of_sum_le ha hb hc hsum
  simpa [a, b, c, M, mul_assoc] using hprod

/--
The real part of the full cross-term sum is the squared norm of the total sum.
This is the algebraic core behind the general pairwise-distance identity.
-/
lemma cross_sum_re_eq_normSq_sum
    {n : ℕ} (x : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, (x i * (starRingEnd ℂ) (x j)).re)
      = Complex.normSq (∑ i : Fin n, x i) := by
  have hcomplex :
      (∑ i : Fin n, ∑ j : Fin n, x i * (starRingEnd ℂ) (x j))
        = (∑ i : Fin n, x i) * (starRingEnd ℂ) (∑ i : Fin n, x i) := by
    rw [Finset.sum_comm]
    simp [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i : Fin n, ∑ j : Fin n, (x i * (starRingEnd ℂ) (x j)).re)
        = (∑ i : Fin n, ∑ j : Fin n, x i * (starRingEnd ℂ) (x j)).re := by
          simp
    _ = ((∑ i : Fin n, x i) * (starRingEnd ℂ) (∑ i : Fin n, x i)).re := by
          rw [hcomplex]
    _ = Complex.normSq (∑ i : Fin n, x i) := by
          rw [Complex.mul_conj]
          simp

/-- The doubled cross-term version of `cross_sum_re_eq_normSq_sum`. -/
lemma two_mul_cross_sum_re_eq_two_normSq_sum
    {n : ℕ} (x : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, 2 * (x i * (starRingEnd ℂ) (x j)).re)
      = 2 * Complex.normSq (∑ i : Fin n, x i) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, 2 * (x i * (starRingEnd ℂ) (x j)).re)
        = 2 * (∑ i : Fin n, ∑ j : Fin n, (x i * (starRingEnd ℂ) (x j)).re) := by
          simp [Finset.mul_sum]
    _ = 2 * Complex.normSq (∑ i : Fin n, x i) := by
          rw [cross_sum_re_eq_normSq_sum]

/--
The ordered-pair squared-distance identity:
`Σ_{i,j} ‖x_i - x_j‖² + 2‖Σ_i x_i‖² = 2n Σ_i ‖x_i‖²`.
-/
lemma ordered_pair_sq_sum_identity
    {n : ℕ} (x : Fin n → ℂ) :
    (∑ p : Fin n × Fin n, ‖x p.1 - x p.2‖ ^ (2 : ℕ))
        + 2 * Complex.normSq (∑ i : Fin n, x i)
      = 2 * (n : ℝ) * (∑ i : Fin n, ‖x i‖ ^ (2 : ℕ)) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [two_mul_cross_sum_re_eq_two_normSq_sum]
  rw [← Finset.mul_sum]
  ring

/-- The diagonal contributes zero to the ordered squared-distance sum. -/
lemma ordered_sq_sum_eq_offDiag_sum
    {n : ℕ} (x : Fin n → ℂ) :
    (∑ p : Fin n × Fin n, ‖x p.1 - x p.2‖ ^ (2 : ℕ))
      = (offDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖x p.1 - x p.2‖ ^ (2 : ℕ)) := by
  classical
  symm
  rw [offDiagPairs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : p.2 = p.1
  · simp [h]
  · simp [h]

/--
The paired separation product factors into the separation product for the roots
and the separation product for the nearby points.
-/
lemma pairedSeparationProduct_eq_mul
    {n : ℕ} (z w : Fin n → ℂ) (σ : ℝ) :
    pairedSeparationProduct z w σ
      = separationProduct z σ * separationProduct w σ := by
  unfold pairedSeparationProduct separationProduct
  rw [Finset.prod_mul_distrib]

/--
The off-diagonal product can also be read as a product over ordered pairs
`(j, i)` with `i ≠ j`.
-/
lemma offDiagProduct_eq_pairProduct
    {n : ℕ} (z w : Fin n → ℂ) :
    offDiagProduct z w
      = (offDiagPairs : Finset (Fin n × Fin n)).prod
          (fun p => ‖w p.1 - z p.2‖) := by
  classical
  symm
  simpa [offDiagProduct, offDiagPairs, and_assoc, and_left_comm, and_comm] using
    (Finset.prod_finset_product
      (r := (Finset.univ.product Finset.univ).filter fun p : Fin n × Fin n => p.2 ≠ p.1)
      (s := (Finset.univ : Finset (Fin n)))
      (t := fun j : Fin n => Finset.univ.erase j)
      (f := fun p : Fin n × Fin n => ‖w p.1 - z p.2‖)
      (by
        intro p
        simp [and_comm]))

/-- The off-diagonal ordered pairs split into the two strict halves. -/
lemma offDiagPairs_eq_upper_union_lower {n : ℕ} :
    (offDiagPairs : Finset (Fin n × Fin n))
      = upperOffDiagPairs ∪ lowerOffDiagPairs := by
  classical
  ext p
  simp only [offDiagPairs, upperOffDiagPairs, lowerOffDiagPairs,
    Finset.mem_filter, Finset.mem_union]
  constructor
  · intro hne
    rcases lt_or_gt_of_ne hne.2.symm with hlt | hlt
    · exact Or.inl ⟨hne.1, hlt⟩
    · exact Or.inr ⟨hne.1, hlt⟩
  · intro hlt
    rcases hlt with hlt | hlt
    · exact ⟨hlt.1, (ne_of_lt hlt.2).symm⟩
    · exact ⟨hlt.1, ne_of_lt hlt.2⟩

/-- The two strict halves of the off-diagonal are disjoint. -/
lemma upperOffDiagPairs_disjoint_lowerOffDiagPairs {n : ℕ} :
    Disjoint (upperOffDiagPairs : Finset (Fin n × Fin n)) lowerOffDiagPairs := by
  classical
  rw [Finset.disjoint_left]
  intro p hp_upper hp_lower
  simp [upperOffDiagPairs] at hp_upper
  simp [lowerOffDiagPairs] at hp_lower
  exact (not_lt_of_ge hp_upper.le) hp_lower

/-- Split a product over all ordered off-diagonal pairs into upper and lower halves. -/
lemma offDiagPairProduct_eq_upper_mul_lower
    {n : ℕ} (F : Fin n × Fin n → ℝ) :
    (offDiagPairs : Finset (Fin n × Fin n)).prod F
      = ((upperOffDiagPairs : Finset (Fin n × Fin n)).prod F)
        * ((lowerOffDiagPairs : Finset (Fin n × Fin n)).prod F) := by
  rw [offDiagPairs_eq_upper_union_lower]
  exact Finset.prod_union upperOffDiagPairs_disjoint_lowerOffDiagPairs

/--
The lower-half product is the upper-half product after swapping the two
coordinates.
-/
lemma lowerOffDiagPairProduct_eq_upper_swap
    {n : ℕ} (F : Fin n × Fin n → ℝ) :
    (lowerOffDiagPairs : Finset (Fin n × Fin n)).prod F
      = (upperOffDiagPairs : Finset (Fin n × Fin n)).prod
          (fun p => F (p.2, p.1)) := by
  classical
  refine Finset.prod_equiv (Equiv.prodComm (Fin n) (Fin n)) ?_ ?_
  · intro p
    cases p
    simp [lowerOffDiagPairs, upperOffDiagPairs]
  · intro p _hp
    cases p
    rfl

/-- Sum version of the upper/lower off-diagonal split. -/
lemma offDiagPairSum_eq_upper_add_lower
    {n : ℕ} (F : Fin n × Fin n → ℝ) :
    (offDiagPairs : Finset (Fin n × Fin n)).sum F
      = ((upperOffDiagPairs : Finset (Fin n × Fin n)).sum F)
        + ((lowerOffDiagPairs : Finset (Fin n × Fin n)).sum F) := by
  rw [offDiagPairs_eq_upper_union_lower]
  exact Finset.sum_union upperOffDiagPairs_disjoint_lowerOffDiagPairs

/-- Sum version of swapping the lower off-diagonal half into the upper half. -/
lemma lowerOffDiagPairSum_eq_upper_swap
    {n : ℕ} (F : Fin n × Fin n → ℝ) :
    (lowerOffDiagPairs : Finset (Fin n × Fin n)).sum F
      = (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => F (p.2, p.1)) := by
  classical
  refine Finset.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) ?_ ?_
  · intro p
    cases p
    simp [lowerOffDiagPairs, upperOffDiagPairs]
  · intro p _hp
    cases p
    rfl

/-- Our ordered off-diagonal pairs are the usual `Finset.offDiag` of `univ`. -/
lemma offDiagPairs_eq_univ_offDiag {n : ℕ} :
    (offDiagPairs : Finset (Fin n × Fin n)) = (Finset.univ : Finset (Fin n)).offDiag := by
  ext p
  simp [offDiagPairs, ne_comm]

/-- The ordered off-diagonal pairs have cardinality `n² - n`. -/
lemma offDiagPairs_card {n : ℕ} :
    (offDiagPairs : Finset (Fin n × Fin n)).card = n * n - n := by
  rw [offDiagPairs_eq_univ_offDiag]
  simp [Finset.offDiag_card, Fintype.card_fin]

/-- The lower and upper off-diagonal halves have the same cardinality. -/
lemma lowerOffDiagPairs_card_eq_upperOffDiagPairs_card {n : ℕ} :
    (lowerOffDiagPairs : Finset (Fin n × Fin n)).card
      = (upperOffDiagPairs : Finset (Fin n × Fin n)).card := by
  have hsum :=
    lowerOffDiagPairSum_eq_upper_swap (n := n) (fun _ : Fin n × Fin n => (1 : ℝ))
  have hcast :
      ((lowerOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)
        = ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  exact Nat.cast_injective hcast

/-- Twice the number of upper off-diagonal pairs is the number of ordered pairs. -/
lemma two_mul_upperOffDiagPairs_card {n : ℕ} :
    2 * (upperOffDiagPairs : Finset (Fin n × Fin n)).card = n * n - n := by
  have hsplit :
      (offDiagPairs : Finset (Fin n × Fin n)).card
        = (upperOffDiagPairs : Finset (Fin n × Fin n)).card
          + (lowerOffDiagPairs : Finset (Fin n × Fin n)).card := by
    rw [offDiagPairs_eq_upper_union_lower]
    exact Finset.card_union_of_disjoint upperOffDiagPairs_disjoint_lowerOffDiagPairs
  have hoff : (offDiagPairs : Finset (Fin n × Fin n)).card = n * n - n :=
    offDiagPairs_card
  have hlower :
      (lowerOffDiagPairs : Finset (Fin n × Fin n)).card
        = (upperOffDiagPairs : Finset (Fin n × Fin n)).card :=
    lowerOffDiagPairs_card_eq_upperOffDiagPairs_card
  omega

/-- The number of unordered index pairs `i < j` is `n choose 2`. -/
lemma two_mul_choose_two (n : ℕ) : 2 * (n.choose 2) = n * n - n := by
  rw [Nat.choose_two_right]
  have hdiv : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [Nat.mul_comm 2]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd
  rw [hdiv]
  rw [Nat.mul_sub_left_distrib, mul_one]

/-- The upper off-diagonal pairs have cardinality `n choose 2`. -/
lemma upperOffDiagPairs_card {n : ℕ} :
    (upperOffDiagPairs : Finset (Fin n × Fin n)).card = n.choose 2 := by
  apply Nat.mul_left_cancel (by norm_num : 0 < 2)
  rw [two_mul_upperOffDiagPairs_card, two_mul_choose_two]

/--
The ordered Blaschke product is the square of the upper-triangular product.

The lower half is the complex conjugate of the upper half term-by-term, hence
has the same norm.
-/
lemma blaschkeOffDiagProduct_eq_upper_sq
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) :
    blaschkeOffDiagProduct x a =
      (upperOffDiagPairs : Finset (Fin n × Fin n)).prod
        (fun p => ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖ ^ (2 : ℕ)) := by
  unfold blaschkeOffDiagProduct
  rw [offDiagPairProduct_eq_upper_mul_lower]
  rw [lowerOffDiagPairProduct_eq_upper_swap]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  have hnorm :
      ‖1 - (a : ℂ) * x p.2 * (starRingEnd ℂ) (x p.1)‖ =
        ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖ := by
    have hstar :
        (starRingEnd ℂ) (1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2))
          = 1 - (a : ℂ) * x p.2 * (starRingEnd ℂ) (x p.1) := by
      simp
      ring
    rw [← hstar]
    simpa using
      (norm_star (1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)))
  rw [hnorm]
  ring

/-- For `n ≥ 2`, the pair count `n choose 2` is positive. -/
lemma choose_two_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 < n.choose 2 := by
  exact Nat.choose_pos hn

/-- The real-valued pair count is positive for `n ≥ 2`. -/
lemma choose_two_cast_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 < (n.choose 2 : ℝ) := by
  exact Nat.cast_pos.mpr (choose_two_pos_of_two_le hn)

/-- The ordered squared-distance sum is twice the upper-triangular sum. -/
lemma ordered_sq_sum_eq_two_mul_upper_sq_sum
    {n : ℕ} (x : Fin n → ℂ) :
    (∑ p : Fin n × Fin n, ‖x p.1 - x p.2‖ ^ (2 : ℕ))
      = 2 * (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖x p.1 - x p.2‖ ^ (2 : ℕ)) := by
  classical
  rw [ordered_sq_sum_eq_offDiag_sum]
  rw [offDiagPairSum_eq_upper_add_lower]
  rw [lowerOffDiagPairSum_eq_upper_swap]
  have hswap :
      (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖x p.2 - x p.1‖ ^ (2 : ℕ))
        = (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖x p.1 - x p.2‖ ^ (2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    rw [norm_sub_rev]
  rw [hswap]
  ring

/--
General squared-distance input for the separation-product strategy:
if all points lie in the disk of radius `A`, then the sum of squared distances
over unordered pairs is at most `n² A²`.
-/
lemma upper_pair_sq_sum_le_card_sq_mul
    {n : ℕ} (x : Fin n → ℂ) {A : ℝ}
    (hA : 0 ≤ A)
    (hx : ∀ i, ‖x i‖ ≤ A) :
    (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
        (fun p => ‖x p.1 - x p.2‖ ^ (2 : ℕ))
      ≤ (n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ) := by
  let upperSum : ℝ := (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
        (fun p => ‖x p.1 - x p.2‖ ^ (2 : ℕ))
  let orderedSum : ℝ := ∑ p : Fin n × Fin n, ‖x p.1 - x p.2‖ ^ (2 : ℕ)
  let normSum : ℝ := ∑ i : Fin n, ‖x i‖ ^ (2 : ℕ)
  have hordered_eq : orderedSum = 2 * upperSum := by
    dsimp [orderedSum, upperSum]
    exact ordered_sq_sum_eq_two_mul_upper_sq_sum x
  have hidentity :
      orderedSum + 2 * Complex.normSq (∑ i : Fin n, x i)
        = 2 * (n : ℝ) * normSum := by
    dsimp [orderedSum, normSum]
    exact ordered_pair_sq_sum_identity x
  have hcentroid_nonneg : 0 ≤ Complex.normSq (∑ i : Fin n, x i) :=
    Complex.normSq_nonneg _
  have hordered_le : orderedSum ≤ 2 * (n : ℝ) * normSum := by
    nlinarith
  have hnormSum_le : normSum ≤ (n : ℝ) * A ^ (2 : ℕ) := by
    dsimp [normSum]
    calc
      (∑ i : Fin n, ‖x i‖ ^ (2 : ℕ)) ≤ ∑ _i : Fin n, A ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact (sq_le_sq₀ (norm_nonneg _) hA).2 (hx i)
      _ = (n : ℝ) * A ^ (2 : ℕ) := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  dsimp [upperSum] at hordered_eq ⊢
  nlinarith

/--
Cauchy-Schwarz companion to `upper_pair_sq_sum_le_card_sq_mul`.

If one point cloud lies in the disk of radius `A` and another in the disk of
radius `B`, then the sum of products of corresponding edge lengths is at most
`n² A B`.
-/
lemma upper_pair_dist_mul_sum_le_card_sq_mul
    {n : ℕ} (x y : Fin n → ℂ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : ∀ i, ‖x i‖ ≤ A)
    (hy : ∀ i, ‖y i‖ ≤ B) :
    (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
        (fun p => ‖x p.1 - x p.2‖ * ‖y p.1 - y p.2‖)
      ≤ (n : ℝ) ^ (2 : ℕ) * A * B := by
  let s : Finset (Fin n × Fin n) := upperOffDiagPairs
  let F : Fin n × Fin n → ℝ := fun p => ‖x p.1 - x p.2‖
  let G : Fin n × Fin n → ℝ := fun p => ‖y p.1 - y p.2‖
  have hcauchy :
      ((∑ p ∈ s, F p * G p) ^ (2 : ℕ))
        ≤ (∑ p ∈ s, F p ^ (2 : ℕ)) * ∑ p ∈ s, G p ^ (2 : ℕ) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq s F G
  have hxsum :
      (∑ p ∈ s, F p ^ (2 : ℕ)) ≤ (n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ) := by
    dsimp [s, F]
    simpa using upper_pair_sq_sum_le_card_sq_mul x hA hx
  have hysum :
      (∑ p ∈ s, G p ^ (2 : ℕ)) ≤ (n : ℝ) ^ (2 : ℕ) * B ^ (2 : ℕ) := by
    dsimp [s, G]
    simpa using upper_pair_sq_sum_le_card_sq_mul y hB hy
  have hGsum_nonneg : 0 ≤ ∑ p ∈ s, G p ^ (2 : ℕ) := by
    exact Finset.sum_nonneg (fun p _hp => sq_nonneg (G p))
  have hXupper_nonneg : 0 ≤ (n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ) := by
    positivity
  have hprod :
      (∑ p ∈ s, F p ^ (2 : ℕ)) * ∑ p ∈ s, G p ^ (2 : ℕ)
        ≤ ((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ)) *
          ((n : ℝ) ^ (2 : ℕ) * B ^ (2 : ℕ)) := by
    exact mul_le_mul hxsum hysum hGsum_nonneg hXupper_nonneg
  have hsq :
      ((∑ p ∈ s, F p * G p) ^ (2 : ℕ))
        ≤ ((n : ℝ) ^ (2 : ℕ) * A * B) ^ (2 : ℕ) := by
    nlinarith [hcauchy, hprod]
  have hleft_nonneg : 0 ≤ ∑ p ∈ s, F p * G p := by
    exact Finset.sum_nonneg (fun p _hp => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hright_nonneg : 0 ≤ (n : ℝ) ^ (2 : ℕ) * A * B := by
    positivity
  have hle := (sq_le_sq₀ hleft_nonneg hright_nonneg).1 hsq
  simpa [s, F, G] using hle

/--
Finite-product part of PDF Lemma 4.

If each quadratic distance factor is bounded by the corresponding scaled
Blaschke factor, then the whole quadratic separation product is bounded by the
scaled ordered Blaschke product.  This is the purely finite-product bridge
between PDF Lemma 3 and PDF Lemma 4.
-/
lemma quadraticSeparationProduct_le_scaled_blaschkeOffDiagProduct
    {n : ℕ} (y x : Fin n → ℂ) {A lam σ a : ℝ}
    (hpoint :
      ∀ p ∈ (upperOffDiagPairs : Finset (Fin n × Fin n)),
        ‖y p.1 - y p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)
          ≤ (A ^ (2 : ℕ) * lam ^ (2 : ℕ))
            * ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖ ^ (2 : ℕ)) :
    quadraticSeparationProduct y σ
      ≤ (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card
        * blaschkeOffDiagProduct x a := by
  let s : Finset (Fin n × Fin n) := upperOffDiagPairs
  let C : ℝ := A ^ (2 : ℕ) * lam ^ (2 : ℕ)
  let g : Fin n × Fin n → ℝ :=
    fun p => ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖ ^ (2 : ℕ)
  have hprod :
      (s.prod fun p => ‖y p.1 - y p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ))
        ≤ s.prod fun p => C * g p := by
    exact Finset.prod_le_prod
      (fun p _hp => add_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun p hp => by
        dsimp [C, g]
        exact hpoint p (by simpa [s] using hp))
  calc
    quadraticSeparationProduct y σ
        = s.prod fun p => ‖y p.1 - y p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ) := by
          rfl
    _ ≤ s.prod fun p => C * g p := hprod
    _ = C ^ s.card * s.prod g := by
          rw [Finset.prod_mul_distrib]
          simp [Finset.prod_const]
    _ = (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card
        * blaschkeOffDiagProduct x a := by
          dsimp [C, g, s]
          rw [blaschkeOffDiagProduct_eq_upper_sq]

/-- For `n ≥ 2`, there is at least one upper off-diagonal pair. -/
lemma upperOffDiagPairs_card_pos_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    0 < (upperOffDiagPairs : Finset (Fin n × Fin n)).card := by
  have h0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have h1 : 1 < n := lt_of_lt_of_le (by norm_num) hn
  let i : Fin n := ⟨0, h0⟩
  let j : Fin n := ⟨1, h1⟩
  have hij : i < j := by
    simp [i, j]
  have hmem : (i, j) ∈ (upperOffDiagPairs : Finset (Fin n × Fin n)) := by
    simp [upperOffDiagPairs, hij]
  exact Finset.card_pos.mpr ⟨(i, j), hmem⟩

/--
General AM-GM bound for the quadratic separation product.

This is weaker than the PDF Lemma 4, but it is the first general product
estimate obtained from the already-proved squared-distance sum bound.
-/
lemma quadraticSeparationProduct_rpow_inv_card_le_average_bound
    {n : ℕ} (x : Fin n → ℂ) {A σ : ℝ}
    (hA : 0 ≤ A)
    (hx : ∀ i, ‖x i‖ ≤ A)
    (hcard : 0 < (upperOffDiagPairs : Finset (Fin n × Fin n)).card) :
    (quadraticSeparationProduct x σ) ^
        (((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)⁻¹)
      ≤ (((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ)
          + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) * σ ^ (2 : ℕ)) /
        ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)) := by
  let s : Finset (Fin n × Fin n) := upperOffDiagPairs
  let f : Fin n × Fin n → ℝ :=
    fun p => ‖x p.1 - x p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)
  have hcard_pos : 0 < (s.card : ℝ) :=
    Nat.cast_pos.mpr (by simpa [s] using hcard)
  have hgm := Real.geom_mean_le_arith_mean
    (s := s)
    (w := fun _ : Fin n × Fin n => (1 : ℝ))
    (z := f)
    (by intro _p _hp; norm_num)
    (by simpa [s, hcard_pos.ne'] using hcard_pos)
    (by
      intro p _hp
      dsimp [f]
      positivity)
  have hgm' :
      (quadraticSeparationProduct x σ) ^ (s.card : ℝ)⁻¹
        ≤ (∑ p ∈ s, f p) / (s.card : ℝ) := by
    simpa [quadraticSeparationProduct, s, f, Finset.sum_const, hcard_pos.ne',
      div_eq_mul_inv] using hgm
  have hdist_sum :
      (∑ p ∈ s, ‖x p.1 - x p.2‖ ^ (2 : ℕ))
        ≤ (n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ) := by
    simpa [s] using upper_pair_sq_sum_le_card_sq_mul x hA hx
  have hsum :
      (∑ p ∈ s, f p)
        ≤ (n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ) + (s.card : ℝ) * σ ^ (2 : ℕ) := by
    dsimp [f]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    nlinarith
  have hdiv :
      (∑ p ∈ s, f p) / (s.card : ℝ)
        ≤ (((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ) + (s.card : ℝ) * σ ^ (2 : ℕ)) /
          (s.card : ℝ)) := by
    exact div_le_div_of_nonneg_right hsum hcard_pos.le
  exact hgm'.trans hdiv

/-- The same AM-GM bound, with the nonempty pair condition discharged by `2 ≤ n`. -/
lemma quadraticSeparationProduct_rpow_inv_card_le_average_bound_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℂ) {A σ : ℝ}
    (hA : 0 ≤ A)
    (hx : ∀ i, ‖x i‖ ≤ A) :
    (quadraticSeparationProduct x σ) ^
        (((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)⁻¹)
      ≤ (((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ)
          + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) * σ ^ (2 : ℕ)) /
        ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)) := by
  exact quadraticSeparationProduct_rpow_inv_card_le_average_bound
    x hA hx (upperOffDiagPairs_card_pos_of_two_le hn)

/--
Coarse general separation-product bound obtained by raising the AM-GM estimate
back to the number of unordered pairs.

This is not the sharp hyperbolic PDF Lemma 4, but it is a genuine all-`n`
product estimate with no remaining root or average on the left.
-/
lemma quadraticSeparationProduct_le_average_bound_pow_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℂ) {A σ : ℝ}
    (hA : 0 ≤ A)
    (hx : ∀ i, ‖x i‖ ≤ A) :
    quadraticSeparationProduct x σ
      ≤ (((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ)
          + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) * σ ^ (2 : ℕ)) /
        ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card := by
  let s : Finset (Fin n × Fin n) := upperOffDiagPairs
  let B : ℝ := (((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ)
      + (s.card : ℝ) * σ ^ (2 : ℕ)) / (s.card : ℝ))
  have hcard_pos_nat : 0 < s.card := by
    simpa [s] using upperOffDiagPairs_card_pos_of_two_le hn
  have hcard_ne : s.card ≠ 0 := Nat.ne_of_gt hcard_pos_nat
  have hq_nonneg : 0 ≤ quadraticSeparationProduct x σ := by
    unfold quadraticSeparationProduct
    exact Finset.prod_nonneg
      (fun p _hp => add_nonneg (sq_nonneg ‖x p.1 - x p.2‖) (sq_nonneg σ))
  have hroot :
      (quadraticSeparationProduct x σ) ^ ((s.card : ℝ)⁻¹) ≤ B := by
    dsimp [B, s]
    exact quadraticSeparationProduct_rpow_inv_card_le_average_bound_of_two_le hn x hA hx
  have hpow :=
    pow_le_pow_left₀
      (Real.rpow_nonneg hq_nonneg ((s.card : ℝ)⁻¹))
      hroot
      s.card
  have hleft :
      ((quadraticSeparationProduct x σ) ^ ((s.card : ℝ)⁻¹)) ^ s.card
        = quadraticSeparationProduct x σ := by
    exact Real.rpow_inv_natCast_pow hq_nonneg hcard_ne
  rw [hleft] at hpow
  dsimp [B, s] at hpow ⊢
  exact hpow

/--
The same coarse product estimate with the number of unordered pairs simplified
to `n.choose 2`.
-/
lemma quadraticSeparationProduct_le_average_bound_choose_two_pow_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℂ) {A σ : ℝ}
    (hA : 0 ≤ A)
    (hx : ∀ i, ‖x i‖ ≤ A) :
    quadraticSeparationProduct x σ
      ≤ (((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ)
          + (n.choose 2 : ℝ) * σ ^ (2 : ℕ)) /
        (n.choose 2 : ℝ)) ^ n.choose 2 := by
  simpa [upperOffDiagPairs_card] using
    quadraticSeparationProduct_le_average_bound_pow_of_two_le hn x hA hx

/--
The average in the coarse AM-GM bound after substituting
`#pairs = n.choose 2`.
-/
lemma average_bound_choose_two_eq_explicit
    {n : ℕ} (hn : 2 ≤ n) (A σ : ℝ) :
    (((n : ℝ) ^ (2 : ℕ) * A ^ (2 : ℕ)
        + (n.choose 2 : ℝ) * σ ^ (2 : ℕ)) /
      (n.choose 2 : ℝ))
      = (2 * (n : ℝ) / ((n : ℝ) - 1)) * A ^ (2 : ℕ) + σ ^ (2 : ℕ) := by
  have hn_real : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hn_minus_pos : 0 < (n : ℝ) - 1 := by linarith
  rw [Nat.cast_choose_two]
  field_simp [hn_minus_pos.ne', (by norm_num : (2 : ℝ) ≠ 0)]

/--
Coarse quadratic separation-product estimate in fully explicit average form.

This says that the already-proved AM-GM route gives
`∏(‖x_i-x_j‖²+σ²) ≤ ((2n/(n-1))A²+σ²)^(n choose 2)`.
-/
lemma quadraticSeparationProduct_le_explicit_average_bound_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℂ) {A σ : ℝ}
    (hA : 0 ≤ A)
    (hx : ∀ i, ‖x i‖ ≤ A) :
    quadraticSeparationProduct x σ
      ≤ ((2 * (n : ℝ) / ((n : ℝ) - 1)) * A ^ (2 : ℕ)
          + σ ^ (2 : ℕ)) ^ n.choose 2 := by
  simpa [average_bound_choose_two_eq_explicit hn A σ] using
    (quadraticSeparationProduct_le_average_bound_choose_two_pow_of_two_le
      (n := n) (σ := σ) hn x hA hx)

/--
The off-diagonal product is exactly the product over paired cross terms
`‖w_i - z_j‖ * ‖w_j - z_i‖`.
-/
lemma offDiagProduct_eq_pairedOffDiagProduct
    {n : ℕ} (z w : Fin n → ℂ) :
    offDiagProduct z w = pairedOffDiagProduct z w := by
  rw [offDiagProduct_eq_pairProduct]
  rw [offDiagPairProduct_eq_upper_mul_lower]
  rw [lowerOffDiagPairProduct_eq_upper_swap]
  unfold pairedOffDiagProduct
  rw [← Finset.prod_mul_distrib]

/--
If `w_i` is within `ε` of `z_i`, then its distance to any other root `z_j`
is at most the root-root distance plus `ε`.
-/
lemma norm_w_sub_other_le_norm_z_sub_add
    {zi zj wi : ℂ}
    {ε : ℝ}
    (hwi : ‖wi - zi‖ ≤ ε) :
    ‖wi - zj‖ ≤ ‖zi - zj‖ + ε := by
  have hsplit : wi - zj = (zi - zj) + (wi - zi) := by ring
  calc
    ‖wi - zj‖ = ‖(zi - zj) + (wi - zi)‖ := by rw [hsplit]
    _ ≤ ‖zi - zj‖ + ‖wi - zi‖ := norm_add_le _ _
    _ ≤ ‖zi - zj‖ + ε := by linarith

/--
If `wi` is close to `zi`, then `wj` is close to `zi` up to the distance
between `wi` and `wj`.
-/
lemma norm_w_sub_root_le_norm_w_sub_add
    {zi wi wj : ℂ}
    {ε σ : ℝ}
    (hwi : ‖wi - zi‖ ≤ ε)
    (hεσ : ε ≤ σ) :
    ‖wj - zi‖ ≤ ‖wi - wj‖ + σ := by
  have hsplit : wj - zi = (wj - wi) + (wi - zi) := by ring
  calc
    ‖wj - zi‖ = ‖(wj - wi) + (wi - zi)‖ := by rw [hsplit]
    _ ≤ ‖wj - wi‖ + ‖wi - zi‖ := norm_add_le _ _
    _ = ‖wi - wj‖ + ‖wi - zi‖ := by rw [norm_sub_rev]
    _ ≤ ‖wi - wj‖ + σ := by linarith

/--
The elementary pairwise bound obtained from the triangle inequality.

This is weaker than the sharp PDF estimate, but it is the next useful
formalized reduction: each paired off-diagonal factor is controlled by the
distance between the two roots.
-/
lemma paired_cross_terms_le_sq
    {n : ℕ} (z w : Fin n → ℂ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε)
    (p : Fin n × Fin n) :
    ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖
      ≤ (‖z p.1 - z p.2‖ + ε) ^ (2 : ℕ) := by
  have h₁ : ‖w p.1 - z p.2‖ ≤ ‖z p.1 - z p.2‖ + ε :=
    norm_w_sub_other_le_norm_z_sub_add (hw p.1)
  have h₂_raw : ‖w p.2 - z p.1‖ ≤ ‖z p.2 - z p.1‖ + ε :=
    norm_w_sub_other_le_norm_z_sub_add (hw p.2)
  have h₂ : ‖w p.2 - z p.1‖ ≤ ‖z p.1 - z p.2‖ + ε := by
    simpa [norm_sub_rev] using h₂_raw
  have hright : 0 ≤ ‖z p.1 - z p.2‖ + ε :=
    add_nonneg (norm_nonneg _) hε
  calc
    ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖
        ≤ (‖z p.1 - z p.2‖ + ε) * (‖z p.1 - z p.2‖ + ε) :=
      mul_le_mul h₁ h₂ (norm_nonneg _) hright
    _ = (‖z p.1 - z p.2‖ + ε) ^ (2 : ℕ) := by ring

/--
The PDF-shaped pairwise estimate: a paired cross term is controlled by one
root-root distance and one nearby-point distance.
-/
lemma paired_cross_terms_le_separation_terms
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hσ : 0 ≤ σ)
    (hεσ : ε ≤ σ)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε)
    (p : Fin n × Fin n) :
    ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖
      ≤ (‖z p.1 - z p.2‖ + σ) * (‖w p.1 - w p.2‖ + σ) := by
  have hroot_raw : ‖w p.1 - z p.2‖ ≤ ‖z p.1 - z p.2‖ + ε :=
    norm_w_sub_other_le_norm_z_sub_add (hw p.1)
  have hroot : ‖w p.1 - z p.2‖ ≤ ‖z p.1 - z p.2‖ + σ := by
    linarith
  have hnear : ‖w p.2 - z p.1‖ ≤ ‖w p.1 - w p.2‖ + σ :=
    norm_w_sub_root_le_norm_w_sub_add (hw p.1) hεσ
  have hroot_nonneg : 0 ≤ ‖z p.1 - z p.2‖ + σ :=
    add_nonneg (norm_nonneg _) hσ
  calc
    ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖
        ≤ (‖z p.1 - z p.2‖ + σ) * (‖w p.1 - w p.2‖ + σ) :=
      mul_le_mul hroot hnear (norm_nonneg _) hroot_nonneg

/--
A sharper Ptolemy-type pair estimate in the complex plane.

The algebraic identity
`(wi-zj)(wj-zi) = (wi-wj)(zj-zi) + (wi-zi)(wj-zj)`
turns the two cross terms into a root-root term, a `w`-`w` term, and the two
small diagonal errors.
-/
lemma paired_cross_terms_le_mul_add_sq
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hε : 0 ≤ ε)
    (hεσ : ε ≤ σ)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε)
    (p : Fin n × Fin n) :
    ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖
      ≤ ‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖ + σ ^ (2 : ℕ) := by
  have hident :
      (w p.1 - z p.2) * (w p.2 - z p.1)
        =
      (w p.1 - w p.2) * (z p.2 - z p.1)
        + (w p.1 - z p.1) * (w p.2 - z p.2) := by
    ring
  have hdiag :
      ‖w p.1 - z p.1‖ * ‖w p.2 - z p.2‖ ≤ ε * ε := by
    exact mul_le_mul (hw p.1) (hw p.2) (norm_nonneg _) hε
  have hεsq : ε * ε ≤ σ ^ (2 : ℕ) := by
    nlinarith
  calc
    ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖
        = ‖(w p.1 - z p.2) * (w p.2 - z p.1)‖ := by
          rw [norm_mul]
    _ = ‖(w p.1 - w p.2) * (z p.2 - z p.1)
        + (w p.1 - z p.1) * (w p.2 - z p.2)‖ := by
          rw [hident]
    _ ≤ ‖(w p.1 - w p.2) * (z p.2 - z p.1)‖
        + ‖(w p.1 - z p.1) * (w p.2 - z p.2)‖ := norm_add_le _ _
    _ = ‖w p.1 - w p.2‖ * ‖z p.2 - z p.1‖
        + ‖w p.1 - z p.1‖ * ‖w p.2 - z p.2‖ := by
          simp
    _ ≤ ‖w p.1 - w p.2‖ * ‖z p.2 - z p.1‖ + ε * ε := by
          linarith
    _ ≤ ‖w p.1 - w p.2‖ * ‖z p.2 - z p.1‖ + σ ^ (2 : ℕ) := by
          linarith
    _ = ‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖ + σ ^ (2 : ℕ) := by
          have hzrev : ‖z p.2 - z p.1‖ = ‖z p.1 - z p.2‖ := by
            rw [norm_sub_rev]
          rw [hzrev]
          ring

/--
Pointwise bridge to the PDF's quadratic separation factors.
-/
lemma paired_cross_terms_sq_le_quadratic_terms
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hε : 0 ≤ ε)
    (hεσ : ε ≤ σ)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε)
    (p : Fin n × Fin n) :
    (‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖) ^ (2 : ℕ)
      ≤ (‖z p.1 - z p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ))
          * (‖w p.1 - w p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) := by
  have hσ : 0 ≤ σ := hε.trans hεσ
  have hcross_nonneg :
      0 ≤ ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound := paired_cross_terms_le_mul_add_sq z w hε hεσ hw p
  have hbound_nonneg :
      0 ≤ ‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖ + σ ^ (2 : ℕ) :=
    add_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (sq_nonneg σ)
  have hsquare :
      (‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖) ^ (2 : ℕ)
        ≤ (‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖ + σ ^ (2 : ℕ)) ^ (2 : ℕ) := by
    exact sq_le_sq' (by linarith) hbound
  calc
    (‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖) ^ (2 : ℕ)
        ≤ (‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖ + σ ^ (2 : ℕ)) ^ (2 : ℕ) :=
      hsquare
    _ ≤ (‖z p.1 - z p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ))
          * (‖w p.1 - w p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)) := by
      nlinarith [sq_nonneg (‖z p.1 - z p.2‖ - ‖w p.1 - w p.2‖)]

/--
Consequently, the whole off-diagonal product is bounded by a product over
root-root distances.  This is a proved coarse version of the next product step.
-/
lemma offDiagProduct_le_paired_distance_bound
    {n : ℕ} (z w : Fin n → ℂ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    offDiagProduct z w
      ≤ (upperOffDiagPairs : Finset (Fin n × Fin n)).prod
          (fun p => (‖z p.1 - z p.2‖ + ε) ^ (2 : ℕ)) := by
  rw [offDiagProduct_eq_pairedOffDiagProduct]
  unfold pairedOffDiagProduct
  exact Finset.prod_le_prod
    (fun p _hp => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun p _hp => paired_cross_terms_le_sq z w hε hw p)

/--
PDF-shaped product reduction for the off-diagonal part.

After pairing, the off-diagonal product is bounded by the product of a
separation product for `z` and a separation product for `w`.
-/
lemma offDiagProduct_le_pairedSeparationProduct
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hσ : 0 ≤ σ)
    (hεσ : ε ≤ σ)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    offDiagProduct z w ≤ pairedSeparationProduct z w σ := by
  rw [offDiagProduct_eq_pairedOffDiagProduct]
  unfold pairedOffDiagProduct pairedSeparationProduct
  exact Finset.prod_le_prod
    (fun p _hp => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun p _hp => paired_cross_terms_le_separation_terms z w hσ hεσ hw p)

lemma offDiagProduct_le_separationProduct_mul
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hσ : 0 ≤ σ)
    (hεσ : ε ≤ σ)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    offDiagProduct z w ≤ separationProduct z σ * separationProduct w σ := by
  simpa [pairedSeparationProduct_eq_mul] using
    offDiagProduct_le_pairedSeparationProduct z w hσ hεσ hw

/--
The sharp PDF-shaped product reduction, squared to avoid square roots.

The left side is the square of the off-diagonal product.  The right side is
exactly the product of the two quadratic separation products appearing in
Lemma 4 of the PDF.
-/
lemma offDiagProduct_sq_le_quadraticSeparationProduct_mul
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hε : 0 ≤ ε)
    (hεσ : ε ≤ σ)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    offDiagProduct z w ^ (2 : ℕ)
      ≤ quadraticSeparationProduct z σ * quadraticSeparationProduct w σ := by
  rw [offDiagProduct_eq_pairedOffDiagProduct]
  unfold pairedOffDiagProduct quadraticSeparationProduct
  rw [← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod
    (fun p _hp =>
      sq_nonneg (‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖))
    (fun p _hp => paired_cross_terms_sq_le_quadratic_terms z w hε hεσ hw p)

/--
The distance matrix splits into its diagonal part and its off-diagonal part.
-/
lemma prod_distances_eq_diag_mul_offDiagProduct
    {n : ℕ} (z w : Fin n → ℂ) :
    (∏ j : Fin n, ∏ i : Fin n, ‖w j - z i‖)
      = (∏ j : Fin n, ‖w j - z j‖) * offDiagProduct z w := by
  classical
  unfold offDiagProduct
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j _hj
  symm
  simpa using
    (Finset.mul_prod_erase
      (s := Finset.univ)
      (f := fun i : Fin n => ‖w j - z i‖)
      (a := j)
      (Finset.mem_univ j))

/--
The diagonal part is exactly the part controlled directly by the hypotheses
`‖w i - z i‖ ≤ ε`.
-/
lemma diagonal_product_le_eps_pow
    {n : ℕ} (z w : Fin n → ℂ)
    {ε : ℝ}
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    (∏ i : Fin n, ‖w i - z i‖) ≤ ε ^ n := by
  calc
    (∏ i : Fin n, ‖w i - z i‖) ≤ ∏ _i : Fin n, ε := by
      exact Finset.prod_le_prod
        (fun i _hi => norm_nonneg (w i - z i))
        (fun i _hi => hw i)
    _ = ε ^ n := by
      simp

/-- The off-diagonal product is nonnegative, since it is a product of norms. -/
lemma offDiagProduct_nonneg
    {n : ℕ} (z w : Fin n → ℂ) :
    0 ≤ offDiagProduct z w := by
  classical
  unfold offDiagProduct
  exact Finset.prod_nonneg
    (fun j _hj =>
      Finset.prod_nonneg (fun i _hi => norm_nonneg (w j - z i)))

/-- The quadratic separation product is nonnegative. -/
lemma quadraticSeparationProduct_nonneg
    {n : ℕ} (x : Fin n → ℂ) (σ : ℝ) :
    0 ≤ quadraticSeparationProduct x σ := by
  classical
  unfold quadraticSeparationProduct
  exact Finset.prod_nonneg
    (fun p _hp =>
      add_nonneg (sq_nonneg ‖x p.1 - x p.2‖) (sq_nonneg σ))

/-- The product over the values `f(w_j)` is nonnegative. -/
lemma prod_norm_fval_nonneg
    {n : ℕ} (z w : Fin n → ℂ) :
    0 ≤ ∏ j : Fin n, ‖fval z (w j)‖ := by
  exact Finset.prod_nonneg (fun j _hj => norm_nonneg (fval z (w j)))

/--
Squared version of the whole value product, reduced to the quadratic
separation products from the PDF.
-/
lemma prod_norm_fval_sq_le_quadraticSeparationProduct_mul
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hε : 0 ≤ ε)
    (hεσ : ε ≤ σ)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    (∏ j : Fin n, ‖fval z (w j)‖) ^ (2 : ℕ)
      ≤ (ε ^ n) ^ (2 : ℕ)
          * (quadraticSeparationProduct z σ * quadraticSeparationProduct w σ) := by
  have hdiag :
      (∏ j : Fin n, ‖w j - z j‖) ≤ ε ^ n :=
    diagonal_product_le_eps_pow z w hw
  have hdiag_nonneg : 0 ≤ ∏ j : Fin n, ‖w j - z j‖ :=
    Finset.prod_nonneg (fun j _hj => norm_nonneg (w j - z j))
  have hdiag_sq :
      (∏ j : Fin n, ‖w j - z j‖) ^ (2 : ℕ)
        ≤ (ε ^ n) ^ (2 : ℕ) :=
    (sq_le_sq₀ hdiag_nonneg (pow_nonneg hε n)).2 hdiag
  have hoff_sq :
      offDiagProduct z w ^ (2 : ℕ)
        ≤ quadraticSeparationProduct z σ * quadraticSeparationProduct w σ :=
    offDiagProduct_sq_le_quadraticSeparationProduct_mul z w hε hεσ hw
  calc
    (∏ j : Fin n, ‖fval z (w j)‖) ^ (2 : ℕ)
        = ((∏ j : Fin n, ‖w j - z j‖) * offDiagProduct z w) ^ (2 : ℕ) := by
          rw [prod_norm_fval_eq_prod_prod, prod_distances_eq_diag_mul_offDiagProduct]
    _ = (∏ j : Fin n, ‖w j - z j‖) ^ (2 : ℕ)
        * offDiagProduct z w ^ (2 : ℕ) := by ring
    _ ≤ (ε ^ n) ^ (2 : ℕ)
        * (quadraticSeparationProduct z σ * quadraticSeparationProduct w σ) :=
      mul_le_mul hdiag_sq hoff_sq
        (sq_nonneg (offDiagProduct z w))
        (sq_nonneg (ε ^ n))

/-- The diagonal and off-diagonal pair sets are disjoint. -/
lemma diag_disjoint_offDiag {n : ℕ} :
    Disjoint ((Finset.univ : Finset (Fin n)).diag)
      ((Finset.univ : Finset (Fin n)).offDiag) := by
  rw [Finset.disjoint_left]
  intro p hpdiag hpoff
  simp [Finset.mem_diag] at hpdiag
  simp [Finset.mem_offDiag] at hpoff
  exact hpoff hpdiag

/-- The full Blaschke product splits into diagonal and off-diagonal parts. -/
lemma blaschkeFullProduct_eq_diag_mul_offDiag
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) :
    blaschkeFullProduct x a = blaschkeDiagProduct x a * blaschkeOffDiagProduct x a := by
  unfold blaschkeFullProduct blaschkeDiagProduct blaschkeOffDiagProduct
  rw [Finset.prod_union diag_disjoint_offDiag]
  rw [offDiagPairs_eq_univ_offDiag]

/-- The `diag ∪ offDiag` full product is the same as the product over all pairs. -/
lemma blaschkeFullProduct_eq_allPairsProduct
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) :
    blaschkeFullProduct x a = blaschkeAllPairsProduct x a := by
  unfold blaschkeFullProduct blaschkeAllPairsProduct
  rw [Finset.diag_union_offDiag]
  rw [Finset.univ_product_univ]

/--
Each diagonal Blaschke factor is at least `1 - a` for points in the unit disk.

Indeed the factor is `|1 - a |u|²|`, and `0 ≤ |u|² ≤ 1`.
-/
lemma blaschke_diag_factor_lower
    {a : ℝ} {u : ℂ}
    (h0a : 0 ≤ a)
    (ha1 : a < 1)
    (hu : ‖u‖ ≤ 1) :
    1 - a ≤ ‖1 - (a : ℂ) * u * (starRingEnd ℂ) u‖ := by
  have hleft_nonneg : 0 ≤ 1 - a := by
    linarith
  have hnormSq_le_one : Complex.normSq u ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_one_iff₀ (norm_nonneg u)).2 hu
  have hbase : 1 - a ≤ 1 - a * Complex.normSq u := by
    have hmul_le : a * Complex.normSq u ≤ a * 1 :=
      mul_le_mul_of_nonneg_left hnormSq_le_one h0a
    nlinarith
  have hreal_nonneg : 0 ≤ 1 - a * Complex.normSq u :=
    hleft_nonneg.trans hbase
  let z : ℂ := 1 - (a : ℂ) * u * (starRingEnd ℂ) u
  have hcomplex : z = ((1 - a * Complex.normSq u : ℝ) : ℂ) := by
    dsimp [z]
    rw [show (a : ℂ) * u * (starRingEnd ℂ) u =
        (a : ℂ) * (u * (starRingEnd ℂ) u) by ring]
    rw [Complex.mul_conj]
    apply Complex.ext <;> simp
  have hsqnorm : ‖z‖ ^ (2 : ℕ) = (1 - a * Complex.normSq u) ^ (2 : ℕ) := by
    rw [hcomplex, Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have hsq_le : (1 - a) ^ (2 : ℕ) ≤ ‖z‖ ^ (2 : ℕ) := by
    rw [hsqnorm]
    exact (sq_le_sq₀ hleft_nonneg hreal_nonneg).2 hbase
  exact (sq_le_sq₀ hleft_nonneg (norm_nonneg z)).1 hsq_le

/-- The diagonal part of the full Blaschke product is at least `(1-a)^n`. -/
lemma blaschkeDiagProduct_lower_bound
    {n : ℕ} (x : Fin n → ℂ) {a : ℝ}
    (h0a : 0 ≤ a)
    (ha1 : a < 1)
    (hx : ∀ i, ‖x i‖ ≤ 1) :
    (1 - a) ^ n ≤ blaschkeDiagProduct x a := by
  have hcard : ((Finset.univ : Finset (Fin n)).diag).card = n := by
    simp [Finset.diag_card]
  calc
    (1 - a) ^ n
        = ((Finset.univ : Finset (Fin n)).diag).prod (fun _ => 1 - a) := by
          rw [Finset.prod_const, hcard]
    _ ≤ blaschkeDiagProduct x a := by
          unfold blaschkeDiagProduct
          exact Finset.prod_le_prod
            (fun _ _ => by linarith)
            (fun p hp => by
              simp [Finset.mem_diag] at hp
              rw [hp]
              exact blaschke_diag_factor_lower h0a ha1 (hx p.2))

/--
On the unit circle, a diagonal Blaschke factor is exactly `1 - a`.
-/
lemma blaschke_diag_factor_torus
    {a : ℝ} {u : ℂ}
    (_h0a : 0 ≤ a)
    (ha1 : a < 1)
    (hu : ‖u‖ = 1) :
    ‖1 - (a : ℂ) * u * (starRingEnd ℂ) u‖ = 1 - a := by
  have hnormSq : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hcomplex : 1 - (a : ℂ) * u * (starRingEnd ℂ) u = ((1 - a : ℝ) : ℂ) := by
    rw [show (a : ℂ) * u * (starRingEnd ℂ) u =
        (a : ℂ) * (u * (starRingEnd ℂ) u) by ring]
    rw [Complex.mul_conj]
    apply Complex.ext <;> simp [hnormSq]
  rw [hcomplex]
  rw [Complex.norm_def, Complex.normSq_ofReal]
  rw [← sq]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by linarith)

/-- On the torus, the diagonal Blaschke product is exactly `(1-a)^n`. -/
lemma blaschkeDiagProduct_torus_eq
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (h0a : 0 ≤ a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    blaschkeDiagProduct ω a = (1 - a) ^ n := by
  unfold blaschkeDiagProduct
  calc
    ((Finset.univ : Finset (Fin n)).diag).prod
        (fun p => ‖1 - (a : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖)
        = ((Finset.univ : Finset (Fin n)).diag).prod (fun _ => 1 - a) := by
          apply Finset.prod_congr rfl
          intro p hp
          simp [Finset.mem_diag] at hp
          rw [hp]
          exact blaschke_diag_factor_torus h0a ha1 (hω p.2)
    _ = (1 - a) ^ n := by
          rw [Finset.prod_const]
          simp [Finset.diag_card]

/--
The one-variable polynomial obtained from the Blaschke off-diagonal product by
freezing every coordinate except `k`.
-/
def blaschkeCoordinatePolynomial
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) (u : ℂ) : ℂ :=
  (Finset.univ.erase k).prod
    (fun i => 1 - (a : ℂ) * u * (starRingEnd ℂ) (x i))

/--
The squared-norm factor in the off-diagonal product that depends on one
coordinate.
-/
def blaschkeCoordinateSlice
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) (u : ℂ) : ℝ :=
  (Finset.univ.erase k).prod
    (fun i => ‖1 - (a : ℂ) * u * (starRingEnd ℂ) (x i)‖ ^ (2 : ℕ))

/--
The one-coordinate slice is the squared norm of an honest complex polynomial.
This is the local shape needed for the maximum-modulus step.
-/
lemma blaschkeCoordinatePolynomial_norm_sq
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) (u : ℂ) :
    ‖blaschkeCoordinatePolynomial x a k u‖ ^ (2 : ℕ) =
      blaschkeCoordinateSlice x a k u := by
  simp [blaschkeCoordinatePolynomial, blaschkeCoordinateSlice, norm_prod,
    Finset.prod_pow]

/-- The ordered factors starting at `k` are indexed by `Finset.univ.erase k`. -/
lemma offDiagPairs_outgoing_prod_eq_erase
    {n : ℕ} (F : Fin n × Fin n → ℝ) (k : Fin n) :
    ((offDiagPairs : Finset (Fin n × Fin n)).filter (fun p => p.1 = k)).prod F =
      (Finset.univ.erase k).prod (fun i => F (k, i)) := by
  classical
  refine Finset.prod_bij (fun p _hp => p.2) ?hi ?hinj ?hsurj ?hfg
  · intro p hp
    rcases p with ⟨i, j⟩
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_erase]
    have hji : j ≠ i := by
      simpa [offDiagPairs] using hp.1
    exact ⟨by intro hjk; exact hji (hjk.trans hp.2.symm), Finset.mem_univ j⟩
  · intro p hp q hq hpq
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    rw [Finset.mem_filter] at hp hq
    simp at hpq
    cases hpq
    have hi_eq : i = i' := hp.2.trans hq.2.symm
    cases hi_eq
    rfl
  · intro j hj
    refine ⟨(k, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    rw [Finset.mem_erase] at hj
    exact ⟨by simpa [offDiagPairs] using hj.1, rfl⟩
  · intro p hp
    rcases p with ⟨i, j⟩
    rw [Finset.mem_filter] at hp
    have hik : i = k := by simpa using hp.2
    change F (i, j) = F (k, j)
    rw [hik]

/-- The ordered factors ending at `k` are indexed by `Finset.univ.erase k`. -/
lemma offDiagPairs_incoming_prod_eq_erase
    {n : ℕ} (F : Fin n × Fin n → ℝ) (k : Fin n) :
    ((offDiagPairs : Finset (Fin n × Fin n)).filter (fun p => p.2 = k)).prod F =
      (Finset.univ.erase k).prod (fun i => F (i, k)) := by
  classical
  refine Finset.prod_bij (fun p _hp => p.1) ?hi ?hinj ?hsurj ?hfg
  · intro p hp
    rcases p with ⟨i, j⟩
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_erase]
    have hji : j ≠ i := by
      simpa [offDiagPairs] using hp.1
    exact ⟨by intro hik; exact hji (hp.2.trans hik.symm), Finset.mem_univ i⟩
  · intro p hp q hq hpq
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    rw [Finset.mem_filter] at hp hq
    simp at hpq
    cases hpq
    have hj_eq : j = j' := hp.2.trans hq.2.symm
    cases hj_eq
    rfl
  · intro i hi
    refine ⟨(i, k), ?_, rfl⟩
    rw [Finset.mem_filter]
    rw [Finset.mem_erase] at hi
    exact ⟨by
      simpa [offDiagPairs] using (show k ≠ i from fun hki => hi.1 hki.symm), rfl⟩
  · intro p hp
    rcases p with ⟨i, j⟩
    rw [Finset.mem_filter] at hp
    have hjk : j = k := by simpa using hp.2
    change F (i, j) = F (i, k)
    rw [hjk]

/--
The ordered incident pairs are exactly the outgoing and incoming copies of
`Finset.univ.erase k`.
-/
lemma offDiagPairs_incident_prod_eq_erase
    {n : ℕ} (F : Fin n × Fin n → ℝ) (k : Fin n) :
    ((offDiagPairs : Finset (Fin n × Fin n)).filter
        (fun p => p.1 = k ∨ p.2 = k)).prod F =
      (Finset.univ.erase k).prod (fun i => F (k, i) * F (i, k)) := by
  classical
  rw [Finset.filter_or]
  rw [Finset.prod_union]
  · rw [offDiagPairs_outgoing_prod_eq_erase, offDiagPairs_incoming_prod_eq_erase]
    rw [← Finset.prod_mul_distrib]
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases p with ⟨i, j⟩
    rw [Finset.mem_filter] at hp1 hp2
    have hji : j ≠ i := by simpa [offDiagPairs] using hp1.1
    exact hji (hp2.2.trans hp1.2.symm)

/-- The full off-diagonal product splits into incident and nonincident factors. -/
lemma blaschkeOffDiagProduct_eq_incident_mul_nonincident
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) :
    blaschkeOffDiagProduct x a =
      blaschkeIncidentPairProduct x a k * blaschkeNonincidentProduct x a k := by
  unfold blaschkeOffDiagProduct blaschkeIncidentPairProduct
    blaschkeNonincidentProduct blaschkePairFactor
  exact (Finset.prod_filter_mul_prod_filter_not
    (offDiagPairs : Finset (Fin n × Fin n))
    (fun p => p.1 = k ∨ p.2 = k)
    (fun p => ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖)).symm

/-- Updating coordinate `k` leaves all nonincident factors unchanged. -/
lemma blaschkeNonincidentProduct_update_eq
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) (u : ℂ) :
    blaschkeNonincidentProduct (Function.update x k u) a k =
      blaschkeNonincidentProduct x a k := by
  unfold blaschkeNonincidentProduct
  apply Finset.prod_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have hp1 : p.1 ≠ k := by
    intro h
    exact hp.2 (Or.inl h)
  have hp2 : p.2 ≠ k := by
    intro h
    exact hp.2 (Or.inr h)
  simp [blaschkePairFactor, Function.update_of_ne hp1, Function.update_of_ne hp2]

/-- The nonincident product is nonnegative. -/
lemma blaschkeNonincidentProduct_nonneg
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) :
    0 ≤ blaschkeNonincidentProduct x a k := by
  unfold blaschkeNonincidentProduct blaschkePairFactor
  exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)

/--
The two ordered factors involving one coordinate combine into the corresponding
one-coordinate slice.
-/
lemma blaschkeIncidentProduct_eq_coordinateSlice
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) :
    (Finset.univ.erase k).prod
        (fun i => ‖1 - (a : ℂ) * x k * (starRingEnd ℂ) (x i)‖ *
          ‖1 - (a : ℂ) * x i * (starRingEnd ℂ) (x k)‖) =
      blaschkeCoordinateSlice x a k (x k) := by
  unfold blaschkeCoordinateSlice
  apply Finset.prod_congr rfl
  intro i _hi
  have hnorm :
      ‖1 - (a : ℂ) * x i * (starRingEnd ℂ) (x k)‖ =
        ‖1 - (a : ℂ) * x k * (starRingEnd ℂ) (x i)‖ := by
    have hstar :
        (starRingEnd ℂ) (1 - (a : ℂ) * x k * (starRingEnd ℂ) (x i)) =
          1 - (a : ℂ) * x i * (starRingEnd ℂ) (x k) := by
      simp
      ring
    rw [← hstar]
    simpa using
      (norm_star (1 - (a : ℂ) * x k * (starRingEnd ℂ) (x i)))
  rw [hnorm]
  ring

/--
The incident part of the ordered Blaschke product is exactly the coordinate
slice.
-/
lemma blaschkeIncidentPairProduct_eq_coordinateSlice
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) :
    blaschkeIncidentPairProduct x a k =
      blaschkeCoordinateSlice x a k (x k) := by
  unfold blaschkeIncidentPairProduct
  rw [offDiagPairs_incident_prod_eq_erase]
  simpa [blaschkePairFactor] using
    blaschkeIncidentProduct_eq_coordinateSlice x a k

/-- Updating `k` does not change the frozen coordinates in the coordinate slice. -/
lemma blaschkeCoordinateSlice_update_eq
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) (u : ℂ) :
    blaschkeCoordinateSlice (Function.update x k u) a k u =
      blaschkeCoordinateSlice x a k u := by
  unfold blaschkeCoordinateSlice
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  simp [Function.update_of_ne hik]

/--
After updating `k`, the incident product is the same coordinate slice evaluated
at the new value.
-/
lemma blaschkeIncidentPairProduct_update_eq_coordinateSlice
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) (k : Fin n) (u : ℂ) :
    blaschkeIncidentPairProduct (Function.update x k u) a k =
      blaschkeCoordinateSlice x a k u := by
  rw [blaschkeIncidentPairProduct_eq_coordinateSlice]
  rw [show (Function.update x k u) k = u by simp]
  exact blaschkeCoordinateSlice_update_eq x a k u

/--
One-coordinate maximum-modulus step for the coordinate slice.

The slice is the squared norm of a one-variable polynomial in `u`, so the
maximum-modulus principle pushes a point of the closed unit disk to the
boundary without decreasing the slice.
-/
theorem blaschkeCoordinateSlice_boundary_step
    {n : ℕ} (x : Fin n → ℂ) {a : ℝ}
    (_h0a : 0 < a)
    (_ha1 : a < 1)
    (hx : ∀ i, ‖x i‖ ≤ 1)
    (k : Fin n) :
    ∃ u : ℂ,
      ‖u‖ = 1 ∧
        blaschkeCoordinateSlice x a k (x k) ≤
          blaschkeCoordinateSlice x a k u := by
  let P : ℂ → ℂ := fun u => blaschkeCoordinatePolynomial x a k u
  have hdiff : DiffContOnCl ℂ P (Metric.ball (0 : ℂ) 1) := by
    have hdiff_all : Differentiable ℂ P := by
      dsimp [P, blaschkeCoordinatePolynomial]
      fun_prop
    exact hdiff_all.diffContOnCl
  have hbounded : Bornology.IsBounded (Metric.ball (0 : ℂ) 1) :=
    Metric.isBounded_ball
  have hnonempty : (Metric.ball (0 : ℂ) 1).Nonempty :=
    ⟨0, by simp⟩
  rcases Complex.exists_mem_frontier_isMaxOn_norm
      (U := Metric.ball (0 : ℂ) 1) hbounded hnonempty hdiff with
    ⟨u, hu_frontier, hmax⟩
  refine ⟨u, ?hu_norm, ?hle⟩
  · have hu_sphere : u ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
        hu_frontier
    simpa [Metric.mem_sphere, dist_eq_norm] using hu_sphere
  · have hxk_closure : x k ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx k
    have hnorm : ‖P (x k)‖ ≤ ‖P u‖ :=
      hmax hxk_closure
    have hsquare : ‖P (x k)‖ ^ (2 : ℕ) ≤ ‖P u‖ ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    simpa [P, blaschkeCoordinatePolynomial_norm_sq] using hsquare

/--
One-coordinate maximum-modulus step for the off-diagonal product, derived from
the coordinate-slice boundary step.
-/
theorem blaschkeOffDiagProduct_coordinate_boundary_step
    {n : ℕ} (x : Fin n → ℂ) {a : ℝ}
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hx : ∀ i, ‖x i‖ ≤ 1)
    (k : Fin n) :
    ∃ u : ℂ,
      ‖u‖ = 1 ∧
        blaschkeOffDiagProduct x a ≤
          blaschkeOffDiagProduct (Function.update x k u) a := by
  rcases blaschkeCoordinateSlice_boundary_step x h0a ha1 hx k with
    ⟨u, hu, hslice⟩
  refine ⟨u, hu, ?_⟩
  rw [blaschkeOffDiagProduct_eq_incident_mul_nonincident x a k]
  rw [blaschkeOffDiagProduct_eq_incident_mul_nonincident
    (Function.update x k u) a k]
  rw [blaschkeIncidentPairProduct_eq_coordinateSlice]
  rw [blaschkeIncidentPairProduct_update_eq_coordinateSlice]
  rw [blaschkeNonincidentProduct_update_eq]
  exact mul_le_mul_of_nonneg_right hslice
    (blaschkeNonincidentProduct_nonneg x a k)

/--
Iterate the one-coordinate boundary step over a chosen finite set of
coordinates.
-/
lemma blaschkeOffDiagProduct_boundary_iteration
    {n : ℕ} (s : Finset (Fin n)) (x : Fin n → ℂ) {a : ℝ}
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ y : Fin n → ℂ,
      (∀ i, ‖y i‖ ≤ 1) ∧
        (∀ i, i ∈ s → ‖y i‖ = 1) ∧
          blaschkeOffDiagProduct x a ≤ blaschkeOffDiagProduct y a := by
  classical
  refine Finset.induction_on s ?base ?step
  · refine ⟨x, hx, ?_, le_rfl⟩
    intro i hi
    cases hi
  · intro k s hks ih
    rcases ih with ⟨y, hy_unit, hy_boundary, hxy⟩
    rcases blaschkeOffDiagProduct_coordinate_boundary_step y h0a ha1 hy_unit k with
      ⟨u, hu, hstep⟩
    let y' : Fin n → ℂ := Function.update y k u
    refine ⟨y', ?_, ?_, hxy.trans hstep⟩
    · intro i
      by_cases hik : i = k
      · subst i
        simp [y', hu.le]
      · rw [show y' i = y i by
          dsimp [y']
          rw [Function.update_of_ne hik]]
        exact hy_unit i
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with hik | his
      · subst i
        simp [y', hu]
      · have hik : i ≠ k := by
          intro h
          subst i
          exact hks his
        rw [show y' i = y i by
          dsimp [y']
          rw [Function.update_of_ne hik]]
        exact hy_boundary i his

/--
Maximum-modulus step in PDF Lemma 3, in the off-diagonal form actually used by
Lemma 4.

This is now a theorem obtained by applying the one-coordinate boundary step to
all coordinates.  The analogous statement for the full product including the
diagonal factors is false already in degree one.
-/
theorem blaschkeOffDiagProduct_le_torus_product_of_pos_a
    {n : ℕ} (x : Fin n → ℂ) {a : ℝ}
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ ω : Fin n → ℂ,
      onUnitCircle ω ∧ blaschkeOffDiagProduct x a ≤ blaschkeOffDiagProduct ω a := by
  rcases blaschkeOffDiagProduct_boundary_iteration
      (Finset.univ : Finset (Fin n)) x h0a ha1 hx with
    ⟨ω, _hω_unit, hω_boundary, hle⟩
  exact ⟨ω, by intro i; exact hω_boundary i (Finset.mem_univ i), hle⟩

/--
Guardrail: the analogous maximum-modulus statement for the full product,
including diagonal factors, is false already for one point.
-/
lemma not_fullProduct_torus_max_boundary_one :
    ¬ (∀ x : Fin 1 → ℂ,
      (∀ i, ‖x i‖ ≤ 1) →
        ∃ ω : Fin 1 → ℂ,
          onUnitCircle ω ∧
            blaschkeFullProduct x (1 / 2 : ℝ) ≤
              blaschkeFullProduct ω (1 / 2 : ℝ)) := by
  intro h
  let x : Fin 1 → ℂ := fun _ => 0
  have hxunit : ∀ i, ‖x i‖ ≤ 1 := by
    intro i
    simp [x]
  rcases h x hxunit with ⟨ω, hω, hle⟩
  have hxval : blaschkeFullProduct x (1 / 2 : ℝ) = 1 := by
    simp [blaschkeFullProduct, x]
  have hωval : blaschkeFullProduct ω (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
    rw [blaschkeFullProduct_eq_diag_mul_offDiag]
    rw [blaschkeDiagProduct_torus_eq ω (by norm_num) (by norm_num) hω]
    have hOff : (offDiagPairs : Finset (Fin 1 × Fin 1)) = ∅ := by
      ext p
      rcases p with ⟨i, j⟩
      fin_cases i
      fin_cases j
      simp [offDiagPairs]
    unfold blaschkeOffDiagProduct
    rw [hOff]
    norm_num
  rw [hxval, hωval] at hle
  norm_num at hle

/-- In degree zero, there are no off-diagonal pairs. -/
lemma blaschkeOffDiagProduct_degree_zero
    (x : Fin 0 → ℂ) (a : ℝ) :
    blaschkeOffDiagProduct x a = 1 := by
  simp [blaschkeOffDiagProduct, offDiagPairs]

/-- The off-diagonal maximum boundary is trivial in degree zero. -/
theorem blaschkeOffDiagProduct_le_torus_product_degree_zero
    (x : Fin 0 → ℂ) {a : ℝ} :
    ∃ ω : Fin 0 → ℂ,
      onUnitCircle ω ∧ blaschkeOffDiagProduct x a ≤ blaschkeOffDiagProduct ω a := by
  let ω : Fin 0 → ℂ := fun i => False.elim i.elim0
  refine ⟨ω, ?_, ?_⟩
  · intro i
    exact False.elim i.elim0
  · simp [blaschkeOffDiagProduct, offDiagPairs]

/-- In degree one, there are no off-diagonal pairs. -/
lemma offDiagPairs_one :
    (offDiagPairs : Finset (Fin 1 × Fin 1)) = ∅ := by
  ext p
  rcases p with ⟨i, j⟩
  fin_cases i
  fin_cases j
  simp [offDiagPairs]

/-- In degree one, the off-diagonal Blaschke product is empty. -/
lemma blaschkeOffDiagProduct_degree_one
    (x : Fin 1 → ℂ) (a : ℝ) :
    blaschkeOffDiagProduct x a = 1 := by
  unfold blaschkeOffDiagProduct
  rw [offDiagPairs_one]
  simp

/-- The off-diagonal maximum boundary is trivial in degree one. -/
theorem blaschkeOffDiagProduct_le_torus_product_degree_one
    (x : Fin 1 → ℂ) {a : ℝ} :
    ∃ ω : Fin 1 → ℂ,
      onUnitCircle ω ∧ blaschkeOffDiagProduct x a ≤ blaschkeOffDiagProduct ω a := by
  let ω : Fin 1 → ℂ := fun _ => 1
  refine ⟨ω, ?_, ?_⟩
  · intro i
    simp [ω]
  · rw [blaschkeOffDiagProduct_degree_one x a]
    rw [blaschkeOffDiagProduct_degree_one ω a]

/-- In degree two, the off-diagonal Blaschke product has one squared factor. -/
lemma blaschkeOffDiagProduct_two
    (x : Fin 2 → ℂ) (a : ℝ) :
    blaschkeOffDiagProduct x a =
      ‖1 - (a : ℂ) * x 0 * (starRingEnd ℂ) (x 1)‖ ^ (2 : ℕ) := by
  rw [blaschkeOffDiagProduct_eq_upper_sq]
  simp [upperOffDiagPairs_two]

/--
For two disk points, one Blaschke factor is bounded by its largest possible
boundary value.
-/
lemma norm_one_sub_real_mul_mul_conj_le_one_add
    {a : ℝ} (h0a : 0 ≤ a)
    {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ≤ 1 + a := by
  calc
    ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖
        ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) * u * (starRingEnd ℂ) v‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le (1 : ℂ) (-((a : ℂ) * u * (starRingEnd ℂ) v))
    _ = 1 + |a| * ‖u‖ * ‖v‖ := by
          simp
    _ = 1 + a * ‖u‖ * ‖v‖ := by
          rw [abs_of_nonneg h0a]
    _ ≤ 1 + a * 1 * 1 := by
          gcongr
    _ = 1 + a := by
          ring

/-- A two-point torus configuration that maximizes the one pair factor. -/
lemma omegaTwo_onUnitCircle :
    onUnitCircle (fun i : Fin 2 => if i = 0 then (1 : ℂ) else (-1 : ℂ)) := by
  intro i
  fin_cases i <;> simp

/-- The chosen two-point torus configuration gives the value `(1+a)^2`. -/
lemma blaschkeOffDiagProduct_two_boundary_value
    {a : ℝ} (h0a : 0 ≤ a) :
    blaschkeOffDiagProduct
        (fun i : Fin 2 => if i = 0 then (1 : ℂ) else (-1 : ℂ)) a =
      (1 + a) ^ (2 : ℕ) := by
  rw [blaschkeOffDiagProduct_two]
  simp
  have hnorm : ‖((1 + a : ℝ) : ℂ)‖ = 1 + a := by
    rw [Complex.norm_def, Complex.normSq_ofReal]
    rw [← sq]
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (by linarith)
  simpa using congrArg (fun t : ℝ => t ^ (2 : ℕ)) hnorm

/-- The off-diagonal maximum boundary is proved directly in degree two. -/
theorem blaschkeOffDiagProduct_le_torus_product_degree_two
    (x : Fin 2 → ℂ) {a : ℝ}
    (h0a : 0 ≤ a)
    (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ ω : Fin 2 → ℂ,
      onUnitCircle ω ∧ blaschkeOffDiagProduct x a ≤ blaschkeOffDiagProduct ω a := by
  let ω : Fin 2 → ℂ := fun i => if i = 0 then (1 : ℂ) else (-1 : ℂ)
  refine ⟨ω, ?_, ?_⟩
  · exact omegaTwo_onUnitCircle
  · rw [blaschkeOffDiagProduct_two_boundary_value h0a]
    rw [blaschkeOffDiagProduct_two]
    have hnorm :
        ‖1 - (a : ℂ) * x 0 * (starRingEnd ℂ) (x 1)‖ ≤ 1 + a :=
      norm_one_sub_real_mul_mul_conj_le_one_add h0a (hx 0) (hx 1)
    have hrhs_nonneg : 0 ≤ 1 + a := by
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) hrhs_nonneg).2 hnorm

/--
The off-diagonal maximum boundary is fully proved in all degrees `n ≤ 2`.
The general theorem below handles all degrees; this small-degree statement is
kept as a useful sanity check.
-/
theorem blaschkeOffDiagProduct_le_torus_product_of_degree_le_two
    {n : ℕ} (hn : n ≤ 2) (x : Fin n → ℂ) {a : ℝ}
    (h0a : 0 ≤ a)
    (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ ω : Fin n → ℂ,
      onUnitCircle ω ∧ blaschkeOffDiagProduct x a ≤ blaschkeOffDiagProduct ω a := by
  interval_cases n
  · exact blaschkeOffDiagProduct_le_torus_product_degree_zero x
  · exact blaschkeOffDiagProduct_le_torus_product_degree_one x
  · exact blaschkeOffDiagProduct_le_torus_product_degree_two x h0a hx

/--
Positivity of every torus factor in the Blaschke all-pairs product.
-/
lemma blaschke_torus_factor_pos_of_nonneg_lt_one
    {n : ℕ} {ω : Fin n → ℂ} {t : ℝ}
    (h0t : 0 ≤ t)
    (ht1 : t < 1)
    (hω : onUnitCircle ω)
    (p : Fin n × Fin n) :
    0 < ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖ := by
  have hnorm_z :
      ‖(t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖ = t := by
    rw [norm_mul, norm_mul]
    simp [abs_of_nonneg h0t, hω p.1, hω p.2]
  have hne : 1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2) ≠ 0 := by
    intro hzero
    have hz_eq_one :
        (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2) = 1 := by
      have hsub :
          (1 : ℂ) = (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2) :=
        sub_eq_zero.mp hzero
      exact hsub.symm
    have hnorm_one :
        ‖(t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖ = 1 := by
      rw [hz_eq_one]
      simp
    linarith
  exact norm_pos_iff.mpr hne

/-- If `0 < n` and `0 ≤ t < 1`, then `1 - t^n` is positive. -/
lemma one_sub_pow_pos_of_nonneg_lt_one
    {n : ℕ} {t : ℝ}
    (hn : 0 < n)
    (h0t : 0 ≤ t)
    (ht1 : t < 1) :
    0 < 1 - t ^ n := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hpow_lt : t ^ n < 1 := by
    simpa using (pow_lt_one₀ h0t ht1 hn_ne)
  linarith

/--
Positivity of every torus factor in the Blaschke all-pairs product for a
positive parameter.
-/
lemma blaschke_torus_factor_pos
    {n : ℕ} {ω : Fin n → ℂ} {a : ℝ}
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω)
    (p : Fin n × Fin n) :
    0 < ‖1 - (a : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖ := by
  exact blaschke_torus_factor_pos_of_nonneg_lt_one h0a.le ha1 hω p

/-- If `0 < n` and `0 < a < 1`, then `1 - a^n` is positive. -/
lemma one_sub_pow_pos_of_pos_nat_of_lt_one
    {n : ℕ} {a : ℝ}
    (hn : 0 < n)
    (h0a : 0 < a)
    (ha1 : a < 1) :
    0 < 1 - a ^ n := by
  exact one_sub_pow_pos_of_nonneg_lt_one hn h0a.le ha1

/-- At the starting point of the PDF's logarithmic argument, `g(0)=0`. -/
lemma blaschkeLogGap_zero
    {n : ℕ} (hn : 0 < n) (ω : Fin n → ℂ) :
    blaschkeLogGap n ω 0 = 0 := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  simp [blaschkeLogGap, hn_ne]

/-- Continuity of the PDF's logarithmic gap on `[0,a]`. -/
theorem blaschkeLogGap_continuousOn_Icc_of_torus
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (hn : 0 < n)
    (_h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    ContinuousOn (fun t => blaschkeLogGap n ω t) (Set.Icc 0 a) := by
  have hfirst :
      ContinuousOn (fun t : ℝ => (n : ℝ) * Real.log (1 - t ^ n)) (Set.Icc 0 a) := by
    have hbase : ContinuousOn (fun t : ℝ => 1 - t ^ n) (Set.Icc 0 a) := by
      exact (continuous_const.sub (continuous_id.pow n)).continuousOn
    exact (hbase.log (fun t ht =>
      ne_of_gt (one_sub_pow_pos_of_nonneg_lt_one hn ht.1 (lt_of_le_of_lt ht.2 ha1)))).const_mul _
  have hsum :
      ContinuousOn
        (fun t : ℝ => (Finset.univ : Finset (Fin n × Fin n)).sum
          (fun p => Real.log
            ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖))
        (Set.Icc 0 a) := by
    have hterm : ∀ p : Fin n × Fin n,
        ContinuousOn
          (fun t : ℝ => Real.log
            ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖)
          (Set.Icc 0 a) := by
      intro p
      have hfac :
          ContinuousOn
            (fun t : ℝ => ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖)
            (Set.Icc 0 a) := by
        have hcont :
            Continuous
              (fun t : ℝ => ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖) := by
          fun_prop
        exact hcont.continuousOn
      exact hfac.log (fun t ht =>
        ne_of_gt (blaschke_torus_factor_pos_of_nonneg_lt_one
          ht.1 (lt_of_le_of_lt ht.2 ha1) hω p))
    have hsum_general : ∀ s : Finset (Fin n × Fin n),
        ContinuousOn
          (fun t : ℝ => s.sum
            (fun p => Real.log
              ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖))
          (Set.Icc 0 a) := by
      intro s
      refine Finset.induction_on s ?empty ?insert
      · fun_prop
      · intro p s hp ih
        convert! (hterm p).add ih using 1
        funext t
        simp [Finset.sum_insert hp]
    exact hsum_general Finset.univ
  dsimp [blaschkeLogGap]
  exact hfirst.sub hsum

/-- Differentiability of the logarithmic gap in the interior of `[0,a]`. -/
theorem blaschkeLogGap_differentiableOn_interior_Icc_of_torus
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (hn : 0 < n)
    (_h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    DifferentiableOn ℝ (fun t => blaschkeLogGap n ω t) (interior (Set.Icc 0 a)) := by
  let s := interior (Set.Icc 0 a)
  have hfirst :
      DifferentiableOn ℝ (fun t : ℝ => (n : ℝ) * Real.log (1 - t ^ n)) s := by
    have hbase : DifferentiableOn ℝ (fun t : ℝ => 1 - t ^ n) s := by
      fun_prop
    exact (hbase.log (fun t ht => by
      have htIcc : t ∈ Set.Icc 0 a := interior_subset ht
      exact ne_of_gt
        (one_sub_pow_pos_of_nonneg_lt_one hn htIcc.1 (lt_of_le_of_lt htIcc.2 ha1)))).const_mul _
  have hsum :
      DifferentiableOn ℝ
        (fun t : ℝ => (Finset.univ : Finset (Fin n × Fin n)).sum
          (fun p => Real.log
            ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖))
        s := by
    apply DifferentiableOn.fun_sum
    intro p _hp
    have hfac :
        DifferentiableOn ℝ
          (fun t : ℝ => ‖1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖)
          s := by
      intro t ht
      have htIcc : t ∈ Set.Icc 0 a := interior_subset ht
      have hco : DifferentiableAt ℝ (fun r : ℝ => (r : ℂ)) t := by
        change DifferentiableAt ℝ (fun r : ℝ => Complex.ofRealCLM r) t
        exact Complex.ofRealCLM.differentiableAt
      have hterm :
          DifferentiableAt ℝ
            (fun r : ℝ => (r : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)) t := by
        exact (hco.mul (differentiableAt_const (c := ω p.1))).mul
          (differentiableAt_const (c := (starRingEnd ℂ) (ω p.2)))
      have hlin :
          DifferentiableAt ℝ
            (fun r : ℝ => 1 - (r : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)) t := by
        exact (differentiableAt_const (c := (1 : ℂ))).sub hterm
      have hnonzero :
          1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2) ≠ 0 := by
        exact norm_pos_iff.mp
          (blaschke_torus_factor_pos_of_nonneg_lt_one
            htIcc.1 (lt_of_le_of_lt htIcc.2 ha1) hω p)
      exact (hlin.norm ℂ hnonzero).differentiableWithinAt
    exact hfac.log (fun t ht => by
      have htIcc : t ∈ Set.Icc 0 a := interior_subset ht
      exact ne_of_gt
        (blaschke_torus_factor_pos_of_nonneg_lt_one
          htIcc.1 (lt_of_le_of_lt htIcc.2 ha1) hω p))
  dsimp [blaschkeLogGap]
  exact hfirst.sub hsum

/--
Derivative of the squared norm of the affine complex factor
`1 - tζ`, written as a real polynomial in `t`.
-/
lemma hasDerivAt_normSq_one_sub_mul (ζ : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.normSq (1 - (r : ℂ) * ζ))
      (-2 * ζ.re + 2 * t * Complex.normSq ζ) t := by
  have hpoly :
      (fun r : ℝ => Complex.normSq (1 - (r : ℂ) * ζ)) =
        fun r : ℝ => (1 - r * ζ.re) ^ (2 : ℕ) + (r * ζ.im) ^ (2 : ℕ) := by
    funext r
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [hpoly]
  have h1 : HasDerivAt (fun r : ℝ => 1 - r * ζ.re) (-(ζ.re)) t := by
    convert! (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      ((hasDerivAt_id t).mul_const ζ.re) using 1 <;> simp
  have h2 : HasDerivAt (fun r : ℝ => r * ζ.im) (ζ.im) t := by
    simpa using (hasDerivAt_id t).mul_const ζ.im
  have h := (h1.pow 2).add (h2.pow 2)
  convert! h using 1
  simp [Complex.normSq_apply]
  ring

/--
Algebraic rewrite of the derivative of `log |1-tζ|` when `ζ` lies on the
unit circle.
-/
lemma log_norm_deriv_value_eq_re_div
    {ζ : ℂ} {t : ℝ}
    (hζ : ‖ζ‖ = 1)
    (hden : 1 - (t : ℂ) * ζ ≠ 0) :
    (1 / 2 : ℝ) *
        ((-2 * ζ.re + 2 * t * Complex.normSq ζ) /
          Complex.normSq (1 - (t : ℂ) * ζ)) =
      ((-ζ) / (1 - (t : ℂ) * ζ)).re := by
  have hnormSqζ : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hζ]
    norm_num
  have hparts : ζ.re ^ (2 : ℕ) + ζ.im ^ (2 : ℕ) = 1 := by
    simpa [Complex.normSq_apply, sq] using hnormSqζ
  have hparts_mul : ζ.re ^ (2 : ℕ) * t + ζ.im ^ (2 : ℕ) * t = t := by
    calc
      ζ.re ^ (2 : ℕ) * t + ζ.im ^ (2 : ℕ) * t =
          (ζ.re ^ (2 : ℕ) + ζ.im ^ (2 : ℕ)) * t := by ring
      _ = 1 * t := by rw [hparts]
      _ = t := by ring
  have hdenSq_ne : Complex.normSq (1 - (t : ℂ) * ζ) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp hden
  have hdenSq_simp :
      ((1 - ζ.re * t) ^ (2 : ℕ) + t ^ (2 : ℕ) * ζ.im ^ (2 : ℕ)) ≠ 0 := by
    simpa [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, sq, mul_comm, mul_left_comm, mul_assoc] using hdenSq_ne
  rw [Complex.div_re]
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    hnormSqζ]
  field_simp [hdenSq_simp]
  ring_nf at hparts_mul ⊢
  nlinarith

/-- The local derivative formula `d/dt log |1-tζ| = Re(-ζ/(1-tζ))`. -/
lemma hasDerivAt_log_norm_one_sub_mul
    {ζ : ℂ} {t : ℝ}
    (hζ : ‖ζ‖ = 1)
    (hden : 1 - (t : ℂ) * ζ ≠ 0) :
    HasDerivAt (fun r : ℝ => Real.log ‖1 - (r : ℂ) * ζ‖)
      (((-ζ) / (1 - (t : ℂ) * ζ)).re) t := by
  have hsq := hasDerivAt_normSq_one_sub_mul ζ t
  have hsq_ne : Complex.normSq (1 - (t : ℂ) * ζ) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp hden
  have hlog := hsq.log hsq_ne
  have hhalf :
      HasDerivAt
        (fun r : ℝ => (1 / 2 : ℝ) * Real.log (Complex.normSq (1 - (r : ℂ) * ζ)))
        ((1 / 2 : ℝ) * ((-2 * ζ.re + 2 * t * Complex.normSq ζ) /
          Complex.normSq (1 - (t : ℂ) * ζ))) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.const_mul (1 / 2 : ℝ) hlog)
  have heq :
      (fun r : ℝ => Real.log ‖1 - (r : ℂ) * ζ‖) =ᶠ[nhds t]
        (fun r : ℝ => (1 / 2 : ℝ) * Real.log (Complex.normSq (1 - (r : ℂ) * ζ))) := by
    filter_upwards with r
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
    ring
  have htarget := hhalf.congr_of_eventuallyEq heq
  convert! htarget using 1
  exact (log_norm_deriv_value_eq_re_div hζ hden).symm

/--
After multiplying the derivative of a logarithmic torus factor by `-t`, the
PDF's `Re(1/(1-tζ))-1` term appears.
-/
lemma neg_mul_log_norm_deriv_eq_inv_re_sub_one
    (ζ : ℂ) (t : ℝ)
    (hden : 1 - (t : ℂ) * ζ ≠ 0) :
    -t * (((-ζ) / (1 - (t : ℂ) * ζ)).re) =
      ((1 : ℂ) / (1 - (t : ℂ) * ζ)).re - 1 := by
  have hneg :
      (((-ζ) / (1 - (t : ℂ) * ζ)).re) =
        -((ζ / (1 - (t : ℂ) * ζ)).re) := by
    simp [neg_div]
  have hre_mul :
      t * ((ζ / (1 - (t : ℂ) * ζ)).re) =
        (((t : ℂ) * ζ) / (1 - (t : ℂ) * ζ)).re := by
    calc
      t * ((ζ / (1 - (t : ℂ) * ζ)).re) =
          ((t : ℂ) * (ζ / (1 - (t : ℂ) * ζ))).re := by
            simp [Complex.mul_re]
      _ = (((t : ℂ) * ζ) / (1 - (t : ℂ) * ζ)).re := by
            congr 1
            ring
  have hcomplex :
      ((t : ℂ) * ζ) / (1 - (t : ℂ) * ζ) =
        (1 : ℂ) / (1 - (t : ℂ) * ζ) - 1 := by
    field_simp [hden]
    ring
  calc
    -t * (((-ζ) / (1 - (t : ℂ) * ζ)).re)
        = t * ((ζ / (1 - (t : ℂ) * ζ)).re) := by
            rw [hneg]
            ring
    _ = (((t : ℂ) * ζ) / (1 - (t : ℂ) * ζ)).re := hre_mul
    _ = ((1 : ℂ) / (1 - (t : ℂ) * ζ) - 1).re := congrArg Complex.re hcomplex
    _ = ((1 : ℂ) / (1 - (t : ℂ) * ζ)).re - 1 := by simp

/--
The PDF's derivative identity after multiplying by the positive parameter.

This is the formal target for the line
`a g'(a) = Σ 1/(1-aω_j\barω_k) - n²/(1-a^n)`.
-/
theorem blaschkeLogGap_mul_deriv_eq_derivativeGap_of_torus
    {n : ℕ} (ω : Fin n → ℂ) {a t : ℝ}
    (hn : 0 < n)
    (_h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω)
    (ht : t ∈ interior (Set.Icc 0 a)) :
    t * deriv (fun s => blaschkeLogGap n ω s) t = blaschkeDerivativeGap n ω t := by
  let ζ : Fin n × Fin n → ℂ := fun p => ω p.1 * (starRingEnd ℂ) (ω p.2)
  let D : Fin n × Fin n → ℝ :=
    fun p => (((-ζ p) / (1 - (t : ℂ) * ζ p)).re)
  let E : Fin n × Fin n → ℝ :=
    fun p => (((1 : ℂ) / (1 - (t : ℂ) * ζ p)).re)
  have htIcc : t ∈ Set.Icc 0 a := interior_subset ht
  have ht_nonneg : 0 ≤ t := htIcc.1
  have ht_lt_one : t < 1 := lt_of_le_of_lt htIcc.2 ha1
  have hden_real_pos : 0 < 1 - t ^ n :=
    one_sub_pow_pos_of_nonneg_lt_one hn ht_nonneg ht_lt_one
  have hden_real_ne : 1 - t ^ n ≠ 0 := ne_of_gt hden_real_pos
  have hpow_deriv :
      HasDerivAt (fun r : ℝ => r ^ n) ((n : ℝ) * t ^ (n - 1)) t := by
    convert! (hasDerivAt_id t).pow n using 1 <;> simp
  have hbase :
      HasDerivAt (fun r : ℝ => 1 - r ^ n) (-(n : ℝ) * t ^ (n - 1)) t := by
    convert! (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hpow_deriv using 1 <;> simp
  have hlog_first :
      HasDerivAt (fun r : ℝ => Real.log (1 - r ^ n))
        ((-(n : ℝ) * t ^ (n - 1)) / (1 - t ^ n)) t :=
    hbase.log hden_real_ne
  have hfirst :
      HasDerivAt (fun r : ℝ => (n : ℝ) * Real.log (1 - r ^ n))
        ((n : ℝ) * ((-(n : ℝ) * t ^ (n - 1)) / (1 - t ^ n))) t := by
    simpa [mul_assoc] using (HasDerivAt.const_mul (n : ℝ) hlog_first)
  have hsum :
      HasDerivAt
        (fun r : ℝ => (Finset.univ : Finset (Fin n × Fin n)).sum
          (fun p => Real.log ‖1 - (r : ℂ) * ζ p‖))
        ((Finset.univ : Finset (Fin n × Fin n)).sum D) t := by
    apply HasDerivAt.fun_sum
    intro p _hp
    have hzeta_norm : ‖ζ p‖ = 1 := by
      simp [ζ, hω p.1, hω p.2]
    have hden : 1 - (t : ℂ) * ζ p ≠ 0 := by
      have hraw := norm_pos_iff.mp
        (blaschke_torus_factor_pos_of_nonneg_lt_one ht_nonneg ht_lt_one hω p)
      simpa [ζ, mul_assoc] using hraw
    exact hasDerivAt_log_norm_one_sub_mul hzeta_norm hden
  have hgap :
      HasDerivAt (fun r : ℝ => blaschkeLogGap n ω r)
        (((n : ℝ) * ((-(n : ℝ) * t ^ (n - 1)) / (1 - t ^ n))) -
          (Finset.univ : Finset (Fin n × Fin n)).sum D) t := by
    convert! hfirst.sub hsum using 1 <;> simp [blaschkeLogGap, ζ, mul_assoc]
    funext r
    rfl
  rw [hgap.deriv]
  have ht_pow : t * t ^ (n - 1) = t ^ n := by
    cases n with
    | zero => cases hn
    | succ m => simp [pow_succ, mul_comm]
  have hfirst_alg :
      t * ((n : ℝ) * ((-(n : ℝ) * t ^ (n - 1)) / (1 - t ^ n))) =
        -((n : ℝ) ^ (2 : ℕ)) * t ^ n / (1 - t ^ n) := by
    rw [← ht_pow]
    ring
  have hsum_alg :
      -t * ((Finset.univ : Finset (Fin n × Fin n)).sum D) =
        (Finset.univ : Finset (Fin n × Fin n)).sum E - (n : ℝ) ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    calc
      ∑ x ∈ Finset.univ, -t * D x = ∑ x ∈ Finset.univ, (E x - 1) := by
        apply Finset.sum_congr rfl
        intro p _hp
        have hden : 1 - (t : ℂ) * ζ p ≠ 0 := by
          have hraw := norm_pos_iff.mp
            (blaschke_torus_factor_pos_of_nonneg_lt_one ht_nonneg ht_lt_one hω p)
          simpa [ζ, mul_assoc] using hraw
        exact neg_mul_log_norm_deriv_eq_inv_re_sub_one (ζ p) t hden
      _ = ∑ x ∈ Finset.univ, E x - ∑ x : Fin n × Fin n, (1 : ℝ) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ x ∈ Finset.univ, E x - (n : ℝ) ^ (2 : ℕ) := by
        simp [Fintype.card_prod, pow_two]
  have hcombine :
      t * (((n : ℝ) * ((-(n : ℝ) * t ^ (n - 1)) / (1 - t ^ n))) -
          (Finset.univ : Finset (Fin n × Fin n)).sum D) =
        (Finset.univ : Finset (Fin n × Fin n)).sum E -
          (n : ℝ) ^ (2 : ℕ) / (1 - t ^ n) := by
    calc
      t * (((n : ℝ) * ((-(n : ℝ) * t ^ (n - 1)) / (1 - t ^ n))) -
          (Finset.univ : Finset (Fin n × Fin n)).sum D)
          = t * ((n : ℝ) * ((-(n : ℝ) * t ^ (n - 1)) / (1 - t ^ n))) +
              -t * ((Finset.univ : Finset (Fin n × Fin n)).sum D) := by ring
      _ = -((n : ℝ) ^ (2 : ℕ)) * t ^ n / (1 - t ^ n) +
            ((Finset.univ : Finset (Fin n × Fin n)).sum E - (n : ℝ) ^ (2 : ℕ)) := by
        rw [hfirst_alg, hsum_alg]
      _ = (Finset.univ : Finset (Fin n × Fin n)).sum E -
            (n : ℝ) ^ (2 : ℕ) / (1 - t ^ n) := by
        field_simp [hden_real_ne]
        ring
  rw [hcombine]
  simp [blaschkeDerivativeGap, ζ, E, mul_assoc]

/-- If all points are in the open unit disk, then their product is also inside it. -/
lemma szegoKernel_product_norm_lt_one
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    ‖(∏ i : Fin n, z i)‖ < 1 := by
  let i0 : Fin n := ⟨0, hn⟩
  have hprod_norm : ‖(∏ i : Fin n, z i)‖ = ∏ i : Fin n, ‖z i‖ := by
    rw [norm_prod]
  rw [hprod_norm]
  have herase_le_one :
      (∏ x ∈ (Finset.univ.erase i0), ‖z x‖) ≤ (1 : ℝ) := by
    calc
      (∏ x ∈ (Finset.univ.erase i0), ‖z x‖) ≤
          ∏ _x ∈ (Finset.univ.erase i0), (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro x _hx
          exact norm_nonneg (z x)
        · intro x _hx
          exact le_of_lt (hz x)
      _ = 1 := by simp
  have hfac_nonneg : 0 ≤ ‖z i0‖ := norm_nonneg _
  have hsplit :
      (∏ i : Fin n, ‖z i‖) =
        ‖z i0‖ * (∏ x ∈ (Finset.univ.erase i0), ‖z x‖) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i : Fin n => ‖z i‖) (Finset.mem_univ i0)]
  rw [hsplit]
  have hmul_le :
      ‖z i0‖ * (∏ x ∈ (Finset.univ.erase i0), ‖z x‖) ≤ ‖z i0‖ * 1 := by
    exact mul_le_mul_of_nonneg_left herase_le_one hfac_nonneg
  have hfac_lt : ‖z i0‖ * 1 < 1 := by
    simpa using hz i0
  exact lt_of_le_of_lt hmul_le hfac_lt

/-- Positivity of the denominator `1 - |∏ z_i|²` in PDF Lemma 2. -/
lemma szegoKernel_denominator_pos
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    0 < szegoKernelProductDefect z := by
  have hp : ‖(∏ i : Fin n, z i)‖ < 1 :=
    szegoKernel_product_norm_lt_one z hn hz
  have hp_nonneg : 0 ≤ ‖(∏ i : Fin n, z i)‖ := norm_nonneg _
  have hsq : ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ) < 1 := by
    nlinarith [sq_nonneg ‖(∏ i : Fin n, z i)‖]
  dsimp [szegoKernelProductDefect]
  linarith

/--
A real algebra wrapper for the Cauchy-Schwarz estimate used in PDF Lemma 2.
-/
lemma sq_le_mul_of_abs_le_sqrt_mul
    {x A B : ℝ}
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (h : |x| ≤ Real.sqrt A * Real.sqrt B) :
    x ^ (2 : ℕ) ≤ A * B := by
  have hrhs_nonneg : 0 ≤ Real.sqrt A * Real.sqrt B := by positivity
  have hsq :
      |x| ^ (2 : ℕ) ≤ (Real.sqrt A * Real.sqrt B) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ (abs_nonneg x) hrhs_nonneg).2 h
  calc
    x ^ (2 : ℕ) = |x| ^ (2 : ℕ) := by rw [sq_abs]
    _ ≤ (Real.sqrt A * Real.sqrt B) ^ (2 : ℕ) := hsq
    _ = A * B := by rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- Real parts of the complex geometric series. -/
lemma geometric_re_tsum_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    ((1 : ℂ) / (1 - q)).re = ∑' m : ℕ, (q ^ m).re := by
  have hsum : HasSum (fun m : ℕ => q ^ m) ((1 - q)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hq
  have hreal : HasSum (fun m : ℕ => (q ^ m).re) ((1 - q)⁻¹).re := by
    simpa [Function.comp_def] using hsum.map Complex.reCLM Complex.reCLM.continuous
  rw [hreal.tsum_eq]
  congr 1
  field_simp

/-- Each Szego-kernel ratio has norm strictly smaller than one. -/
lemma szegoKernel_pair_norm_lt_one
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) (p : Fin n × Fin n) :
    ‖z p.1 * (starRingEnd ℂ) (z p.2)‖ < 1 := by
  calc
    ‖z p.1 * (starRingEnd ℂ) (z p.2)‖ = ‖z p.1‖ * ‖z p.2‖ := by simp
    _ < 1 * 1 := mul_lt_mul'' (hz p.1) (hz p.2) (norm_nonneg _) (norm_nonneg _)
    _ = 1 := by norm_num

/--
For a fixed power `m`, the pair sum is the squared norm of the power sum.
-/
lemma szegoKernel_pair_power_sum_eq_normSq
    {n : ℕ} (z : Fin n → ℂ) (m : ℕ) :
    (Finset.univ : Finset (Fin n × Fin n)).sum
      (fun p => ((z p.1 * (starRingEnd ℂ) (z p.2)) ^ m).re) =
    Complex.normSq (∑ i : Fin n, z i ^ m) := by
  rw [← cross_sum_re_eq_normSq_sum (fun i : Fin n => z i ^ m)]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  rw [map_pow]
  exact mul_pow (z i) ((starRingEnd ℂ) (z j)) m

/--
The Szego-kernel power-series identity.

This is the finite-sum/geometric-series computation behind
`Σ Re K(z_j,z_k) = Σ_m |Σ_j z_j^m|²`.
-/
theorem szegoKernelRealSum_eq_powerNormSqSum
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    szegoKernelRealSum z = szegoKernelPowerNormSqSum z := by
  dsimp [szegoKernelRealSum, szegoKernelPowerNormSqSum]
  calc
    (Finset.univ : Finset (Fin n × Fin n)).sum
        (fun p => ((1 : ℂ) / (1 - z p.1 * (starRingEnd ℂ) (z p.2))).re)
        = (Finset.univ : Finset (Fin n × Fin n)).sum
          (fun p => ∑' m : ℕ, ((z p.1 * (starRingEnd ℂ) (z p.2)) ^ m).re) := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact geometric_re_tsum_of_norm_lt_one
              (szegoKernel_pair_norm_lt_one z hz p)
    _ = ∑' m : ℕ,
          (Finset.univ : Finset (Fin n × Fin n)).sum
            (fun p => ((z p.1 * (starRingEnd ℂ) (z p.2)) ^ m).re) := by
            rw [← Summable.tsum_finsetSum]
            intro p _hp
            have hgeom : HasSum
                (fun m : ℕ => (z p.1 * (starRingEnd ℂ) (z p.2)) ^ m)
                ((1 - z p.1 * (starRingEnd ℂ) (z p.2))⁻¹) :=
              hasSum_geometric_of_norm_lt_one (szegoKernel_pair_norm_lt_one z hz p)
            have hreal : HasSum
                (fun m : ℕ => ((z p.1 * (starRingEnd ℂ) (z p.2)) ^ m).re)
                (((1 - z p.1 * (starRingEnd ℂ) (z p.2))⁻¹).re) := by
              simpa [Function.comp_def] using hgeom.map Complex.reCLM Complex.reCLM.continuous
            exact hreal.summable
    _ = ∑' m : ℕ, Complex.normSq (∑ i : Fin n, z i ^ m) := by
            apply tsum_congr
            intro m
            exact szegoKernel_pair_power_sum_eq_normSq z m

/--
The Hardy-space norm identity saying that the Szego-kernel sum is nonnegative.

It now follows from the power-series expansion as a sum of nonnegative squared
norms.
-/
theorem szegoKernelRealSum_nonneg
    {n : ℕ} (z : Fin n → ℂ)
    (_hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    0 ≤ szegoKernelRealSum z := by
  rw [szegoKernelRealSum_eq_powerNormSqSum z hz]
  exact tsum_nonneg (fun m => Complex.normSq_nonneg (∑ i : Fin n, z i ^ m))

/--
The Hardy-space point kernel coefficients at a point of the disk.

Analytically this is the sequence `(1, z, z², ...)`; the strict disk hypothesis
makes it square-summable by the geometric series.
-/
lemma hardyPointKernel_memℓp {z : ℂ} (hz : ‖z‖ < 1) :
    Memℓp (fun m : ℕ => z ^ m) (2 : ℝ≥0∞) := by
  apply memℓp_gen
  have hs : Summable fun m : ℕ => (‖z‖ ^ (2 : ℕ)) ^ m := by
    apply summable_geometric_of_lt_one
    · positivity
    · have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith [sq_nonneg ‖z‖]
  convert! hs using 1
  ext m
  rw [norm_pow]
  norm_num
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

/-- The `ℓ²` vector `(1, z, z², ...)` for `‖z‖ < 1`. -/
def hardyPointKernel (z : ℂ) (hz : ‖z‖ < 1) :
    lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞) :=
  ⟨fun m : ℕ => z ^ m, hardyPointKernel_memℓp hz⟩

/--
The Szego-kernel sum vector `F = Σ_i (1, z_i, z_i², ...)` in coefficient
Hardy space.
-/
def hardySzegoKernelVector {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞) :=
  ∑ i : Fin n, hardyPointKernel (z i) (hz i)

/-- The `m`th coefficient of the finite Szego-kernel sum. -/
lemma hardySzegoKernelVector_apply
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) (m : ℕ) :
    hardySzegoKernelVector z hz m = ∑ i : Fin n, z i ^ m := by
  simp [hardySzegoKernelVector, hardyPointKernel]

/--
The concrete Hardy-space norm computation for the Szego-kernel sum.

This is the `F_normSq` half of the Hardy-space data used in PDF Lemma 2.
-/
theorem hardySzegoKernelVector_norm_sq_eq_szegoKernelRealSum
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    ‖hardySzegoKernelVector z hz‖ ^ (2 : ℕ) = szegoKernelRealSum z := by
  rw [szegoKernelRealSum_eq_powerNormSqSum z hz]
  dsimp [szegoKernelPowerNormSqSum]
  calc
    ‖hardySzegoKernelVector z hz‖ ^ (2 : ℕ)
        = ‖hardySzegoKernelVector z hz‖ ^ (2 : ℝ≥0∞).toReal := by
          norm_cast
    _ = ∑' m : ℕ, ‖hardySzegoKernelVector z hz m‖ ^ (2 : ℝ≥0∞).toReal := by
          exact lp.norm_rpow_eq_tsum (by norm_num)
            (hardySzegoKernelVector z hz)
    _ = ∑' m : ℕ, Complex.normSq (∑ i : Fin n, z i ^ m) := by
          apply tsum_congr
          intro m
          rw [hardySzegoKernelVector_apply z hz m]
          rw [Complex.normSq_eq_norm_sq]
          norm_cast

/--
The same norm computation in the real inner-product form expected by
`SzegoKernelHardyData`.
-/
theorem hardySzegoKernelVector_real_inner_eq_szegoKernelRealSum
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    szegoKernelRealSum z =
      inner ℝ (hardySzegoKernelVector z hz) (hardySzegoKernelVector z hz) := by
  rw [real_inner_self_eq_norm_sq]
  exact (hardySzegoKernelVector_norm_sq_eq_szegoKernelRealSum z hz).symm

/--
Taylor coefficients of one disk Blaschke factor
`(w - a) / (1 - conjugate a * w)`.

The expansion is

`-a + (1 - |a|²) * Σ_m conjugate(a)^m w^(m+1)`.
-/
def diskBlaschkeFactorCoeff (a : ℂ) : ℕ → ℂ
  | 0 => -a
  | m + 1 => ((1 - ‖a‖ ^ (2 : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ a) ^ m

/--
The coefficient sequence of a disk Blaschke factor belongs to `ℓ²`.

This is the first concrete `H²` building block needed for the remaining
Blaschke-defect vector.
-/
lemma diskBlaschkeFactorCoeff_memℓp {a : ℂ} (ha : ‖a‖ < 1) :
    Memℓp (diskBlaschkeFactorCoeff a) (2 : ℝ≥0∞) := by
  apply memℓp_gen
  have ha_sq_lt : ‖a‖ ^ (2 : ℕ) < 1 := by
    have hnonneg : 0 ≤ ‖a‖ := norm_nonneg a
    nlinarith [sq_nonneg ‖a‖]
  have hgeom : Summable fun m : ℕ => (‖a‖ ^ (2 : ℕ)) ^ m :=
    summable_geometric_of_lt_one (sq_nonneg ‖a‖) ha_sq_lt
  have htail :
      Summable fun m : ℕ => ‖diskBlaschkeFactorCoeff a (m + 1)‖ ^ (2 : ℕ) := by
    convert! hgeom.mul_left ((1 - ‖a‖ ^ (2 : ℕ)) ^ (2 : ℕ)) using 1
    ext m
    dsimp [diskBlaschkeFactorCoeff]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, RCLike.norm_conj]
    have hnonneg : 0 ≤ 1 - ‖a‖ ^ (2 : ℕ) := by nlinarith
    rw [abs_of_nonneg hnonneg]
    ring
  convert!
    (summable_nat_add_iff
      (f := fun m : ℕ => ‖diskBlaschkeFactorCoeff a m‖ ^ (2 : ℕ)) 1).mp htail
    using 1
  ext m
  norm_num

/-- The `H²` coefficient vector of one disk Blaschke factor. -/
def hardyBlaschkeFactorVector (a : ℂ) (ha : ‖a‖ < 1) :
    lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞) :=
  ⟨diskBlaschkeFactorCoeff a, diskBlaschkeFactorCoeff_memℓp ha⟩

/-- The squared coefficient norms of one Blaschke factor sum to `1`. -/
lemma diskBlaschkeFactorCoeff_norm_sq_tsum {a : ℂ} (ha : ‖a‖ < 1) :
    (∑' m : ℕ, ‖diskBlaschkeFactorCoeff a m‖ ^ (2 : ℕ)) = 1 := by
  have ha_sq_lt : ‖a‖ ^ (2 : ℕ) < 1 := by
    have hnonneg : 0 ≤ ‖a‖ := norm_nonneg a
    nlinarith [sq_nonneg ‖a‖]
  have ha_sq_nonneg : 0 ≤ ‖a‖ ^ (2 : ℕ) := sq_nonneg ‖a‖
  have hsumm :
      Summable fun m : ℕ => ‖diskBlaschkeFactorCoeff a m‖ ^ (2 : ℕ) := by
    have hmem := diskBlaschkeFactorCoeff_memℓp ha
    convert! hmem.summable (by norm_num) using 1
    ext m
    norm_num
  have htail_eq :
      (∑' m : ℕ, ‖diskBlaschkeFactorCoeff a (m + 1)‖ ^ (2 : ℕ)) =
        1 - ‖a‖ ^ (2 : ℕ) := by
    calc
      (∑' m : ℕ, ‖diskBlaschkeFactorCoeff a (m + 1)‖ ^ (2 : ℕ))
          = ∑' m : ℕ,
              (1 - ‖a‖ ^ (2 : ℕ)) ^ (2 : ℕ) *
                (‖a‖ ^ (2 : ℕ)) ^ m := by
            apply tsum_congr
            intro m
            dsimp [diskBlaschkeFactorCoeff]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
              RCLike.norm_conj]
            have hnonneg : 0 ≤ 1 - ‖a‖ ^ (2 : ℕ) := by nlinarith
            rw [abs_of_nonneg hnonneg]
            ring
      _ = (1 - ‖a‖ ^ (2 : ℕ)) ^ (2 : ℕ) *
            ∑' m : ℕ, (‖a‖ ^ (2 : ℕ)) ^ m := by
            rw [tsum_mul_left]
      _ = (1 - ‖a‖ ^ (2 : ℕ)) ^ (2 : ℕ) *
            (1 - ‖a‖ ^ (2 : ℕ))⁻¹ := by
            rw [tsum_geometric_of_lt_one ha_sq_nonneg ha_sq_lt]
      _ = 1 - ‖a‖ ^ (2 : ℕ) := by
            have hne : 1 - ‖a‖ ^ (2 : ℕ) ≠ 0 := by nlinarith
            field_simp [hne]
  rw [hsumm.tsum_eq_zero_add]
  rw [htail_eq]
  dsimp [diskBlaschkeFactorCoeff]
  rw [norm_neg]
  ring

/-- One disk Blaschke factor has `H²` norm one in coefficient space. -/
theorem hardyBlaschkeFactorVector_norm_sq_eq_one
    {a : ℂ} (ha : ‖a‖ < 1) :
    ‖hardyBlaschkeFactorVector a ha‖ ^ (2 : ℕ) = 1 := by
  calc
    ‖hardyBlaschkeFactorVector a ha‖ ^ (2 : ℕ)
        = ‖hardyBlaschkeFactorVector a ha‖ ^ (2 : ℝ≥0∞).toReal := by
          norm_cast
    _ = ∑' m : ℕ, ‖hardyBlaschkeFactorVector a ha m‖ ^ (2 : ℝ≥0∞).toReal := by
          exact lp.norm_rpow_eq_tsum (by norm_num)
            (hardyBlaschkeFactorVector a ha)
    _ = ∑' m : ℕ, ‖diskBlaschkeFactorCoeff a m‖ ^ (2 : ℕ) := by
          apply tsum_congr
          intro m
          norm_num [hardyBlaschkeFactorVector]
    _ = 1 := diskBlaschkeFactorCoeff_norm_sq_tsum ha

/-- Inside the disk, the denominator of a disk Blaschke factor is nonzero. -/
lemma diskBlaschkeFactor_den_ne_zero_of_norm_lt_one
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 - (starRingEnd ℂ) a * w ≠ 0 := by
  intro hzero
  have hqeq : (starRingEnd ℂ) a * w = 1 := (sub_eq_zero.mp hzero).symm
  have hqnorm : ‖(starRingEnd ℂ) a * w‖ = 1 := by
    rw [hqeq, norm_one]
  have hq_lt : ‖(starRingEnd ℂ) a * w‖ < 1 := by
    calc
      ‖(starRingEnd ℂ) a * w‖ = ‖a‖ * ‖w‖ := by simp
      _ < 1 * 1 := mul_lt_mul'' ha hw (norm_nonneg _) (norm_nonneg _)
      _ = 1 := by norm_num
  linarith

/--
The coefficient sequence above really expands the disk Blaschke factor on the
unit disk.
-/
lemma diskBlaschkeFactorCoeff_hasSum
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun m : ℕ => diskBlaschkeFactorCoeff a m * w ^ m)
      (diskBlaschkeFactor a w) := by
  let q : ℂ := (starRingEnd ℂ) a * w
  have hqnorm : ‖q‖ < 1 := by
    dsimp [q]
    calc
      ‖(starRingEnd ℂ) a * w‖ = ‖a‖ * ‖w‖ := by simp
      _ < 1 * 1 := mul_lt_mul'' ha hw (norm_nonneg _) (norm_nonneg _)
      _ = 1 := by norm_num
  have hgeom : HasSum (fun m : ℕ => q ^ m) ((1 - q)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hqnorm
  have htail : HasSum
      (fun m : ℕ => diskBlaschkeFactorCoeff a (m + 1) * w ^ (m + 1))
      ((((1 - ‖a‖ ^ (2 : ℕ) : ℝ) : ℂ) * w) * (1 - q)⁻¹) := by
    convert! hgeom.mul_left (((1 - ‖a‖ ^ (2 : ℕ) : ℝ) : ℂ) * w) using 1
    ext m
    dsimp [diskBlaschkeFactorCoeff, q]
    rw [mul_pow]
    ring
  have hfull : HasSum (fun m : ℕ => diskBlaschkeFactorCoeff a m * w ^ m)
      (((((1 - ‖a‖ ^ (2 : ℕ) : ℝ) : ℂ) * w) * (1 - q)⁻¹) + (-a)) := by
    simpa [diskBlaschkeFactorCoeff] using
      (hasSum_nat_add_iff
        (f := fun m : ℕ => diskBlaschkeFactorCoeff a m * w ^ m) 1).mp htail
  convert! hfull using 1
  dsimp [diskBlaschkeFactor]
  dsimp [q]
  have hden : 1 - (starRingEnd ℂ) a * w ≠ 0 :=
    diskBlaschkeFactor_den_ne_zero_of_norm_lt_one ha hw
  have hden' : 1 - w * (starRingEnd ℂ) a ≠ 0 := by
    simpa [mul_comm] using hden
  field_simp [hden, hden']
  have hnorm : ((‖a‖ ^ (2 : ℕ) : ℝ) : ℂ) = a * (starRingEnd ℂ) a := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj a).symm
  norm_num [hnorm]
  ring

/-- The Blaschke-factor coefficient series is absolutely summable after evaluation in the disk. -/
lemma diskBlaschkeFactorCoeff_eval_summable_norm
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    Summable fun m : ℕ => ‖diskBlaschkeFactorCoeff a m * w ^ m‖ := by
  have hq_lt : ‖a‖ * ‖w‖ < 1 := by
    calc
      ‖a‖ * ‖w‖ < 1 * 1 := mul_lt_mul'' ha hw (norm_nonneg _) (norm_nonneg _)
      _ = 1 := by norm_num
  have hq_nonneg : 0 ≤ ‖a‖ * ‖w‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgeom : Summable fun m : ℕ => (‖a‖ * ‖w‖) ^ m :=
    summable_geometric_of_lt_one hq_nonneg hq_lt
  have htail :
      Summable fun m : ℕ => ‖diskBlaschkeFactorCoeff a (m + 1) * w ^ (m + 1)‖ := by
    convert! hgeom.mul_left (|1 - ‖a‖ ^ (2 : ℕ)| * ‖w‖) using 1
    ext m
    dsimp [diskBlaschkeFactorCoeff]
    rw [norm_mul, norm_mul, Complex.norm_real, norm_pow, RCLike.norm_conj, norm_pow]
    rw [Real.norm_eq_abs]
    ring
  exact
    (summable_nat_add_iff
      (f := fun m : ℕ => ‖diskBlaschkeFactorCoeff a m * w ^ m‖) 1).mp htail

/-- The coefficient sequence of one Blaschke factor is absolutely summable. -/
lemma diskBlaschkeFactorCoeff_summable_norm
    {a : ℂ} (ha : ‖a‖ < 1) :
    Summable fun m : ℕ => ‖diskBlaschkeFactorCoeff a m‖ := by
  have hgeom : Summable fun m : ℕ => ‖a‖ ^ m :=
    summable_geometric_of_lt_one (norm_nonneg a) ha
  have htail :
      Summable fun m : ℕ => ‖diskBlaschkeFactorCoeff a (m + 1)‖ := by
    convert! hgeom.mul_left |1 - ‖a‖ ^ (2 : ℕ)| using 1
    ext m
    dsimp [diskBlaschkeFactorCoeff]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, RCLike.norm_conj]
  exact
    (summable_nat_add_iff
      (f := fun m : ℕ => ‖diskBlaschkeFactorCoeff a m‖) 1).mp htail

/--
Cauchy convolution of two coefficient sequences.

This is the coefficient-level multiplication used to build the finite
Blaschke product from its one-factor Taylor expansions.
-/
def sequenceConvolution (u v : ℕ → ℂ) : ℕ → ℂ :=
  fun m => (Finset.range (m + 1)).sum fun k => u k * v (m - k)

/-- The zeroth coefficient of a Cauchy convolution is the product of zeroth coefficients. -/
lemma sequenceConvolution_zero (u v : ℕ → ℂ) :
    sequenceConvolution u v 0 = u 0 * v 0 := by
  simp [sequenceConvolution]

/-- The coefficient sequence `(1, 0, 0, ...)` is a right unit for Cauchy convolution. -/
lemma sequenceConvolution_right_unit (u : ℕ → ℂ) :
    sequenceConvolution u (fun m => if m = 0 then 1 else 0) = u := by
  funext m
  rw [sequenceConvolution]
  calc
    (∑ k ∈ Finset.range (m + 1),
        u k * (fun m => if m = 0 then (1 : ℂ) else 0) (m - k))
        = u m * (if m - m = 0 then (1 : ℂ) else 0) := by
          refine Finset.sum_eq_single m ?_ ?_
          · intro k hk hkm
            have hk_le : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            have hsub_ne : m - k ≠ 0 := by
              intro hsub
              have hk_eq : k = m := by omega
              exact hkm hk_eq
            simp [hsub_ne]
          · intro hm
            simp at hm
    _ = u m := by simp

/-- Cauchy convolution is additive-linear in the right input. -/
lemma sequenceConvolution_sub_right (f u v : ℕ → ℂ) :
    sequenceConvolution f (fun n => u n - v n) =
      fun m => sequenceConvolution f u m - sequenceConvolution f v m := by
  funext m
  simp [sequenceConvolution, mul_sub, Finset.sum_sub_distrib]

/--
The auxiliary tail that appears when Cauchy-multiplying by one disk Blaschke
factor.  If `c = conjugate a`, then this is
`u n + c u (n - 1) + ... + c^n u 0`.
-/
def blaschkeConvolutionTail (a : ℂ) (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => u 0
  | n + 1 => u (n + 1) + (starRingEnd ℂ) a * blaschkeConvolutionTail a u n

/-- The recursive tail is the expected finite geometric convolution. -/
lemma blaschkeConvolutionTail_eq_sum (a : ℂ) (u : ℕ → ℂ) (n : ℕ) :
    blaschkeConvolutionTail a u n =
      ∑ k ∈ Finset.range (n + 1), ((starRingEnd ℂ) a) ^ k * u (n - k) := by
  induction n with
  | zero =>
      simp [blaschkeConvolutionTail]
  | succ n ih =>
      rw [blaschkeConvolutionTail, ih]
      conv_rhs => rw [Finset.sum_range_succ']
      simp [pow_succ, add_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The Blaschke tail is additive-linear in the input sequence. -/
lemma blaschkeConvolutionTail_sub_right (a : ℂ) (u v : ℕ → ℂ) (N : ℕ) :
    blaschkeConvolutionTail a (fun n => u n - v n) N =
      blaschkeConvolutionTail a u N - blaschkeConvolutionTail a v N := by
  induction N with
  | zero =>
      simp [blaschkeConvolutionTail]
  | succ N ih =>
      simp [blaschkeConvolutionTail, ih]
      ring

/--
If the input sequence has vanished from index `K` onward, then after any
later index `N ≥ K` the Blaschke tail evolves by pure geometric decay.
-/
lemma blaschkeConvolutionTail_after_zero
    (a : ℂ) (u : ℕ → ℂ) {K : ℕ}
    (hu : ∀ n, K ≤ n → u n = 0) (N m : ℕ) (hKN : K ≤ N) :
    blaschkeConvolutionTail a u (N + m) =
      ((starRingEnd ℂ) a) ^ m * blaschkeConvolutionTail a u N := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Nat.add_succ, blaschkeConvolutionTail, ih]
      have hzero : u (N + m + 1) = 0 := hu (N + m + 1) (by omega)
      simp [hzero, pow_succ, mul_comm, mul_left_comm]

/--
For a finitely supported input and `|a| < 1`, the Blaschke tail tends to zero
along the shifted sequence `K + m`.
-/
lemma blaschkeConvolutionTail_norm_sq_tendsto_zero_shift
    {a : ℂ} (ha : ‖a‖ < 1) (u : ℕ → ℂ) {K : ℕ}
    (hu : ∀ n, K ≤ n → u n = 0) :
    Filter.Tendsto (fun m : ℕ =>
      ‖blaschkeConvolutionTail a u (K + m)‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
  have ha_sq_lt : ‖a‖ ^ (2 : ℕ) < 1 := by
    have hmul : ‖a‖ * ‖a‖ < 1 * 1 :=
      mul_lt_mul'' ha ha (norm_nonneg a) (norm_nonneg a)
    nlinarith
  have hpow :
      Filter.Tendsto (fun m : ℕ => (‖a‖ ^ (2 : ℕ)) ^ m)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ‖a‖) ha_sq_lt
  have hmul :
      Filter.Tendsto
        (fun m : ℕ => (‖a‖ ^ (2 : ℕ)) ^ m *
          ‖blaschkeConvolutionTail a u K‖ ^ (2 : ℕ)) Filter.atTop
        (nhds (0 * ‖blaschkeConvolutionTail a u K‖ ^ (2 : ℕ))) :=
    hpow.mul tendsto_const_nhds
  convert! hmul using 1
  · ext m
    rw [blaschkeConvolutionTail_after_zero a u hu K m le_rfl]
    rw [norm_mul, norm_pow, RCLike.norm_conj]
    ring
  · simp

/--
For a finitely supported input and `|a| < 1`, the Blaschke tail tends to zero.
-/
lemma blaschkeConvolutionTail_norm_sq_tendsto_zero_of_eventually_zero
    {a : ℂ} (ha : ‖a‖ < 1) (u : ℕ → ℂ) {K : ℕ}
    (hu : ∀ n, K ≤ n → u n = 0) :
    Filter.Tendsto (fun N : ℕ =>
      ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
  have hshift := blaschkeConvolutionTail_norm_sq_tendsto_zero_shift ha u hu
  have hsub : Filter.Tendsto (fun N : ℕ => N - K) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b + K, by intro a ha; omega⟩
  have hcomp := hshift.comp hsub
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop K] with N hN
  simp [Nat.add_sub_of_le hN]

/--
The coefficient update obtained by multiplying a sequence by the one-factor
Blaschke series `(w - a) / (1 - conjugate a * w)`.
-/
def diskBlaschkeConvolutionCoeff (a : ℂ) (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => -a * u 0
  | n + 1 =>
      -a * u (n + 1) +
        (((1 - ‖a‖ ^ (2 : ℕ) : ℝ) : ℂ) * blaschkeConvolutionTail a u n)

/--
The abstract Cauchy convolution with the disk-Blaschke coefficient sequence is
exactly the explicit tail recurrence above.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_eq_diskBlaschkeConvolutionCoeff
    (a : ℂ) (u : ℕ → ℂ) :
    sequenceConvolution (diskBlaschkeFactorCoeff a) u =
      diskBlaschkeConvolutionCoeff a u := by
  funext m
  cases m with
  | zero =>
      simp [sequenceConvolution, diskBlaschkeConvolutionCoeff, diskBlaschkeFactorCoeff]
  | succ n =>
      rw [sequenceConvolution, diskBlaschkeConvolutionCoeff, blaschkeConvolutionTail_eq_sum]
      conv_lhs => rw [Finset.sum_range_succ']
      simp [diskBlaschkeFactorCoeff, pow_succ, mul_assoc]
      rw [← Finset.mul_sum]
      ring

/-- Base energy identity for the zeroth coefficient of a one-factor Blaschke update. -/
lemma diskBlaschke_energy_base (a x : ℂ) :
    let r : ℝ := 1 - ‖a‖ ^ (2 : ℕ)
    ‖-a * x‖ ^ (2 : ℕ) + r * ‖x‖ ^ (2 : ℕ) =
      ‖x‖ ^ (2 : ℕ) := by
  dsimp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_mul, Complex.normSq_neg]
  rw [Complex.sq_norm x]
  ring_nf

/--
The local energy identity behind the one-step Blaschke isometry.

With `r = 1 - |a|²`, the update
`g = -a*x + r*y`, `y' = x + conjugate a*y` preserves
`|g|² + r|y'|² = |x|² + r|y|²`.
-/
lemma diskBlaschke_energy_step (a x y : ℂ) :
    let r : ℝ := 1 - ‖a‖ ^ (2 : ℕ)
    ‖-a * x + (r : ℂ) * y‖ ^ (2 : ℕ) +
        r * ‖x + (starRingEnd ℂ) a * y‖ ^ (2 : ℕ) =
      ‖x‖ ^ (2 : ℕ) + r * ‖y‖ ^ (2 : ℕ) := by
  dsimp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_conj]
  rw [Complex.sq_norm y]
  have hreal :
      Complex.normSq (1 - ↑(Complex.normSq a)) =
        (1 - Complex.normSq a) ^ (2 : ℕ) := by
    rw [show (1 - ↑(Complex.normSq a) : ℂ) =
        ((1 - Complex.normSq a : ℝ) : ℂ) by norm_num,
      Complex.normSq_ofReal]
    ring
  rw [hreal]
  ring_nf

/-- A convenient two-term square estimate for complex norms. -/
lemma complex_norm_add_sq_le_two (x y : ℂ) :
    ‖x + y‖ ^ (2 : ℕ) ≤ 2 * ‖x‖ ^ (2 : ℕ) + 2 * ‖y‖ ^ (2 : ℕ) := by
  have htri := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖),
    mul_nonneg hxy (by nlinarith : 0 ≤ ‖x‖ + ‖y‖)]

/-- The zeroth coefficient form of the energy identity. -/
lemma diskBlaschkeConvolutionCoeff_energy_base (a : ℂ) (u : ℕ → ℂ) :
    let r : ℝ := 1 - ‖a‖ ^ (2 : ℕ)
    ‖diskBlaschkeConvolutionCoeff a u 0‖ ^ (2 : ℕ) +
        r * ‖blaschkeConvolutionTail a u 0‖ ^ (2 : ℕ) =
      ‖u 0‖ ^ (2 : ℕ) := by
  simpa [diskBlaschkeConvolutionCoeff, blaschkeConvolutionTail] using
    diskBlaschke_energy_base a (u 0)

/-- The successor coefficient form of the energy identity. -/
lemma diskBlaschkeConvolutionCoeff_energy_step (a : ℂ) (u : ℕ → ℂ) (n : ℕ) :
    let r : ℝ := 1 - ‖a‖ ^ (2 : ℕ)
    ‖diskBlaschkeConvolutionCoeff a u (n + 1)‖ ^ (2 : ℕ) +
        r * ‖blaschkeConvolutionTail a u (n + 1)‖ ^ (2 : ℕ) =
      ‖u (n + 1)‖ ^ (2 : ℕ) +
        r * ‖blaschkeConvolutionTail a u n‖ ^ (2 : ℕ) := by
  simpa [diskBlaschkeConvolutionCoeff, blaschkeConvolutionTail] using
    diskBlaschke_energy_step a (u (n + 1)) (blaschkeConvolutionTail a u n)

/--
Finite telescoping form of the one-factor Blaschke energy identity.

This is the finite-support core of the remaining Hardy-space isometry: after
`N` coefficients, the possible discrepancy is exactly the nonnegative tail
term `(1 - |a|²) * |tail_N|²`.
-/
lemma diskBlaschkeConvolutionCoeff_partial_energy
    (a : ℂ) (u : ℕ → ℂ) (N : ℕ) :
    let r : ℝ := 1 - ‖a‖ ^ (2 : ℕ)
    (∑ m ∈ Finset.range (N + 1),
        ‖diskBlaschkeConvolutionCoeff a u m‖ ^ (2 : ℕ)) +
        r * ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ) =
      ∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ) := by
  induction N with
  | zero =>
      simpa using diskBlaschkeConvolutionCoeff_energy_base a u
  | succ N ih =>
      dsimp
      calc
        (∑ m ∈ Finset.range (N + 1 + 1),
            ‖diskBlaschkeConvolutionCoeff a u m‖ ^ (2 : ℕ)) +
            (1 - ‖a‖ ^ (2 : ℕ)) *
              ‖blaschkeConvolutionTail a u (N + 1)‖ ^ (2 : ℕ)
            =
          ((∑ m ∈ Finset.range (N + 1),
              ‖diskBlaschkeConvolutionCoeff a u m‖ ^ (2 : ℕ)) +
              ‖diskBlaschkeConvolutionCoeff a u (N + 1)‖ ^ (2 : ℕ)) +
            (1 - ‖a‖ ^ (2 : ℕ)) *
              ‖blaschkeConvolutionTail a u (N + 1)‖ ^ (2 : ℕ) := by
              rw [Finset.sum_range_succ]
        _ =
          (∑ m ∈ Finset.range (N + 1),
              ‖diskBlaschkeConvolutionCoeff a u m‖ ^ (2 : ℕ)) +
            (‖u (N + 1)‖ ^ (2 : ℕ) +
              (1 - ‖a‖ ^ (2 : ℕ)) *
                ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ)) := by
              have hstep := diskBlaschkeConvolutionCoeff_energy_step a u N
              dsimp at hstep
              nlinarith [hstep]
        _ =
          ((∑ m ∈ Finset.range (N + 1),
              ‖diskBlaschkeConvolutionCoeff a u m‖ ^ (2 : ℕ)) +
              (1 - ‖a‖ ^ (2 : ℕ)) *
                ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ)) +
            ‖u (N + 1)‖ ^ (2 : ℕ) := by
              ring
        _ =
          (∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ)) +
            ‖u (N + 1)‖ ^ (2 : ℕ) := by
              rw [ih]
        _ =
          ∑ m ∈ Finset.range (N + 1 + 1), ‖u m‖ ^ (2 : ℕ) := by
              conv_rhs => rw [Finset.sum_range_succ]

/--
For `|a| ≤ 1`, every finite initial segment of the Blaschke-updated
coefficient sequence has no larger squared norm than the matching segment of
the input sequence.
-/
lemma diskBlaschkeConvolutionCoeff_partial_norm_le
    {a : ℂ} (ha : ‖a‖ ≤ 1) (u : ℕ → ℂ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1),
        ‖diskBlaschkeConvolutionCoeff a u m‖ ^ (2 : ℕ)) ≤
      ∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ) := by
  have henergy := diskBlaschkeConvolutionCoeff_partial_energy a u N
  dsimp at henergy
  have hsq_le : ‖a‖ ^ (2 : ℕ) ≤ 1 := by
    have hmul := mul_le_mul ha ha (norm_nonneg a) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hr : 0 ≤ 1 - ‖a‖ ^ (2 : ℕ) := by nlinarith
  have htail_nonneg :
      0 ≤ (1 - ‖a‖ ^ (2 : ℕ)) *
        ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ) := by
    exact mul_nonneg hr (sq_nonneg _)
  nlinarith

/--
The same finite telescoping identity, written directly for the Cauchy
convolution by the one-factor Blaschke coefficient sequence.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_partial_energy
    (a : ℂ) (u : ℕ → ℂ) (N : ℕ) :
    let r : ℝ := 1 - ‖a‖ ^ (2 : ℕ)
    (∑ m ∈ Finset.range (N + 1),
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ)) +
        r * ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ) =
      ∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ) := by
  simpa [sequenceConvolution_diskBlaschkeFactorCoeff_eq_diskBlaschkeConvolutionCoeff a u]
    using diskBlaschkeConvolutionCoeff_partial_energy a u N

/--
For `|a| ≤ 1`, finite initial segments are contractive after direct Cauchy
convolution by the one-factor Blaschke coefficient sequence.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_partial_norm_le
    {a : ℂ} (ha : ‖a‖ ≤ 1) (u : ℕ → ℂ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1),
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ)) ≤
      ∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ) := by
  simpa [sequenceConvolution_diskBlaschkeFactorCoeff_eq_diskBlaschkeConvolutionCoeff a u]
    using diskBlaschkeConvolutionCoeff_partial_norm_le ha u N

/--
The Blaschke tail term in the finite energy identity is bounded by the input
`ℓ²` squared norm.  This is the estimate used to control tails of truncation
errors.
-/
lemma blaschkeConvolutionTail_mul_norm_sq_le_tsum
    (a : ℂ) {u : ℕ → ℂ}
    (hu : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ)) (N : ℕ) :
    (1 - ‖a‖ ^ (2 : ℕ)) * ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ) ≤
      ∑' n : ℕ, ‖u n‖ ^ (2 : ℕ) := by
  have henergy := sequenceConvolution_diskBlaschkeFactorCoeff_partial_energy a u N
  dsimp at henergy
  have hsum_nonneg :
      0 ≤ ∑ m ∈ Finset.range (N + 1),
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ) := by
    exact Finset.sum_nonneg fun m hm => sq_nonneg _
  have hpartial_le :
      (∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ)) ≤
        ∑' n : ℕ, ‖u n‖ ^ (2 : ℕ) :=
    hu.sum_le_tsum (Finset.range (N + 1)) (fun m hm => sq_nonneg ‖u m‖)
  nlinarith

/-- The finite truncation of a coefficient sequence to indices `< K`. -/
def sequenceTruncation (u : ℕ → ℂ) (K : ℕ) : ℕ → ℂ :=
  fun n => if n < K then u n else 0

@[simp]
lemma sequenceTruncation_apply_of_lt (u : ℕ → ℂ) {K n : ℕ} (hn : n < K) :
    sequenceTruncation u K n = u n := by
  simp [sequenceTruncation, hn]

@[simp]
lemma sequenceTruncation_apply_of_le (u : ℕ → ℂ) {K n : ℕ} (hn : K ≤ n) :
    sequenceTruncation u K n = 0 := by
  simp [sequenceTruncation, not_lt.mpr hn]

/-- A truncation is eventually zero, hence finitely supported. -/
lemma sequenceTruncation_eventually_zero (u : ℕ → ℂ) (K : ℕ) :
    ∀ n, K ≤ n → sequenceTruncation u K n = 0 := by
  intro n hn
  exact sequenceTruncation_apply_of_le u hn

/-- Split a Blaschke tail into the tail of a truncation and the tail of the truncation error. -/
lemma blaschkeConvolutionTail_eq_truncation_add_error
    (a : ℂ) (u : ℕ → ℂ) (K N : ℕ) :
    blaschkeConvolutionTail a u N =
      blaschkeConvolutionTail a (sequenceTruncation u K) N +
        blaschkeConvolutionTail a (fun n => u n - sequenceTruncation u K n) N := by
  have hsub := blaschkeConvolutionTail_sub_right a u (sequenceTruncation u K) N
  rw [hsub]
  ring

/-- Truncation does not increase pointwise norms. -/
lemma norm_sequenceTruncation_le (u : ℕ → ℂ) (K n : ℕ) :
    ‖sequenceTruncation u K n‖ ≤ ‖u n‖ := by
  by_cases hn : n < K
  · simp [sequenceTruncation, hn]
  · simp [sequenceTruncation, hn, norm_nonneg]

/-- Truncating a Hardy `ℓ²` coefficient sequence keeps it in Hardy `ℓ²`. -/
lemma sequenceTruncation_memℓp
    {u : ℕ → ℂ} (hu : Memℓp u (2 : ℝ≥0∞)) (K : ℕ) :
    Memℓp (sequenceTruncation u K) (2 : ℝ≥0∞) := by
  apply memℓp_gen
  have htwo : 0 < ENNReal.toReal (2 : ℝ≥0∞) := by norm_num
  have hs :
      Summable fun n : ℕ => ‖u n‖ ^ ENNReal.toReal (2 : ℝ≥0∞) :=
    hu.summable htwo
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hs
  intro n
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_sequenceTruncation_le u K n)
    (by norm_num)

/-- The truncation error of a Hardy `ℓ²` coefficient sequence is again in Hardy `ℓ²`. -/
lemma sequenceTruncation_error_memℓp
    {u : ℕ → ℂ} (hu : Memℓp u (2 : ℝ≥0∞)) (K : ℕ) :
    Memℓp (fun n => u n - sequenceTruncation u K n) (2 : ℝ≥0∞) :=
  hu.sub (sequenceTruncation_memℓp hu K)

/-- The truncation error has summable squared norm whenever the original sequence does. -/
lemma sequenceTruncation_error_summable_norm_sq
    {u : ℕ → ℂ} (hu : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ)) (K : ℕ) :
    Summable fun n : ℕ => ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hu
  intro n
  by_cases hn : n < K
  · simp [sequenceTruncation, hn]
  · simp [sequenceTruncation, hn]

/-- The squared norm of the truncation error is exactly the tail squared norm. -/
lemma sequenceTruncation_error_norm_sq_tsum_eq_nat_add
    {u : ℕ → ℂ} (hu : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ)) (K : ℕ) :
    (∑' n : ℕ, ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ)) =
      ∑' n : ℕ, ‖u (n + K)‖ ^ (2 : ℕ) := by
  have herr_summ := sequenceTruncation_error_summable_norm_sq hu K
  have hsplit := herr_summ.sum_add_tsum_nat_add K
  have hfirst :
      (∑ i ∈ Finset.range K, ‖u i - sequenceTruncation u K i‖ ^ (2 : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi_lt : i < K := Finset.mem_range.mp hi
    simp [sequenceTruncation, hi_lt]
  have htail :
      (∑' i : ℕ, ‖u (i + K) - sequenceTruncation u K (i + K)‖ ^ (2 : ℕ)) =
        ∑' i : ℕ, ‖u (i + K)‖ ^ (2 : ℕ) := by
    apply tsum_congr
    intro i
    have hle : K ≤ i + K := by omega
    simp [sequenceTruncation, not_lt.mpr hle]
  linarith

/-- The truncation error tends to zero in squared `ℓ²` norm. -/
lemma sequenceTruncation_error_norm_sq_tsum_tendsto_zero
    {u : ℕ → ℂ} (hu : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ)) :
    Filter.Tendsto
      (fun K : ℕ => ∑' n : ℕ, ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
  have htail :
      Filter.Tendsto (fun K : ℕ => ∑' n : ℕ, ‖u (n + K)‖ ^ (2 : ℕ))
        Filter.atTop (nhds 0) := by
    exact tendsto_sum_nat_add (fun n : ℕ => ‖u n‖ ^ (2 : ℕ))
  convert! htail using 1
  ext K
  exact sequenceTruncation_error_norm_sq_tsum_eq_nat_add hu K

/-- The truncation error tends to zero for Hardy `ℓ²` coefficient sequences. -/
lemma sequenceTruncation_error_norm_sq_tsum_tendsto_zero_of_memℓp
    {u : ℕ → ℂ} (hu : Memℓp u (2 : ℝ≥0∞)) :
    Filter.Tendsto
      (fun K : ℕ => ∑' n : ℕ, ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
  have hu_summ : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ) := by
    convert! hu.summable (by norm_num) using 1
    ext n
    norm_num
  exact sequenceTruncation_error_norm_sq_tsum_tendsto_zero hu_summ

/--
The Blaschke tail of a truncation error is controlled by the `ℓ²` tail of the
original sequence.
-/
lemma blaschkeConvolutionTail_truncation_error_mul_norm_sq_le_tsum
    (a : ℂ) {u : ℕ → ℂ}
    (hu : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ)) (K N : ℕ) :
    (1 - ‖a‖ ^ (2 : ℕ)) *
        ‖blaschkeConvolutionTail a (fun n => u n - sequenceTruncation u K n) N‖ ^
          (2 : ℕ) ≤
      ∑' n : ℕ, ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ) :=
  blaschkeConvolutionTail_mul_norm_sq_le_tsum a
    (sequenceTruncation_error_summable_norm_sq hu K) N

/--
The squared Blaschke tail of an arbitrary sequence is bounded by the squared
tails of a truncation and of the corresponding truncation error.
-/
lemma blaschkeConvolutionTail_norm_sq_le_truncation_add_error
    (a : ℂ) (u : ℕ → ℂ) (K N : ℕ) :
    ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ) ≤
      2 * ‖blaschkeConvolutionTail a (sequenceTruncation u K) N‖ ^ (2 : ℕ) +
        2 *
          ‖blaschkeConvolutionTail a (fun n => u n - sequenceTruncation u K n) N‖ ^
            (2 : ℕ) := by
  rw [blaschkeConvolutionTail_eq_truncation_add_error a u K N]
  exact complex_norm_add_sq_le_two _ _

/--
After multiplying by the positive defect `1 - ‖a‖²`, the Blaschke tail of an
arbitrary `ℓ²` sequence is controlled by a finite truncation tail plus the
global squared `ℓ²` truncation error.
-/
lemma blaschkeConvolutionTail_mul_norm_sq_le_truncation_add_error_bound
    {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → ℂ}
    (hu : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ)) (K N : ℕ) :
    (1 - ‖a‖ ^ (2 : ℕ)) * ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ) ≤
      2 * ((1 - ‖a‖ ^ (2 : ℕ)) *
          ‖blaschkeConvolutionTail a (sequenceTruncation u K) N‖ ^ (2 : ℕ)) +
        2 *
          (∑' n : ℕ, ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ)) := by
  let r : ℝ := 1 - ‖a‖ ^ (2 : ℕ)
  let A : ℝ := ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ)
  let B : ℝ := ‖blaschkeConvolutionTail a (sequenceTruncation u K) N‖ ^ (2 : ℕ)
  let C : ℝ :=
    ‖blaschkeConvolutionTail a (fun n => u n - sequenceTruncation u K n) N‖ ^
      (2 : ℕ)
  let E : ℝ := ∑' n : ℕ, ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ)
  have hr_nonneg : 0 ≤ r := by
    have ha_sq_lt : ‖a‖ ^ (2 : ℕ) < 1 := by
      have hnonneg : 0 ≤ ‖a‖ := norm_nonneg a
      nlinarith [sq_nonneg ‖a‖]
    dsimp [r]
    nlinarith
  have hsplit : A ≤ 2 * B + 2 * C := by
    dsimp [A, B, C]
    exact blaschkeConvolutionTail_norm_sq_le_truncation_add_error a u K N
  have hmul : r * A ≤ r * (2 * B + 2 * C) :=
    mul_le_mul_of_nonneg_left hsplit hr_nonneg
  have herr : r * C ≤ E := by
    dsimp [r, C, E]
    exact blaschkeConvolutionTail_truncation_error_mul_norm_sq_le_tsum a hu K N
  have hrewrite : r * (2 * B + 2 * C) = 2 * (r * B) + 2 * (r * C) := by
    ring
  calc
    r * A ≤ r * (2 * B + 2 * C) := hmul
    _ = 2 * (r * B) + 2 * (r * C) := hrewrite
    _ ≤ 2 * (r * B) + 2 * E := by nlinarith

lemma blaschkeConvolutionTail_truncation_mul_norm_sq_tendsto_zero
    {a : ℂ} (ha : ‖a‖ < 1) (u : ℕ → ℂ) (K : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (1 - ‖a‖ ^ (2 : ℕ)) *
          ‖blaschkeConvolutionTail a (sequenceTruncation u K) N‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
  have htail :=
    blaschkeConvolutionTail_norm_sq_tendsto_zero_of_eventually_zero ha
      (sequenceTruncation u K) (sequenceTruncation_eventually_zero u K)
  have hmul :
      Filter.Tendsto
        (fun N : ℕ =>
          (1 - ‖a‖ ^ (2 : ℕ)) *
            ‖blaschkeConvolutionTail a (sequenceTruncation u K) N‖ ^ (2 : ℕ))
        Filter.atTop (nhds ((1 - ‖a‖ ^ (2 : ℕ)) * 0)) :=
    tendsto_const_nhds.mul htail
  simpa using hmul

lemma blaschkeConvolutionTail_mul_norm_sq_tendsto_zero
    {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → ℂ}
    (hu : Summable fun n : ℕ => ‖u n‖ ^ (2 : ℕ)) :
    Filter.Tendsto
      (fun N : ℕ =>
        (1 - ‖a‖ ^ (2 : ℕ)) * ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
  have hr_nonneg : 0 ≤ 1 - ‖a‖ ^ (2 : ℕ) := by
    have ha_sq_lt : ‖a‖ ^ (2 : ℕ) < 1 := by
      have hnonneg : 0 ≤ ‖a‖ := norm_nonneg a
      nlinarith [sq_nonneg ‖a‖]
    nlinarith
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro δ hδ
    exact Filter.Eventually.of_forall (fun N => by
      have hnonneg :
          0 ≤ (1 - ‖a‖ ^ (2 : ℕ)) * ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ) :=
        mul_nonneg hr_nonneg (sq_nonneg _)
      nlinarith)
  · intro δ hδ
    have hδ4 : 0 < δ / 4 := by positivity
    have herror :=
      sequenceTruncation_error_norm_sq_tsum_tendsto_zero hu
    have herror_eventually :
        ∀ᶠ K : ℕ in Filter.atTop,
          (∑' n : ℕ, ‖u n - sequenceTruncation u K n‖ ^ (2 : ℕ)) < δ / 4 :=
      (tendsto_order.1 herror).2 (δ / 4) hδ4
    rw [Filter.eventually_atTop] at herror_eventually
    rcases herror_eventually with ⟨K, hK⟩
    have htrunc :=
      blaschkeConvolutionTail_truncation_mul_norm_sq_tendsto_zero ha u K
    have htrunc_eventually :
        ∀ᶠ N : ℕ in Filter.atTop,
          (1 - ‖a‖ ^ (2 : ℕ)) *
            ‖blaschkeConvolutionTail a (sequenceTruncation u K) N‖ ^ (2 : ℕ) <
              δ / 4 :=
      (tendsto_order.1 htrunc).2 (δ / 4) hδ4
    rw [Filter.eventually_atTop] at htrunc_eventually
    rcases htrunc_eventually with ⟨N0, hN0⟩
    refine Filter.eventually_atTop.2 ⟨N0, ?_⟩
    intro N hN
    have hbound :=
      blaschkeConvolutionTail_mul_norm_sq_le_truncation_add_error_bound
        ha hu K N
    have hB := hN0 N hN
    have hE := hK K le_rfl
    nlinarith

/-- A sequence that is eventually zero has summable squared norms. -/
lemma summable_norm_sq_of_eventually_zero
    (u : ℕ → ℂ) {K : ℕ} (hu : ∀ n, K ≤ n → u n = 0) :
    Summable fun m : ℕ => ‖u m‖ ^ (2 : ℕ) := by
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  exact (Set.finite_Iio K).subset (by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_Iio]
    by_contra hlt
    have hK : K ≤ n := by omega
    simp [hu n hK] at hn)

/--
For an eventually-zero input, the finite partial sums of the Blaschke-updated
sequence converge to the original squared-norm sum.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_partial_sum_tendsto_tsum_of_eventually_zero
    {a : ℂ} (ha : ‖a‖ < 1) (u : ℕ → ℂ) {K : ℕ}
    (hu : ∀ n, K ≤ n → u n = 0) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ m ∈ Finset.range (N + 1),
          ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ))
      Filter.atTop (nhds (∑' m : ℕ, ‖u m‖ ^ (2 : ℕ))) := by
  have hsu_summ := summable_norm_sq_of_eventually_zero u hu
  have hsu :
      Filter.Tendsto
        (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ))
        Filter.atTop (nhds (∑' m : ℕ, ‖u m‖ ^ (2 : ℕ))) :=
    hsu_summ.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have htail0 :=
    blaschkeConvolutionTail_norm_sq_tendsto_zero_of_eventually_zero ha u hu
  have htail :
      Filter.Tendsto
        (fun N : ℕ =>
          (1 - ‖a‖ ^ (2 : ℕ)) *
            ‖blaschkeConvolutionTail a u N‖ ^ (2 : ℕ))
        Filter.atTop (nhds ((1 - ‖a‖ ^ (2 : ℕ)) * 0)) :=
    tendsto_const_nhds.mul htail0
  have hdiff := hsu.sub htail
  convert! hdiff using 1
  · ext N
    have henergy := sequenceConvolution_diskBlaschkeFactorCoeff_partial_energy a u N
    dsimp at henergy
    nlinarith
  · simp

/--
For an eventually-zero input, Cauchy convolution by one disk Blaschke factor
has the desired squared-norm `HasSum`.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_hasSum_norm_sq_of_eventually_zero
    {a : ℂ} (ha : ‖a‖ < 1) (u : ℕ → ℂ) {K : ℕ}
    (hu : ∀ n, K ≤ n → u n = 0) :
    HasSum
      (fun m : ℕ =>
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ))
      (∑' m : ℕ, ‖u m‖ ^ (2 : ℕ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun m =>
    sq_nonneg ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖)]
  have hplus :=
    sequenceConvolution_diskBlaschkeFactorCoeff_partial_sum_tendsto_tsum_of_eventually_zero
      ha u hu
  have hsub : Filter.Tendsto (fun N : ℕ => N - 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b + 1, by intro a ha; omega⟩
  have hcomp := hplus.comp hsub
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  simp [Nat.sub_add_cancel hN]

/--
The one-step Blaschke multiplier isometry is fully proved for eventually-zero
coefficient sequences.
-/
theorem sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_eq_of_eventually_zero
    {a : ℂ} (ha : ‖a‖ < 1) (u : ℕ → ℂ) {K : ℕ}
    (hu : ∀ n, K ≤ n → u n = 0) :
    (∑' m : ℕ,
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ)) =
      ∑' m : ℕ, ‖u m‖ ^ (2 : ℕ) := by
  exact
    (sequenceConvolution_diskBlaschkeFactorCoeff_hasSum_norm_sq_of_eventually_zero
      ha u hu).tsum_eq

/--
The one-step Blaschke isometry is available for every finite truncation of an
arbitrary input sequence.
-/
theorem sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_eq_truncation
    {a : ℂ} (ha : ‖a‖ < 1) (u : ℕ → ℂ) (K : ℕ) :
    (∑' m : ℕ,
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) (sequenceTruncation u K) m‖ ^
          (2 : ℕ)) =
      ∑' m : ℕ, ‖sequenceTruncation u K m‖ ^ (2 : ℕ) :=
  sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_eq_of_eventually_zero
    ha (sequenceTruncation u K) (sequenceTruncation_eventually_zero u K)

/--
The one-factor Blaschke coefficient multiplier is contractive at the level of
summability: if the input has summable squared norm, so does the output.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_summable_norm_sq
    {a : ℂ} (ha : ‖a‖ ≤ 1) {u : ℕ → ℂ}
    (hu : Summable fun m : ℕ => ‖u m‖ ^ (2 : ℕ)) :
    Summable fun m : ℕ =>
      ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ) := by
  apply summable_of_sum_range_le (c := ∑' m : ℕ, ‖u m‖ ^ (2 : ℕ))
    (fun m => sq_nonneg ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖)
  intro n
  cases n with
  | zero =>
      simp
      exact hu.hasSum.nonneg fun m => sq_nonneg ‖u m‖
  | succ N =>
      exact (sequenceConvolution_diskBlaschkeFactorCoeff_partial_norm_le ha u N).trans
        (hu.sum_le_tsum (Finset.range (N + 1)) (fun m hm => sq_nonneg ‖u m‖))

/--
The one-factor Blaschke coefficient multiplier is a contraction for squared
`H²` norms.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_le
    {a : ℂ} (ha : ‖a‖ ≤ 1) {u : ℕ → ℂ}
    (hu : Summable fun m : ℕ => ‖u m‖ ^ (2 : ℕ)) :
    (∑' m : ℕ,
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ)) ≤
      ∑' m : ℕ, ‖u m‖ ^ (2 : ℕ) := by
  apply Real.tsum_le_of_sum_range_le
    (fun m => sq_nonneg ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖)
  intro n
  cases n with
  | zero =>
      simp
      exact hu.hasSum.nonneg fun m => sq_nonneg ‖u m‖
  | succ N =>
      exact (sequenceConvolution_diskBlaschkeFactorCoeff_partial_norm_le ha u N).trans
        (hu.sum_le_tsum (Finset.range (N + 1)) (fun m hm => sq_nonneg ‖u m‖))

/--
The contraction estimate in difference form.  This is the continuity estimate
needed for passing from finite truncations to an arbitrary `ℓ²` sequence.
-/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_sub_norm_sq_tsum_le
    {a : ℂ} (ha : ‖a‖ ≤ 1) {u v : ℕ → ℂ}
    (huv : Summable fun m : ℕ => ‖u m - v m‖ ^ (2 : ℕ)) :
    (∑' m : ℕ,
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m -
          sequenceConvolution (diskBlaschkeFactorCoeff a) v m‖ ^ (2 : ℕ)) ≤
      ∑' m : ℕ, ‖u m - v m‖ ^ (2 : ℕ) := by
  have hle := sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_le
    (a := a) ha (u := fun n => u n - v n) huv
  simpa [sequenceConvolution_sub_right] using hle

/-- The one-factor Blaschke coefficient multiplier sends Hardy `ℓ²` sequences to `ℓ²`. -/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_memℓp
    {a : ℂ} (ha : ‖a‖ ≤ 1) {u : ℕ → ℂ}
    (hu : Memℓp u (2 : ℝ≥0∞)) :
    Memℓp (sequenceConvolution (diskBlaschkeFactorCoeff a) u) (2 : ℝ≥0∞) := by
  have hu_summ : Summable fun m : ℕ => ‖u m‖ ^ (2 : ℕ) := by
    convert! hu.summable (by norm_num) using 1
    ext m
    norm_num
  apply memℓp_gen
  convert! sequenceConvolution_diskBlaschkeFactorCoeff_summable_norm_sq ha hu_summ using 1
  ext m
  norm_num

/-- The contraction estimate, stated directly for Hardy `ℓ²` input sequences. -/
lemma sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_le_of_memℓp
    {a : ℂ} (ha : ‖a‖ ≤ 1) {u : ℕ → ℂ}
    (hu : Memℓp u (2 : ℝ≥0∞)) :
    (∑' m : ℕ,
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ)) ≤
      ∑' m : ℕ, ‖u m‖ ^ (2 : ℕ) := by
  have hu_summ : Summable fun m : ℕ => ‖u m‖ ^ (2 : ℕ) := by
    convert! hu.summable (by norm_num) using 1
    ext m
    norm_num
  exact sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_le ha hu_summ

/--
Multiplying coefficient sequences by a single disk Blaschke factor preserves
the `H²` norm.

The proof passes the finite partial energy identity to the limit.  The only
boundary term is the Blaschke tail, and the truncation argument above shows
that its defect-weighted square tends to zero for every `ℓ²` input.
-/
theorem sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_eq
    {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → ℂ}
    (hu : Memℓp u (2 : ℝ≥0∞)) :
    (∑' m : ℕ, ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ)) =
      ∑' m : ℕ, ‖u m‖ ^ (2 : ℕ) := by
  have ha_le : ‖a‖ ≤ 1 := le_of_lt ha
  have hu_summ : Summable fun m : ℕ => ‖u m‖ ^ (2 : ℕ) := by
    convert! hu.summable (by norm_num) using 1
    ext m
    norm_num
  have hconv_summ :
      Summable fun m : ℕ =>
        ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ) :=
    sequenceConvolution_diskBlaschkeFactorCoeff_summable_norm_sq ha_le hu_summ
  have hu_tendsto :
      Filter.Tendsto
        (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), ‖u m‖ ^ (2 : ℕ))
        Filter.atTop (nhds (∑' m : ℕ, ‖u m‖ ^ (2 : ℕ))) :=
    hu_summ.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hconv_tendsto :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ m ∈ Finset.range (N + 1),
            ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ))
        Filter.atTop
        (nhds
          (∑' m : ℕ,
            ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ))) :=
    hconv_summ.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have htail := blaschkeConvolutionTail_mul_norm_sq_tendsto_zero ha hu_summ
  have hconv_tendsto_u :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ m ∈ Finset.range (N + 1),
            ‖sequenceConvolution (diskBlaschkeFactorCoeff a) u m‖ ^ (2 : ℕ))
        Filter.atTop (nhds (∑' m : ℕ, ‖u m‖ ^ (2 : ℕ))) := by
    have hdiff := hu_tendsto.sub htail
    convert! hdiff using 1
    · ext N
      have henergy := sequenceConvolution_diskBlaschkeFactorCoeff_partial_energy a u N
      dsimp at henergy
      nlinarith
    · simp
  exact tendsto_nhds_unique hconv_tendsto hconv_tendsto_u

/--
Coefficient sequence for a finite product of disk Blaschke factors, built by
iterated Cauchy convolution over a list of zeros.
-/
def finiteBlaschkeProductCoeffList : List ℂ → ℕ → ℂ
  | [] => fun m => if m = 0 then 1 else 0
  | a :: rest => sequenceConvolution (diskBlaschkeFactorCoeff a)
      (finiteBlaschkeProductCoeffList rest)

/-- The empty finite product has constant coefficient `1`. -/
lemma finiteBlaschkeProductCoeffList_nil_zero :
    finiteBlaschkeProductCoeffList [] 0 = 1 := by
  simp [finiteBlaschkeProductCoeffList]

/-- The zeroth coefficient after adding one Blaschke factor. -/
lemma finiteBlaschkeProductCoeffList_cons_zero (a : ℂ) (rest : List ℂ) :
    finiteBlaschkeProductCoeffList (a :: rest) 0 =
      (-a) * finiteBlaschkeProductCoeffList rest 0 := by
  simp [finiteBlaschkeProductCoeffList, sequenceConvolution, diskBlaschkeFactorCoeff]

/-- The zeroth coefficient of the list product is the product of the zeroth coefficients. -/
lemma finiteBlaschkeProductCoeffList_zero (as : List ℂ) :
    finiteBlaschkeProductCoeffList as 0 = (as.map fun a => -a).prod := by
  induction as with
  | nil => simp [finiteBlaschkeProductCoeffList]
  | cons a rest ih =>
      rw [finiteBlaschkeProductCoeffList_cons_zero, ih]
      simp

/--
The coefficient sequence for a finite Blaschke product is absolutely summable.

This is stronger than the `ℓ²` membership needed for Hardy space, and it is
stable under the finite Cauchy products used here.
-/
lemma finiteBlaschkeProductCoeffList_summable_norm
    (as : List ℂ) (has : ∀ a ∈ as, ‖a‖ < 1) :
    Summable fun m : ℕ => ‖finiteBlaschkeProductCoeffList as m‖ := by
  induction as with
  | nil =>
      apply summable_of_hasFiniteSupport
      rw [Function.HasFiniteSupport]
      exact (Set.finite_singleton 0).subset (by
        intro m hm
        by_contra hnot
        have hmne : m ≠ 0 := by simpa using hnot
        have hz : ‖finiteBlaschkeProductCoeffList [] m‖ = 0 := by
          simp [finiteBlaschkeProductCoeffList, hmne]
        exact hm hz)
  | cons a rest ih =>
      have ha : ‖a‖ < 1 := has a (by simp)
      have hrest : ∀ b ∈ rest, ‖b‖ < 1 := by
        intro b hb
        exact has b (by simp [hb])
      have hf := diskBlaschkeFactorCoeff_summable_norm ha
      have hg := ih hrest
      have hconv := summable_norm_sum_mul_range_of_summable_norm
        (R := ℂ)
        (f := diskBlaschkeFactorCoeff a)
        (g := finiteBlaschkeProductCoeffList rest)
        hf hg
      exact hconv.congr (fun m => by
        congr 1)

/-- The finite list-product coefficient sequence belongs to Hardy `ℓ²`. -/
lemma finiteBlaschkeProductCoeffList_memℓp
    (as : List ℂ) (has : ∀ a ∈ as, ‖a‖ < 1) :
    Memℓp (finiteBlaschkeProductCoeffList as) (2 : ℝ≥0∞) := by
  have h1 : Memℓp (finiteBlaschkeProductCoeffList as) (1 : ℝ≥0∞) := by
    apply memℓp_gen
    convert! finiteBlaschkeProductCoeffList_summable_norm as has using 1
    ext m
    norm_num
  exact h1.of_exponent_ge (by norm_num)

/--
The finite list-product coefficient sequence has Hardy `H²` norm one.

The proof is an induction over the list, using the one-step Blaschke
isometry calculation for Cauchy convolution.
-/
lemma finiteBlaschkeProductCoeffList_norm_sq_tsum_eq_one
    (as : List ℂ) (has : ∀ a ∈ as, ‖a‖ < 1) :
    (∑' m : ℕ, ‖finiteBlaschkeProductCoeffList as m‖ ^ (2 : ℕ)) = 1 := by
  induction as with
  | nil =>
      rw [← (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq]
      apply tsum_congr
      intro m
      by_cases hm : m = 0 <;> simp [finiteBlaschkeProductCoeffList, hm]
  | cons a rest ih =>
      have ha : ‖a‖ < 1 := has a (by simp)
      have hrest : ∀ b ∈ rest, ‖b‖ < 1 := by
        intro b hb
        exact has b (by simp [hb])
      calc
        (∑' m : ℕ, ‖finiteBlaschkeProductCoeffList (a :: rest) m‖ ^ (2 : ℕ))
            =
          ∑' m : ℕ, ‖finiteBlaschkeProductCoeffList rest m‖ ^ (2 : ℕ) := by
            rw [finiteBlaschkeProductCoeffList]
            exact sequenceConvolution_diskBlaschkeFactorCoeff_norm_sq_tsum_eq
              ha (finiteBlaschkeProductCoeffList_memℓp rest hrest)
        _ = 1 := ih hrest

/--
The evaluated coefficient series for a finite Blaschke product is absolutely
summable inside the unit disk.
-/
lemma finiteBlaschkeProductCoeffList_eval_summable_norm
    (as : List ℂ) (has : ∀ a ∈ as, ‖a‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable fun m : ℕ => ‖finiteBlaschkeProductCoeffList as m * w ^ m‖ := by
  induction as with
  | nil =>
      apply summable_of_hasFiniteSupport
      rw [Function.HasFiniteSupport]
      exact (Set.finite_singleton 0).subset (by
        intro m hm
        by_contra hnot
        have hmne : m ≠ 0 := by simpa using hnot
        have hz : ‖finiteBlaschkeProductCoeffList [] m * w ^ m‖ = 0 := by
          simp [finiteBlaschkeProductCoeffList, hmne]
        exact hm hz)
  | cons a rest ih =>
      have ha : ‖a‖ < 1 := has a (by simp)
      have hrest : ∀ b ∈ rest, ‖b‖ < 1 := by
        intro b hb
        exact has b (by simp [hb])
      have hf := diskBlaschkeFactorCoeff_eval_summable_norm ha hw
      have hg := ih hrest
      have hconv := summable_norm_sum_mul_range_of_summable_norm
        (R := ℂ)
        (f := fun m : ℕ => diskBlaschkeFactorCoeff a m * w ^ m)
        (g := fun m : ℕ => finiteBlaschkeProductCoeffList rest m * w ^ m)
        hf hg
      exact hconv.congr (fun m => by
        congr 1
        rw [finiteBlaschkeProductCoeffList, sequenceConvolution, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hk_le : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hkm : k + (m - k) = m := Nat.add_sub_of_le hk_le
        calc
          (fun m => diskBlaschkeFactorCoeff a m * w ^ m) k *
              (fun m => finiteBlaschkeProductCoeffList rest m * w ^ m) (m - k)
              = (diskBlaschkeFactorCoeff a k * w ^ k) *
                  (finiteBlaschkeProductCoeffList rest (m - k) * w ^ (m - k)) := rfl
          _ = diskBlaschkeFactorCoeff a k * finiteBlaschkeProductCoeffList rest (m - k) *
                  (w ^ k * w ^ (m - k)) := by ring
          _ = diskBlaschkeFactorCoeff a k * finiteBlaschkeProductCoeffList rest (m - k) *
                  w ^ m := by rw [← pow_add, hkm])

/--
The coefficient series of a finite Blaschke product expands to the finite
product of the one-factor Blaschke functions.
-/
lemma finiteBlaschkeProductCoeffList_hasSum
    (as : List ℂ) (has : ∀ a ∈ as, ‖a‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun m : ℕ => finiteBlaschkeProductCoeffList as m * w ^ m)
      ((as.map fun a => diskBlaschkeFactor a w).prod) := by
  induction as with
  | nil =>
      convert! hasSum_ite_eq 0 (1 : ℂ) using 1
      ext m
      by_cases hm : m = 0 <;> simp [finiteBlaschkeProductCoeffList, hm]
  | cons a rest ih =>
      have ha : ‖a‖ < 1 := has a (by simp)
      have hrest : ∀ b ∈ rest, ‖b‖ < 1 := by
        intro b hb
        exact has b (by simp [hb])
      have hf_norm := diskBlaschkeFactorCoeff_eval_summable_norm ha hw
      have hg_norm := finiteBlaschkeProductCoeffList_eval_summable_norm rest hrest hw
      have hfactor := diskBlaschkeFactorCoeff_hasSum ha hw
      have hrest_sum := ih hrest
      have hseq_norm := finiteBlaschkeProductCoeffList_eval_summable_norm (a :: rest) has hw
      have hseq :
          Summable fun m : ℕ => finiteBlaschkeProductCoeffList (a :: rest) m * w ^ m :=
        hseq_norm.of_norm
      refine hseq.hasSum_iff.2 ?_
      have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
        (R := ℂ)
        (f := fun m : ℕ => diskBlaschkeFactorCoeff a m * w ^ m)
        (g := fun m : ℕ => finiteBlaschkeProductCoeffList rest m * w ^ m)
        hf_norm hg_norm
      rw [hfactor.tsum_eq, hrest_sum.tsum_eq] at hcauchy
      have htsum_congr :
          (∑' n : ℕ,
              ∑ k ∈ Finset.range (n + 1),
                (fun m : ℕ => diskBlaschkeFactorCoeff a m * w ^ m) k *
                  (fun m : ℕ => finiteBlaschkeProductCoeffList rest m * w ^ m) (n - k))
            =
          ∑' n : ℕ, finiteBlaschkeProductCoeffList (a :: rest) n * w ^ n := by
        apply tsum_congr
        intro n
        rw [finiteBlaschkeProductCoeffList, sequenceConvolution, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hkn : k + (n - k) = n := Nat.add_sub_of_le hk_le
        calc
          (fun m : ℕ => diskBlaschkeFactorCoeff a m * w ^ m) k *
              (fun m : ℕ => finiteBlaschkeProductCoeffList rest m * w ^ m) (n - k)
              = (diskBlaschkeFactorCoeff a k * w ^ k) *
                  (finiteBlaschkeProductCoeffList rest (n - k) * w ^ (n - k)) := rfl
          _ = diskBlaschkeFactorCoeff a k * finiteBlaschkeProductCoeffList rest (n - k) *
                  (w ^ k * w ^ (n - k)) := by ring
          _ = diskBlaschkeFactorCoeff a k * finiteBlaschkeProductCoeffList rest (n - k) *
                  w ^ n := by rw [← pow_add, hkn]
      rw [htsum_congr] at hcauchy
      rw [← hcauchy]
      simp

/-- Coefficient sequence for the finite Blaschke product with indexed zeros. -/
def finiteBlaschkeProductCoeff {n : ℕ} (z : Fin n → ℂ) : ℕ → ℂ :=
  finiteBlaschkeProductCoeffList (List.ofFn z)

/-- The indexed finite Blaschke-product coefficient sequence is absolutely summable. -/
lemma finiteBlaschkeProductCoeff_summable_norm
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    Summable fun m : ℕ => ‖finiteBlaschkeProductCoeff z m‖ := by
  have hlist : ∀ a ∈ List.ofFn z, ‖a‖ < 1 := by
    intro a ha
    rw [List.mem_ofFn'] at ha
    rcases ha with ⟨i, rfl⟩
    exact hz i
  simpa [finiteBlaschkeProductCoeff] using
    finiteBlaschkeProductCoeffList_summable_norm (List.ofFn z) hlist

/-- The finite Blaschke-product coefficient sequence belongs to Hardy `ℓ²`. -/
lemma finiteBlaschkeProductCoeff_memℓp
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    Memℓp (finiteBlaschkeProductCoeff z) (2 : ℝ≥0∞) := by
  have h1 : Memℓp (finiteBlaschkeProductCoeff z) (1 : ℝ≥0∞) := by
    apply memℓp_gen
    convert! finiteBlaschkeProductCoeff_summable_norm z hz using 1
    ext m
    norm_num
  exact h1.of_exponent_ge (by norm_num)

/--
The finite Blaschke product coefficient sequence has Hardy `H²` norm one.

This is now proved from the list-level induction and the one-step Blaschke
isometry for Cauchy convolution.
-/
theorem finiteBlaschkeProductCoeff_norm_sq_tsum_eq_one
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    (∑' m : ℕ, ‖finiteBlaschkeProductCoeff z m‖ ^ (2 : ℕ)) = 1 := by
  have hlist : ∀ a ∈ List.ofFn z, ‖a‖ < 1 := by
    intro a ha
    rw [List.mem_ofFn'] at ha
    rcases ha with ⟨i, rfl⟩
    exact hz i
  simpa [finiteBlaschkeProductCoeff] using
    finiteBlaschkeProductCoeffList_norm_sq_tsum_eq_one (List.ofFn z) hlist

/-- The finite Blaschke coefficient norm identity is proved directly in degree `0`. -/
lemma finiteBlaschkeProductCoeff_norm_sq_tsum_eq_one_zero
    (z : Fin 0 → ℂ) :
    (∑' m : ℕ, ‖finiteBlaschkeProductCoeff z m‖ ^ (2 : ℕ)) = 1 := by
  rw [← (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq]
  apply tsum_congr
  intro m
  by_cases hm : m = 0 <;> simp [finiteBlaschkeProductCoeff, finiteBlaschkeProductCoeffList, hm]

/-- In degree `1`, the finite Blaschke coefficient sequence is the one-factor sequence. -/
lemma finiteBlaschkeProductCoeff_one_eq_diskBlaschkeFactorCoeff
    (z : Fin 1 → ℂ) :
    finiteBlaschkeProductCoeff z = diskBlaschkeFactorCoeff (z 0) := by
  funext m
  simp [finiteBlaschkeProductCoeff, finiteBlaschkeProductCoeffList,
    sequenceConvolution_right_unit]

/-- The finite Blaschke coefficient norm identity is proved directly in degree `1`. -/
lemma finiteBlaschkeProductCoeff_norm_sq_tsum_eq_one_one
    (z : Fin 1 → ℂ) (hz : ∀ i, ‖z i‖ < 1) :
    (∑' m : ℕ, ‖finiteBlaschkeProductCoeff z m‖ ^ (2 : ℕ)) = 1 := by
  rw [finiteBlaschkeProductCoeff_one_eq_diskBlaschkeFactorCoeff z]
  exact diskBlaschkeFactorCoeff_norm_sq_tsum (hz 0)

/-- The zeroth coefficient of the finite Blaschke product is `B(0) = Λ`. -/
lemma finiteBlaschkeProductCoeff_zero {n : ℕ} (z : Fin n → ℂ) :
    finiteBlaschkeProductCoeff z 0 = blaschkeLambda z := by
  dsimp [finiteBlaschkeProductCoeff]
  rw [finiteBlaschkeProductCoeffList_zero]
  rw [List.prod_map_neg, List.length_ofFn, List.prod_ofFn]
  simp [blaschkeLambda]

/-- The indexed finite Blaschke-product coefficient series expands to `B(w)`. -/
lemma finiteBlaschkeProductCoeff_hasSum
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun m : ℕ => finiteBlaschkeProductCoeff z m * w ^ m)
      (finiteBlaschkeProduct z w) := by
  have hlist : ∀ a ∈ List.ofFn z, ‖a‖ < 1 := by
    intro a ha
    rw [List.mem_ofFn'] at ha
    rcases ha with ⟨i, rfl⟩
    exact hz i
  simpa [finiteBlaschkeProductCoeff, finiteBlaschkeProduct, List.map_ofFn,
    List.prod_ofFn] using
    finiteBlaschkeProductCoeffList_hasSum (List.ofFn z) hlist hw

/--
Coefficient sequence for the defect function `1 - overline{B(0)} B`.

This is the candidate coefficient sequence for the remaining vector `G` in
PDF Lemma 2.
-/
def szegoKernelDefectCoeff {n : ℕ} (z : Fin n → ℂ) (m : ℕ) : ℂ :=
  (if m = 0 then 1 else 0) -
    (starRingEnd ℂ) (blaschkeLambda z) * finiteBlaschkeProductCoeff z m

/-- The constant coefficient of the defect sequence is the scalar defect. -/
lemma szegoKernelDefectCoeff_zero {n : ℕ} (z : Fin n → ℂ) :
    szegoKernelDefectCoeff z 0 = ((szegoKernelProductDefect z : ℝ) : ℂ) := by
  rw [szegoKernelDefectCoeff, finiteBlaschkeProductCoeff_zero]
  dsimp [szegoKernelProductDefect]
  rw [mul_comm ((starRingEnd ℂ) (blaschkeLambda z)) (blaschkeLambda z)]
  rw [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  simp [blaschkeLambda]

/-- The defect coefficient sequence belongs to Hardy `ℓ²`. -/
lemma szegoKernelDefectCoeff_memℓp
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    Memℓp (szegoKernelDefectCoeff z) (2 : ℝ≥0∞) := by
  have hdelta : Memℓp (fun m : ℕ => if m = 0 then (1 : ℂ) else 0) (2 : ℝ≥0∞) := by
    apply memℓp_gen
    apply summable_of_hasFiniteSupport
    rw [Function.HasFiniteSupport]
    exact (Set.finite_singleton 0).subset (by
      intro m hm
      by_contra hnot
      have hmne : m ≠ 0 := by simpa using hnot
      have hz : ‖(if m = 0 then (1 : ℂ) else 0)‖ ^ (2 : ℝ≥0∞).toReal = 0 := by
        simp [hmne]
      exact hm hz)
  have hB := finiteBlaschkeProductCoeff_memℓp z hz
  have hscaled :
      Memℓp
        (fun m : ℕ =>
          (starRingEnd ℂ) (blaschkeLambda z) * finiteBlaschkeProductCoeff z m)
        (2 : ℝ≥0∞) :=
    hB.const_mul ((starRingEnd ℂ) (blaschkeLambda z))
  convert! hdelta.sub hscaled using 1

/-- The concrete Hardy-space coefficient vector for `1 - overline{B(0)} B`. -/
def hardySzegoDefectVector
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ < 1) :
    lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞) :=
  ⟨szegoKernelDefectCoeff z, szegoKernelDefectCoeff_memℓp z hz⟩

/-- The `m`th coefficient of the concrete Blaschke-defect Hardy vector. -/
lemma hardySzegoDefectVector_apply
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ < 1) (m : ℕ) :
    hardySzegoDefectVector z hz m = szegoKernelDefectCoeff z m := rfl

/--
The conjugated coefficient vector for `1 - overline{B(0)} B`.

With mathlib's convention that complex inner products are conjugate-linear in
the first argument, this is the orientation that pairs with the concrete
Szego-kernel vector by evaluating the defect function at the roots.
-/
def hardySzegoDefectConjVector
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ < 1) :
    lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞) :=
  ⟨fun m : ℕ => (starRingEnd ℂ) (szegoKernelDefectCoeff z m), by
    apply memℓp_gen
    have hs := (szegoKernelDefectCoeff_memℓp z hz).summable (by norm_num)
    convert! hs using 1
    ext m
    simp⟩

/-- The `m`th coefficient of the conjugated Blaschke-defect Hardy vector. -/
lemma hardySzegoDefectConjVector_apply
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ < 1) (m : ℕ) :
    hardySzegoDefectConjVector z hz m =
      (starRingEnd ℂ) (szegoKernelDefectCoeff z m) := rfl

/-- The defect coefficient sequence expands to `1 - overline{B(0)} B(w)`. -/
lemma szegoKernelDefectCoeff_hasSum
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun m : ℕ => szegoKernelDefectCoeff z m * w ^ m)
      (szegoKernelDefectValue z w) := by
  have hconst : HasSum (fun m : ℕ => (if m = 0 then (1 : ℂ) else 0) * w ^ m) 1 := by
    convert! hasSum_ite_eq 0 (1 : ℂ) using 1
    ext m
    by_cases hm : m = 0 <;> simp [hm]
  have hB := finiteBlaschkeProductCoeff_hasSum z hz hw
  have hscaled :
      HasSum
        (fun m : ℕ =>
          (starRingEnd ℂ) (blaschkeLambda z) *
            (finiteBlaschkeProductCoeff z m * w ^ m))
        ((starRingEnd ℂ) (blaschkeLambda z) * finiteBlaschkeProduct z w) :=
    hB.mul_left ((starRingEnd ℂ) (blaschkeLambda z))
  have hdiff := hconst.sub hscaled
  convert! hdiff using 1
  ext m
  dsimp [szegoKernelDefectCoeff]
  ring

/-- The finite Blaschke product has the expected value at zero. -/
lemma finiteBlaschkeProduct_zero
    {n : ℕ} (z : Fin n → ℂ) :
    finiteBlaschkeProduct z 0 = blaschkeLambda z := by
  dsimp [finiteBlaschkeProduct, diskBlaschkeFactor, blaschkeLambda]
  simp
  rw [Finset.prod_neg]
  simp

/-- The finite Blaschke product vanishes at each listed zero. -/
lemma finiteBlaschkeProduct_at_root
    {n : ℕ} (z : Fin n → ℂ) (j : Fin n) :
    finiteBlaschkeProduct z (z j) = 0 := by
  dsimp [finiteBlaschkeProduct]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [diskBlaschkeFactor])

/-- The defect function `1 - \bar Λ B` takes value `1` at each listed zero. -/
lemma szegoKernelDefectValue_at_root
    {n : ℕ} (z : Fin n → ℂ) (j : Fin n) :
    szegoKernelDefectValue z (z j) = 1 := by
  rw [szegoKernelDefectValue, finiteBlaschkeProduct_at_root z j]
  ring

/--
Summing the defect power series at all listed roots gives `n`.

This is the coefficient-level version of the PDF fact
`Σ_j (1 - overline{B(0)} B(z_j)) = n`, since each `z_j` is a zero of `B`.
-/
lemma szegoKernelDefectCoeff_tsum_root_sum
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    (∑' m : ℕ,
        (∑ i : Fin n, z i ^ m) * szegoKernelDefectCoeff z m) = (n : ℂ) := by
  have hroot :
      ∀ i : Fin n,
        HasSum (fun m : ℕ => szegoKernelDefectCoeff z m * z i ^ m) 1 := by
    intro i
    simpa [szegoKernelDefectValue_at_root z i] using
      szegoKernelDefectCoeff_hasSum z hz (hz i)
  have htsum :
      (∑' m : ℕ,
          ∑ i : Fin n, szegoKernelDefectCoeff z m * z i ^ m) =
        ∑ i : Fin n, (1 : ℂ) := by
    rw [Summable.tsum_finsetSum
      (s := Finset.univ)
      (f := fun i : Fin n => fun m : ℕ => szegoKernelDefectCoeff z m * z i ^ m)]
    · apply Finset.sum_congr rfl
      intro i _hi
      exact (hroot i).tsum_eq
    · intro i _hi
      exact (hroot i).summable
  calc
    (∑' m : ℕ,
        (∑ i : Fin n, z i ^ m) * szegoKernelDefectCoeff z m)
        = ∑' m : ℕ,
            ∑ i : Fin n, szegoKernelDefectCoeff z m * z i ^ m := by
          apply tsum_congr
          intro m
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = ∑ i : Fin n, (1 : ℂ) := htsum
    _ = (n : ℂ) := by simp

/--
The concrete Szego vector pairs with the conjugated defect vector to give `n`.

This proves the `pairing` field of the remaining Hardy-data package, leaving
only the norm identity for the Blaschke-defect vector as the serious analytic
input.
-/
theorem hardySzegoKernelVector_real_inner_defectConj_eq_nat
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    (n : ℝ) =
      inner ℝ (hardySzegoKernelVector z hz) (hardySzegoDefectConjVector z hz) := by
  have hcomplex :
      inner ℂ (hardySzegoKernelVector z hz) (hardySzegoDefectConjVector z hz) =
        (starRingEnd ℂ) ((n : ℂ)) := by
    rw [lp.inner_eq_tsum]
    calc
      (∑' m : ℕ,
          inner ℂ ((hardySzegoKernelVector z hz) m)
            ((hardySzegoDefectConjVector z hz) m))
          =
        ∑' m : ℕ,
          (starRingEnd ℂ)
            ((∑ i : Fin n, z i ^ m) * szegoKernelDefectCoeff z m) := by
            apply tsum_congr
            intro m
            rw [hardySzegoKernelVector_apply, hardySzegoDefectConjVector_apply]
            rw [RCLike.inner_apply']
            simp [map_mul, mul_comm]
      _ = (starRingEnd ℂ)
          (∑' m : ℕ, (∑ i : Fin n, z i ^ m) * szegoKernelDefectCoeff z m) := by
            simpa using
              (RCLike.conjCLE.map_tsum
                (f := fun m : ℕ =>
                  (∑ i : Fin n, z i ^ m) * szegoKernelDefectCoeff z m)).symm
      _ = (starRingEnd ℂ) ((n : ℂ)) := by
            rw [szegoKernelDefectCoeff_tsum_root_sum z hz]
  have hreal_eq :
      inner ℝ (hardySzegoKernelVector z hz) (hardySzegoDefectConjVector z hz) =
        RCLike.re
          (inner ℂ (hardySzegoKernelVector z hz) (hardySzegoDefectConjVector z hz)) := by
    calc
      inner ℝ (hardySzegoKernelVector z hz) (hardySzegoDefectConjVector z hz)
          =
        ∑' m : ℕ,
          inner ℝ ((hardySzegoKernelVector z hz) m)
            ((hardySzegoDefectConjVector z hz) m) := by
            rw [lp.inner_eq_tsum]
      _ =
        ∑' m : ℕ,
          RCLike.re
            (inner ℂ ((hardySzegoKernelVector z hz) m)
              ((hardySzegoDefectConjVector z hz) m)) := by
            apply tsum_congr
            intro m
            rw [real_inner_eq_re_inner ℂ]
      _ =
        RCLike.re
          (∑' m : ℕ,
            inner ℂ ((hardySzegoKernelVector z hz) m)
              ((hardySzegoDefectConjVector z hz) m)) := by
            simpa using
              (RCLike.reCLM.map_tsum
                (lp.summable_inner
                  (𝕜 := ℂ) (hardySzegoKernelVector z hz) (hardySzegoDefectConjVector z hz))).symm
      _ =
        RCLike.re
          (inner ℂ (hardySzegoKernelVector z hz) (hardySzegoDefectConjVector z hz)) := by
            rw [lp.inner_eq_tsum]
  rw [hreal_eq, hcomplex]
  simp

/-- On the unit circle, the denominator of a Blaschke factor has the numerator's norm. -/
lemma norm_one_sub_conj_mul_of_norm_eq_one
    {a w : ℂ} (hw : ‖w‖ = 1) :
    ‖1 - (starRingEnd ℂ) a * w‖ = ‖w - a‖ := by
  have hnormSq_w : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, hw]
    norm_num
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [Complex.sq_norm, Complex.sq_norm]
  rw [Complex.normSq_sub, Complex.normSq_sub]
  simp [Complex.normSq_conj, Complex.normSq_mul, hnormSq_w]
  ring_nf

/-- A disk Blaschke factor has norm one on the unit circle. -/
lemma diskBlaschkeFactor_norm_of_norm_eq_one
    {a w : ℂ}
    (ha : ‖a‖ < 1)
    (hw : ‖w‖ = 1) :
    ‖diskBlaschkeFactor a w‖ = 1 := by
  have hnorm_eq : ‖1 - (starRingEnd ℂ) a * w‖ = ‖w - a‖ :=
    norm_one_sub_conj_mul_of_norm_eq_one hw
  have hwa_ne : ‖w - a‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro hsub
    have hwa : w = a := sub_eq_zero.mp hsub
    have : ‖a‖ = 1 := by simpa [hwa] using hw
    linarith
  rw [diskBlaschkeFactor, norm_div, hnorm_eq]
  field_simp [hwa_ne]

/-- A finite Blaschke product has norm one on the unit circle. -/
lemma finiteBlaschkeProduct_norm_of_norm_eq_one
    {n : ℕ} (z : Fin n → ℂ) {w : ℂ}
    (hz : ∀ i, ‖z i‖ < 1)
    (hw : ‖w‖ = 1) :
    ‖finiteBlaschkeProduct z w‖ = 1 := by
  rw [finiteBlaschkeProduct, norm_prod]
  simp [diskBlaschkeFactor_norm_of_norm_eq_one, hz, hw]

/-- Multiplying a complex number by its conjugate gives its squared norm. -/
lemma conj_mul_self_eq_normSq (x : ℂ) :
    (starRingEnd ℂ) x * x = ((Complex.normSq x : ℝ) : ℂ) := by
  rw [mul_comm]
  rw [Complex.mul_conj]

/-- The sign in `Λ = (-1)^n ∏ z_i` does not affect its squared norm. -/
lemma blaschkeLambda_norm_sq
    {n : ℕ} (z : Fin n → ℂ) :
    ‖blaschkeLambda z‖ ^ (2 : ℕ) =
      ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ) := by
  simp [blaschkeLambda]

/-- If all zeros are in the disk, then `Λ = B(0)` is also in the disk. -/
lemma blaschkeLambda_norm_lt_one
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    ‖blaschkeLambda z‖ < 1 := by
  simpa [blaschkeLambda] using szegoKernel_product_norm_lt_one z hn hz

/--
At zero, the Blaschke-product defect function is exactly the scalar defect
`1 - |∏ z_i|²` from PDF Lemma 2.
-/
lemma szegoKernelDefectValue_zero
    {n : ℕ} (z : Fin n → ℂ) :
    szegoKernelDefectValue z 0 = ((szegoKernelProductDefect z : ℝ) : ℂ) := by
  rw [szegoKernelDefectValue, finiteBlaschkeProduct_zero]
  dsimp [szegoKernelProductDefect]
  rw [conj_mul_self_eq_normSq]
  rw [Complex.normSq_eq_norm_sq, blaschkeLambda_norm_sq]
  norm_num

/--
The value of the defect function at zero has norm equal to the positive scalar
defect from PDF Lemma 2.
-/
lemma norm_szegoKernelDefectValue_zero
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    ‖szegoKernelDefectValue z 0‖ = szegoKernelProductDefect z := by
  rw [szegoKernelDefectValue_zero]
  rw [Complex.norm_def, Complex.normSq_ofReal]
  rw [← sq]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (szegoKernel_denominator_pos z hn hz).le

/--
The coefficient norm of the Blaschke defect follows algebraically from the
unit `H²` norm of the finite Blaschke product coefficients.
-/
lemma szegoKernelDefectCoeff_norm_sq_tsum_eq_productDefect
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    (∑' m : ℕ, ‖szegoKernelDefectCoeff z m‖ ^ (2 : ℕ)) =
      szegoKernelProductDefect z := by
  let A : ℝ := ‖blaschkeLambda z‖ ^ (2 : ℕ)
  have hBnorm := finiteBlaschkeProductCoeff_norm_sq_tsum_eq_one z hz
  have hBsum : Summable fun m : ℕ => ‖finiteBlaschkeProductCoeff z m‖ ^ (2 : ℕ) := by
    have hmem := finiteBlaschkeProductCoeff_memℓp z hz
    convert! hmem.summable (by norm_num) using 1
    ext m
    norm_num
  have hDsum : Summable fun m : ℕ => ‖szegoKernelDefectCoeff z m‖ ^ (2 : ℕ) := by
    have hmem := szegoKernelDefectCoeff_memℓp z hz
    convert! hmem.summable (by norm_num) using 1
    ext m
    norm_num
  have hdefect_eq : szegoKernelProductDefect z = 1 - A := by
    dsimp [A, szegoKernelProductDefect]
    rw [← blaschkeLambda_norm_sq z]
  have hBtail :
      (∑' m : ℕ, ‖finiteBlaschkeProductCoeff z (m + 1)‖ ^ (2 : ℕ)) = 1 - A := by
    have hsplit :
        1 = A + ∑' m : ℕ, ‖finiteBlaschkeProductCoeff z (m + 1)‖ ^ (2 : ℕ) := by
      rw [← hBnorm, hBsum.tsum_eq_zero_add]
      dsimp [A]
      rw [finiteBlaschkeProductCoeff_zero]
    linarith
  have hDzero :
      ‖szegoKernelDefectCoeff z 0‖ ^ (2 : ℕ) = (1 - A) ^ (2 : ℕ) := by
    rw [szegoKernelDefectCoeff_zero]
    rw [Complex.norm_def, Complex.normSq_ofReal]
    rw [← sq]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (szegoKernel_denominator_pos z hn hz).le]
    rw [hdefect_eq]
  have hDtail :
      (∑' m : ℕ, ‖szegoKernelDefectCoeff z (m + 1)‖ ^ (2 : ℕ)) = A * (1 - A) := by
    calc
      (∑' m : ℕ, ‖szegoKernelDefectCoeff z (m + 1)‖ ^ (2 : ℕ))
          = ∑' m : ℕ, A * ‖finiteBlaschkeProductCoeff z (m + 1)‖ ^ (2 : ℕ) := by
              apply tsum_congr
              intro m
              dsimp [szegoKernelDefectCoeff, A]
              simp
              ring
      _ = A * (∑' m : ℕ, ‖finiteBlaschkeProductCoeff z (m + 1)‖ ^ (2 : ℕ)) := by
              rw [tsum_mul_left]
      _ = A * (1 - A) := by rw [hBtail]
  calc
    (∑' m : ℕ, ‖szegoKernelDefectCoeff z m‖ ^ (2 : ℕ))
        = ‖szegoKernelDefectCoeff z 0‖ ^ (2 : ℕ) +
            ∑' m : ℕ, ‖szegoKernelDefectCoeff z (m + 1)‖ ^ (2 : ℕ) :=
          hDsum.tsum_eq_zero_add
    _ = (1 - A) ^ (2 : ℕ) + A * (1 - A) := by rw [hDzero, hDtail]
    _ = szegoKernelProductDefect z := by
          rw [hdefect_eq]
          ring

/--
The concrete Blaschke-defect coefficient vector has the expected `H²` norm,
assuming the standard unit norm identity for the finite Blaschke product
coefficients.
-/
theorem hardySzegoDefectConjVector_real_inner_eq_productDefect
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    szegoKernelProductDefect z =
      inner ℝ (hardySzegoDefectConjVector z hz) (hardySzegoDefectConjVector z hz) := by
  rw [real_inner_self_eq_norm_sq]
  symm
  calc
    ‖hardySzegoDefectConjVector z hz‖ ^ (2 : ℕ)
        = ‖hardySzegoDefectConjVector z hz‖ ^ (2 : ℝ≥0∞).toReal := by
          norm_cast
    _ = ∑' m : ℕ, ‖hardySzegoDefectConjVector z hz m‖ ^ (2 : ℝ≥0∞).toReal := by
          exact lp.norm_rpow_eq_tsum (by norm_num)
            (hardySzegoDefectConjVector z hz)
    _ = ∑' m : ℕ, ‖szegoKernelDefectCoeff z m‖ ^ (2 : ℕ) := by
          apply tsum_congr
          intro m
          rw [hardySzegoDefectConjVector_apply]
          norm_num
    _ = szegoKernelProductDefect z :=
          szegoKernelDefectCoeff_norm_sq_tsum_eq_productDefect z hn hz

/--
The Hardy-space data behind PDF Lemma 2.

`F` is the Szego-kernel sum, while `G` is the Blaschke-product defect function
`1 - overline{B(0)} B`.  The fields record exactly the three computations
needed before applying Cauchy-Schwarz.
-/
structure SzegoKernelHardyData {n : ℕ} (z : Fin n → ℂ) where
  H : Type
  [normed : NormedAddCommGroup H]
  [innerSpace : InnerProductSpace ℝ H]
  F : H
  G : H
  pairing : (n : ℝ) = inner ℝ F G
  F_normSq : szegoKernelRealSum z = inner ℝ F F
  G_normSq : szegoKernelProductDefect z = inner ℝ G G

/--
The reduced remaining Hardy-space construction in PDF Lemma 2.

The Szego-kernel vector `F` and the Blaschke-defect vector `G` are now
concrete.  The pairing identity is proved below; the remaining analytic
boundary is the `G_normSq` identity.
-/
structure SzegoKernelDefectHardyData
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ < 1) where
  G : lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞)
  pairing : (n : ℝ) = inner ℝ (hardySzegoKernelVector z hz) G
  G_normSq : szegoKernelProductDefect z = inner ℝ G G

/--
The remaining Hardy-space data assembled from the concrete defect vector.

The finite-Blaschke coefficient norm theorem, defect vector construction,
pairing identity, and defect norm calculation are assembled here.
-/
def szegoKernel_defect_hardyData
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    SzegoKernelDefectHardyData z hz :=
  { G := hardySzegoDefectConjVector z hz
    pairing := hardySzegoKernelVector_real_inner_defectConj_eq_nat z hz
    G_normSq := hardySzegoDefectConjVector_real_inner_eq_productDefect z hn hz }

/--
Assemble the full Hardy-space data from the concrete Szego-kernel vector and
the still-remaining Blaschke-defect vector.
-/
def szegoKernel_hardyData
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    SzegoKernelHardyData z := by
  let D := szegoKernel_defect_hardyData z hn hz
  exact
    { H := lp (fun _ : ℕ => ℂ) (2 : ℝ≥0∞)
      normed := inferInstance
      innerSpace := inferInstance
      F := hardySzegoKernelVector z hz
      G := D.G
      pairing := D.pairing
      F_normSq := hardySzegoKernelVector_real_inner_eq_szegoKernelRealSum z hz
      G_normSq := D.G_normSq }

/--
Abstract real Hilbert-space Cauchy-Schwarz, packaged with named norm-square
identities.
-/
lemma abs_real_inner_le_sqrt_mul_of_inner_data
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) {x A B : ℝ}
    (hx : x = inner ℝ u v)
    (hA : A = inner ℝ u u)
    (hB : B = inner ℝ v v) :
    |x| ≤ Real.sqrt A * Real.sqrt B := by
  rw [hx, hA, hB]
  have h := abs_real_inner_le_norm u v
  rw [norm_eq_sqrt_real_inner u, norm_eq_sqrt_real_inner v] at h
  exact h

/--
The Cauchy-Schwarz step in PDF Lemma 2, after the Hardy-space pairing and norm
computations have been identified:

`|n| ≤ sqrt(Σ Re K(z_j,z_k)) * sqrt(1 - |∏ z_i|²)`.
-/
theorem szegoKernel_cauchySchwarz_bound
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    |(n : ℝ)| ≤
      Real.sqrt (szegoKernelRealSum z) * Real.sqrt (szegoKernelProductDefect z) := by
  let D := szegoKernel_hardyData z hn hz
  letI := D.normed
  letI := D.innerSpace
  exact abs_real_inner_le_sqrt_mul_of_inner_data
    D.F D.G D.pairing D.F_normSq D.G_normSq

/--
PDF Lemma 2 in the product form delivered by Cauchy-Schwarz.

The remaining analytic boundary is now the square-root Cauchy-Schwarz estimate
above; this theorem only squares it and rewrites the named quantities.
-/
theorem szegoKernel_re_sum_mul_denominator_bound
    {n : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n)
    (hz : ∀ i, ‖z i‖ < 1) :
    (n : ℝ) ^ (2 : ℕ) ≤
      ((Finset.univ : Finset (Fin n × Fin n)).sum
        (fun p => ((1 : ℂ) /
          (1 - z p.1 * (starRingEnd ℂ) (z p.2))).re)) *
        (1 - ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ)) := by
  have hS : 0 ≤ szegoKernelRealSum z :=
    szegoKernelRealSum_nonneg z hn hz
  have hD : 0 ≤ szegoKernelProductDefect z :=
    (szegoKernel_denominator_pos z hn hz).le
  have hcs := szegoKernel_cauchySchwarz_bound z hn hz
  have hmain :
      (n : ℝ) ^ (2 : ℕ) ≤
        szegoKernelRealSum z * szegoKernelProductDefect z :=
    sq_le_mul_of_abs_le_sqrt_mul hS hD hcs
  simpa [szegoKernelRealSum, szegoKernelProductDefect] using hmain

/--
PDF Lemma 2 in its divided Szego-kernel form.

For points `z_i` in the open unit disk, the real part of the full Szego-kernel
sum is bounded below by the value forced by the product of the points.
-/
theorem szegoKernel_re_sum_lower_bound
    {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    (n : ℝ) ^ (2 : ℕ) / (1 - ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ)) ≤
      (Finset.univ : Finset (Fin n × Fin n)).sum
        (fun p => ((1 : ℂ) /
          (1 - z p.1 * (starRingEnd ℂ) (z p.2))).re) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hden : 0 < 1 - ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ) :=
      szegoKernel_denominator_pos z hn hz
    rw [div_le_iff₀ hden]
    exact szegoKernel_re_sum_mul_denominator_bound z hn hz

/--
The torus specialization of PDF Lemma 2.

Apply the preceding disk inequality to `z_i = sqrt(t) * ω_i`.  The product
term becomes `t^n`, while the kernel denominator becomes
`1 - t ω_j \barω_k`.
-/
theorem szegoKernel_re_sum_lower_bound_on_torus
    {n : ℕ} (ω : Fin n → ℂ) {t : ℝ}
    (h0t : 0 ≤ t)
    (ht1 : t < 1)
    (hω : onUnitCircle ω) :
    (n : ℝ) ^ (2 : ℕ) / (1 - t ^ n) ≤
      (Finset.univ : Finset (Fin n × Fin n)).sum
        (fun p => ((1 : ℂ) /
          (1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2))).re) := by
  let r : ℝ := Real.sqrt t
  let z : Fin n → ℂ := fun i => (r : ℂ) * ω i
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg t
  have hr_lt_one : r < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h0t ht1
  have hz : ∀ i, ‖z i‖ < 1 := by
    intro i
    calc
      ‖z i‖ = r := by simp [z, r, hω i, abs_of_nonneg hr_nonneg]
      _ < 1 := hr_lt_one
  have hkernel := szegoKernel_re_sum_lower_bound z hz
  have hsqC : ((r : ℂ) ^ (2 : ℕ)) = (t : ℂ) := by
    have hsqR : r * r = t := by
      dsimp [r]
      rw [← sq, Real.sq_sqrt h0t]
    rw [sq, ← Complex.ofReal_mul, hsqR]
  have hprod_norm : ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ) = t ^ n := by
    calc
      ‖(∏ i : Fin n, z i)‖ ^ (2 : ℕ) =
          ((∏ i : Fin n, ‖z i‖) ^ (2 : ℕ)) := by
        rw [norm_prod]
      _ = ((∏ _i : Fin n, r) ^ (2 : ℕ)) := by
        congr 1
        apply Finset.prod_congr rfl
        intro i _hi
        simp [z, r, hω i, abs_of_nonneg hr_nonneg]
      _ = (r ^ n) ^ (2 : ℕ) := by
        simp [Finset.prod_const]
      _ = (r ^ (2 : ℕ)) ^ n := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = t ^ n := by
        have hsqR : r ^ (2 : ℕ) = t := by
          dsimp [r]
          exact Real.sq_sqrt h0t
        rw [hsqR]
  have hsum_eq :
      (Finset.univ : Finset (Fin n × Fin n)).sum
        (fun p => ((1 : ℂ) /
          (1 - z p.1 * (starRingEnd ℂ) (z p.2))).re) =
      (Finset.univ : Finset (Fin n × Fin n)).sum
        (fun p => ((1 : ℂ) /
          (1 - (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2))).re) := by
    apply Finset.sum_congr rfl
    intro p _hp
    have hmul : z p.1 * (starRingEnd ℂ) (z p.2) =
        (t : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2) := by
      simp [z]
      calc
        (↑r * ω p.1) * (↑r * (starRingEnd ℂ) (ω p.2))
            = (↑r ^ (2 : ℕ)) * (ω p.1 * (starRingEnd ℂ) (ω p.2)) := by ring
        _ = ↑t * (ω p.1 * (starRingEnd ℂ) (ω p.2)) := by rw [hsqC]
        _ = ↑t * ω p.1 * (starRingEnd ℂ) (ω p.2) := by ring
    rw [hmul]
  rw [hprod_norm, hsum_eq] at hkernel
  exact hkernel

/-- PDF Lemma 2, now derived from the Szego-kernel boundary above. -/
theorem blaschkeDerivativeGap_nonneg_of_torus
    {n : ℕ} (ω : Fin n → ℂ) {a t : ℝ}
    (_hn : 0 < n)
    (_h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω)
    (ht : t ∈ interior (Set.Icc 0 a)) :
    0 ≤ blaschkeDerivativeGap n ω t := by
  have htIcc : t ∈ Set.Icc 0 a := interior_subset ht
  have ht_nonneg : 0 ≤ t := htIcc.1
  have ht_lt_one : t < 1 := lt_of_le_of_lt htIcc.2 ha1
  have hle :=
    szegoKernel_re_sum_lower_bound_on_torus
      (n := n) (ω := ω) (t := t) ht_nonneg ht_lt_one hω
  dsimp [blaschkeDerivativeGap]
  linarith

/-- The derivative of `g` is nonnegative on the interior of `[0,a]`. -/
lemma blaschkeLogGap_deriv_nonneg_on_interior_Icc_of_torus
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (hn : 0 < n)
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    ∀ t ∈ interior (Set.Icc 0 a),
      0 ≤ deriv (fun s => blaschkeLogGap n ω s) t := by
  intro t ht
  have htpos : 0 < t := by
    rw [interior_Icc] at ht
    exact ht.1
  have hmul : 0 ≤ t * deriv (fun s => blaschkeLogGap n ω s) t := by
    rw [blaschkeLogGap_mul_deriv_eq_derivativeGap_of_torus ω hn h0a ha1 hω ht]
    exact blaschkeDerivativeGap_nonneg_of_torus ω hn h0a ha1 hω ht
  exact (mul_nonneg_iff_of_pos_left htpos).1 hmul

/--
Monotonicity step in the torus proof of PDF Lemma 3, now reduced to the
standard derivative test plus the derivative-gap inputs above.
-/
theorem blaschkeLogGap_monotoneOn_Icc_of_torus
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (hn : 0 < n)
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    MonotoneOn (fun t => blaschkeLogGap n ω t) (Set.Icc 0 a) := by
  exact monotoneOn_of_deriv_nonneg (convex_Icc 0 a)
    (blaschkeLogGap_continuousOn_Icc_of_torus ω hn h0a ha1 hω)
    (blaschkeLogGap_differentiableOn_interior_Icc_of_torus ω hn h0a ha1 hω)
    (blaschkeLogGap_deriv_nonneg_on_interior_Icc_of_torus ω hn h0a ha1 hω)

/--
The PDF's conclusion `g(a) ≥ 0`, now reduced to monotonicity plus `g(0)=0`.
-/
theorem blaschkeLogGap_nonneg_of_torus
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (hn : 0 < n)
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    0 ≤ blaschkeLogGap n ω a := by
  have hmono := blaschkeLogGap_monotoneOn_Icc_of_torus ω hn h0a ha1 hω
  have hle : blaschkeLogGap n ω 0 ≤ blaschkeLogGap n ω a :=
    hmono (by simp [h0a.le]) (by simp [h0a.le]) h0a.le
  rw [blaschkeLogGap_zero hn ω] at hle
  exact hle

/--
Turning the logarithmic gap `g(a) ≥ 0` into the torus product estimate.
-/
lemma blaschkeAllPairsProduct_torus_bound_of_log_gap
    {n : ℕ} {ω : Fin n → ℂ} {a : ℝ}
    (hn : 0 < n)
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω)
    (hgap : 0 ≤ blaschkeLogGap n ω a) :
    blaschkeAllPairsProduct ω a ≤ (1 - a ^ n) ^ n := by
  have hrhs_pos : 0 < (1 - a ^ n) ^ n :=
    pow_pos (one_sub_pow_pos_of_pos_nat_of_lt_one hn h0a ha1) n
  have hprod_pos : 0 < blaschkeAllPairsProduct ω a := by
    unfold blaschkeAllPairsProduct
    exact Finset.prod_pos (fun p _hp => blaschke_torus_factor_pos h0a ha1 hω p)
  have hlog_prod :
      Real.log (blaschkeAllPairsProduct ω a) =
        (Finset.univ : Finset (Fin n × Fin n)).sum
          (fun p => Real.log
            ‖1 - (a : ℂ) * ω p.1 * (starRingEnd ℂ) (ω p.2)‖) := by
    unfold blaschkeAllPairsProduct
    rw [Real.log_prod]
    intro p _hp
    exact ne_of_gt (blaschke_torus_factor_pos h0a ha1 hω p)
  have hlog_rhs :
      Real.log ((1 - a ^ n) ^ n) = (n : ℝ) * Real.log (1 - a ^ n) := by
    rw [Real.log_pow]
  have hlog_le :
      Real.log (blaschkeAllPairsProduct ω a)
        ≤ Real.log ((1 - a ^ n) ^ n) := by
    rw [hlog_prod, hlog_rhs]
    dsimp [blaschkeLogGap] at hgap
    linarith
  exact (Real.log_le_log_iff hprod_pos hrhs_pos).1 hlog_le

/--
Torus case of PDF Lemma 3, now reduced to the logarithmic-gap statement.
-/
theorem blaschkeFullProduct_torus_bound_of_pos_a
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    blaschkeFullProduct ω a ≤ (1 - a ^ n) ^ n := by
  by_cases hn0 : n = 0
  · subst n
    simp [blaschkeFullProduct]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rw [blaschkeFullProduct_eq_allPairsProduct]
    exact blaschkeAllPairsProduct_torus_bound_of_log_gap hn h0a ha1 hω
      (blaschkeLogGap_nonneg_of_torus ω hn h0a ha1 hω)

/-- The off-diagonal Blaschke product is nonnegative. -/
lemma blaschkeOffDiagProduct_nonneg
    {n : ℕ} (x : Fin n → ℂ) (a : ℝ) :
    0 ≤ blaschkeOffDiagProduct x a := by
  unfold blaschkeOffDiagProduct
  exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)

/--
Torus case of PDF Lemma 3, in the off-diagonal form used by Lemma 4.

The full torus product is bounded by `(1-a^n)^n`; its diagonal part is exactly
`(1-a)^n`, so division gives the off-diagonal estimate.
-/
theorem blaschkeOffDiagProduct_torus_bound_of_pos_a
    {n : ℕ} (ω : Fin n → ℂ) {a : ℝ}
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hω : onUnitCircle ω) :
    blaschkeOffDiagProduct ω a ≤ ((1 - a ^ n) / (1 - a)) ^ n := by
  let D : ℝ := blaschkeDiagProduct ω a
  let O : ℝ := blaschkeOffDiagProduct ω a
  change O ≤ ((1 - a ^ n) / (1 - a)) ^ n
  have hden_pos : 0 < (1 - a) ^ n := by
    exact pow_pos (by linarith : 0 < 1 - a) n
  have hdiag_eq : D = (1 - a) ^ n := by
    dsimp [D]
    exact blaschkeDiagProduct_torus_eq ω h0a.le ha1 hω
  have hfull : D * O ≤ (1 - a ^ n) ^ n := by
    have h := blaschkeFullProduct_torus_bound_of_pos_a ω h0a ha1 hω
    rw [blaschkeFullProduct_eq_diag_mul_offDiag] at h
    simpa [D, O, mul_comm] using h
  have htarget_mul : O * (1 - a) ^ n ≤ (1 - a ^ n) ^ n := by
    rw [← hdiag_eq]
    simpa [mul_comm] using hfull
  rw [div_pow]
  exact (le_div_iff₀ hden_pos).2 htarget_mul

/--
Positive-parameter off-diagonal form of PDF Lemma 3.

This is the composition of the off-diagonal maximum-modulus reduction to the
torus and the torus product estimate.
-/
theorem blaschkeOffDiagProduct_bound_of_pos_a
    {n : ℕ} (x : Fin n → ℂ) {a : ℝ}
    (h0a : 0 < a)
    (ha1 : a < 1)
    (hx : ∀ i, ‖x i‖ ≤ 1) :
    blaschkeOffDiagProduct x a ≤ ((1 - a ^ n) / (1 - a)) ^ n := by
  rcases blaschkeOffDiagProduct_le_torus_product_of_pos_a x h0a ha1 hx with
    ⟨ω, hω, hle⟩
  exact hle.trans (blaschkeOffDiagProduct_torus_bound_of_pos_a ω h0a ha1 hω)

/-- At `a = 0`, the off-diagonal Blaschke product is the empty/constant product `1`. -/
lemma blaschkeOffDiagProduct_zero
    {n : ℕ} (x : Fin n → ℂ) :
    blaschkeOffDiagProduct x 0 = 1 := by
  unfold blaschkeOffDiagProduct
  simp

/--
PDF Lemma 3 in the off-diagonal form used by Lemma 4.

The `a = 0` case is proved directly; the positive case uses the proved
off-diagonal maximum-modulus reduction plus the torus logarithmic estimate.
-/
theorem blaschkeOffDiagProduct_bound
    {n : ℕ} (x : Fin n → ℂ) {a : ℝ}
    (h0a : 0 ≤ a)
    (ha1 : a < 1)
    (hx : ∀ i, ‖x i‖ ≤ 1) :
    blaschkeOffDiagProduct x a ≤ ((1 - a ^ n) / (1 - a)) ^ n := by
  by_cases ha0 : a = 0
  · subst a
    rw [blaschkeOffDiagProduct_zero]
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [hnpos.ne']
  · exact blaschkeOffDiagProduct_bound_of_pos_a x
      (lt_of_le_of_ne h0a (Ne.symm ha0)) ha1 hx

/-- Expansion of one Blaschke factor with a real parameter. -/
lemma norm_one_sub_real_mul_mul_conj_sq
    (a : ℝ) (u v : ℂ) :
    ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ)
      = 1 + a ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) * ‖v‖ ^ (2 : ℕ)
          - 2 * a * (u * (starRingEnd ℂ) v).re := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofReal,
    Complex.sq_norm]
  ring

/-- Expansion of one ordinary distance factor. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq_sub_re
    (u v : ℂ) :
    ‖u - v‖ ^ (2 : ℕ)
      = ‖u‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ)
          - 2 * (u * (starRingEnd ℂ) v).re := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  rw [← Complex.sq_norm u, ← Complex.sq_norm v]

/--
The unscaled pointwise algebraic inequality in PDF Lemma 4.

This is exactly the PDF's direct calculation:
`λ² |1 - λ⁻² u \bar v|² - (|u-v|² + (λ-λ⁻¹)²)` is a sum of nonnegative
terms when `|u|, |v| ≤ 1` and `1 ≤ λ`.
-/
lemma pdf_lemma4_pointwise_unit_bound
    {lam a : ℝ} {u v : ℂ}
    (hlam : 1 ≤ lam)
    (ha : a = lam⁻¹ ^ (2 : ℕ))
    (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) :
    ‖u - v‖ ^ (2 : ℕ) + (lam - lam⁻¹) ^ (2 : ℕ)
      ≤ lam ^ (2 : ℕ)
        * ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ) := by
  let U : ℝ := ‖u‖ ^ (2 : ℕ)
  let V : ℝ := ‖v‖ ^ (2 : ℕ)
  let R : ℝ := (u * (starRingEnd ℂ) v).re
  let t : ℝ := lam⁻¹ ^ (2 : ℕ)
  have hlam_nonneg : 0 ≤ lam := zero_le_one.trans hlam
  have hlam_pos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hdist :
      ‖u - v‖ ^ (2 : ℕ) = U + V - 2 * R := by
    dsimp [U, V, R]
    exact norm_sub_sq_eq_norm_sq_add_norm_sq_sub_re u v
  have hblas :
      ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ)
        = 1 + t ^ (2 : ℕ) * U * V - 2 * t * R := by
    dsimp [t, U, V, R]
    simpa [ha] using norm_one_sub_real_mul_mul_conj_sq a u v
  have ht_nonneg : 0 ≤ t := by dsimp [t]; positivity
  have hinv_le_one : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    exact (sq_le_one_iff₀ (inv_nonneg.mpr hlam_nonneg)).2 hinv_le_one
  have hU_nonneg : 0 ≤ U := by dsimp [U]; positivity
  have hV_nonneg : 0 ≤ V := by dsimp [V]; positivity
  have hU_le_one : U ≤ 1 := by
    dsimp [U]
    simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hu
  have hV_le_one : V ≤ 1 := by
    dsimp [V]
    simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hv
  have htV_le_one : t * V ≤ 1 := by
    have hmul : t * V ≤ 1 * 1 :=
      mul_le_mul ht_le_one hV_le_one hV_nonneg zero_le_one
    simpa using hmul
  have hlam_sq_t : lam ^ (2 : ℕ) * t = 1 := by
    dsimp [t]
    field_simp [ne_of_gt hlam_pos]
  have hlam_sq_t_sq : lam ^ (2 : ℕ) * t ^ (2 : ℕ) = t := by
    dsimp [t]
    field_simp [ne_of_gt hlam_pos]
  have hidentity :
      lam ^ (2 : ℕ)
          * ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ)
        - (‖u - v‖ ^ (2 : ℕ) + (lam - lam⁻¹) ^ (2 : ℕ))
        =
          (1 - V) * (1 - t) + (1 - U) * (1 - t * V) := by
    rw [hblas, hdist]
    dsimp [t]
    field_simp [ne_of_gt hlam_pos]
    ring
  have hnonneg :
      0 ≤ (1 - V) * (1 - t) + (1 - U) * (1 - t * V) := by
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hV_le_one) (sub_nonneg.mpr ht_le_one))
      (mul_nonneg (sub_nonneg.mpr hU_le_one) (sub_nonneg.mpr htV_le_one))
  have hdiff_nonneg :
      0 ≤ lam ^ (2 : ℕ)
          * ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ)
        - (‖u - v‖ ^ (2 : ℕ) + (lam - lam⁻¹) ^ (2 : ℕ)) := by
    rw [hidentity]
    exact hnonneg
  linarith

/--
The pointwise algebraic inequality used in PDF Lemma 4.

After scaling `y_i = A x_i`, with `λ = exp α` and `a = λ⁻²`, each Euclidean
distance factor is bounded by the corresponding Blaschke factor.  The PDF
calls this a direct calculation.
-/
theorem pdf_lemma4_pointwise_scaled_bound
    {A σ lam a : ℝ} {u v yu yv : ℂ}
    (hA : 0 < A)
    (hlam : 1 ≤ lam)
    (hscale_u : yu = (A : ℂ) * u)
    (hscale_v : yv = (A : ℂ) * v)
    (hsigma : σ = A * (lam - lam⁻¹))
    (ha : a = lam⁻¹ ^ (2 : ℕ))
    (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) :
    ‖yu - yv‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)
      ≤ (A ^ (2 : ℕ) * lam ^ (2 : ℕ))
        * ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ) := by
  rw [hscale_u, hscale_v, hsigma]
  have hunit := pdf_lemma4_pointwise_unit_bound hlam ha hu hv
  have hnormA : ‖(A : ℂ)‖ = A := by
    simp [abs_of_pos hA]
  have hleft :
      ‖(A : ℂ) * u - (A : ℂ) * v‖ ^ (2 : ℕ)
          + (A * (lam - lam⁻¹)) ^ (2 : ℕ)
        = A ^ (2 : ℕ)
          * (‖u - v‖ ^ (2 : ℕ) + (lam - lam⁻¹) ^ (2 : ℕ)) := by
    have hsub : (A : ℂ) * u - (A : ℂ) * v = (A : ℂ) * (u - v) := by
      ring
    rw [hsub, norm_mul, hnormA]
    ring
  calc
    ‖(A : ℂ) * u - (A : ℂ) * v‖ ^ (2 : ℕ)
          + (A * (lam - lam⁻¹)) ^ (2 : ℕ)
        = A ^ (2 : ℕ)
          * (‖u - v‖ ^ (2 : ℕ) + (lam - lam⁻¹) ^ (2 : ℕ)) := hleft
    _ ≤ A ^ (2 : ℕ)
        * (lam ^ (2 : ℕ)
          * ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hunit (sq_nonneg A)
    _ = (A ^ (2 : ℕ) * lam ^ (2 : ℕ))
        * ‖1 - (a : ℂ) * u * (starRingEnd ℂ) v‖ ^ (2 : ℕ) := by
          ring

/--
The final hyperbolic simplification in PDF Lemma 4.

With `α = arsinh(σ/(2A))`, `λ = exp α`, and `a = λ⁻²`, the prefactor produced
by Lemma 3 is exactly the stated `sinh` expression.
-/
lemma pow_mul_inv_pow_double {lam : ℝ} (hlam : lam ≠ 0) (m : ℕ) :
    lam ^ m * (lam⁻¹) ^ (2 * m) = (lam⁻¹) ^ m := by
  have hsplit : (lam⁻¹) ^ (2 * m) = (lam⁻¹) ^ m * (lam⁻¹) ^ m := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, ← mul_assoc]
  have hcancel : lam ^ m * (lam⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hlam, one_pow]
  rw [hcancel, one_mul]

/--
The geometric factor in PDF Lemma 4 is the usual hyperbolic-sine quotient.

For `λ = exp α` and `a = λ⁻²`,
`λ^{n-1} * (1 - a^n)/(1-a) = sinh(nα)/sinh α`.
-/
lemma pdf_lemma4_sinh_ratio
    {n : ℕ} {α lam a : ℝ}
    (hα : 0 < α)
    (hlam : lam = Real.exp α)
    (ha : a = lam⁻¹ ^ (2 : ℕ)) :
    lam ^ (n - 1) * ((1 - a ^ n) / (1 - a)) =
      Real.sinh ((n : ℝ) * α) / Real.sinh α := by
  by_cases hn : n = 0
  · subst n
    simp [Real.sinh_eq]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    subst n
    have hlam_pos : 0 < lam := by
      rw [hlam]
      positivity
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
    have hlam_gt_one : 1 < lam := by
      rw [hlam]
      exact Real.one_lt_exp_iff.mpr hα
    have hsq_gt : 1 < lam ^ (2 : ℕ) := by
      simpa using (pow_lt_pow_left₀ hlam_gt_one (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (2 : ℕ) ≠ 0))
    have hden_ne : lam ^ (2 : ℕ) - 1 ≠ 0 := by
      linarith
    have hneg1 : Real.exp (-α) = lam⁻¹ := by
      rw [Real.exp_neg, ← hlam]
    rw [Real.sinh_eq, Real.sinh_eq]
    rw [Real.exp_nat_mul]
    have hneg : Real.exp (-(↑(k + 1) * α)) = lam⁻¹ ^ (k + 1) := by
      rw [show -(↑(k + 1) * α) = ↑(k + 1) * (-α) by ring]
      rw [Real.exp_nat_mul, hneg1]
    rw [hneg]
    rw [hneg1]
    rw [← hlam]
    rw [ha]
    field_simp [hlam_ne]
    rw [show k.succ - 1 = k by omega]
    have hinv_sq : 1 / lam ^ (2 : ℕ) = lam⁻¹ ^ (2 : ℕ) := by
      field_simp [hlam_ne]
    rw [hinv_sq]
    rw [show lam ^ k * lam = lam ^ k.succ by exact (pow_succ lam k).symm]
    rw [show k + 1 = k.succ by rfl]
    simp only [one_div]
    rw [← pow_mul]
    rw [mul_sub, mul_one]
    rw [pow_mul_inv_pow_double hlam_ne k.succ]

/--
The purely algebraic prefactor rearrangement in PDF Lemma 4.

The exponent `card {i < j}` contributes the factor `n(n-1)/2`; after the
square in `A²λ²`, this becomes `n(n-1)`.
-/
lemma pdf_lemma4_prefactor_algebra
    {n : ℕ} (A lam Q : ℝ) :
    (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
        (upperOffDiagPairs : Finset (Fin n × Fin n)).card
      * Q ^ n
      = A ^ (n * (n - 1)) * (lam ^ (n - 1) * Q) ^ n := by
  let C := (upperOffDiagPairs : Finset (Fin n × Fin n)).card
  have hC : 2 * C = n * (n - 1) := by
    dsimp [C]
    calc
      2 * (upperOffDiagPairs : Finset (Fin n × Fin n)).card
          = n * n - n := two_mul_upperOffDiagPairs_card
      _ = n * (n - 1) := (Nat.mul_sub_one n n).symm
  have hLamExp : (n - 1) * n = n * (n - 1) := by
    rw [Nat.mul_comm]
  dsimp [C] at hC
  calc
    (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
        (upperOffDiagPairs : Finset (Fin n × Fin n)).card * Q ^ n
        = (A ^ (2 : ℕ)) ^ C * (lam ^ (2 : ℕ)) ^ C * Q ^ n := by
          dsimp [C]
          rw [mul_pow]
    _ = A ^ (2 * C) * lam ^ (2 * C) * Q ^ n := by
          rw [show (A ^ (2 : ℕ)) ^ C = A ^ (2 * C) by rw [← pow_mul]]
          rw [show (lam ^ (2 : ℕ)) ^ C = lam ^ (2 * C) by rw [← pow_mul]]
    _ = A ^ (n * (n - 1)) * lam ^ (n * (n - 1)) * Q ^ n := by
          rw [hC]
    _ = A ^ (n * (n - 1)) * (lam ^ (n - 1)) ^ n * Q ^ n := by
          rw [show (lam ^ (n - 1)) ^ n = lam ^ ((n - 1) * n) by
            rw [← pow_mul]]
          rw [hLamExp]
    _ = A ^ (n * (n - 1)) * (lam ^ (n - 1) * Q) ^ n := by
          rw [mul_pow]
          ring

theorem pdf_lemma4_prefactor_bound
    {n : ℕ} {A σ lam a : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ)
    (hlam : lam = Real.exp (Real.arsinh (σ / (2 * A))))
    (ha : a = lam⁻¹ ^ (2 : ℕ)) :
    (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
        (upperOffDiagPairs : Finset (Fin n × Fin n)).card
      * ((1 - a ^ n) / (1 - a)) ^ n
        ≤ quadraticSeparationBound n A σ := by
  let α : ℝ := Real.arsinh (σ / (2 * A))
  let Q : ℝ := (1 - a ^ n) / (1 - a)
  have hα_pos : 0 < α := by
    dsimp [α]
    exact Real.arsinh_pos_iff.mpr (by positivity)
  have hlamα : lam = Real.exp α := by
    simpa [α] using hlam
  have hratio :
      lam ^ (n - 1) * Q = Real.sinh ((n : ℝ) * α) / Real.sinh α := by
    dsimp [Q]
    exact pdf_lemma4_sinh_ratio (n := n) hα_pos hlamα ha
  have halg := pdf_lemma4_prefactor_algebra (n := n) A lam Q
  exact le_of_eq <| by
    calc
      (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card
        * ((1 - a ^ n) / (1 - a)) ^ n
          = (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
              (upperOffDiagPairs : Finset (Fin n × Fin n)).card
            * Q ^ n := by rfl
      _ = A ^ (n * (n - 1)) * (lam ^ (n - 1) * Q) ^ n := halg
      _ = A ^ (n * (n - 1))
            * (Real.sinh ((n : ℝ) * α) / Real.sinh α) ^ n := by
          rw [hratio]
      _ = quadraticSeparationBound n A σ := by
          rfl

/--
PDF Lemma 4, now proved from the PDF Lemma 3 boundary plus the elementary
pointwise and hyperbolic calculations above.

This replaces the previous monolithic Lemma 4 placeholder by a more faithful
decomposition of the PDF proof.
-/
theorem quadraticSeparationProduct_bound
    {n : ℕ} (y : Fin n → ℂ)
    {A σ : ℝ}
    (hA : 0 < A)
    (hσ : 0 < σ)
    (hy : ∀ i, ‖y i‖ ≤ A) :
    quadraticSeparationProduct y σ ≤ quadraticSeparationBound n A σ := by
  let α : ℝ := Real.arsinh (σ / (2 * A))
  let lam : ℝ := Real.exp α
  let a : ℝ := lam⁻¹ ^ (2 : ℕ)
  let x : Fin n → ℂ := fun i => (A : ℂ)⁻¹ * y i
  have hA_nonneg : 0 ≤ A := hA.le
  have hlam_pos : 0 < lam := by dsimp [lam]; positivity
  have hα_pos : 0 < α := by
    dsimp [α]
    exact Real.arsinh_pos_iff.mpr (by positivity)
  have hα_nonneg : 0 ≤ α := hα_pos.le
  have hlam_ge_one : 1 ≤ lam := by
    dsimp [lam]
    exact Real.one_le_exp hα_nonneg
  have hlam_gt_one : 1 < lam := by
    dsimp [lam]
    exact Real.one_lt_exp_iff.mpr hα_pos
  have h0a : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    have hpos_inv : 0 < lam⁻¹ := inv_pos.mpr hlam_pos
    have hlam_inv_lt_one : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam_gt_one
    have hsq_lt : lam⁻¹ * lam⁻¹ < 1 := by
      have hmul : lam⁻¹ * lam⁻¹ < 1 * lam⁻¹ :=
        mul_lt_mul_of_pos_right hlam_inv_lt_one hpos_inv
      have hmul' : lam⁻¹ * lam⁻¹ < lam⁻¹ := by simpa using hmul
      exact hmul'.trans hlam_inv_lt_one
    simpa [pow_two] using hsq_lt
  have hx_unit : ∀ i, ‖x i‖ ≤ 1 := by
    intro i
    have hnormA : ‖(A : ℂ)‖ = A := by
      simp [abs_of_pos hA]
    calc
      ‖x i‖ = ‖(A : ℂ)⁻¹‖ * ‖y i‖ := by
        simp [x]
      _ = A⁻¹ * ‖y i‖ := by
        rw [norm_inv, hnormA]
      _ ≤ A⁻¹ * A := by
        exact mul_le_mul_of_nonneg_left (hy i) (inv_nonneg.mpr hA_nonneg)
      _ = 1 := by
        exact inv_mul_cancel₀ (ne_of_gt hA)
  have hsinh : Real.sinh α = σ / (2 * A) := by
    dsimp [α]
    rw [Real.sinh_arsinh]
  have hlam_sub_inv : lam - lam⁻¹ = 2 * Real.sinh α := by
    dsimp [lam]
    rw [Real.sinh_eq, Real.exp_neg]
    ring
  have hsigma : σ = A * (lam - lam⁻¹) := by
    rw [hlam_sub_inv, hsinh]
    field_simp [ne_of_gt hA]
  have hscale : ∀ i, y i = (A : ℂ) * x i := by
    intro i
    dsimp [x]
    rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact_mod_cast (ne_of_gt hA)
  have hpoint :
      ∀ p ∈ (upperOffDiagPairs : Finset (Fin n × Fin n)),
        ‖y p.1 - y p.2‖ ^ (2 : ℕ) + σ ^ (2 : ℕ)
          ≤ (A ^ (2 : ℕ) * lam ^ (2 : ℕ))
            * ‖1 - (a : ℂ) * x p.1 * (starRingEnd ℂ) (x p.2)‖ ^ (2 : ℕ) := by
    intro p _hp
    exact pdf_lemma4_pointwise_scaled_bound hA hlam_ge_one
      (hscale p.1) (hscale p.2) hsigma rfl (hx_unit p.1) (hx_unit p.2)
  have hfinite :
      quadraticSeparationProduct y σ
        ≤ (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
            (upperOffDiagPairs : Finset (Fin n × Fin n)).card
          * blaschkeOffDiagProduct x a :=
    quadraticSeparationProduct_le_scaled_blaschkeOffDiagProduct y x hpoint
  have hblaschke :
      blaschkeOffDiagProduct x a ≤ ((1 - a ^ n) / (1 - a)) ^ n :=
    blaschkeOffDiagProduct_bound x h0a ha1 hx_unit
  have hscaled :
      (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card
        * blaschkeOffDiagProduct x a
        ≤ (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
            (upperOffDiagPairs : Finset (Fin n × Fin n)).card
          * ((1 - a ^ n) / (1 - a)) ^ n := by
    exact mul_le_mul_of_nonneg_left hblaschke (by positivity)
  have hpref :
      (A ^ (2 : ℕ) * lam ^ (2 : ℕ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card
        * ((1 - a ^ n) / (1 - a)) ^ n
          ≤ quadraticSeparationBound n A σ :=
    pdf_lemma4_prefactor_bound (n := n) hA hσ (by rfl) (by rfl)
  exact hfinite.trans (hscaled.trans hpref)

/-- Nearby points to roots in the unit disk lie in the disk of radius `1 + ε`. -/
lemma norm_w_le_one_add_eps
    {n : ℕ} (z w : Fin n → ℂ)
    {ε : ℝ}
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    ∀ i, ‖w i‖ ≤ 1 + ε := by
  intro i
  calc
    ‖w i‖ = ‖z i + (w i - z i)‖ := by
      congr 1
      ring
    _ ≤ ‖z i‖ + ‖w i - z i‖ := norm_add_le _ _
    _ ≤ 1 + ε := by linarith [hz i, hw i]

/--
General direct-route sum bound for the paired cross terms.

This is the `n`-variable version of the estimate used in the proved cubic
case: Ptolemy gives each cross term as a root-root/w-w product plus `ε²`, and
Cauchy-Schwarz controls the sum of those products by `n²(1+ε)`.
-/
lemma paired_cross_terms_sum_le_direct_average_bound
    {n : ℕ} (z w : Fin n → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
        (fun p => ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖)
      ≤ (n : ℝ) ^ (2 : ℕ) * (1 + ε)
          + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) *
            ε ^ (2 : ℕ) := by
  have hw_radius : ∀ i, ‖w i‖ ≤ 1 + ε :=
    norm_w_le_one_add_eps z w hz hw
  have hA_w : 0 ≤ 1 + ε := by linarith
  have hmulsum :
      (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖)
        ≤ (n : ℝ) ^ (2 : ℕ) * (1 : ℝ) * (1 + ε) := by
    simpa using
      (upper_pair_dist_mul_sum_le_card_sq_mul
        (n := n) z w (A := (1 : ℝ)) (B := 1 + ε)
        (by norm_num) hA_w hz hw_radius)
  have hsum_le :
      (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖)
        ≤ (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖
            + ε ^ (2 : ℕ)) := by
    exact Finset.sum_le_sum
      (fun p _hp => paired_cross_terms_le_mul_add_sq z w hε le_rfl hw p)
  calc
    (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
        (fun p => ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖)
        ≤ (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖
            + ε ^ (2 : ℕ)) := hsum_le
    _ = (upperOffDiagPairs : Finset (Fin n × Fin n)).sum
          (fun p => ‖z p.1 - z p.2‖ * ‖w p.1 - w p.2‖)
        + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) *
          ε ^ (2 : ℕ) := by
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ (2 : ℕ) * (1 + ε)
        + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) *
          ε ^ (2 : ℕ) := by
          nlinarith

/--
AM-GM form of the direct-route off-diagonal bound.

The left side is the geometric mean of the paired cross terms; the right side
is the average supplied by `paired_cross_terms_sum_le_direct_average_bound`.
-/
lemma pairedOffDiagProduct_rpow_inv_card_le_direct_average_bound
    {n : ℕ} (z w : Fin n → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε)
    (hcard : 0 < (upperOffDiagPairs : Finset (Fin n × Fin n)).card) :
    (pairedOffDiagProduct z w) ^
        (((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)⁻¹)
      ≤ (((n : ℝ) ^ (2 : ℕ) * (1 + ε)
          + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) *
            ε ^ (2 : ℕ)) /
        ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)) := by
  let s : Finset (Fin n × Fin n) := upperOffDiagPairs
  let f : Fin n × Fin n → ℝ :=
    fun p => ‖w p.1 - z p.2‖ * ‖w p.2 - z p.1‖
  have hcard_pos : 0 < (s.card : ℝ) :=
    Nat.cast_pos.mpr (by simpa [s] using hcard)
  have hgm := Real.geom_mean_le_arith_mean
    (s := s)
    (w := fun _ : Fin n × Fin n => (1 : ℝ))
    (z := f)
    (by intro _p _hp; norm_num)
    (by simpa [s, hcard_pos.ne'] using hcard_pos)
    (by
      intro p _hp
      dsimp [f]
      positivity)
  have hgm' :
      (pairedOffDiagProduct z w) ^ (s.card : ℝ)⁻¹
        ≤ (∑ p ∈ s, f p) / (s.card : ℝ) := by
    simpa [pairedOffDiagProduct, s, f, Finset.sum_const, hcard_pos.ne',
      div_eq_mul_inv] using hgm
  have hsum :
      (∑ p ∈ s, f p)
        ≤ (n : ℝ) ^ (2 : ℕ) * (1 + ε) + (s.card : ℝ) * ε ^ (2 : ℕ) := by
    dsimp [s, f]
    simpa using paired_cross_terms_sum_le_direct_average_bound z w hε hz hw
  have hdiv :
      (∑ p ∈ s, f p) / (s.card : ℝ)
        ≤ (((n : ℝ) ^ (2 : ℕ) * (1 + ε)
            + (s.card : ℝ) * ε ^ (2 : ℕ)) / (s.card : ℝ)) := by
    exact div_le_div_of_nonneg_right hsum hcard_pos.le
  exact hgm'.trans hdiv

/--
The same direct AM-GM estimate after raising back to the number of unordered
pairs.
-/
lemma pairedOffDiagProduct_le_direct_average_bound_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (z w : Fin n → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    pairedOffDiagProduct z w
      ≤ (((n : ℝ) ^ (2 : ℕ) * (1 + ε)
          + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) *
            ε ^ (2 : ℕ)) /
        ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card := by
  let s : Finset (Fin n × Fin n) := upperOffDiagPairs
  let B : ℝ := (((n : ℝ) ^ (2 : ℕ) * (1 + ε)
      + (s.card : ℝ) * ε ^ (2 : ℕ)) / (s.card : ℝ))
  have hcard_pos_nat : 0 < s.card := by
    simpa [s] using upperOffDiagPairs_card_pos_of_two_le hn
  have hcard_ne : s.card ≠ 0 := Nat.ne_of_gt hcard_pos_nat
  have hprod_nonneg : 0 ≤ pairedOffDiagProduct z w := by
    unfold pairedOffDiagProduct
    exact Finset.prod_nonneg
      (fun p _hp => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hroot :
      (pairedOffDiagProduct z w) ^ ((s.card : ℝ)⁻¹) ≤ B := by
    dsimp [B, s]
    exact pairedOffDiagProduct_rpow_inv_card_le_direct_average_bound
      z w hε hz hw (upperOffDiagPairs_card_pos_of_two_le hn)
  have hpow :=
    pow_le_pow_left₀
      (Real.rpow_nonneg hprod_nonneg ((s.card : ℝ)⁻¹))
      hroot
      s.card
  have hleft :
      ((pairedOffDiagProduct z w) ^ ((s.card : ℝ)⁻¹)) ^ s.card
        = pairedOffDiagProduct z w := by
    exact Real.rpow_inv_natCast_pow hprod_nonneg hcard_ne
  rw [hleft] at hpow
  dsimp [B, s] at hpow ⊢
  exact hpow

/-- Direct-route estimate for the full off-diagonal product. -/
lemma offDiagProduct_le_direct_average_bound_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (z w : Fin n → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    offDiagProduct z w
      ≤ (((n : ℝ) ^ (2 : ℕ) * (1 + ε)
          + ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ) *
            ε ^ (2 : ℕ)) /
        ((upperOffDiagPairs : Finset (Fin n × Fin n)).card : ℝ)) ^
          (upperOffDiagPairs : Finset (Fin n × Fin n)).card := by
  rw [offDiagProduct_eq_pairedOffDiagProduct]
  exact pairedOffDiagProduct_le_direct_average_bound_of_two_le hn z w hε hz hw

/-- Direct-route off-diagonal estimate with `#pairs = n.choose 2`. -/
lemma offDiagProduct_le_direct_average_bound_choose_two_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (z w : Fin n → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    offDiagProduct z w
      ≤ (((n : ℝ) ^ (2 : ℕ) * (1 + ε)
          + (n.choose 2 : ℝ) * ε ^ (2 : ℕ)) /
        (n.choose 2 : ℝ)) ^ n.choose 2 := by
  simpa [upperOffDiagPairs_card] using
    offDiagProduct_le_direct_average_bound_of_two_le hn z w hε hz hw

/--
The direct-route average after substituting `#pairs = n.choose 2`.

For large `n` this average is roughly `2(1+ε) + ε²`; for `n = 3` it is exactly
`3 + 3ε + ε²`, which is why the cubic case closes cleanly.
-/
lemma direct_average_bound_choose_two_eq_explicit
    {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) :
    (((n : ℝ) ^ (2 : ℕ) * (1 + ε)
        + (n.choose 2 : ℝ) * ε ^ (2 : ℕ)) /
      (n.choose 2 : ℝ))
      = (2 * (n : ℝ) / ((n : ℝ) - 1)) * (1 + ε)
          + ε ^ (2 : ℕ) := by
  have hn_real : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hn_minus_pos : 0 < (n : ℝ) - 1 := by linarith
  rw [Nat.cast_choose_two]
  field_simp [hn_minus_pos.ne', (by norm_num : (2 : ℝ) ≠ 0)]

/-- Direct-route off-diagonal estimate in explicit average form. -/
lemma offDiagProduct_le_explicit_direct_average_bound_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (z w : Fin n → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    offDiagProduct z w
      ≤ ((2 * (n : ℝ) / ((n : ℝ) - 1)) * (1 + ε)
          + ε ^ (2 : ℕ)) ^ n.choose 2 := by
  simpa [direct_average_bound_choose_two_eq_explicit hn ε] using
    offDiagProduct_le_direct_average_bound_choose_two_of_two_le hn z w hε hz hw

/--
If a point is outside `{w | ‖f(w)‖ < 1}`, then `1 ≤ ‖f(w)‖`.
This tiny order lemma is one of the steps needed for the contradiction.
-/
lemma one_le_norm_fval_of_not_mem_lemniscate
    {n : ℕ} (z : Fin n → ℂ) {w : ℂ}
    (hw : w ∉ lemniscate z) :
    1 ≤ ‖fval z w‖ := by
  dsimp [lemniscate] at hw
  exact le_of_not_gt hw

/-- From lower bounds on every factor, get a lower bound on the finite product. -/
lemma one_le_prod_of_one_le
    {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ j, 1 ≤ a j) :
    1 ≤ ∏ j : Fin n, a j := by
  simpa using Finset.one_le_prod (s := Finset.univ) (f := a) (fun j _ => ha j)

/-- If every chosen point lies outside the lemniscate, the value product is at least `1`. -/
lemma one_le_prod_norm_fval_of_all_not_mem
    {n : ℕ} (z w : Fin n → ℂ)
    (hw : ∀ j, w j ∉ lemniscate z) :
    1 ≤ ∏ j : Fin n, ‖fval z (w j)‖ := by
  apply one_le_prod_of_one_le
  intro j
  exact one_le_norm_fval_of_not_mem_lemniscate z (hw j)

/--
The witness-selection step:
if no zero-centered ball is contained in the lemniscate, choose one bad point
near every zero.
-/
lemma choose_bad_points
    {n : ℕ} {r : ℝ} (z : Fin n → ℂ)
    (hbad : ∀ j : Fin n, ¬ Metric.ball (z j) r ⊆ lemniscate z) :
    ∃ w : Fin n → ℂ,
      (∀ j : Fin n, w j ∈ Metric.ball (z j) r)
        ∧ (∀ j : Fin n, w j ∉ lemniscate z) := by
  classical
  choose w hw using fun j => Set.not_subset.mp (hbad j)
  exact ⟨w, fun j => (hw j).1, fun j => (hw j).2⟩

/-- For nonnegative `x`, `arsinh x ≤ x`. -/
lemma arsinh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.arsinh x ≤ x := by
  rw [← Real.sinh_le_sinh]
  rw [Real.sinh_arsinh]
  exact (Real.self_le_sinh_iff).2 hx

/--
The first hyperbolic ratio estimate used on page 5 of the PDF:
with `α = arsinh (c/(2n))`,
`sinh(nα)/sinh α ≤ (2n/c) sinh(c/2)`.
-/
lemma pdf_page5_sinh_ratio_one_le
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) :
    let α : ℝ := Real.arsinh (c / (2 * (n : ℝ)))
    Real.sinh ((n : ℝ) * α) / Real.sinh α
      ≤ (2 * (n : ℝ) / c) * Real.sinh (c / 2) := by
  intro α
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hxpos : 0 < c / (2 * (n : ℝ)) := by positivity
  have hαpos : 0 < α := by
    dsimp [α]
    exact Real.arsinh_pos_iff.mpr hxpos
  have hαle : α ≤ c / (2 * (n : ℝ)) := by
    dsimp [α]
    exact arsinh_le_self_of_nonneg hxpos.le
  have hmul : (n : ℝ) * α ≤ c / 2 := by
    calc
      (n : ℝ) * α ≤ (n : ℝ) * (c / (2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hαle hnpos.le
      _ = c / 2 := by field_simp [ne_of_gt hnpos]
  have hsinh_le : Real.sinh ((n : ℝ) * α) ≤ Real.sinh (c / 2) :=
    Real.sinh_le_sinh.mpr hmul
  have hdenpos : 0 < Real.sinh α :=
    Real.sinh_pos_iff.mpr hαpos
  calc
    Real.sinh ((n : ℝ) * α) / Real.sinh α
        ≤ Real.sinh (c / 2) / Real.sinh α :=
          div_le_div_of_nonneg_right hsinh_le hdenpos.le
    _ = (2 * (n : ℝ) / c) * Real.sinh (c / 2) := by
          have hden : Real.sinh α = c / (2 * (n : ℝ)) := by
            dsimp [α]
            rw [Real.sinh_arsinh]
          rw [hden]
          field_simp [ne_of_gt hc0, ne_of_gt hnpos]

/--
The second hyperbolic ratio estimate used on page 5 of the PDF:
with `β = arsinh ((c/n)/(2(1+c/n)))`,
`sinh(nβ)/sinh β ≤ (2n(1+c/n)/c) sinh(c/2)`.
-/
lemma pdf_page5_sinh_ratio_one_add_le
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) :
    let β : ℝ := Real.arsinh ((c / (n : ℝ)) / (2 * (1 + c / (n : ℝ))))
    Real.sinh ((n : ℝ) * β) / Real.sinh β
      ≤ (2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2) := by
  intro β
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hε_nonneg : 0 ≤ c / (n : ℝ) := div_nonneg hc0.le hnpos.le
  have hApos : 0 < 1 + c / (n : ℝ) := by positivity
  have hxpos : 0 < (c / (n : ℝ)) / (2 * (1 + c / (n : ℝ))) := by
    positivity
  have hβpos : 0 < β := by
    dsimp [β]
    exact Real.arsinh_pos_iff.mpr hxpos
  have hβle : β ≤ (c / (n : ℝ)) / (2 * (1 + c / (n : ℝ))) := by
    dsimp [β]
    exact arsinh_le_self_of_nonneg hxpos.le
  have hmul_arg :
      (n : ℝ) * ((c / (n : ℝ)) / (2 * (1 + c / (n : ℝ))))
        = c / (2 * (1 + c / (n : ℝ))) := by
    field_simp [ne_of_gt hnpos]
  have harg_le : c / (2 * (1 + c / (n : ℝ))) ≤ c / 2 := by
    field_simp [ne_of_gt hApos]
    nlinarith [mul_nonneg hc0.le hε_nonneg]
  have hmul : (n : ℝ) * β ≤ c / 2 := by
    calc
      (n : ℝ) * β
          ≤ (n : ℝ) * ((c / (n : ℝ)) / (2 * (1 + c / (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left hβle hnpos.le
      _ = c / (2 * (1 + c / (n : ℝ))) := hmul_arg
      _ ≤ c / 2 := harg_le
  have hsinh_le : Real.sinh ((n : ℝ) * β) ≤ Real.sinh (c / 2) :=
    Real.sinh_le_sinh.mpr hmul
  have hdenpos : 0 < Real.sinh β :=
    Real.sinh_pos_iff.mpr hβpos
  calc
    Real.sinh ((n : ℝ) * β) / Real.sinh β
        ≤ Real.sinh (c / 2) / Real.sinh β :=
          div_le_div_of_nonneg_right hsinh_le hdenpos.le
    _ = (2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2) := by
          have hden :
              Real.sinh β = (c / (n : ℝ)) / (2 * (1 + c / (n : ℝ))) := by
            dsimp [β]
            rw [Real.sinh_arsinh]
          rw [hden]
          field_simp [ne_of_gt hc0, ne_of_gt hnpos, ne_of_gt hApos]

/-- Page-5 bound for Lemma 4 applied to the roots, with `A = 1`. -/
lemma quadraticSeparationBound_page5_one_le
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) :
    quadraticSeparationBound n 1 (c / (n : ℝ))
      ≤ ((2 * (n : ℝ) / c) * Real.sinh (c / 2)) ^ n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  let α : ℝ := Real.arsinh (c / (2 * (n : ℝ)))
  have hαpos : 0 < α := by
    dsimp [α]
    exact Real.arsinh_pos_iff.mpr (by positivity)
  have hratio_nonneg :
      0 ≤ Real.sinh ((n : ℝ) * α) / Real.sinh α := by
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hnpos.le hαpos.le))
      (Real.sinh_nonneg_iff.mpr hαpos.le)
  have hratio :=
    pdf_page5_sinh_ratio_one_le (n := n) hn (c := c) hc0
  have hpow :=
    pow_le_pow_left₀ hratio_nonneg hratio n
  dsimp [quadraticSeparationBound] at hpow ⊢
  simpa [α, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpow

/-- Page-5 bound for Lemma 4 applied to the nearby points, with `A = 1 + c/n`. -/
lemma quadraticSeparationBound_page5_one_add_le
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) :
    quadraticSeparationBound n (1 + c / (n : ℝ)) (c / (n : ℝ))
      ≤ (1 + c / (n : ℝ)) ^ (n * (n - 1))
          * ((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) ^ n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hApos : 0 < 1 + c / (n : ℝ) := by positivity
  let β : ℝ := Real.arsinh ((c / (n : ℝ)) / (2 * (1 + c / (n : ℝ))))
  have hβpos : 0 < β := by
    dsimp [β]
    exact Real.arsinh_pos_iff.mpr (by positivity)
  have hratio_nonneg :
      0 ≤ Real.sinh ((n : ℝ) * β) / Real.sinh β := by
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hnpos.le hβpos.le))
      (Real.sinh_nonneg_iff.mpr hβpos.le)
  have hratio :=
    pdf_page5_sinh_ratio_one_add_le (n := n) hn (c := c) hc0
  have hpow :=
    pow_le_pow_left₀ hratio_nonneg hratio n
  have hmul :=
    mul_le_mul_of_nonneg_left hpow
      (pow_nonneg (le_of_lt hApos) (n * (n - 1)))
  dsimp [quadraticSeparationBound] at hmul ⊢
  simpa [β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

/--
The PDF Lemma 5 scale after substituting `ε = σ = c/n`, reduced to the
explicit page-5 hyperbolic expression before the final simplification to
`(exp c - 1)`.
-/
lemma pdf_page5_scale_bound_le_raw_expression
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) :
    ((c / (n : ℝ)) ^ n) ^ (2 : ℕ)
        * (quadraticSeparationBound n 1 (c / (n : ℝ))
            * quadraticSeparationBound n (1 + c / (n : ℝ)) (c / (n : ℝ)))
      ≤ ((c / (n : ℝ)) ^ n) ^ (2 : ℕ)
        * ((((2 * (n : ℝ) / c) * Real.sinh (c / 2)) ^ n)
          * ((1 + c / (n : ℝ)) ^ (n * (n - 1))
            * (((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) ^ n))) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hApos : 0 < 1 + c / (n : ℝ) := by positivity
  have hσpos : 0 < c / (n : ℝ) := div_pos hc0 hnpos
  have hq1 := quadraticSeparationBound_page5_one_le (n := n) hn (c := c) hc0
  have hq2 := quadraticSeparationBound_page5_one_add_le (n := n) hn (c := c) hc0
  have hq2_nonneg :
      0 ≤ quadraticSeparationBound n (1 + c / (n : ℝ)) (c / (n : ℝ)) := by
    exact (quadraticSeparationProduct_nonneg (fun _ : Fin n => (0 : ℂ))
      (c / (n : ℝ))).trans
        (quadraticSeparationProduct_bound
          (fun _ : Fin n => (0 : ℂ))
          (A := 1 + c / (n : ℝ)) (σ := c / (n : ℝ))
          hApos hσpos (by intro i; simp; positivity))
  have hq1_bound_nonneg :
      0 ≤ ((2 * (n : ℝ) / c) * Real.sinh (c / 2)) ^ n := by
    positivity
  have hprod :
      quadraticSeparationBound n 1 (c / (n : ℝ))
          * quadraticSeparationBound n (1 + c / (n : ℝ)) (c / (n : ℝ))
        ≤ (((2 * (n : ℝ) / c) * Real.sinh (c / 2)) ^ n)
          * ((1 + c / (n : ℝ)) ^ (n * (n - 1))
            * (((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) ^ n)) :=
    mul_le_mul hq1 hq2 hq2_nonneg hq1_bound_nonneg
  exact mul_le_mul_of_nonneg_left hprod (sq_nonneg ((c / (n : ℝ)) ^ n))

/-- Pure algebra for compressing the page-5 raw expression. -/
lemma page5_raw_expression_algebra
    (r A t : ℝ) {n : ℕ} (hn : 0 < n) :
    ((r ^ n) ^ (2 : ℕ)) * (A ^ n * (t ^ (n * (n - 1)) * ((A * t) ^ n)))
      = (r * A) ^ (2 * n) * t ^ (n * n) := by
  rw [mul_pow]
  rw [← mul_assoc (A ^ n) (t ^ (n * (n - 1))) (A ^ n * t ^ n)]
  rw [mul_assoc (A ^ n) (t ^ (n * (n - 1))) (A ^ n * t ^ n)]
  have ht : t ^ n * t ^ (n * (n - 1)) = t ^ (n ^ (2 : ℕ)) := by
    rw [← pow_add]
    have hexp : n + n * (n - 1) = n ^ (2 : ℕ) := by
      rw [pow_two]
      calc
        n + n * (n - 1) = n * 1 + n * (n - 1) := by rw [Nat.mul_one]
        _ = n * (1 + (n - 1)) := by rw [Nat.mul_add]
        _ = n * n := by
          have hlin : 1 + (n - 1) = n := by omega
          rw [hlin]
    rw [hexp]
  ring_nf
  rw [show r ^ (n * 2) * A ^ (n * 2) * t ^ n * t ^ (n * (n - 1)) =
      r ^ (n * 2) * A ^ (n * 2) * (t ^ n * t ^ (n * (n - 1))) by ring]
  rw [ht]

/-- The page-5 raw expression compressed to the two visible factors. -/
lemma pdf_page5_raw_expression_eq_simplified
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) :
    ((c / (n : ℝ)) ^ n) ^ (2 : ℕ)
        * ((((2 * (n : ℝ) / c) * Real.sinh (c / 2)) ^ n)
          * ((1 + c / (n : ℝ)) ^ (n * (n - 1))
            * (((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) ^ n)))
      =
        (2 * Real.sinh (c / 2)) ^ (2 * n)
          * (1 + c / (n : ℝ)) ^ (n * n) := by
  let r : ℝ := c / (n : ℝ)
  let A : ℝ := (2 * (n : ℝ) / c) * Real.sinh (c / 2)
  let t : ℝ := 1 + c / (n : ℝ)
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hC :
      ((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) = A * t := by
    dsimp [A, t]
    field_simp [hcne]
  have hrA : r * A = 2 * Real.sinh (c / 2) := by
    dsimp [r, A]
    field_simp [hnne, hcne]
  change
    ((r ^ n) ^ (2 : ℕ)) * (A ^ n * (t ^ (n * (n - 1)) *
        (((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) ^ n)))
      =
        (2 * Real.sinh (c / 2)) ^ (2 * n) * t ^ (n * n)
  rw [hC]
  rw [page5_raw_expression_algebra r A t hn]
  rw [hrA]

/-- Standard estimate `(1 + c/n)^n ≤ exp c`, for `c ≥ 0`. -/
lemma one_add_div_pow_le_exp
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 ≤ c) :
    (1 + c / (n : ℝ)) ^ n ≤ Real.exp c := by
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_real_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  have hε_nonneg : 0 ≤ c / (n : ℝ) := div_nonneg hc0 hn_real_pos.le
  have hsum : (∑ _i : Fin n, c / (n : ℝ)) = c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    exact div_mul_cancel₀ c hn_real_ne
  calc
    (1 + c / (n : ℝ)) ^ n ≤ (Real.exp (c / (n : ℝ))) ^ n := by
        have hbase : 1 + c / (n : ℝ) ≤ Real.exp (c / (n : ℝ)) := by
          simpa [add_comm] using Real.add_one_le_exp (c / (n : ℝ))
        exact pow_le_pow_left₀ (by positivity) hbase n
    _ = Real.exp (∑ _i : Fin n, c / (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.exp c := by rw [hsum]

/--
The page-5 exponential estimate in squared form:
`(1+c/n)^(n^2) ≤ exp(c/2)^(2n)`.
-/
lemma one_add_div_pow_square_le_exp_half_pow
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 ≤ c) :
    (1 + c / (n : ℝ)) ^ (n * n) ≤ Real.exp (c / 2) ^ (2 * n) := by
  have ht_nonneg : 0 ≤ 1 + c / (n : ℝ) := by positivity
  have hpow := one_add_div_pow_le_exp hn hc0
  have hpow_n :
      ((1 + c / (n : ℝ)) ^ n) ^ n ≤ (Real.exp c) ^ n :=
    pow_le_pow_left₀ (pow_nonneg ht_nonneg n) hpow n
  have hexp_half_sq : Real.exp (c / 2) ^ (2 : ℕ) = Real.exp c := by
    rw [sq, ← Real.exp_add]
    ring_nf
  calc
    (1 + c / (n : ℝ)) ^ (n * n)
        = ((1 + c / (n : ℝ)) ^ n) ^ n := by rw [pow_mul]
    _ ≤ (Real.exp c) ^ n := hpow_n
    _ = Real.exp (c / 2) ^ (2 * n) := by
        rw [← hexp_half_sq, pow_mul]

/-- The hyperbolic factor on page 5 simplifies to `exp c - 1`. -/
lemma two_exp_half_mul_sinh_half (c : ℝ) :
    2 * Real.exp (c / 2) * Real.sinh (c / 2) = Real.exp c - 1 := by
  rw [Real.sinh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  rw [show Real.exp (c / 2) ^ (2 : ℕ) = Real.exp c by
    rw [sq, ← Real.exp_add]
    ring_nf]

/-- If `0 < c < log 2`, then the final PDF page-5 factor is strictly below `1`. -/
lemma exp_sub_one_pow_two_mul_lt_one
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) (hclog : c < Real.log 2) :
    (Real.exp c - 1) ^ (2 * n) < 1 := by
  have hexp_lt_two : Real.exp c < 2 :=
    (Real.lt_log_iff_exp_lt zero_lt_two).1 hclog
  have hbase_nonneg : 0 ≤ Real.exp c - 1 := by
    linarith [Real.one_lt_exp_iff.mpr hc0]
  have hbase_lt_one : Real.exp c - 1 < 1 := by
    linarith
  exact pow_lt_one₀ hbase_nonneg hbase_lt_one (by omega)

/-- The page-5 raw expression is bounded by `(exp c - 1)^(2n)`. -/
lemma pdf_page5_raw_expression_le_exp_sub_one_pow
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) :
    ((c / (n : ℝ)) ^ n) ^ (2 : ℕ)
        * ((((2 * (n : ℝ) / c) * Real.sinh (c / 2)) ^ n)
          * ((1 + c / (n : ℝ)) ^ (n * (n - 1))
            * (((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) ^ n)))
      ≤ (Real.exp c - 1) ^ (2 * n) := by
  have hraw := pdf_page5_raw_expression_eq_simplified (n := n) hn (c := c) hc0
  have hT := one_add_div_pow_square_le_exp_half_pow (n := n) hn (c := c) hc0.le
  have hs_nonneg : 0 ≤ 2 * Real.sinh (c / 2) := by positivity
  calc
    ((c / (n : ℝ)) ^ n) ^ (2 : ℕ)
        * ((((2 * (n : ℝ) / c) * Real.sinh (c / 2)) ^ n)
          * ((1 + c / (n : ℝ)) ^ (n * (n - 1))
            * (((2 * (n : ℝ) * (1 + c / (n : ℝ)) / c) * Real.sinh (c / 2)) ^ n)))
        = (2 * Real.sinh (c / 2)) ^ (2 * n)
          * (1 + c / (n : ℝ)) ^ (n * n) := hraw
    _ ≤ (2 * Real.sinh (c / 2)) ^ (2 * n)
          * Real.exp (c / 2) ^ (2 * n) := by
          exact mul_le_mul_of_nonneg_left hT (pow_nonneg hs_nonneg (2 * n))
    _ = (2 * Real.sinh (c / 2) * Real.exp (c / 2)) ^ (2 * n) := by
          rw [← mul_pow]
    _ = (Real.exp c - 1) ^ (2 * n) := by
          have hfactor :
              2 * Real.sinh (c / 2) * Real.exp (c / 2)
                = 2 * Real.exp (c / 2) * Real.sinh (c / 2) := by ring
          rw [hfactor, two_exp_half_mul_sinh_half c]

/-- The final scalar estimate on page 5 of the PDF. -/
lemma pdf_page5_scale_bound_lt_one
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc0 : 0 < c) (hclog : c < Real.log 2) :
    ((c / (n : ℝ)) ^ n) ^ (2 : ℕ)
        * (quadraticSeparationBound n 1 (c / (n : ℝ))
            * quadraticSeparationBound n (1 + c / (n : ℝ)) (c / (n : ℝ)))
          < 1 := by
  exact (pdf_page5_scale_bound_le_raw_expression (n := n) hn (c := c) hc0).trans_lt
    ((pdf_page5_raw_expression_le_exp_sub_one_pow (n := n) hn (c := c) hc0).trans_lt
      (exp_sub_one_pow_two_mul_lt_one (n := n) hn (c := c) hc0 hclog))

/--
PDF Lemma 5, stated in a squared form to avoid introducing square roots.

This is the product estimate actually used in the PDF proof of #1039.  It is
exactly suited to the final substitution `ε = σ = c / n`.
-/
theorem pdf_lemma5_product_bound_sq
    {n : ℕ} (z w : Fin n → ℂ)
    {ε σ : ℝ}
    (hε : 0 ≤ ε)
    (hσ : 0 < σ)
    (hεσ : ε ≤ σ)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    (hw : ∀ i, ‖w i - z i‖ ≤ ε) :
    (∏ j : Fin n, ‖fval z (w j)‖) ^ (2 : ℕ)
      ≤ (ε ^ n) ^ (2 : ℕ)
          * (quadraticSeparationBound n 1 σ
              * quadraticSeparationBound n (1 + ε) σ) := by
  have hbase :=
    prod_norm_fval_sq_le_quadraticSeparationProduct_mul z w hε hεσ hw
  have hzquad :
      quadraticSeparationProduct z σ ≤ quadraticSeparationBound n 1 σ :=
    quadraticSeparationProduct_bound z (A := 1) (σ := σ) zero_lt_one hσ hz
  have hw_radius : ∀ i, ‖w i‖ ≤ 1 + ε :=
    norm_w_le_one_add_eps z w hz hw
  have hA_w : 0 < 1 + ε := by linarith
  have hwquad :
      quadraticSeparationProduct w σ ≤ quadraticSeparationBound n (1 + ε) σ :=
    quadraticSeparationProduct_bound w (A := 1 + ε) (σ := σ) hA_w hσ hw_radius
  have hbound_z_nonneg : 0 ≤ quadraticSeparationBound n 1 σ :=
    (quadraticSeparationProduct_nonneg z σ).trans hzquad
  have hquad_prod :
      quadraticSeparationProduct z σ * quadraticSeparationProduct w σ
        ≤ quadraticSeparationBound n 1 σ
            * quadraticSeparationBound n (1 + ε) σ := by
    exact mul_le_mul hzquad hwquad
      (quadraticSeparationProduct_nonneg w σ)
      hbound_z_nonneg
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hquad_prod (sq_nonneg (ε ^ n)))

/--
The contradiction step in the #1039 proof only needs a strict product upper
bound `< 1` at the chosen scale.
-/
theorem exists_zero_centered_disk_of_product_lt_one_at_scale
    {n : ℕ} (_hn : 0 < n)
    (z : Fin n → ℂ)
    {r : ℝ}
    (hproduct :
      ∀ w : Fin n → ℂ,
        (∀ i, ‖w i - z i‖ ≤ r) →
          (∏ j : Fin n, ‖fval z (w j)‖) < 1) :
    ∃ j : Fin n,
      Metric.ball (z j) r ⊆ lemniscate z := by
  classical
  by_contra hnone
  have hbad : ∀ j : Fin n, ¬ Metric.ball (z j) r ⊆ lemniscate z := by
    intro j hj
    exact hnone ⟨j, hj⟩
  rcases choose_bad_points z hbad with ⟨w, hw_ball, hw_not_mem⟩
  have hw_close : ∀ j : Fin n, ‖w j - z j‖ ≤ r := by
    intro j
    have hdist : dist (w j) (z j) < r := by
      simpa [Metric.mem_ball, dist_comm] using hw_ball j
    calc
      ‖w j - z j‖ = dist (w j) (z j) := by
        simp [dist_eq_norm]
      _ ≤ r := le_of_lt hdist
  have h_lower : 1 ≤ ∏ j : Fin n, ‖fval z (w j)‖ :=
    one_le_prod_norm_fval_of_all_not_mem z w hw_not_mem
  exact not_lt_of_ge h_lower (hproduct w hw_close)

/--
If the PDF Lemma 5 squared upper bound is already known to be `< 1` after the
substitution `ε = σ = c/n`, then the zero-centered disk conclusion follows.

The remaining scalar inequality is exactly the final hyperbolic estimate on
page 5 of the PDF.
-/
theorem erdos1039_from_pdf_lemma5_sq_scale_bound
    {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    {c : ℝ} (hc0 : 0 < c)
    (hscale :
      ((c / (n : ℝ)) ^ n) ^ (2 : ℕ)
        * (quadraticSeparationBound n 1 (c / (n : ℝ))
            * quadraticSeparationBound n (1 + c / (n : ℝ)) (c / (n : ℝ)))
          < 1) :
    ∃ j : Fin n,
      Metric.ball (z j) (c / (n : ℝ)) ⊆ lemniscate z := by
  apply exists_zero_centered_disk_of_product_lt_one_at_scale hn z
  intro w hw_close
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hε : 0 ≤ c / (n : ℝ) := div_nonneg hc0.le hn_real_pos.le
  have hσ : 0 < c / (n : ℝ) := div_pos hc0 hn_real_pos
  have hsq :=
    pdf_lemma5_product_bound_sq z w
      (ε := c / (n : ℝ)) (σ := c / (n : ℝ))
      hε hσ le_rfl hz hw_close
  have hprod_sq_lt :
      (∏ j : Fin n, ‖fval z (w j)‖) ^ (2 : ℕ) < 1 :=
    lt_of_le_of_lt hsq hscale
  have hprod_nonneg : 0 ≤ ∏ j : Fin n, ‖fval z (w j)‖ :=
    prod_norm_fval_nonneg z w
  exact (sq_lt_one_iff₀ hprod_nonneg).1 hprod_sq_lt

/--
Erdos Problems #1039, proved through the PDF Lemma 5 route.

If `f(w) = ∏ i, (w - z_i)` and all zeros `z_i` lie in the closed unit disk,
then for every `0 < c < log 2` one of the zero-centered disks
`ball (z_j) (c / n)` is contained in the lemniscate `{w | |f(w)| < 1}`.

This proof uses PDF Lemma 5, the page-5 scalar estimate, and the contradiction
argument.
-/
theorem erdos1039
    {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1)
    {c : ℝ} (hc0 : 0 < c) (hclog : c < Real.log 2) :
    ∃ j : Fin n,
      Metric.ball (z j) (c / (n : ℝ)) ⊆ lemniscate z := by
  exact erdos1039_from_pdf_lemma5_sq_scale_bound hn z hz hc0
    (pdf_page5_scale_bound_lt_one hn hc0 hclog)


/-- Exact complete Jig p366 root, using the positive universal constant (log 2)/2. -/
theorem proof :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 0 < n → ∀ roots : Fin n → ℂ,
        (∀ i, ‖roots i‖ ≤ 1) →
        ∃ center : ℂ, ∀ z : ℂ,
          dist z center < c / n →
            ‖(∏ i, (z - roots i))‖ < 1 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 2, by positivity, ?_⟩
  intro n hn roots hr
  obtain ⟨j, hj⟩ := erdos1039 hn roots hr (by positivity : 0 < Real.log 2 / 2)
    (by linarith : Real.log 2 / 2 < Real.log 2)
  exact ⟨roots j, fun z hz => hj hz⟩

end Submissions.Erdos1039LemniscateInradius.KitamuraPort

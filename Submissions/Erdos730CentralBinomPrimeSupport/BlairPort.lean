/-
Full proof port of William Blair's public Erdős 730 formalization.
Original informal argument: Liam Price, June 24, 2026.
Analytic dependency: PrimeNumberTheoremAnd and its contributors.
Original source: https://github.com/williamjblair/lean-proofs
Pinned Lean 4.33.0 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
PNT dependency: ajirving/PrimeNumberTheoremAnd at commit 769d3b81fb.
This is a prior-art proof port, not a claim of a new mathematical solution.
Original author comments and mathematical proof bodies are retained below.
Blueprint metadata, two unused admitted PNT declarations and the unused dependent decay_alt are omitted.
-/
/-
Upstream license: Will Blair (MIT)
MIT License

Copyright (c) 2026 Will Blair

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-
Upstream license: PrimeNumberTheoremAnd (Apache 2.0)
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
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Mathlib.Data.List.Indexes

set_option maxHeartbeats 0
set_option maxRecDepth 4000

/- Source module: ErdosProblems.Erdos730.KummerTransition -/
section Campaign180File0
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: Kummer and the lower-half digit criterion

This module formalizes the exact transition from Kummer's theorem to the
digit set `D_p` used in equation (4) of the positive-density proof.

For an odd prime `p`, `LowerHalfDigits p t` says that every base-`p` digit
of `t` is at most `(p-1)/2`.  We prove

`p ∤ centralBinom t ↔ LowerHalfDigits p t`.

The intermediate predicate `NoSelfCarry` is an exact prefix-remainder form
of saying that adding `t+t` creates no base-`p` carry.  The proof imports
mathlib's kernel-checked `Nat.factorization_choose'`; it introduces no
analytic hypothesis and no new axiom.
-/

namespace Erdos730
namespace KummerTransition

open Finset

/-- A carry occurs at depth `i` when the two length-`i` base-`p` prefixes
of `t` sum to at least `p^i`. -/
def SelfCarryAt (p t i : ℕ) : Prop :=
  p ^ i ≤ t % p ^ i + t % p ^ i

instance selfCarryAtDecidable (p t i : ℕ) : Decidable (SelfCarryAt p t i) := by
  unfold SelfCarryAt
  infer_instance

/-- There is no carry at any positive base-`p` prefix depth. -/
def NoSelfCarry (p t : ℕ) : Prop :=
  ∀ i, 0 < i → ¬SelfCarryAt p t i

/-- The digit set `D_p` from the paper. -/
def LowerHalfDigits (p t : ℕ) : Prop :=
  ∀ d ∈ p.digits t, d ≤ (p - 1) / 2

/-- Mathlib's Kummer theorem specialized to the central binomial
coefficient.  The right side counts all carry depths below any strict
logarithmic bound `b`. -/
theorem factorization_centralBinom_eq_carryCount
    {p t b : ℕ} (hp : p.Prime) (hb : Nat.log p (2 * t) < b) :
    t.centralBinom.factorization p =
      #{i ∈ Finset.Ico 1 b | SelfCarryAt p t i} := by
  classical
  simpa only [Nat.centralBinom, two_mul, SelfCarryAt] using
    (Nat.factorization_choose' (n := t) (k := t) hp (by simpa [two_mul] using hb))

/-- For an odd base, its paper half `(p-1)/2` is characterized by
`2*h+1=p`. -/
theorem two_mul_paperHalf_add_one {p : ℕ} (hpodd : Odd p) :
    2 * ((p - 1) / 2) + 1 = p := by
  have h := Nat.two_mul_div_two_add_one_of_odd hpodd
  omega

/-- A list whose digits lie in the lower half has no self-carry within its
own length.  This is the finite combinatorial core of the `D_p` criterion. -/
theorem two_mul_ofDigits_lt_pow_length
    {p : ℕ} (hpodd : Odd p) (l : List ℕ)
    (hl : ∀ d ∈ l, d ≤ (p - 1) / 2) :
    2 * Nat.ofDigits p l < p ^ l.length := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons d l ih =>
      have hd : 2 * d + 1 ≤ p := by
        have hd' := hl d (by simp)
        have hpform := two_mul_paperHalf_add_one hpodd
        omega
      have htail : ∀ e ∈ l, e ≤ (p - 1) / 2 := by
        intro e he
        exact hl e (by simp [he])
      have hih := ih htail
      rw [Nat.ofDigits_cons, List.length_cons, pow_succ']
      rw [Nat.lt_iff_add_one_le]
      calc
        2 * (d + p * Nat.ofDigits p l) + 1 =
            (2 * d + 1) + p * (2 * Nat.ofDigits p l) := by ring
        _ ≤ p + p * (2 * Nat.ofDigits p l) :=
          Nat.add_le_add_right hd _
        _ = p * (2 * Nat.ofDigits p l + 1) := by ring
        _ ≤ p * p ^ l.length := by
          exact Nat.mul_le_mul_left p (Nat.lt_iff_add_one_le.mp hih)

/-- The contribution of digit `j` is a lower bound for the represented
number. -/
theorem pow_mul_getElem_le_ofDigits
    (p : ℕ) (l : List ℕ) (j : ℕ) (hj : j < l.length) :
    p ^ j * l[j] ≤ Nat.ofDigits p l := by
  induction l generalizing j with
  | nil => simp at hj
  | cons d l ih =>
      cases j with
      | zero =>
          simp only [pow_zero, one_mul, List.getElem_cons_zero, Nat.ofDigits_cons]
          exact Nat.le_add_right _ _
      | succ j =>
          have hj' : j < l.length := by simpa using hj
          have hih := ih j hj'
          simp only [List.getElem_cons_succ, pow_succ', Nat.ofDigits_cons]
          calc
            p * p ^ j * l[j] = p * (p ^ j * l[j]) := by ring
            _ ≤ p * Nat.ofDigits p l := Nat.mul_le_mul_left p hih
            _ ≤ d + p * Nat.ofDigits p l := Nat.le_add_left _ _

/-- Lower-half digits imply the exact absence of every self-carry. -/
theorem noSelfCarry_of_lowerHalfDigits
    {p t : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (ht : LowerHalfDigits p t) : NoSelfCarry p t := by
  intro i hi
  rw [SelfCarryAt, not_le]
  rw [Nat.self_mod_pow_eq_ofDigits_take i t hp.two_le]
  have htake : ∀ d ∈ (p.digits t).take i, d ≤ (p - 1) / 2 := by
    intro d hd
    exact ht d (List.mem_of_mem_take hd)
  have hshort := two_mul_ofDigits_lt_pow_length hpodd _ htake
  simpa [two_mul] using hshort.trans_le
    (Nat.pow_le_pow_right hp.one_le (List.length_take_le i (p.digits t)))

/-- Absence of every self-carry forces every base-`p` digit into the lower
half. -/
theorem lowerHalfDigits_of_noSelfCarry
    {p t : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (ht : NoSelfCarry p t) : LowerHalfDigits p t := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := (List.mem_iff_getElem.mp hd)
  by_contra hlarge
  have hdlarge : (p - 1) / 2 < (p.digits t)[j] := Nat.lt_of_not_ge hlarge
  have hp_le_two_digit : p ≤ 2 * (p.digits t)[j] := by
    have hpform := two_mul_paperHalf_add_one hpodd
    omega
  have hjtake : j < ((p.digits t).take (j + 1)).length := by
    simp [List.length_take, hj]
  have hget : ((p.digits t).take (j + 1))[j] = (p.digits t)[j] := by
    simp [List.getElem_take]
  have hlower := pow_mul_getElem_le_ofDigits p ((p.digits t).take (j + 1)) j hjtake
  rw [hget] at hlower
  have hprefix :
      2 * Nat.ofDigits p ((p.digits t).take (j + 1)) < p ^ (j + 1) := by
    have := ht (j + 1) (by omega)
    rw [SelfCarryAt, not_le] at this
    simpa [Nat.self_mod_pow_eq_ofDigits_take (j + 1) t hp.two_le, two_mul] using this
  have hcontra : p ^ (j + 1) ≤
      2 * Nat.ofDigits p ((p.digits t).take (j + 1)) := by
    calc
      p ^ (j + 1) = p ^ j * p := by rw [pow_succ]
      _ ≤ p ^ j * (2 * (p.digits t)[j]) :=
        Nat.mul_le_mul_left (p ^ j) hp_le_two_digit
      _ = 2 * (p ^ j * (p.digits t)[j]) := by ring
      _ ≤ 2 * Nat.ofDigits p ((p.digits t).take (j + 1)) :=
        Nat.mul_le_mul_left 2 hlower
  exact (not_le_of_gt hprefix) hcontra

/-- Exact equivalence between the paper's digit set `D_p` and Kummer's
prefix carry condition. -/
theorem lowerHalfDigits_iff_noSelfCarry
    {p t : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    LowerHalfDigits p t ↔ NoSelfCarry p t :=
  ⟨noSelfCarry_of_lowerHalfDigits hp hpodd,
    lowerHalfDigits_of_noSelfCarry hp hpodd⟩

/-! ## Kummer's theorem and divisibility -/

/-- Kummer's finite carry count vanishes exactly when no positive prefix
has a self-carry.  Carry depths beyond the logarithmic window are impossible
because `p^i > 2*t`. -/
theorem factorization_centralBinom_eq_zero_iff_noSelfCarry
    {p t : ℕ} (hp : p.Prime) :
    t.centralBinom.factorization p = 0 ↔ NoSelfCarry p t := by
  let b := Nat.log p (2 * t) + 1
  have hb : Nat.log p (2 * t) < b := by
    simp only [b]
    omega
  rw [factorization_centralBinom_eq_carryCount hp hb]
  constructor
  · intro hzero i hi
    have hempty : {j ∈ Finset.Ico 1 b | SelfCarryAt p t j} = ∅ :=
      Finset.card_eq_zero.mp hzero
    by_cases hib : i < b
    · have hiIco : i ∈ Finset.Ico 1 b := Finset.mem_Ico.mpr ⟨hi, hib⟩
      exact (Finset.filter_eq_empty_iff.mp hempty) hiIco
    · rw [SelfCarryAt, not_le]
      have hbi : b ≤ i := Nat.le_of_not_gt hib
      have hlogi : Nat.log p (2 * t) < i := hb.trans_le hbi
      have hpow : 2 * t < p ^ i := Nat.lt_pow_of_log_lt hp.one_lt hlogi
      have hmod : t % p ^ i ≤ t := Nat.mod_le _ _
      omega
  · intro hnone
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    exact hnone i (Finset.mem_Ico.mp hi).1

/-- For a prime, zero factorization is the same as nondivisibility of the
nonzero central binomial coefficient. -/
theorem not_dvd_centralBinom_iff_factorization_eq_zero
    {p t : ℕ} (hp : p.Prime) :
    ¬p ∣ t.centralBinom ↔ t.centralBinom.factorization p = 0 := by
  constructor
  · intro hnot
    exact (Nat.factorization_eq_zero_iff _ _).2 (Or.inr (Or.inl hnot))
  · intro hzero
    rcases (Nat.factorization_eq_zero_iff _ _).1 hzero with hnp | hnot | hzero'
    · exact (hnp hp).elim
    · exact hnot
    · exact (Nat.centralBinom_ne_zero t hzero').elim

/-- Equation (4) of the paper, with `D_p` represented by
`LowerHalfDigits`: an odd prime is absent from the support of `B(t)` exactly
when every base-`p` digit of `t` lies in the lower half. -/
theorem not_dvd_centralBinom_iff_lowerHalfDigits
    {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ t.centralBinom ↔ LowerHalfDigits p t := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rw [not_dvd_centralBinom_iff_factorization_eq_zero hp,
    factorization_centralBinom_eq_zero_iff_noSelfCarry hp]
  exact (lowerHalfDigits_iff_noSelfCarry hp hpodd).symm

/-- Contrapositive support form of equation (4). -/
theorem dvd_centralBinom_iff_not_lowerHalfDigits
    {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ t.centralBinom ↔ ¬LowerHalfDigits p t := by
  constructor
  · intro hd hlow
    exact (not_dvd_centralBinom_iff_lowerHalfDigits hp hp2).2 hlow hd
  · intro hnlow
    by_contra hndvd
    exact hnlow ((not_dvd_centralBinom_iff_lowerHalfDigits hp hp2).1 hndvd)

/-! ## Elementary digit shifts used in Proposition 1 -/

/-- Appending `a` zero digits does not affect membership in `D_p`. -/
theorem lowerHalfDigits_primePow_mul_iff
    {p a c : ℕ} (hp : p.Prime) (hc : 0 < c) :
    LowerHalfDigits p (p ^ a * c) ↔ LowerHalfDigits p c := by
  rw [LowerHalfDigits, LowerHalfDigits,
    Nat.digits_base_pow_mul hp.one_lt hc]
  constructor
  · intro h d hd
    exact h d (List.mem_append_right _ hd)
  · intro h d hd
    rcases List.mem_append.mp hd with hzero | hc
    · have hd0 : d = 0 := List.eq_of_mem_replicate hzero
      omega
    · exact h d hc

/-- Exact value of the block of `a` repeated lower-half digits. -/
theorem two_mul_ofDigits_replicate_paperHalf_add_one
    {p : ℕ} (hpodd : Odd p) (a : ℕ) :
    2 * Nat.ofDigits p (List.replicate a ((p - 1) / 2)) + 1 = p ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ']
      have hpform := two_mul_paperHalf_add_one hpodd
      calc
        2 * ((p - 1) / 2 +
            p * Nat.ofDigits p (List.replicate a ((p - 1) / 2))) + 1 =
            (2 * ((p - 1) / 2) + 1) +
              p * (2 * Nat.ofDigits p
                (List.replicate a ((p - 1) / 2))) := by ring
        _ = p + p * (2 * Nat.ofDigits p
              (List.replicate a ((p - 1) / 2))) := by rw [hpform]
        _ = p * (2 * Nat.ofDigits p
              (List.replicate a ((p - 1) / 2)) + 1) := by ring
        _ = p * p ^ a := by rw [ih]

/-- The represented repeated block is `(p^a-1)/2`. -/
theorem ofDigits_replicate_paperHalf
    {p : ℕ} (hpodd : Odd p) (a : ℕ) :
    Nat.ofDigits p (List.replicate a ((p - 1) / 2)) =
      (p ^ a - 1) / 2 := by
  have h := two_mul_ofDigits_replicate_paperHalf_add_one hpodd a
  omega

/-- The low block `(p^a-1)/2` consists of exactly `a` copies of the
lower-half endpoint. -/
theorem digits_pow_sub_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    p.digits ((p ^ a - 1) / 2) =
      List.replicate a ((p - 1) / 2) := by
  have hpodd := hp.odd_of_ne_two hp2
  rw [← ofDigits_replicate_paperHalf hpodd a]
  apply Nat.digits_ofDigits p hp.one_lt
  · intro d hd
    have hdeq : d = (p - 1) / 2 := List.eq_of_mem_replicate hd
    rw [hdeq]
    have hpform := two_mul_paperHalf_add_one hpodd
    omega
  · intro hne
    cases a with
    | zero => simp at hne
    | succ a =>
        have hhalf : 0 < (p - 1) / 2 := by
          have hpform := two_mul_paperHalf_add_one hpodd
          have hp3 : 3 ≤ p := by
            have hp2le := hp.two_le
            omega
          omega
        simpa using hhalf.ne'

/-- Concatenation identity for equation (7): the lower `a` digits of
`p^a*m + (p^a-1)/2` are all the permitted endpoint digit. -/
theorem digits_mul_pow_add_pow_sub_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    p.digits (p ^ a * m + (p ^ a - 1) / 2) =
      List.replicate a ((p - 1) / 2) ++ p.digits m := by
  have happ := Nat.digits_append_digits (m := m)
    (n := (p ^ a - 1) / 2) hp.pos
  rw [digits_pow_sub_one_div_two hp hp2 a] at happ
  simpa [List.length_replicate, Nat.add_comm] using happ.symm

/-- Equation (8): adjoining the permitted low half-block preserves and
reflects membership in `D_p`. -/
theorem lowerHalfDigits_mul_pow_add_pow_sub_one_div_two_iff
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    LowerHalfDigits p (p ^ a * m + (p ^ a - 1) / 2) ↔
      LowerHalfDigits p m := by
  rw [LowerHalfDigits, LowerHalfDigits,
    digits_mul_pow_add_pow_sub_one_div_two hp hp2 a m]
  constructor
  · intro h d hd
    exact h d (List.mem_append_right _ hd)
  · intro h d hd
    rcases List.mem_append.mp hd with hhalf | hm
    · exact (List.eq_of_mem_replicate hhalf).le
    · exact h d hm

/-- Exact value of the exceptional low block occurring in `n+1` in the
second transition case. -/
theorem two_mul_ofDigits_upperHalfBlock
    {p : ℕ} (hpodd : Odd p) (a : ℕ) :
    2 * Nat.ofDigits p
        (((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2)) =
      p ^ (a + 1) + 1 := by
  rw [Nat.ofDigits_cons]
  have hpform := two_mul_paperHalf_add_one hpodd
  have hrep := two_mul_ofDigits_replicate_paperHalf_add_one hpodd a
  rw [pow_succ']
  calc
    2 * ((p - 1) / 2 + 1 +
        p * Nat.ofDigits p (List.replicate a ((p - 1) / 2))) =
        (2 * ((p - 1) / 2) + 1) + 1 +
          p * (2 * Nat.ofDigits p
            (List.replicate a ((p - 1) / 2))) := by ring
    _ = p + 1 + p * (2 * Nat.ofDigits p
          (List.replicate a ((p - 1) / 2))) := by rw [hpform]
    _ = p * (2 * Nat.ofDigits p
          (List.replicate a ((p - 1) / 2)) + 1) + 1 := by ring
    _ = p * p ^ a + 1 := by rw [hrep]

/-- The low block `(p^(a+1)+1)/2` begins with the forbidden digit
`(p-1)/2+1`, followed by `a` endpoint digits. -/
theorem digits_pow_add_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    p.digits ((p ^ (a + 1) + 1) / 2) =
      ((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2) := by
  have hpodd := hp.odd_of_ne_two hp2
  have hvalue : Nat.ofDigits p
      (((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2)) =
      (p ^ (a + 1) + 1) / 2 := by
    have h := two_mul_ofDigits_upperHalfBlock hpodd a
    omega
  rw [← hvalue]
  apply Nat.digits_ofDigits p hp.one_lt
  · intro d hd
    have hp2le := hp.two_le
    have hpform := two_mul_paperHalf_add_one hpodd
    have hp3 : 3 ≤ p := by omega
    rcases List.mem_cons.mp hd with rfl | hdrep
    · omega
    · have hdeq : d = (p - 1) / 2 := List.eq_of_mem_replicate hdrep
      omega
  · intro hne
    have hmem := List.getLast_mem hne
    have hp2le := hp.two_le
    have hpform := two_mul_paperHalf_add_one hpodd
    have hp3 : 3 ≤ p := by omega
    rcases List.mem_cons.mp hmem with hfirst | hrep
    · omega
    · have hlast := List.eq_of_mem_replicate hrep
      rw [hlast]
      omega

/-- The exceptional low block, even after adjoining arbitrary higher
digits, is outside `D_p`.  This is the units-digit exclusion used in (6). -/
theorem not_lowerHalfDigits_mul_pow_add_pow_add_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    ¬LowerHalfDigits p
      (p ^ (a + 1) * m + (p ^ (a + 1) + 1) / 2) := by
  have happ := Nat.digits_append_digits (m := m)
    (n := (p ^ (a + 1) + 1) / 2) hp.pos
  rw [digits_pow_add_one_div_two hp hp2 a] at happ
  have hdigits :
      p.digits (p ^ (a + 1) * m + (p ^ (a + 1) + 1) / 2) =
        (((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2)) ++
          p.digits m := by
    simpa [Nat.add_comm] using happ.symm
  intro hlow
  have hforbidden := hlow ((p - 1) / 2 + 1) (by
    rw [hdigits]
    simp)
  omega

/-- Equation (5) at its shifted endpoint: after removing a positive power
of `p`, absence from the support is exactly membership of the cofactor in
`D_p`. -/
theorem not_dvd_centralBinom_primePow_mul_iff
    {p a c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : 0 < c) :
    ¬p ∣ (p ^ a * c).centralBinom ↔ LowerHalfDigits p c := by
  rw [not_dvd_centralBinom_iff_lowerHalfDigits hp hp2,
    lowerHalfDigits_primePow_mul_iff hp hc]

/-- Equation (6), lower endpoint: the permitted status of `n` is exactly
that of the high cofactor `(c-1)/2` in decomposition (7). -/
theorem not_dvd_centralBinom_lowerHalfBlock_iff
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    ¬p ∣ (p ^ a * m + (p ^ a - 1) / 2).centralBinom ↔
      LowerHalfDigits p m := by
  rw [not_dvd_centralBinom_iff_lowerHalfDigits hp hp2,
    lowerHalfDigits_mul_pow_add_pow_sub_one_div_two_iff hp hp2]

/-- Equation (6), upper endpoint: the exceptional units digit forces the
prime into the support of `B(n+1)`. -/
theorem dvd_centralBinom_upperHalfBlock
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    p ∣ (p ^ (a + 1) * m + (p ^ (a + 1) + 1) / 2).centralBinom := by
  rw [dvd_centralBinom_iff_not_lowerHalfDigits hp hp2]
  exact not_lowerHalfDigits_mul_pow_add_pow_add_one_div_two hp hp2 a m


end KummerTransition
end Erdos730

end Campaign180File0

/- Source module: ErdosProblems.Erdos730.ConsecutiveTransition -/
section Campaign180File1
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: exact consecutive support-transition criterion

This module formalizes Proposition 1 of the positive-density proof.  For
`n ≥ 1`, equality of the prime supports of the two consecutive central
binomial coefficients is equivalent to the two exact-valuation cofactor
conditions (5) and (6).

The predicate `ExactPrimePowerCofactor p a c N` is the fully quantified
meaning of `p^a ∥ N` together with the named cofactor `c`: `a` is positive,
`N = p^a*c`, and `p ∤ c`.
-/

namespace Erdos730
namespace ConsecutiveTransition

open KummerTransition

/-- `p^a ∥ N`, with the cofactor explicitly named as `c` and with the
positive-exponent convention used in Proposition 1. -/
def ExactPrimePowerCofactor (p a c N : ℕ) : Prop :=
  0 < a ∧ N = p ^ a * c ∧ ¬p ∣ c

/-- The exact quantified condition (5). -/
def DropCondition (n : ℕ) : Prop :=
  ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ {a c : ℕ},
    ExactPrimePowerCofactor p a c (n + 1) →
      ¬LowerHalfDigits p c

/-- The exact quantified condition (6). -/
def EntryCondition (n : ℕ) : Prop :=
  ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ {a c : ℕ},
    ExactPrimePowerCofactor p a c (2 * n + 1) →
      ¬LowerHalfDigits p ((c - 1) / 2)

/-- The two exact obstruction-exclusion conditions in Proposition 1. -/
def TransitionConditions (n : ℕ) : Prop :=
  DropCondition n ∧ EntryCondition n

/-- Every nonzero number admits an exact positive-exponent `p`-power
decomposition once `p` divides it. -/
theorem exists_exactPrimePowerCofactor_of_dvd
    {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) (hpd : p ∣ N) :
    ∃ a c, ExactPrimePowerCofactor p a c N := by
  obtain ⟨a, c, hpc, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  refine ⟨a, c, ?_, hfac, hpc⟩
  by_contra ha
  have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
  subst a
  simp only [pow_zero, one_mul] at hfac
  exact hpc (hfac ▸ hpd)

/-- The two adjacent linear factors are coprime. -/
theorem coprime_succ_two_mul_add_one (n : ℕ) :
    Nat.Coprime (n + 1) (2 * n + 1) := by
  rw [two_mul, add_assoc, Nat.coprime_add_self_right,
    Nat.coprime_self_add_left]
  exact Nat.coprime_one_left n

/-- Hence a prime dividing `n+1` cannot divide `2n+1`. -/
theorem not_dvd_two_mul_add_one_of_dvd_succ
    {p n : ℕ} (hp : p.Prime) (hpd : p ∣ n + 1) :
    ¬p ∣ 2 * n + 1 := by
  intro hpd'
  apply hp.not_dvd_one
  rw [← coprime_succ_two_mul_add_one n]
  exact Nat.dvd_gcd hpd hpd'

/-- Symmetric coprimality consequence. -/
theorem not_dvd_succ_of_dvd_two_mul_add_one
    {p n : ℕ} (hp : p.Prime) (hpd : p ∣ 2 * n + 1) :
    ¬p ∣ n + 1 := by
  intro hpd'
  apply hp.not_dvd_one
  rw [← coprime_succ_two_mul_add_one n]
  exact Nat.dvd_gcd hpd' hpd

/-- Away from the two factors in the central-binomial recurrence, an odd
prime has the same divisibility status at `n` and `n+1`. -/
theorem dvd_centralBinom_succ_iff_of_away
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsucc : ¬p ∣ n + 1) (htwo : ¬p ∣ 2 * n + 1) :
    p ∣ (n + 1).centralBinom ↔ p ∣ n.centralBinom := by
  constructor
  · intro h
    have hprod : p ∣ 2 * (2 * n + 1) * n.centralBinom := by
      rw [← Nat.succ_mul_centralBinom_succ]
      exact dvd_mul_of_dvd_right h (n + 1)
    rcases hp.dvd_mul.mp hprod with hleft | hbinom
    · rcases hp.dvd_mul.mp hleft with htwo' | hlinear
      · exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp htwo')).elim
      · exact (htwo hlinear).elim
    · exact hbinom
  · intro h
    have hprod : p ∣ (n + 1) * (n + 1).centralBinom := by
      rw [Nat.succ_mul_centralBinom_succ]
      exact dvd_mul_of_dvd_right h (2 * (2 * n + 1))
    rcases hp.dvd_mul.mp hprod with hlinear | hbinom
    · exact (hsucc hlinear).elim
    · exact hbinom

/-- Odd-factor arithmetic behind equation (7). -/
theorem lower_endpoint_decomposition
    {n q c : ℕ} (hq : Odd q) (hc : Odd c)
    (h : 2 * n + 1 = q * c) :
    n = q * ((c - 1) / 2) + (q - 1) / 2 := by
  rcases hq with ⟨r, rfl⟩
  rcases hc with ⟨s, rfl⟩
  simp at h ⊢
  nlinarith [h]

/-- The adjacent upper endpoint corresponding to equation (7). -/
theorem upper_endpoint_decomposition
    {n q c : ℕ} (hq : Odd q) (hc : Odd c)
    (h : 2 * n + 1 = q * c) :
    n + 1 = q * ((c - 1) / 2) + (q + 1) / 2 := by
  rcases hq with ⟨r, rfl⟩
  rcases hc with ⟨s, rfl⟩
  simp at h ⊢
  have hhalf : (2 * r + 1 + 1) / 2 = r + 1 := by omega
  rw [hhalf]
  nlinarith [h]

/-- In the `p^a ∥ n+1` case, the prime is always present at the lower
endpoint and is absent at the upper endpoint exactly for a `D_p` cofactor. -/
theorem drop_transition_of_exact
    {p a c n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexact : ExactPrimePowerCofactor p a c (n + 1)) :
    p ∣ n.centralBinom ∧
      (¬p ∣ (n + 1).centralBinom ↔ LowerHalfDigits p c) := by
  rcases hexact with ⟨ha, hfac, hpc⟩
  constructor
  · have hpPow : p ∣ p ^ a := dvd_pow_self p ha.ne'
    have hpsucc : p ∣ n + 1 := by
      rw [hfac]
      exact dvd_mul_of_dvd_left hpPow c
    exact dvd_trans hpsucc (Nat.succ_dvd_centralBinom n)
  · simpa [hfac] using
      (not_dvd_centralBinom_primePow_mul_iff hp hp2
        (Nat.pos_of_ne_zero (fun hc0 ↦ hpc (hc0 ▸ dvd_zero p))) :
        ¬p ∣ (p ^ a * c).centralBinom ↔ LowerHalfDigits p c)

/-- In the `p^a ∥ 2n+1` case, the prime is always present at the upper
endpoint and is absent at the lower endpoint exactly for the cofactor test
in (6). -/
theorem entry_transition_of_exact
    {p a c n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexact : ExactPrimePowerCofactor p a c (2 * n + 1)) :
    (¬p ∣ n.centralBinom ↔ LowerHalfDigits p ((c - 1) / 2)) ∧
      p ∣ (n + 1).centralBinom := by
  rcases hexact with ⟨ha, hfac, hpc⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpowodd : Odd (p ^ a) := hpodd.pow
  have htotalOdd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hcodd : Odd c := by
    rw [hfac] at htotalOdd
    exact (Nat.odd_mul.mp htotalOdd).2
  have hnform :
      n = p ^ a * ((c - 1) / 2) + (p ^ a - 1) / 2 :=
    lower_endpoint_decomposition hpowodd hcodd hfac
  have hsuccform :
      n + 1 = p ^ a * ((c - 1) / 2) + (p ^ a + 1) / 2 :=
    upper_endpoint_decomposition hpowodd hcodd hfac
  constructor
  · simpa [hnform] using
      (not_dvd_centralBinom_lowerHalfBlock_iff hp hp2 a ((c - 1) / 2))
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    simpa [hsuccform, Nat.succ_eq_add_one] using
      (dvd_centralBinom_upperHalfBlock hp hp2 b ((c - 1) / 2))

/-! ## Proposition 1 -/

/-- Prime-by-prime divisibility agrees at the two endpoints exactly when
the two quantified transition conditions hold. -/
theorem prime_dvd_agrees_iff_transitionConditions
    {n : ℕ} (hn : 0 < n) :
    (∀ p, p.Prime →
        (p ∣ n.centralBinom ↔ p ∣ (n + 1).centralBinom)) ↔
      TransitionConditions n := by
  constructor
  · intro hagree
    constructor
    · intro p hp hp2 a c hexact hlow
      have htransition := drop_transition_of_exact hp hp2 hexact
      have hupper : p ∣ (n + 1).centralBinom :=
        (hagree p hp).mp htransition.1
      exact (htransition.2.mpr hlow) hupper
    · intro p hp hp2 a c hexact hlow
      have htransition := entry_transition_of_exact hp hp2 hexact
      have hlower : p ∣ n.centralBinom :=
        (hagree p hp).mpr htransition.2
      exact (htransition.1.mpr hlow) hlower
  · rintro ⟨hdrop, hentry⟩ p hp
    by_cases hp2 : p = 2
    · subst p
      constructor
      · intro _
        exact Nat.two_dvd_centralBinom_of_one_le (by omega)
      · intro _
        exact Nat.two_dvd_centralBinom_of_one_le hn
    · by_cases hsucc : p ∣ n + 1
      · obtain ⟨a, c, hexact⟩ :=
          exists_exactPrimePowerCofactor_of_dvd hp (by omega) hsucc
        have htransition := drop_transition_of_exact hp hp2 hexact
        have hnotlow : ¬LowerHalfDigits p c := hdrop hp hp2 hexact
        have hupper : p ∣ (n + 1).centralBinom := by
          by_contra hnot
          exact hnotlow (htransition.2.mp hnot)
        exact ⟨fun _ ↦ hupper, fun _ ↦ htransition.1⟩
      · by_cases htwo : p ∣ 2 * n + 1
        · obtain ⟨a, c, hexact⟩ :=
            exists_exactPrimePowerCofactor_of_dvd hp (by omega) htwo
          have htransition := entry_transition_of_exact hp hp2 hexact
          have hnotlow : ¬LowerHalfDigits p ((c - 1) / 2) :=
            hentry hp hp2 hexact
          have hlower : p ∣ n.centralBinom := by
            by_contra hnot
            exact hnotlow (htransition.1.mp hnot)
          exact ⟨fun _ ↦ htransition.2, fun _ ↦ hlower⟩
        · exact (dvd_centralBinom_succ_iff_of_away hp hp2 hsucc htwo).symm

/-- Equality of central-binomial prime-factor sets is the same as
prime-by-prime agreement of divisibility. -/
theorem primeFactors_eq_iff_prime_dvd_agrees (n : ℕ) :
    n.centralBinom.primeFactors = (n + 1).centralBinom.primeFactors ↔
      ∀ p, p.Prime →
        (p ∣ n.centralBinom ↔ p ∣ (n + 1).centralBinom) := by
  have hn0 : n.centralBinom ≠ 0 := Nat.centralBinom_ne_zero n
  have hsucc0 : (n + 1).centralBinom ≠ 0 := Nat.centralBinom_ne_zero (n + 1)
  constructor
  · intro heq p hp
    have hmem :
        p ∈ n.centralBinom.primeFactors ↔
          p ∈ (n + 1).centralBinom.primeFactors := by
      rw [heq]
    simpa [Nat.mem_primeFactors_of_ne_zero hn0,
      Nat.mem_primeFactors_of_ne_zero hsucc0, hp] using hmem
  · intro hagree
    ext p
    simp only [Nat.mem_primeFactors_of_ne_zero hn0,
      Nat.mem_primeFactors_of_ne_zero hsucc0]
    constructor
    · rintro ⟨hp, hdvd⟩
      exact ⟨hp, (hagree p hp).mp hdvd⟩
    · rintro ⟨hp, hdvd⟩
      exact ⟨hp, (hagree p hp).mpr hdvd⟩

/-- **Proposition 1 (equations (5) and (6)).**  For every `n ≥ 1`, the
supports of `B(n)` and `B(n+1)` agree if and only if every exact odd-prime
valuation of `n+1` and `2n+1` passes its respective cofactor test. -/
theorem consecutive_primeFactors_eq_iff_transitionConditions
    {n : ℕ} (hn : 0 < n) :
    n.centralBinom.primeFactors = (n + 1).centralBinom.primeFactors ↔
      TransitionConditions n := by
  rw [primeFactors_eq_iff_prime_dvd_agrees]
  exact prime_dvd_agrees_iff_transitionConditions hn

/-! ## Event coverage -/

/-- A witnessed equation-(5) obstruction event. -/
def DropObstruction (n p a c : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ExactPrimePowerCofactor p a c (n + 1) ∧
      LowerHalfDigits p c

/-- A witnessed equation-(6) obstruction event. -/
def EntryObstruction (n p a c : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ExactPrimePowerCofactor p a c (2 * n + 1) ∧
      LowerHalfDigits p ((c - 1) / 2)

/-- Exact event-coverage theorem underlying `Bad(X) ≤ E(X)`: if the two
supports differ, some fully quantified drop or entry obstruction occurs.
No injectivity of the witness assignment is asserted or needed. -/
theorem exists_obstruction_of_primeFactors_ne
    {n : ℕ} (hn : 0 < n)
    (hbad : n.centralBinom.primeFactors ≠
      (n + 1).centralBinom.primeFactors) :
    (∃ p a c, DropObstruction n p a c) ∨
      (∃ p a c, EntryObstruction n p a c) := by
  classical
  have hnot : ¬TransitionConditions n := by
    intro hconditions
    exact hbad
      ((consecutive_primeFactors_eq_iff_transitionConditions hn).mpr hconditions)
  by_cases hdrop : DropCondition n
  · have hnotentry : ¬EntryCondition n := by
      intro hentry
      exact hnot ⟨hdrop, hentry⟩
    unfold EntryCondition at hnotentry
    push Not at hnotentry
    right
    rcases hnotentry with ⟨p, hp, hp2, a, c, hexact, hlow⟩
    exact ⟨p, a, c, hp, hp2, hexact, hlow⟩
  · unfold DropCondition at hdrop
    push Not at hdrop
    left
    rcases hdrop with ⟨p, hp, hp2, a, c, hexact, hlow⟩
    exact ⟨p, a, c, hp, hp2, hexact, hlow⟩


end ConsecutiveTransition
end Erdos730

end Campaign180File1

/- Source module: ErdosProblems.Erdos730.FullDensityCore -/
section Campaign180File2
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: exact arithmetic core of the positive-density family

This file formalizes only the elementary, exact part of the proposed
positive-density proof.  It defines the four linear branches and the
quadratic family, proves all six linear identities and the product identity,
certifies strict growth, records the fixed-prime congruences, and checks the
finite top-digit residue tables.

It also gives the exact bridge to the statement of Erdős 730: an infinite
set of good parameters in this family maps injectively into the upstream set
of unequal pairs with equal central-binomial prime support.

No analytic density estimate, Kummer theorem, Mertens theorem, or prime
number theorem in arithmetic progressions is asserted here.
-/

namespace Erdos730
namespace FullDensityCore

/-! ## The family -/

/-- The fixed modulus factor `3 * 41 * 43`. -/
def T : ℕ := 3 * 41 * 43

/-- The `P` branch. -/
def P (x : ℕ) : ℕ := 42 * T * x + 11

/-- The `Q` branch. -/
def Q (x : ℕ) : ℕ := 72 * T * x + 13

/-- The `R` branch. -/
def R (x : ℕ) : ℕ := 28 * T * x + 5

/-- The `S` branch. -/
def S (x : ℕ) : ℕ := 72 * T * x + 19

/-- The consecutive-pair parameter used in the density argument. -/
def n (x : ℕ) : ℕ := P x * Q x - 1

theorem T_eq : T = 5289 := by
  norm_num [T]

theorem branch_expansions (x : ℕ) :
    P x = 222138 * x + 11 ∧
    Q x = 380808 * x + 13 ∧
    R x = 148092 * x + 5 ∧
    S x = 380808 * x + 19 := by
  norm_num [P, Q, R, S, T]

/-- The exact quadratic polynomial, including the subtraction by one. -/
theorem n_expansion (x : ℕ) :
    n x = 84591927504 * x ^ 2 + 7076682 * x + 142 := by
  unfold n
  have hprod :
      P x * Q x = 84591927504 * x ^ 2 + 7076682 * x + 143 := by
    simp only [P, Q, T]
    ring
  rw [hprod]
  omega

/-! ## Exact branch identities -/

theorem product_identity (x : ℕ) :
    2 * (P x * Q x) = 3 * (R x * S x) + 1 := by
  simp only [P, Q, R, S, T]
  ring

theorem identity_PQ (x : ℕ) : 12 * P x = 7 * Q x + 41 := by
  simp only [P, Q, T]
  ring

theorem identity_RS (x : ℕ) : 18 * R x + 43 = 7 * S x := by
  simp only [R, S, T]
  ring

theorem identity_PS (x : ℕ) : 12 * P x + 1 = 7 * S x := by
  simp only [P, S, T]
  ring

theorem identity_QR (x : ℕ) : 7 * Q x = 18 * R x + 1 := by
  simp only [Q, R, T]
  ring

theorem identity_PR (x : ℕ) : 2 * P x = 3 * R x + 7 := by
  simp only [P, R, T]
  ring

theorem identity_QS (x : ℕ) : S x = Q x + 6 := by
  simp only [Q, S]

theorem n_add_one (x : ℕ) : n x + 1 = P x * Q x := by
  have hpos : 0 < P x * Q x := by
    simp only [P, Q, T]
    positivity
  simp only [n]
  omega

theorem two_n_add_one (x : ℕ) : 2 * n x + 1 = 3 * (R x * S x) := by
  have hprod := product_identity x
  have hn := n_add_one x
  omega

/-! ## Positivity and strict growth -/

theorem branches_positive (x : ℕ) :
    0 < P x ∧ 0 < Q x ∧ 0 < R x ∧ 0 < S x := by
  simp only [P, Q, R, S, T]
  omega

theorem P_strictMono : StrictMono P := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [P, T]
  omega

theorem Q_strictMono : StrictMono Q := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [Q, T]
  omega

theorem R_strictMono : StrictMono R := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [R, T]
  omega

theorem S_strictMono : StrictMono S := by
  apply strictMono_nat_of_lt_succ
  intro x
  simp only [S, T]
  omega

theorem n_strictMono : StrictMono n := by
  apply strictMono_nat_of_lt_succ
  intro x
  rw [n_expansion, n_expansion]
  nlinarith

/-! ## Exact bridge to the upstream Erdős 730 statement -/

/-- This is the set `S` in `FormalConjectures/ErdosProblems/730.lean`. -/
abbrev PairSet : Set (ℕ × ℕ) :=
  {z | z.1 < z.2 ∧
    z.1.centralBinom.primeFactors = z.2.centralBinom.primeFactors}

/-- The consecutive pair produced by a parameter. -/
def familyPair (x : ℕ) : ℕ × ℕ := (n x, n x + 1)

/-- A paper-family parameter, starting at `1`, whose consecutive pair has
equal prime support. -/
def GoodParameter (x : ℕ) : Prop :=
  1 ≤ x ∧
    (n x).centralBinom.primeFactors =
      (n x + 1).centralBinom.primeFactors

def GoodParameters : Set ℕ := {x | GoodParameter x}

theorem familyPair_mem_pairSet {x : ℕ} (hx : GoodParameter x) :
    familyPair x ∈ PairSet := by
  exact ⟨Nat.lt_succ_self _, hx.2⟩

theorem familyPair_mapsTo_pairSet :
    Set.MapsTo familyPair GoodParameters PairSet := by
  intro x hx
  exact familyPair_mem_pairSet hx

theorem familyPair_injective : Function.Injective familyPair := by
  intro x y hxy
  have hnxy : n x = n y := congrArg Prod.fst hxy
  exact n_strictMono.injective hnxy

theorem familyPair_injOn_good : Set.InjOn familyPair GoodParameters :=
  fun _ _ _ _ h => familyPair_injective h

/-- The exact final set-theoretic intake bridge.  Any proof that the good
parameter set is infinite therefore proves the upstream Erdős 730 set is
infinite. -/
theorem pairSet_infinite_of_goodParameters_infinite
    (hgood : GoodParameters.Infinite) : PairSet.Infinite := by
  have himage : (familyPair '' GoodParameters).Infinite :=
    Set.Infinite.image familyPair_injOn_good hgood
  exact himage.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact familyPair_mem_pairSet hx)

/-! ## Fixed-prime congruences -/

theorem branch_mod_41 (x : ℕ) :
    P x % 41 = 11 ∧ Q x % 41 = 13 ∧
    R x % 41 = 5 ∧ S x % 41 = 19 := by
  simp only [P, Q, R, S, T]
  omega

theorem branch_mod_43 (x : ℕ) :
    P x % 43 = 11 ∧ Q x % 43 = 13 ∧
    R x % 43 = 5 ∧ S x % 43 = 19 := by
  simp only [P, Q, R, S, T]
  omega

theorem fixed_primes_do_not_divide_branches (x : ℕ) :
    (¬41 ∣ P x ∧ ¬41 ∣ Q x ∧ ¬41 ∣ R x ∧ ¬41 ∣ S x) ∧
    (¬43 ∣ P x ∧ ¬43 ∣ Q x ∧ ¬43 ∣ R x ∧ ¬43 ∣ S x) := by
  rcases branch_mod_41 x with ⟨hP41, hQ41, hR41, hS41⟩
  rcases branch_mod_43 x with ⟨hP43, hQ43, hR43, hS43⟩
  simp only [Nat.dvd_iff_mod_eq_zero, hP41, hQ41, hR41, hS41,
    hP43, hQ43, hR43, hS43]
  norm_num

theorem branch_mod_3 (x : ℕ) :
    P x % 3 = 2 ∧ Q x % 3 = 1 ∧
    R x % 3 = 2 ∧ S x % 3 = 1 := by
  simp only [P, Q, R, S, T]
  omega

theorem branch_mod_7_fixed (x : ℕ) : P x % 7 = 4 ∧ R x % 7 = 5 := by
  simp only [P, R, T]
  omega

theorem Q_S_odd_and_one_mod_three (x : ℕ) :
    Q x % 2 = 1 ∧ S x % 2 = 1 ∧
    Q x % 3 = 1 ∧ S x % 3 = 1 := by
  simp only [Q, S, T]
  omega

/-! ## Pairwise coprimality of the four branches -/

lemma coprime_of_gcd_dvd_coprime
    {a b c : ℕ} (hac : Nat.Coprime a c) (hdiv : Nat.gcd a b ∣ c) :
    Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply (Nat.coprime_self _).mp
  exact Nat.Coprime.of_dvd (Nat.gcd_dvd_left a b) hdiv hac

theorem P_Q_coprime (x : ℕ) : Nat.Coprime (P x) (Q x) := by
  let g := Nat.gcd (P x) (Q x)
  have hgP : g ∣ P x := Nat.gcd_dvd_left _ _
  have hgQ : g ∣ Q x := Nat.gcd_dvd_right _ _
  have h12P : g ∣ 12 * P x := dvd_mul_of_dvd_right hgP 12
  have h7Q : g ∣ 7 * Q x := dvd_mul_of_dvd_right hgQ 7
  have hdiff : 12 * P x - 7 * Q x = 41 := by
    have hid := identity_PQ x
    omega
  have hgdiff : g ∣ 12 * P x - 7 * Q x := Nat.dvd_sub h12P h7Q
  rw [hdiff] at hgdiff
  have hnot : ¬41 ∣ P x := (fixed_primes_do_not_divide_branches x).1.1
  have hcop : Nat.Coprime (P x) 41 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 41)).2 hnot).symm
  exact coprime_of_gcd_dvd_coprime hcop hgdiff

theorem R_S_coprime (x : ℕ) : Nat.Coprime (R x) (S x) := by
  let g := Nat.gcd (R x) (S x)
  have hgR : g ∣ R x := Nat.gcd_dvd_left _ _
  have hgS : g ∣ S x := Nat.gcd_dvd_right _ _
  have h18R : g ∣ 18 * R x := dvd_mul_of_dvd_right hgR 18
  have h7S : g ∣ 7 * S x := dvd_mul_of_dvd_right hgS 7
  have hdiff : 7 * S x - 18 * R x = 43 := by
    have hid := identity_RS x
    omega
  have hgdiff : g ∣ 7 * S x - 18 * R x := Nat.dvd_sub h7S h18R
  rw [hdiff] at hgdiff
  have hnot : ¬43 ∣ R x := (fixed_primes_do_not_divide_branches x).2.2.2.1
  have hcop : Nat.Coprime (R x) 43 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 43)).2 hnot).symm
  exact coprime_of_gcd_dvd_coprime hcop hgdiff

theorem P_S_coprime (x : ℕ) : Nat.Coprime (P x) (S x) := by
  let g := Nat.gcd (P x) (S x)
  have hgP : g ∣ P x := Nat.gcd_dvd_left _ _
  have hgS : g ∣ S x := Nat.gcd_dvd_right _ _
  have h12P : g ∣ 12 * P x := dvd_mul_of_dvd_right hgP 12
  have h7S : g ∣ 7 * S x := dvd_mul_of_dvd_right hgS 7
  have hdiff : 7 * S x - 12 * P x = 1 := by
    have hid := identity_PS x
    omega
  have hgdiff : g ∣ 7 * S x - 12 * P x := Nat.dvd_sub h7S h12P
  rw [hdiff] at hgdiff
  rw [Nat.coprime_iff_gcd_eq_one]
  exact Nat.dvd_one.mp hgdiff

theorem Q_R_coprime (x : ℕ) : Nat.Coprime (Q x) (R x) := by
  let g := Nat.gcd (Q x) (R x)
  have hgQ : g ∣ Q x := Nat.gcd_dvd_left _ _
  have hgR : g ∣ R x := Nat.gcd_dvd_right _ _
  have h7Q : g ∣ 7 * Q x := dvd_mul_of_dvd_right hgQ 7
  have h18R : g ∣ 18 * R x := dvd_mul_of_dvd_right hgR 18
  have hdiff : 7 * Q x - 18 * R x = 1 := by
    have hid := identity_QR x
    omega
  have hgdiff : g ∣ 7 * Q x - 18 * R x := Nat.dvd_sub h7Q h18R
  rw [hdiff] at hgdiff
  rw [Nat.coprime_iff_gcd_eq_one]
  exact Nat.dvd_one.mp hgdiff

theorem P_R_coprime (x : ℕ) : Nat.Coprime (P x) (R x) := by
  let g := Nat.gcd (P x) (R x)
  have hgP : g ∣ P x := Nat.gcd_dvd_left _ _
  have hgR : g ∣ R x := Nat.gcd_dvd_right _ _
  have h2P : g ∣ 2 * P x := dvd_mul_of_dvd_right hgP 2
  have h3R : g ∣ 3 * R x := dvd_mul_of_dvd_right hgR 3
  have hdiff : 2 * P x - 3 * R x = 7 := by
    have hid := identity_PR x
    omega
  have hgdiff : g ∣ 2 * P x - 3 * R x := Nat.dvd_sub h2P h3R
  rw [hdiff] at hgdiff
  have hPmod := (branch_mod_7_fixed x).1
  have hnot : ¬7 ∣ P x := by
    rw [Nat.dvd_iff_mod_eq_zero, hPmod]
    norm_num
  have hcop : Nat.Coprime (P x) 7 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 hnot).symm
  exact coprime_of_gcd_dvd_coprime hcop hgdiff

theorem Q_S_coprime (x : ℕ) : Nat.Coprime (Q x) (S x) := by
  let g := Nat.gcd (Q x) (S x)
  have hgQ : g ∣ Q x := Nat.gcd_dvd_left _ _
  have hgS : g ∣ S x := Nat.gcd_dvd_right _ _
  have hdiff : S x - Q x = 6 := by
    have hid := identity_QS x
    omega
  have hgdiff : g ∣ S x - Q x := Nat.dvd_sub hgS hgQ
  rw [hdiff] at hgdiff
  rcases Q_S_odd_and_one_mod_three x with ⟨hQ2, _hS2, hQ3, _hS3⟩
  have hnot2 : ¬2 ∣ Q x := by
    rw [Nat.dvd_iff_mod_eq_zero, hQ2]
    norm_num
  have hnot3 : ¬3 ∣ Q x := by
    rw [Nat.dvd_iff_mod_eq_zero, hQ3]
    norm_num
  have hQ2cop : Nat.Coprime (Q x) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnot2).symm
  have hQ3cop : Nat.Coprime (Q x) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnot3).symm
  have hQ6cop : Nat.Coprime (Q x) 6 := by
    exact hQ2cop.mul_right hQ3cop
  exact coprime_of_gcd_dvd_coprime hQ6cop hgdiff

theorem branches_pairwise_coprime (x : ℕ) :
    Nat.Coprime (P x) (Q x) ∧ Nat.Coprime (P x) (R x) ∧
    Nat.Coprime (P x) (S x) ∧ Nat.Coprime (Q x) (R x) ∧
    Nat.Coprime (Q x) (S x) ∧ Nat.Coprime (R x) (S x) := by
  exact ⟨P_Q_coprime x, P_R_coprime x, P_S_coprime x,
    Q_R_coprime x, Q_S_coprime x, R_S_coprime x⟩

/-! ## Finite residue tables used by the top-range classification -/

def unitsMod (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun c => Nat.Coprime c m)

def PAllowedResidues : Finset ℕ :=
  (unitsMod 7).filter (fun c => 12 * c ^ 2 % 7 = 3)

def RAllowedResidues : Finset ℕ :=
  (unitsMod 14).filter (fun c => 54 * c ^ 2 % 14 = 6)

theorem P_unit_residue_table : unitsMod 7 = {1, 2, 3, 4, 5, 6} := by
  decide

theorem P_allowed_residue_table : PAllowedResidues = {3, 4} := by
  decide

theorem R_unit_residue_table : unitsMod 14 = {1, 3, 5, 9, 11, 13} := by
  decide

theorem R_allowed_residue_table : RAllowedResidues = {5, 9} := by
  decide

theorem allowed_residue_card_certificate :
    (unitsMod 7).card = 6 ∧ PAllowedResidues.card = 2 ∧
    (unitsMod 14).card = 6 ∧ RAllowedResidues.card = 2 := by
  rw [P_unit_residue_table, P_allowed_residue_table,
    R_unit_residue_table, R_allowed_residue_table]
  norm_num

theorem P_top_residue_iff (c : Fin 7) :
    12 * c.val ^ 2 % 7 = 3 ↔ c.val = 3 ∨ c.val = 4 := by
  exact (by decide : ∀ z : Fin 7,
    12 * z.val ^ 2 % 7 = 3 ↔ z.val = 3 ∨ z.val = 4) c

theorem R_top_residue_iff (c : Fin 14) (hc : Nat.Coprime c.val 14) :
    54 * c.val ^ 2 % 14 = 6 ↔ c.val = 5 ∨ c.val = 9 := by
  exact (by decide : ∀ z : Fin 14, Nat.Coprime z.val 14 →
    (54 * z.val ^ 2 % 14 = 6 ↔ z.val = 5 ∨ z.val = 9)) c hc

/-! ## Cleared top-digit inequalities -/

/-- Cleared `P`-branch top-digit classification.  The residue numerator is
the lower-half digit exactly in the residue case `r=3`. -/
theorem P_top_digit_classification
    {p c r d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (hr : r = 3 ∨ r = 5 ∨ r = 6)
    (heq : 7 * d + 41 * c = r * p) :
    0 < d ∧ d < p ∧ (2 * d < p ↔ r = 3) := by
  rcases hr with rfl | rfl | rfl <;> omega

/-- The `Q`-branch top digit is strictly above the lower half. -/
theorem Q_top_digit_large
    {p c d : ℕ} (hp : 130 * c < p)
    (heq : 12 * d = 7 * p + 41 * c) :
    p < 2 * d := by
  omega

/-- Cleared `R`-branch top-digit classification. -/
theorem R_top_digit_classification
    {p c r d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (hr : r = 6 ∨ r = 10 ∨ r = 12)
    (heq : 14 * d + 7 = r * p + 129 * c) :
    0 < d ∧ d < p ∧ (2 * d < p ↔ r = 6) := by
  rcases hr with rfl | rfl | rfl <;> omega

/-- The `S`-branch top digit lies strictly between `p/2` and `p`. -/
theorem S_top_digit_large
    {p c d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (heq : 12 * d + 43 * c + 6 = 7 * p) :
    p < 2 * d ∧ d < p := by
  omega

/-! ## Exact modulus-size certificates -/

theorem switching_moduli : 42 * T = 222138 ∧ 28 * T = 148092 := by
  norm_num [T]

theorem switching_modulus_factorizations :
    42 * T = 2 * 3 ^ 2 * 7 * 41 * 43 ∧
    28 * T = 2 ^ 2 * 3 * 7 * 41 * 43 := by
  norm_num [T]

/-- Exact Euler-totient values of the two divisor-switching moduli. -/
theorem switching_modulus_totients :
    Nat.totient (42 * T) = 60480 ∧
    Nat.totient (28 * T) = 40320 := by
  rw [T_eq]
  constructor
  · rw [show 42 * 5289 = 2 * 9 * 7 * 41 * 43 by norm_num]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 * 9 * 7 * 41) 43)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 * 9 * 7) 41)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 * 9) 7)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime 2 9)]
    rw [show 9 = 3 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num)]
    norm_num [Nat.totient_prime]
  · rw [show 28 * 5289 = 4 * 3 * 7 * 41 * 43 by norm_num]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (4 * 3 * 7 * 41) 43)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (4 * 3 * 7) 41)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (4 * 3) 7)]
    rw [Nat.totient_mul (by norm_num : Nat.Coprime 4 3)]
    rw [show 4 = 2 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num)]
    norm_num [Nat.totient_prime]

theorem switching_allowed_class_count_certificate :
    Nat.totient (42 * T) / 3 = 20160 ∧
    Nat.totient (28 * T) / 3 = 13440 := by
  rw [switching_modulus_totients.1, switching_modulus_totients.2]
  norm_num

/-- Numeric certificate for the `1/3` class fraction after the CRT
equal-fiber argument (the CRT argument itself is analytic-paper intake, not
hidden in this arithmetic theorem). -/
theorem switching_class_count_arithmetic :
    3 * 20160 = 60480 ∧ 3 * 13440 = 40320 := by
  norm_num


end FullDensityCore
end Erdos730

end Campaign180File2

/- Source module: ErdosProblems.Erdos730.DensityEvents -/
section Campaign180File3
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: finite bad-event accounting

This module turns the pointwise consecutive-support transition theorem into
the finite counting statement used by the density proof.  All parameter and
witness collections are honest `Finset`s.  In particular, the obstruction
count is a count of fully witnessed quadruples `(x,p,a,c)`, not merely a
count of parameters for which an unspecified witness exists.

No analytic estimate is asserted here.  The final theorem is only the exact
finite union bound `Bad(X) ≤ E_drop(X) + E_entry(X)`.
-/

namespace Erdos730
namespace DensityEvents

open ConsecutiveTransition FullDensityCore

noncomputable section

/-! ## Finite parameter sets -/

/-- The paper's parameter interval `1 ≤ x ≤ X`. -/
def parameterRange (X : ℕ) : Finset ℕ := Finset.Icc 1 X

/-- Good parameters in the paper family up to `X`. -/
def goodParametersUpTo (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (parameterRange X).filter GoodParameter

/-- Bad parameters in the paper family up to `X`. -/
def badParametersUpTo (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (parameterRange X).filter fun x => ¬GoodParameter x

@[simp] theorem mem_parameterRange {X x : ℕ} :
    x ∈ parameterRange X ↔ 1 ≤ x ∧ x ≤ X := by
  simp [parameterRange]

@[simp] theorem mem_goodParametersUpTo {X x : ℕ} :
    x ∈ goodParametersUpTo X ↔ x ∈ parameterRange X ∧ GoodParameter x := by
  simp [goodParametersUpTo]

@[simp] theorem mem_badParametersUpTo {X x : ℕ} :
    x ∈ badParametersUpTo X ↔ x ∈ parameterRange X ∧ ¬GoodParameter x := by
  simp [badParametersUpTo]

theorem good_bad_disjoint (X : ℕ) :
    Disjoint (goodParametersUpTo X) (badParametersUpTo X) := by
  rw [Finset.disjoint_left]
  intro x hxgood hxbad
  exact (mem_badParametersUpTo.mp hxbad).2
    (mem_goodParametersUpTo.mp hxgood).2

theorem good_union_bad (X : ℕ) :
    goodParametersUpTo X ∪ badParametersUpTo X = parameterRange X := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxgood | hxbad
    · exact (mem_goodParametersUpTo.mp hxgood).1
    · exact (mem_badParametersUpTo.mp hxbad).1
  · intro hx
    by_cases hgood : GoodParameter x
    · exact Finset.mem_union_left _ (mem_goodParametersUpTo.mpr ⟨hx, hgood⟩)
    · exact Finset.mem_union_right _ (mem_badParametersUpTo.mpr ⟨hx, hgood⟩)

theorem parameterRange_card (X : ℕ) : (parameterRange X).card = X := by
  simp [parameterRange]

theorem good_card_add_bad_card (X : ℕ) :
    (goodParametersUpTo X).card + (badParametersUpTo X).card = X := by
  rw [← Finset.card_union_of_disjoint (good_bad_disjoint X), good_union_bad,
    parameterRange_card]

/-! ## Fully witnessed finite obstruction sets -/

/-- A nested product representation of the quadruple `(x,p,a,c)`. -/
abbrev ObstructionWitness := ℕ × (ℕ × (ℕ × ℕ))

def witnessParameter (w : ObstructionWitness) : ℕ := w.1
def witnessPrime (w : ObstructionWitness) : ℕ := w.2.1
def witnessExponent (w : ObstructionWitness) : ℕ := w.2.2.1
def witnessCofactor (w : ObstructionWitness) : ℕ := w.2.2.2

/-- A uniform exclusive upper bound for every coordinate other than `x`.
For `x ≤ X`, both possible transition factors are strictly below this
number. -/
def witnessBound (X : ℕ) : ℕ := 2 * n X + 2

/-- The finite box in which all obstruction witnesses for `x ≤ X` live. -/
def witnessBox (X : ℕ) : Finset ObstructionWitness :=
  (parameterRange X).product
    ((Finset.range (witnessBound X)).product
      ((Finset.range (witnessBound X)).product
        (Finset.range (witnessBound X))))

/-- Fully witnessed drop obstructions `(x,p,a,c)` up to `X`. -/
def dropWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  by
    classical
    exact (witnessBox X).filter fun w =>
      DropObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w)

/-- Fully witnessed entry obstructions `(x,p,a,c)` up to `X`. -/
def entryWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  by
    classical
    exact (witnessBox X).filter fun w =>
      EntryObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w)

/-- Parameters hit by at least one witnessed drop obstruction. -/
def dropParametersUpTo (X : ℕ) : Finset ℕ :=
  (dropWitnessesUpTo X).image witnessParameter

/-- Parameters hit by at least one witnessed entry obstruction. -/
def entryParametersUpTo (X : ℕ) : Finset ℕ :=
  (entryWitnessesUpTo X).image witnessParameter

@[simp] theorem mem_witnessBox {X : ℕ} {w : ObstructionWitness} :
    w ∈ witnessBox X ↔
      w.1 ∈ parameterRange X ∧
      w.2.1 < witnessBound X ∧
      w.2.2.1 < witnessBound X ∧
      w.2.2.2 < witnessBound X := by
  simp [witnessBox]

@[simp] theorem mem_dropWitnessesUpTo {X : ℕ} {w : ObstructionWitness} :
    w ∈ dropWitnessesUpTo X ↔
      w ∈ witnessBox X ∧
      DropObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w) := by
  simp [dropWitnessesUpTo]

@[simp] theorem mem_entryWitnessesUpTo {X : ℕ} {w : ObstructionWitness} :
    w ∈ entryWitnessesUpTo X ↔
      w ∈ witnessBox X ∧
      EntryObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w) := by
  simp [entryWitnessesUpTo]

/-- Every field of an exact prime-power cofactor witness is bounded by the
factor being decomposed. -/
theorem exactPrimePowerCofactor_coordinate_bounds
    {p a c N : ℕ} (hp : p.Prime)
    (h : ExactPrimePowerCofactor p a c N) :
    p ≤ N ∧ a ≤ N ∧ c ≤ N := by
  rcases h with ⟨ha, hN, hpc⟩
  have hc : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc0
    subst c
    exact hpc (dvd_zero p)
  have hpow : 0 < p ^ a := pow_pos hp.pos a
  constructor
  · calc
      p ≤ p ^ a := Nat.le_pow ha
      _ ≤ p ^ a * c := Nat.le_mul_of_pos_right _ hc
      _ = N := hN.symm
  constructor
  · calc
      a ≤ p ^ a := (Nat.lt_pow_self hp.one_lt).le
      _ ≤ p ^ a * c := Nat.le_mul_of_pos_right _ hc
      _ = N := hN.symm
  · calc
      c ≤ p ^ a * c := Nat.le_mul_of_pos_left _ hpow
      _ = N := hN.symm

theorem n_mono {x X : ℕ} (hx : x ≤ X) : n x ≤ n X :=
  n_strictMono.monotone hx

theorem drop_factor_lt_witnessBound {x X : ℕ} (hx : x ≤ X) :
    n x + 1 < witnessBound X := by
  have hmono := n_mono hx
  simp only [witnessBound]
  omega

theorem entry_factor_lt_witnessBound {x X : ℕ} (hx : x ≤ X) :
    2 * n x + 1 < witnessBound X := by
  have hmono := n_mono hx
  simp only [witnessBound]
  omega

/-- A pointwise drop obstruction supplied by Proposition 1 belongs to the
finite witnessed drop set. -/
theorem dropWitness_mem
    {X x p a c : ℕ} (hx : x ∈ parameterRange X)
    (hobs : DropObstruction (n x) p a c) :
    (x, (p, (a, c))) ∈ dropWitnessesUpTo X := by
  rcases hobs with ⟨hp, hp2, hexact, hlow⟩
  have hb := drop_factor_lt_witnessBound (mem_parameterRange.mp hx).2
  rcases exactPrimePowerCofactor_coordinate_bounds hp hexact with
    ⟨hpN, haN, hcN⟩
  rw [mem_dropWitnessesUpTo]
  refine ⟨?_, hp, hp2, hexact, hlow⟩
  rw [mem_witnessBox]
  exact ⟨hx, hpN.trans_lt hb, haN.trans_lt hb, hcN.trans_lt hb⟩

/-- A pointwise entry obstruction supplied by Proposition 1 belongs to the
finite witnessed entry set. -/
theorem entryWitness_mem
    {X x p a c : ℕ} (hx : x ∈ parameterRange X)
    (hobs : EntryObstruction (n x) p a c) :
    (x, (p, (a, c))) ∈ entryWitnessesUpTo X := by
  rcases hobs with ⟨hp, hp2, hexact, hlow⟩
  have hb := entry_factor_lt_witnessBound (mem_parameterRange.mp hx).2
  rcases exactPrimePowerCofactor_coordinate_bounds hp hexact with
    ⟨hpN, haN, hcN⟩
  rw [mem_entryWitnessesUpTo]
  refine ⟨?_, hp, hp2, hexact, hlow⟩
  rw [mem_witnessBox]
  exact ⟨hx, hpN.trans_lt hb, haN.trans_lt hb, hcN.trans_lt hb⟩

theorem prime_dvd_factor_of_exactPrimePowerCofactor
    {p a c N : ℕ} (h : ExactPrimePowerCofactor p a c N) : p ∣ N := by
  rcases h with ⟨ha, hN, _hpc⟩
  rw [hN]
  exact dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') c

/-- The same quadruple cannot be both a drop and an entry witness: its prime
would divide the coprime factors `n+1` and `2n+1`. -/
theorem drop_entry_witnesses_disjoint (X : ℕ) :
    Disjoint (dropWitnessesUpTo X) (entryWitnessesUpTo X) := by
  rw [Finset.disjoint_left]
  intro w hdrop hentry
  rcases w with ⟨x, ⟨p, ⟨a, c⟩⟩⟩
  rcases (mem_dropWitnessesUpTo.mp hdrop).2 with
    ⟨hp, _hp2, hexactDrop, _hlowDrop⟩
  rcases (mem_entryWitnessesUpTo.mp hentry).2 with
    ⟨_hp, _hp2, hexactEntry, _hlowEntry⟩
  have hpDrop : p ∣ n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hexactDrop
  have hpEntry : p ∣ 2 * n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hexactEntry
  exact (not_dvd_two_mul_add_one_of_dvd_succ hp hpDrop) hpEntry

/-! ## Pointwise coverage and the finite union bound -/

/-- Every bad paper-family parameter up to `X` is hit by a witnessed drop
or entry event. -/
theorem bad_mem_dropParameters_or_entryParameters
    {X x : ℕ} (hx : x ∈ badParametersUpTo X) :
    x ∈ dropParametersUpTo X ∨ x ∈ entryParametersUpTo X := by
  rcases mem_badParametersUpTo.mp hx with ⟨hxrange, hnotgood⟩
  have hxone : 1 ≤ x := (mem_parameterRange.mp hxrange).1
  have hbad :
      (n x).centralBinom.primeFactors ≠
        (n x + 1).centralBinom.primeFactors := by
    intro heq
    exact hnotgood ⟨hxone, heq⟩
  have hnpos : 0 < n x := by
    rw [n_expansion]
    omega
  rcases exists_obstruction_of_primeFactors_ne hnpos hbad with
    ⟨p, a, c, hdrop⟩ | ⟨p, a, c, hentry⟩
  · left
    rw [dropParametersUpTo, Finset.mem_image]
    exact ⟨(x, (p, (a, c))), dropWitness_mem hxrange hdrop, rfl⟩
  · right
    rw [entryParametersUpTo, Finset.mem_image]
    exact ⟨(x, (p, (a, c))), entryWitness_mem hxrange hentry, rfl⟩

theorem bad_subset_drop_union_entry (X : ℕ) :
    badParametersUpTo X ⊆ dropParametersUpTo X ∪ entryParametersUpTo X := by
  intro x hx
  exact Finset.mem_union.mpr (bad_mem_dropParameters_or_entryParameters hx)

/-- Parameter-level finite union bound. -/
theorem bad_card_le_dropParameters_add_entryParameters (X : ℕ) :
    (badParametersUpTo X).card ≤
      (dropParametersUpTo X).card + (entryParametersUpTo X).card := by
  exact (Finset.card_le_card (bad_subset_drop_union_entry X)).trans
    (Finset.card_union_le _ _)

theorem dropParameters_card_le_dropWitnesses_card (X : ℕ) :
    (dropParametersUpTo X).card ≤ (dropWitnessesUpTo X).card := by
  exact Finset.card_image_le

theorem entryParameters_card_le_entryWitnesses_card (X : ℕ) :
    (entryParametersUpTo X).card ≤ (entryWitnessesUpTo X).card := by
  exact Finset.card_image_le

/-- **Exact finite form of equation (22).**  The number of bad parameters
is at most the number of witnessed drop quadruples plus the number of
witnessed entry quadruples. -/
theorem bad_card_le_witnessed_obstruction_count (X : ℕ) :
    (badParametersUpTo X).card ≤
      (dropWitnessesUpTo X).card + (entryWitnessesUpTo X).card := by
  exact (bad_card_le_dropParameters_add_entryParameters X).trans
    (Nat.add_le_add (dropParameters_card_le_dropWitnesses_card X)
      (entryParameters_card_le_entryWitnesses_card X))

/-! ## Exact four-range partition

The analytic proof later chooses the two cutoffs to be `sqrt X` and
`sqrt X * (log X)^2`.  Here they remain arbitrary natural numbers.  This
section proves only the finite, disjoint classification and makes no claim
about the size of any part.
-/

/-- All witnessed transition obstructions, with duplicates between the two
event types removed. -/
def obstructionWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  dropWitnessesUpTo X ∪ entryWitnessesUpTo X

theorem obstructionWitnesses_card_eq_drop_add_entry (X : ℕ) :
    (obstructionWitnessesUpTo X).card =
      (dropWitnessesUpTo X).card + (entryWitnessesUpTo X).card := by
  rw [obstructionWitnessesUpTo,
    Finset.card_union_of_disjoint (drop_entry_witnesses_disjoint X)]

/-- Equation (22) with `E(X)` represented by the single finite obstruction
witness set. -/
theorem bad_card_le_obstructionWitnesses_card (X : ℕ) :
    (badParametersUpTo X).card ≤ (obstructionWitnessesUpTo X).card := by
  rw [obstructionWitnesses_card_eq_drop_add_entry]
  exact bad_card_le_witnessed_obstruction_count X

/-- The `a ≥ 2` range. -/
def higherPowerWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w => 2 ≤ witnessExponent w

/-- The `a=1, p≤smallCut` range. -/
def smallPrimeWitnessesUpTo (X smallCut : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w =>
    witnessExponent w = 1 ∧ witnessPrime w ≤ smallCut

/-- The `a=1, smallCut<p≤topCut` transition range. -/
def transitionPrimeWitnessesUpTo
    (X smallCut topCut : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w =>
    witnessExponent w = 1 ∧
      smallCut < witnessPrime w ∧ witnessPrime w ≤ topCut

/-- The `a=1, topCut<p` top range. -/
def topPrimeWitnessesUpTo (X topCut : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w =>
    witnessExponent w = 1 ∧ topCut < witnessPrime w

@[simp] theorem mem_obstructionWitnessesUpTo
    {X : ℕ} {w : ObstructionWitness} :
    w ∈ obstructionWitnessesUpTo X ↔
      w ∈ dropWitnessesUpTo X ∨ w ∈ entryWitnessesUpTo X := by
  simp [obstructionWitnessesUpTo]

@[simp] theorem mem_higherPowerWitnessesUpTo
    {X : ℕ} {w : ObstructionWitness} :
    w ∈ higherPowerWitnessesUpTo X ↔
      w ∈ obstructionWitnessesUpTo X ∧ 2 ≤ witnessExponent w := by
  simp [higherPowerWitnessesUpTo]

@[simp] theorem mem_smallPrimeWitnessesUpTo
    {X smallCut : ℕ} {w : ObstructionWitness} :
    w ∈ smallPrimeWitnessesUpTo X smallCut ↔
      w ∈ obstructionWitnessesUpTo X ∧
        witnessExponent w = 1 ∧ witnessPrime w ≤ smallCut := by
  simp [smallPrimeWitnessesUpTo]

@[simp] theorem mem_transitionPrimeWitnessesUpTo
    {X smallCut topCut : ℕ} {w : ObstructionWitness} :
    w ∈ transitionPrimeWitnessesUpTo X smallCut topCut ↔
      w ∈ obstructionWitnessesUpTo X ∧
        witnessExponent w = 1 ∧
          smallCut < witnessPrime w ∧ witnessPrime w ≤ topCut := by
  simp [transitionPrimeWitnessesUpTo]

@[simp] theorem mem_topPrimeWitnessesUpTo
    {X topCut : ℕ} {w : ObstructionWitness} :
    w ∈ topPrimeWitnessesUpTo X topCut ↔
      w ∈ obstructionWitnessesUpTo X ∧
        witnessExponent w = 1 ∧ topCut < witnessPrime w := by
  simp [topPrimeWitnessesUpTo]

theorem obstructionWitness_exponent_pos
    {X : ℕ} {w : ObstructionWitness}
    (hw : w ∈ obstructionWitnessesUpTo X) :
    0 < witnessExponent w := by
  rcases mem_obstructionWitnessesUpTo.mp hw with hdrop | hentry
  · rcases (mem_dropWitnessesUpTo.mp hdrop).2 with
      ⟨_hp, _hp2, hexact, _hlow⟩
    exact hexact.1
  · rcases (mem_entryWitnessesUpTo.mp hentry).2 with
      ⟨_hp, _hp2, hexact, _hlow⟩
    exact hexact.1

/-- The four ranges are exhaustive.  The endpoint conventions are exact:
`p=smallCut` lies in the small range and `p=topCut` in the transition
range. -/
theorem obstructionWitnesses_fourRange
    (X smallCut topCut : ℕ) :
    obstructionWitnessesUpTo X =
      higherPowerWitnessesUpTo X ∪
        (smallPrimeWitnessesUpTo X smallCut ∪
          (transitionPrimeWitnessesUpTo X smallCut topCut ∪
            topPrimeWitnessesUpTo X topCut)) := by
  ext w
  constructor
  · intro hw
    have ha := obstructionWitness_exponent_pos hw
    by_cases hhigh : 2 ≤ witnessExponent w
    · exact Finset.mem_union_left _
        (mem_higherPowerWitnessesUpTo.mpr ⟨hw, hhigh⟩)
    have haone : witnessExponent w = 1 := by omega
    by_cases hsmall : witnessPrime w ≤ smallCut
    · exact Finset.mem_union_right _ <| Finset.mem_union_left _ <|
        mem_smallPrimeWitnessesUpTo.mpr ⟨hw, haone, hsmall⟩
    by_cases htransition : witnessPrime w ≤ topCut
    · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <|
        Finset.mem_union_left _ <|
          mem_transitionPrimeWitnessesUpTo.mpr
            ⟨hw, haone, Nat.lt_of_not_ge hsmall, htransition⟩
    · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <|
        Finset.mem_union_right _ <|
          mem_topPrimeWitnessesUpTo.mpr
            ⟨hw, haone, Nat.lt_of_not_ge htransition⟩
  · intro hw
    rcases Finset.mem_union.mp hw with hhigh | hrest
    · exact (mem_higherPowerWitnessesUpTo.mp hhigh).1
    rcases Finset.mem_union.mp hrest with hsmall | hrest
    · exact (mem_smallPrimeWitnessesUpTo.mp hsmall).1
    rcases Finset.mem_union.mp hrest with htransition | htop
    · exact (mem_transitionPrimeWitnessesUpTo.mp htransition).1
    · exact (mem_topPrimeWitnessesUpTo.mp htop).1

theorem higherPower_disjoint_otherRanges
    (X smallCut topCut : ℕ) :
    Disjoint (higherPowerWitnessesUpTo X)
      (smallPrimeWitnessesUpTo X smallCut ∪
        (transitionPrimeWitnessesUpTo X smallCut topCut ∪
          topPrimeWitnessesUpTo X topCut)) := by
  rw [Finset.disjoint_left]
  intro w hhigh hrest
  have ha2 := (mem_higherPowerWitnessesUpTo.mp hhigh).2
  rcases Finset.mem_union.mp hrest with hsmall | hrest
  · have ha1 := (mem_smallPrimeWitnessesUpTo.mp hsmall).2.1
    omega
  rcases Finset.mem_union.mp hrest with htransition | htop
  · have ha1 := (mem_transitionPrimeWitnessesUpTo.mp htransition).2.1
    omega
  · have ha1 := (mem_topPrimeWitnessesUpTo.mp htop).2.1
    omega

theorem smallPrime_disjoint_largerRanges
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    Disjoint (smallPrimeWitnessesUpTo X smallCut)
      (transitionPrimeWitnessesUpTo X smallCut topCut ∪
        topPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w hsmall hrest
  have hpSmall := (mem_smallPrimeWitnessesUpTo.mp hsmall).2.2
  rcases Finset.mem_union.mp hrest with htransition | htop
  · have hpLarge := (mem_transitionPrimeWitnessesUpTo.mp htransition).2.2.1
    omega
  · have hpTop := (mem_topPrimeWitnessesUpTo.mp htop).2.2
    omega

theorem transitionPrime_disjoint_topRange
    (X smallCut topCut : ℕ) :
    Disjoint (transitionPrimeWitnessesUpTo X smallCut topCut)
      (topPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w htransition htop
  have hpLe := (mem_transitionPrimeWitnessesUpTo.mp htransition).2.2.2
  have hpGt := (mem_topPrimeWitnessesUpTo.mp htop).2.2
  omega

/-- Cardinal form of the exact, disjoint four-range partition. -/
theorem obstructionWitnesses_card_fourRange
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (obstructionWitnessesUpTo X).card =
      (higherPowerWitnessesUpTo X).card +
        ((smallPrimeWitnessesUpTo X smallCut).card +
          ((transitionPrimeWitnessesUpTo X smallCut topCut).card +
            (topPrimeWitnessesUpTo X topCut).card)) := by
  rw [obstructionWitnesses_fourRange X smallCut topCut,
    Finset.card_union_of_disjoint
      (higherPower_disjoint_otherRanges X smallCut topCut),
    Finset.card_union_of_disjoint
      (smallPrime_disjoint_largerRanges X smallCut topCut hcuts),
    Finset.card_union_of_disjoint
      (transitionPrime_disjoint_topRange X smallCut topCut)]

/-- Exact cardinal form of equations (22)--(24): the two witnessed event
counts split into the four disjoint ranges. -/
theorem witnessed_obstruction_count_card_fourRange
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (dropWitnessesUpTo X).card + (entryWitnessesUpTo X).card =
      (higherPowerWitnessesUpTo X).card +
        ((smallPrimeWitnessesUpTo X smallCut).card +
          ((transitionPrimeWitnessesUpTo X smallCut topCut).card +
            (topPrimeWitnessesUpTo X topCut).card)) := by
  rw [← obstructionWitnesses_card_eq_drop_add_entry]
  exact obstructionWitnesses_card_fourRange X smallCut topCut hcuts


end

end DensityEvents
end Erdos730

end Campaign180File3

/- Source module: ErdosProblems.Erdos730.BranchEvents -/
section Campaign180File4
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: assigning every transition obstruction to a linear branch

The finite event ledger first records a drop or entry obstruction against the
products `P*Q` and `3*R*S`.  The analytic argument counts four linear-branch
events instead.  This file proves the exact bridge between those two views.

The only exceptional product factor is `3`.  We prove directly that it can
never be an entry obstruction: its exact quotient is `R*S`, and the least
base-three digit of `(R*S-1)/2` is `2`, outside the lower half.
-/

namespace Erdos730
namespace BranchEvents

open ConsecutiveTransition DensityEvents FullDensityCore KummerTransition

set_option backward.isDefEq.respectTransparency false in
inductive Branch where
  | P | Q | R | S
  deriving DecidableEq, Fintype, Repr

/-- The linear factor belonging to a branch. -/
def branchValue : Branch → ℕ → ℕ
  | .P => FullDensityCore.P
  | .Q => FullDensityCore.Q
  | .R => FullDensityCore.R
  | .S => FullDensityCore.S

/-- A global transition obstruction tagged by the branch containing its
prime.  The cofactor is still the exact cofactor of `P*Q` or `3*R*S`; later
branch-map lemmas identify it with the corresponding `Phi` value. -/
def TaggedObstruction (L : Branch) (x p a c : ℕ) : Prop :=
  match L with
  | .P => DropObstruction (n x) p a c ∧ p ∣ P x
  | .Q => DropObstruction (n x) p a c ∧ p ∣ Q x
  | .R => EntryObstruction (n x) p a c ∧ p ∣ R x
  | .S => EntryObstruction (n x) p a c ∧ p ∣ S x

/-! ## The fixed factor `3` is harmless -/

theorem R_mul_S_eq_six_mul_add_five (x : ℕ) :
    R x * S x =
      6 * (6 * (24682 * x) * (63468 * x + 3) +
        24682 * x + 5 * (63468 * x + 3)) + 5 := by
  simp only [R, S, T]
  ring

theorem R_mul_S_mod_three (x : ℕ) : R x * S x % 3 = 2 := by
  rw [R_mul_S_eq_six_mul_add_five]
  omega

theorem R_mul_S_not_dvd_three (x : ℕ) : ¬3 ∣ R x * S x := by
  rw [Nat.dvd_iff_mod_eq_zero, R_mul_S_mod_three]
  norm_num

theorem entry_three_exact_cofactor
    {x a c : ℕ}
    (hexact : ExactPrimePowerCofactor 3 a c (2 * n x + 1)) :
    a = 1 ∧ c = R x * S x := by
  rcases hexact with ⟨ha, hfac, hthreec⟩
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hfactor : 3 * (R x * S x) = 3 * (3 ^ b * c) := by
    rw [two_n_add_one] at hfac
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hfac
  have hcancel : R x * S x = 3 ^ b * c :=
    Nat.mul_left_cancel (by norm_num) hfactor
  have hbzero : b = 0 := by
    by_contra hb
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hthreePow : 3 ∣ 3 ^ b := dvd_pow_self 3 hbpos.ne'
    have hthreeRS : 3 ∣ R x * S x := by
      rw [hcancel]
      exact dvd_mul_of_dvd_left hthreePow c
    exact R_mul_S_not_dvd_three x hthreeRS
  subst b
  simpa using hcancel.symm

theorem entry_three_test_eq_three_mul_add_two (x : ℕ) :
    (R x * S x - 1) / 2 =
      3 * (6 * (24682 * x) * (63468 * x + 3) +
        24682 * x + 5 * (63468 * x + 3)) + 2 := by
  rw [R_mul_S_eq_six_mul_add_five]
  omega

theorem entry_three_test_mod (x : ℕ) :
    (R x * S x - 1) / 2 % 3 = 2 := by
  rw [entry_three_test_eq_three_mul_add_two]
  omega

theorem not_lowerHalfDigits_entry_three (x : ℕ) :
    ¬LowerHalfDigits 3 ((R x * S x - 1) / 2) := by
  intro hlow
  let t := (R x * S x - 1) / 2
  have htpos : 0 < t := by
    dsimp [t]
    rw [entry_three_test_eq_three_mul_add_two]
    omega
  have hdigits : t % 3 ∈ Nat.digits 3 t := by
    rw [Nat.digits_eq_cons_digits_div (by norm_num) htpos.ne']
    simp
  have hhalf := hlow (t % 3) hdigits
  have htmod : t % 3 = 2 := by
    simpa [t] using entry_three_test_mod x
  norm_num [htmod] at hhalf

theorem entry_obstruction_prime_ne_three
    {x p a c : ℕ} (hobs : EntryObstruction (n x) p a c) : p ≠ 3 := by
  rintro rfl
  rcases hobs with ⟨_hprime, _hne2, hexact, hlow⟩
  rcases entry_three_exact_cofactor hexact with ⟨rfl, rfl⟩
  exact not_lowerHalfDigits_entry_three x hlow

/-! ## Existence of a branch tag -/

theorem dropObstruction_has_branch
    {x p a c : ℕ} (hobs : DropObstruction (n x) p a c) :
    TaggedObstruction .P x p a c ∨ TaggedObstruction .Q x p a c := by
  have hp := hobs.1
  have hpFactor : p ∣ n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hobs.2.2.1
  rw [n_add_one] at hpFactor
  rcases hp.dvd_mul.mp hpFactor with hpP | hpQ
  · exact Or.inl ⟨hobs, hpP⟩
  · exact Or.inr ⟨hobs, hpQ⟩

theorem entryObstruction_has_branch
    {x p a c : ℕ} (hobs : EntryObstruction (n x) p a c) :
    TaggedObstruction .R x p a c ∨ TaggedObstruction .S x p a c := by
  have hp := hobs.1
  have hp3 : p ≠ 3 := entry_obstruction_prime_ne_three hobs
  have hpFactor : p ∣ 2 * n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hobs.2.2.1
  rw [two_n_add_one] at hpFactor
  rcases hp.dvd_mul.mp hpFactor with hpThree | hpRS
  · exact (hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpThree)).elim
  · rcases hp.dvd_mul.mp hpRS with hpR | hpS
    · exact Or.inl ⟨hobs, hpR⟩
    · exact Or.inr ⟨hobs, hpS⟩

/-- Every fully witnessed obstruction has one of the four branch tags. -/
theorem obstruction_has_branch
    {x p a c : ℕ}
    (hobs : DropObstruction (n x) p a c ∨ EntryObstruction (n x) p a c) :
    ∃ L, TaggedObstruction L x p a c := by
  rcases hobs with hdrop | hentry
  · rcases dropObstruction_has_branch hdrop with hP | hQ
    · exact ⟨.P, hP⟩
    · exact ⟨.Q, hQ⟩
  · rcases entryObstruction_has_branch hentry with hR | hS
    · exact ⟨.R, hR⟩
    · exact ⟨.S, hS⟩

/-! ## Recovering the exact branch cofactor -/

/-- If an exact prime power in a coprime product belongs to the left factor,
then the same exponent is exact in that factor and the global cofactor is the
local cofactor times the right factor. -/
theorem exactPrimePowerCofactor_left_of_coprime_product
    {p a c N A B : ℕ} (hp : p.Prime)
    (hexact : ExactPrimePowerCofactor p a c N)
    (hprod : N = A * B) (hcop : Nat.Coprime A B) (hpA : p ∣ A) :
    ∃ d, ExactPrimePowerCofactor p a d A ∧ c = d * B := by
  rcases hexact with ⟨ha, hN, hpc⟩
  have hpCopB : Nat.Coprime p B := hcop.coprime_dvd_left hpA
  have hpowProd : p ^ a ∣ A * B := by
    rw [← hprod, hN]
    exact dvd_mul_right _ _
  have hpowA : p ^ a ∣ A :=
    (hpCopB.pow_left a).dvd_of_dvd_mul_right hpowProd
  obtain ⟨d, hA⟩ := hpowA
  have hcancel : d * B = c := by
    apply Nat.mul_left_cancel (pow_pos hp.pos a)
    calc
      p ^ a * (d * B) = (p ^ a * d) * B := by ring
      _ = A * B := by rw [hA]
      _ = N := hprod.symm
      _ = p ^ a * c := hN
  have hpd : ¬p ∣ d := by
    intro hd
    apply hpc
    rw [← hcancel]
    exact dvd_mul_of_dvd_left hd B
  exact ⟨d, ⟨ha, hA, hpd⟩, hcancel.symm⟩

/-- Right-factor version of the preceding exact-cofactor lemma. -/
theorem exactPrimePowerCofactor_right_of_coprime_product
    {p a c N A B : ℕ} (hp : p.Prime)
    (hexact : ExactPrimePowerCofactor p a c N)
    (hprod : N = A * B) (hcop : Nat.Coprime A B) (hpB : p ∣ B) :
    ∃ d, ExactPrimePowerCofactor p a d B ∧ c = d * A := by
  apply exactPrimePowerCofactor_left_of_coprime_product hp hexact
      (hprod.trans (Nat.mul_comm A B)) hcop.symm hpB

/-- The obstruction value after extracting the exact prime power from one
linear branch.  These are the natural-number versions of `PhiP`--`PhiS`. -/
def branchTestValue : Branch → ℕ → ℕ → ℕ
  | .P, x, d => d * Q x
  | .Q, x, d => d * P x
  | .R, x, d => (3 * d * S x - 1) / 2
  | .S, x, d => (3 * d * R x - 1) / 2

/-- Cofactor of the full transition factor reconstructed from a local branch
cofactor. -/
def branchGlobalCofactor : Branch → ℕ → ℕ → ℕ
  | .P, x, d => d * Q x
  | .Q, x, d => d * P x
  | .R, x, d => 3 * d * S x
  | .S, x, d => 3 * d * R x

/-- Exact local branch event counted by the analytic argument. -/
def LocalBranchObstruction (L : Branch) (x p a d : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ExactPrimePowerCofactor p a d (branchValue L x) ∧
      LowerHalfDigits p (branchTestValue L x d)

theorem R_coprime_three_mul_S (x : ℕ) :
    Nat.Coprime (R x) (3 * S x) := by
  have hR3 : Nat.Coprime (R x) 3 := by
    apply ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num : Nat.Prime 3)).2 ?_).symm
    rw [Nat.dvd_iff_mod_eq_zero, (branch_mod_3 x).2.2.1]
    norm_num
  exact hR3.mul_right (R_S_coprime x)

theorem S_coprime_three_mul_R (x : ℕ) :
    Nat.Coprime (S x) (3 * R x) := by
  have hS3 : Nat.Coprime (S x) 3 := by
    apply ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num : Nat.Prime 3)).2 ?_).symm
    rw [Nat.dvd_iff_mod_eq_zero, (branch_mod_3 x).2.2.2]
    norm_num
  exact hS3.mul_right (R_S_coprime x).symm

/-- A tagged global obstruction supplies the exact local branch cofactor and
recovers its original global cofactor exactly. -/
theorem taggedObstruction_has_local_exact
    {L : Branch} {x p a c : ℕ}
    (h : TaggedObstruction L x p a c) :
    ∃ d, LocalBranchObstruction L x p a d ∧
      branchGlobalCofactor L x d = c := by
  cases L with
  | P =>
      rcases h with ⟨hobs, hpP⟩
      rcases exactPrimePowerCofactor_left_of_coprime_product hobs.1
          hobs.2.2.1 (n_add_one x) (P_Q_coprime x) hpP with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc] using hobs.2.2.2⟩,
        by simpa [branchGlobalCofactor] using hc.symm⟩
  | Q =>
      rcases h with ⟨hobs, hpQ⟩
      rcases exactPrimePowerCofactor_right_of_coprime_product hobs.1
          hobs.2.2.1 (n_add_one x) (P_Q_coprime x) hpQ with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc] using hobs.2.2.2⟩,
        by simpa [branchGlobalCofactor] using hc.symm⟩
  | R =>
      rcases h with ⟨hobs, hpR⟩
      have hprod : 2 * n x + 1 = R x * (3 * S x) := by
        rw [two_n_add_one]
        ring
      rcases exactPrimePowerCofactor_left_of_coprime_product hobs.1
          hobs.2.2.1 hprod (R_coprime_three_mul_S x) hpR with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc, mul_assoc, mul_left_comm, mul_comm]
          using hobs.2.2.2⟩, by
        simpa [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
          using hc.symm⟩
  | S =>
      rcases h with ⟨hobs, hpS⟩
      have hprod : 2 * n x + 1 = S x * (3 * R x) := by
        rw [two_n_add_one]
        ring
      rcases exactPrimePowerCofactor_left_of_coprime_product hobs.1
          hobs.2.2.1 hprod (S_coprime_three_mul_R x) hpS with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc, mul_assoc, mul_left_comm, mul_comm]
          using hobs.2.2.2⟩, by
        simpa [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
          using hc.symm⟩

/-- Existential form used by event-counting clients. -/
theorem taggedObstruction_has_local
    {L : Branch} {x p a c : ℕ}
    (h : TaggedObstruction L x p a c) :
    ∃ d, LocalBranchObstruction L x p a d := by
  obtain ⟨d, hd, _⟩ := taggedObstruction_has_local_exact h
  exact ⟨d, hd⟩

/-! ## Finite local-branch event ledger -/

abbrev LocalBranchWitness := Branch × ObstructionWitness

def localWitnessBranch (w : LocalBranchWitness) : Branch := w.1
def localWitnessParameter (w : LocalBranchWitness) : ℕ := w.2.1
def localWitnessPrime (w : LocalBranchWitness) : ℕ := w.2.2.1
def localWitnessExponent (w : LocalBranchWitness) : ℕ := w.2.2.2.1
def localWitnessCofactor (w : LocalBranchWitness) : ℕ := w.2.2.2.2

def localBranchWitnessBox (X : ℕ) : Finset LocalBranchWitness :=
  Finset.univ.product (witnessBox X)

noncomputable def localBranchWitnessesUpTo (X : ℕ) : Finset LocalBranchWitness := by
  classical
  exact (localBranchWitnessBox X).filter fun w =>
    LocalBranchObstruction (localWitnessBranch w)
      (localWitnessParameter w) (localWitnessPrime w)
      (localWitnessExponent w) (localWitnessCofactor w)

@[simp] theorem mem_localBranchWitnessesUpTo
    {X : ℕ} {w : LocalBranchWitness} :
    w ∈ localBranchWitnessesUpTo X ↔
      w.2 ∈ witnessBox X ∧
        LocalBranchObstruction (localWitnessBranch w)
          (localWitnessParameter w) (localWitnessPrime w)
          (localWitnessExponent w) (localWitnessCofactor w) := by
  simp [localBranchWitnessesUpTo, localBranchWitnessBox]

theorem branchValue_lt_witnessBound
    {X x : ℕ} (L : Branch) (hx : x ∈ parameterRange X) :
    branchValue L x < witnessBound X := by
  have hxle := (mem_parameterRange.mp hx).2
  cases L with
  | P =>
      have hQ := (branches_positive x).2.1
      exact (Nat.le_mul_of_pos_right (P x) hQ).trans_lt (by
        rw [← n_add_one]
        exact drop_factor_lt_witnessBound hxle)
  | Q =>
      have hP := (branches_positive x).1
      exact (Nat.le_mul_of_pos_left (Q x) hP).trans_lt (by
        simpa [n_add_one, Nat.mul_comm] using
          drop_factor_lt_witnessBound hxle)
  | R =>
      have h3S : 0 < 3 * S x := mul_pos (by norm_num) (branches_positive x).2.2.2
      exact (Nat.le_mul_of_pos_right (R x) h3S).trans_lt (by
        rw [show R x * (3 * S x) = 3 * (R x * S x) by ring,
          ← two_n_add_one]
        exact entry_factor_lt_witnessBound hxle)
  | S =>
      have h3R : 0 < 3 * R x := mul_pos (by norm_num) (branches_positive x).2.2.1
      exact (Nat.le_mul_of_pos_right (S x) h3R).trans_lt (by
        rw [show S x * (3 * R x) = 3 * (R x * S x) by ring,
          ← two_n_add_one]
        exact entry_factor_lt_witnessBound hxle)

theorem localBranchWitness_mem
    {X x p a d : ℕ} {L : Branch}
    (hx : x ∈ parameterRange X)
    (hlocal : LocalBranchObstruction L x p a d) :
    (L, (x, (p, (a, d)))) ∈ localBranchWitnessesUpTo X := by
  rw [mem_localBranchWitnessesUpTo, mem_witnessBox]
  have hb := branchValue_lt_witnessBound L hx
  rcases exactPrimePowerCofactor_coordinate_bounds
      hlocal.1 hlocal.2.2.1 with ⟨hpB, haB, hdB⟩
  exact ⟨⟨hx, hpB.trans_lt hb, haB.trans_lt hb, hdB.trans_lt hb⟩, hlocal⟩

theorem localBranchObstruction_globalizes
    {L : Branch} {x p a d : ℕ}
    (h : LocalBranchObstruction L x p a d) :
    TaggedObstruction L x p a (branchGlobalCofactor L x d) := by
  rcases h with ⟨hp, hp2, hexact, hlow⟩
  have hpd := hexact.2.2
  have hpBranch := prime_dvd_factor_of_exactPrimePowerCofactor hexact
  cases L with
  | P =>
      change ExactPrimePowerCofactor p a d (P x) at hexact
      change p ∣ P x at hpBranch
      have hpQ : ¬p ∣ Q x := by
        intro hpQ
        apply hp.not_dvd_one
        rw [← P_Q_coprime x]
        exact Nat.dvd_gcd hpBranch hpQ
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hd | hQ
        · exact hpd hd
        · exact hpQ hQ
      · simpa [branchTestValue, branchGlobalCofactor] using hlow
  | Q =>
      change ExactPrimePowerCofactor p a d (Q x) at hexact
      change p ∣ Q x at hpBranch
      have hpP : ¬p ∣ P x := by
        intro hpP
        apply hp.not_dvd_one
        rw [← P_Q_coprime x]
        exact Nat.dvd_gcd hpP hpBranch
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hd | hP
        · exact hpd hd
        · exact hpP hP
      · simpa [branchTestValue, branchGlobalCofactor] using hlow
  | R =>
      change ExactPrimePowerCofactor p a d (R x) at hexact
      change p ∣ R x at hpBranch
      have hp3 : ¬p ∣ 3 := by
        intro hpThree
        have hpeq : p = 3 :=
          (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpThree
        subst p
        exact R_mul_S_not_dvd_three x
          (dvd_mul_of_dvd_left hpBranch (S x))
      have hpS : ¬p ∣ S x := by
        intro hpS
        apply hp.not_dvd_one
        rw [← R_S_coprime x]
        exact Nat.dvd_gcd hpBranch hpS
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [two_n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hthreeD | hpS'
        · rcases hp.dvd_mul.mp hthreeD with hpThree | hd
          · exact hp3 hpThree
          · exact hpd hd
        · exact hpS hpS'
      · simpa [branchTestValue, branchGlobalCofactor] using hlow
  | S =>
      change ExactPrimePowerCofactor p a d (S x) at hexact
      change p ∣ S x at hpBranch
      have hp3 : ¬p ∣ 3 := by
        intro hpThree
        have hpeq : p = 3 :=
          (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpThree
        subst p
        exact R_mul_S_not_dvd_three x
          (dvd_mul_of_dvd_right hpBranch (R x))
      have hpR : ¬p ∣ R x := by
        intro hpR
        apply hp.not_dvd_one
        rw [← R_S_coprime x]
        exact Nat.dvd_gcd hpR hpBranch
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [two_n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hthreeD | hpR'
        · rcases hp.dvd_mul.mp hthreeD with hpThree | hd
          · exact hp3 hpThree
          · exact hpd hd
        · exact hpR hpR'
      · simpa [branchTestValue, branchGlobalCofactor] using hlow

/-- Forget the branch tag and local cofactor, reconstructing the original
global obstruction witness. -/
def globalizeLocalWitness (w : LocalBranchWitness) : ObstructionWitness :=
  (localWitnessParameter w,
    (localWitnessPrime w,
      (localWitnessExponent w,
        branchGlobalCofactor (localWitnessBranch w)
          (localWitnessParameter w) (localWitnessCofactor w))))

theorem globalizeLocalWitness_mem
    {X : ℕ} {w : LocalBranchWitness}
    (hw : w ∈ localBranchWitnessesUpTo X) :
    globalizeLocalWitness w ∈ obstructionWitnessesUpTo X := by
  rcases w with ⟨L, ⟨x, p, a, d⟩⟩
  have hmem := mem_localBranchWitnessesUpTo.mp hw
  have hx : x ∈ parameterRange X := (mem_witnessBox.mp hmem.1).1
  have htag := localBranchObstruction_globalizes hmem.2
  rw [mem_obstructionWitnessesUpTo]
  cases L with
  | P => exact Or.inl (dropWitness_mem hx htag.1)
  | Q => exact Or.inl (dropWitness_mem hx htag.1)
  | R => exact Or.inr (entryWitness_mem hx htag.1)
  | S => exact Or.inr (entryWitness_mem hx htag.1)

theorem globalizeLocalWitness_surjOn (X : ℕ) :
    Set.SurjOn globalizeLocalWitness
      (localBranchWitnessesUpTo X : Set LocalBranchWitness)
      (obstructionWitnessesUpTo X : Set ObstructionWitness) := by
  intro w hw
  rcases w with ⟨x, p, a, c⟩
  have hobsMem := mem_obstructionWitnessesUpTo.mp hw
  have hobs : DropObstruction (n x) p a c ∨
      EntryObstruction (n x) p a c := by
    rcases hobsMem with hdrop | hentry
    · exact Or.inl (mem_dropWitnessesUpTo.mp hdrop).2
    · exact Or.inr (mem_entryWitnessesUpTo.mp hentry).2
  obtain ⟨L, htag⟩ := obstruction_has_branch hobs
  obtain ⟨d, hlocal, hc⟩ := taggedObstruction_has_local_exact htag
  have hx : x ∈ parameterRange X := by
    rcases hobsMem with hdrop | hentry
    · exact (mem_witnessBox.mp (mem_dropWitnessesUpTo.mp hdrop).1).1
    · exact (mem_witnessBox.mp (mem_entryWitnessesUpTo.mp hentry).1).1
  refine ⟨(L, (x, p, a, d)), localBranchWitness_mem hx hlocal, ?_⟩
  simp [globalizeLocalWitness, localWitnessParameter, localWitnessPrime,
    localWitnessExponent, localWitnessCofactor, localWitnessBranch, hc]

/-- The finite global obstruction count is bounded by the sum of the four
exact local branch-event counts. -/
theorem obstructionWitnesses_card_le_localBranchWitnesses_card (X : ℕ) :
    (obstructionWitnessesUpTo X).card ≤
      (localBranchWitnessesUpTo X).card :=
  Finset.card_le_card_of_surjOn globalizeLocalWitness
    (globalizeLocalWitness_surjOn X)

theorem bad_card_le_localBranchWitnesses_card (X : ℕ) :
    (badParametersUpTo X).card ≤ (localBranchWitnessesUpTo X).card :=
  (bad_card_le_obstructionWitnesses_card X).trans
    (obstructionWitnesses_card_le_localBranchWitnesses_card X)

/-! ## Exact four-range partition of the local branch ledger -/

noncomputable def localHigherPowerWitnessesUpTo (X : ℕ) : Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w => 2 ≤ localWitnessExponent w

noncomputable def localSmallPrimeWitnessesUpTo (X smallCut : ℕ) :
    Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w =>
    localWitnessExponent w = 1 ∧ localWitnessPrime w ≤ smallCut

noncomputable def localTransitionPrimeWitnessesUpTo (X smallCut topCut : ℕ) :
    Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w =>
    localWitnessExponent w = 1 ∧
      smallCut < localWitnessPrime w ∧ localWitnessPrime w ≤ topCut

noncomputable def localTopPrimeWitnessesUpTo (X topCut : ℕ) : Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w =>
    localWitnessExponent w = 1 ∧ topCut < localWitnessPrime w

theorem localWitness_exponent_pos
    {X : ℕ} {w : LocalBranchWitness}
    (hw : w ∈ localBranchWitnessesUpTo X) :
    0 < localWitnessExponent w := by
  exact (mem_localBranchWitnessesUpTo.mp hw).2.2.2.1.1

theorem localBranchWitnesses_fourRange (X smallCut topCut : ℕ) :
    localBranchWitnessesUpTo X =
      localHigherPowerWitnessesUpTo X ∪
        (localSmallPrimeWitnessesUpTo X smallCut ∪
          (localTransitionPrimeWitnessesUpTo X smallCut topCut ∪
            localTopPrimeWitnessesUpTo X topCut)) := by
  ext w
  simp only [localHigherPowerWitnessesUpTo, localSmallPrimeWitnessesUpTo,
    localTransitionPrimeWitnessesUpTo, localTopPrimeWitnessesUpTo,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hw
    have ha := localWitness_exponent_pos hw
    by_cases ha2 : 2 ≤ localWitnessExponent w
    · exact Or.inl ⟨hw, ha2⟩
    have ha1 : localWitnessExponent w = 1 := by omega
    by_cases hs : localWitnessPrime w ≤ smallCut
    · exact Or.inr (Or.inl ⟨hw, ha1, hs⟩)
    by_cases ht : localWitnessPrime w ≤ topCut
    · exact Or.inr (Or.inr (Or.inl
        ⟨hw, ha1, Nat.lt_of_not_ge hs, ht⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨hw, ha1, Nat.lt_of_not_ge ht⟩))
  · rintro (⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw

theorem localHigher_disjoint_rest (X smallCut topCut : ℕ) :
    Disjoint (localHigherPowerWitnessesUpTo X)
      (localSmallPrimeWitnessesUpTo X smallCut ∪
        (localTransitionPrimeWitnessesUpTo X smallCut topCut ∪
          localTopPrimeWitnessesUpTo X topCut)) := by
  rw [Finset.disjoint_left]
  intro w hh hr
  have ha2 := (Finset.mem_filter.mp hh).2
  rcases Finset.mem_union.mp hr with hs | hr
  · have ha1 := (Finset.mem_filter.mp hs).2.1
    omega
  rcases Finset.mem_union.mp hr with ht | hp
  · have ha1 := (Finset.mem_filter.mp ht).2.1
    omega
  · have ha1 := (Finset.mem_filter.mp hp).2.1
    omega

theorem localSmall_disjoint_rest
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    Disjoint (localSmallPrimeWitnessesUpTo X smallCut)
      (localTransitionPrimeWitnessesUpTo X smallCut topCut ∪
        localTopPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w hs hr
  have hpSmall := (Finset.mem_filter.mp hs).2.2
  rcases Finset.mem_union.mp hr with ht | hp
  · have hpLarge := (Finset.mem_filter.mp ht).2.2.1
    omega
  · have hpTop := (Finset.mem_filter.mp hp).2.2
    omega

theorem localTransition_disjoint_top (X smallCut topCut : ℕ) :
    Disjoint (localTransitionPrimeWitnessesUpTo X smallCut topCut)
      (localTopPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w ht hp
  have hle := (Finset.mem_filter.mp ht).2.2.2
  have hgt := (Finset.mem_filter.mp hp).2.2
  omega

theorem localBranchWitnesses_card_fourRange
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (localBranchWitnessesUpTo X).card =
      (localHigherPowerWitnessesUpTo X).card +
        ((localSmallPrimeWitnessesUpTo X smallCut).card +
          ((localTransitionPrimeWitnessesUpTo X smallCut topCut).card +
            (localTopPrimeWitnessesUpTo X topCut).card)) := by
  rw [localBranchWitnesses_fourRange X smallCut topCut,
    Finset.card_union_of_disjoint
      (localHigher_disjoint_rest X smallCut topCut),
    Finset.card_union_of_disjoint
      (localSmall_disjoint_rest X smallCut topCut hcuts),
    Finset.card_union_of_disjoint
      (localTransition_disjoint_top X smallCut topCut)]

/-! ## Uniqueness of the branch tag -/

theorem taggedObstruction_branch_unique
    {L K : Branch} {x p a c : ℕ}
    (hL : TaggedObstruction L x p a c)
    (hK : TaggedObstruction K x p a c) : L = K := by
  cases L <;> cases K
  · rfl
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← P_Q_coprime x]
    exact Nat.dvd_gcd hL.2 hK.2
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← (P_Q_coprime x).symm]
    exact Nat.dvd_gcd hL.2 hK.2
  · rfl
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · rfl
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← R_S_coprime x]
    exact Nat.dvd_gcd hL.2 hK.2
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← (R_S_coprime x).symm]
    exact Nat.dvd_gcd hL.2 hK.2
  · rfl


end BranchEvents
end Erdos730

end Campaign180File4

/- Source module: ErdosProblems.Erdos730.AnalyticInputs -/
section Campaign180File5
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: exact analytic dependency surface

The fixed-depth proof uses two standard analytic-number-theory inputs which
are not both theorems in the pinned Mathlib release: Mertens' reciprocal-prime
asymptotic and the prime number theorem in each fixed arithmetic progression.
This file defines their exact qualitative surfaces and declares no axiom.

The ordinary qualitative PNT in AP is enough for the divisor-switching step:
the modulus is fixed, so convergence is uniform over its finitely many reduced
residue classes, and the weighted main terms have total order `Z`.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.FullDensity

/-- Sum of reciprocal primes at most `N`. -/
noncomputable def reciprocalPrimeSum (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ)⁻¹

/-- The integer specialization of a reciprocal-prime Mertens bound.  The
coefficient is fixed and positive; its numerical value is immaterial to the
uniform depth-tail argument. -/
def MertensReciprocalPrimeInput : Prop :=
  ∃ M C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
      |reciprocalPrimeSum N - Real.log (Real.log N) - M| ≤
        C / Real.log N

/-- Number of primes at most `N` in the residue class `a mod A`. -/
def primeAPCount (A a N : ℕ) : ℕ :=
  ((range (N + 1)).filter fun p => p.Prime ∧ p % A = a % A).card

/-- Qualitative prime number theorem in the reduced residue classes of one
specified fixed modulus.  No zero-free-region error term is required by the
cleaned proof. -/
def PNTAPInputAtModulus (A : ℕ) : Prop :=
  0 < A ∧ ∀ a : ℕ, a < A → a.Coprime A →
    Tendsto
      (fun N : ℕ =>
        (primeAPCount A a N : ℝ) /
          ((N : ℝ) / Real.log N))
      atTop (𝓝 ((Nat.totient A : ℝ)⁻¹))

/-- Exactly the three fixed moduli occurring in the proof: ordinary prime
counting and the two divisor-switching moduli.  This deliberately does not
assume PNT-AP uniformly over arbitrary moduli. -/
def RequiredFixedModulusPNTAPInput : Prop :=
  PNTAPInputAtModulus 1 ∧
    PNTAPInputAtModulus 222138 ∧
      PNTAPInputAtModulus 148092

/-- The single explicit external analytic closure required by the candidate
proof.  This is a conjunction of two independently classical theorems, not an
assumption of strength equivalent to Erdős #730. -/
def RequiredAnalyticInputs : Prop :=
  MertensReciprocalPrimeInput ∧ RequiredFixedModulusPNTAPInput

theorem requiredAnalyticInputs_iff :
    RequiredAnalyticInputs ↔
      MertensReciprocalPrimeInput ∧
        PNTAPInputAtModulus 1 ∧
          PNTAPInputAtModulus 222138 ∧
            PNTAPInputAtModulus 148092 := by
  rfl


end Erdos730.FullDensity

end Campaign180File5

/- Source module: PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic -/
section Campaign180File6

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end Campaign180File6

/- Source module: PrimeNumberTheoremAnd.Sobolev -/
section Campaign180File7

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  ext v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end Campaign180File7

/- Source module: PrimeNumberTheoremAnd.Fourier -/
section Campaign180File8

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp)

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

set_option backward.isDefEq.respectTransparency.types false in
noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _ -- `scomp` introduces ℝ-smul on ℂ, which we undo
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

/-- If, eventually in `T`, the integrand `f T` is bounded on `uIoc lo hi` by `B T`
and `B T * |hi - lo| → 0`, then the interval integral `∫ x in lo..hi, f T x → 0`. -/
lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)

/-- The decay `K * (log (T + 2) / (T + 2)) → 0` as `T → ∞`, for any constant `K`. -/
lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K

/-- Fourier-transform decay from an integrable derivative: for integrable,
differentiable `g` with integrable derivative, `‖𝓕 g w‖ ≤ (∫ ‖deriv g x‖) / (2π·|w|)`. -/
lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)

/-- The oscillatory-integral form of the decay bound: for `0 < T`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / T`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]

/-- The `|T|` variant of the oscillatory-integral decay bound: for `T ≠ 0`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / |T|`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]

end Campaign180File8

/- Source module: PrimeNumberTheoremAnd.Defs -/
section Campaign180File9

open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

noncomputable abbrev nth_prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

noncomputable abbrev nth_prime' (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x

noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

noncomputable abbrev nth_prime_gap (n : ℕ) : ℕ :=
  nth_prime (n + 1) - nth_prime n

def prime_gap_record (p g : ℕ) : Prop :=
  ∃ n, nth_prime n = p ∧ nth_prime_gap n = g ∧
    ∀ k, nth_prime k < p → nth_prime_gap k < g

open Classical in

noncomputable def first_gap (g : ℕ) : ℕ :=
  if h : ∃ n, nth_prime_gap n = g then
    nth_prime (Nat.find h)
  else 0

def first_gap_record (g P : ℕ) : Prop :=
  first_gap g = P ∧
    ∀ g' ∈ Finset.Ico 1 g,
      Even g' ∨ g' = 1 → first_gap g' ∈ Set.Ico 1 P

def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x) ^ k)


noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊


noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k + 1 : ℝ))) / (k + 1 : ℝ)


noncomputable def li (x : ℝ) : ℝ :=
  lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦
    ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)),
      1 / log t))


noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t


noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))


def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x

def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε

def Eψ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eψ.bound (ε x₀) x₀


noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)

noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)


noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x


def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x

def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ ε x₀


def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ.bound (ε x₀) x₀

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))

def Eπ_star.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ admissible_bound A B C R x

def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε

def Eπ_star.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ_star.bound (ε x₀) x₀

def Eπ_star.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))


lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]


lemma Eψ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEψ : Eψ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eψ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEψ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)


lemma Eθ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEθ : Eθ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eθ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEθ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)


lemma Eπ.classicalBound.to_numericalBound
    (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R)
    (hEπ : Eπ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eπ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦
    le_trans (hEπ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
      (admissible_bound.mono A B C R hA hB hC hR
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

end Campaign180File9

/- Source module: PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics -/
section Campaign180File10

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics

end Campaign180File10

/- Source module: PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.Support -/
section Campaign180File11

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

end Campaign180File11

/- Source module: PrimeNumberTheoremAnd.SmoothExistence -/
section Campaign180File12


open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]




lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end Campaign180File12

/- Source module: PrimeNumberTheoremAnd.Wiener -/
section Campaign180File13

set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]



noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

set_option backward.isDefEq.respectTransparency false in

lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp



@[continuity]
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

set_option backward.isDefEq.respectTransparency.types false in
lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- TODO: find out why fun_prop does not play well with Multiplicative.ofAdd
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      Multiplicative.ofAdd, Equiv.coe_fn_mk, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

set_option backward.isDefEq.respectTransparency false in

lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  dsimp [Real.fourierChar, Circle.exp]

  simp_rw [mul_smul_comm, ← smul_mul_assoc, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  conv =>
    lhs
    enter [2]
    ext a
    rw [AddChar.coe_mk, Submonoid.mk_smul, smul_eq_mul]
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I + -↑u * (↑σ' - 1) = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx



lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)


theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..




noncomputable def AbsolutelyContinuous (f : ℝ → ℂ) : Prop := (∀ᵐ x, DifferentiableAt ℝ f x) ∧
  ∀ a b : ℝ, f b - f a = ∫ t in a..b, deriv f t





lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

theorem decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0] ; gcongr


lemma decay_bounds (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_bounds_W21 ψ hA hA' u

lemma decay_bounds_cor_aux (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg (one_add_sq_pos u).le] at hC
  rwa [le_div_iff₀' (one_add_sq_pos _)]

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

set_option backward.isDefEq.respectTransparency false in
@[continuity, fun_prop] lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

lemma nnabla_cast (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  ext n ; simp [nnabla]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right₀ l1 h

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
@[local gcongr]
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    gcongr

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])


lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext ; congr ; ext
    simp only [← ofReal_mul, mul_comm (f _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg,
      neg_mul]
    congr
    rw [← neg_mul] ; congr ; norm_cast ; field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)


lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm






lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  convert! cancel_aux' hf hg hf' hg' n using 1
  match n with
  | n + 2 => simp only [cumsum_succ] ; push_cast ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    simp [-ae_restrict_eq, mem_ae_iff, this]
  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring


set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)


lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead


lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

set_option backward.isDefEq.respectTransparency false in
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]




lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4



lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this




lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith



lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1


theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith



-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)


theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_ofPred_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

-- #print axioms WeakPNT

section auto_cheby

variable {f : ℕ → ℝ}

lemma norm_x_cpow_it (x t : ℝ) (hx : 0 < x) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
  rw [cpow_def_of_ne_zero <| ofReal_ne_zero.mpr hx.ne', ← ofReal_log hx.le]
  convert norm_exp_ofReal_mul_I (t * x.log) using 2
  push_cast; ring_nf

set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux_gt_zero (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 0 < x) (σ' : ℝ) (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) :=
    (((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8).integrable_of_hasCompactSupport
      ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re (sub_eq_zero.mp h); simp at this; linarith
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) *
      (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    have : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) *
        (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
      simp only [one_div, ← mul_assoc]
      exact ((continuous_const.mul (Continuous.inv₀ (by fun_prop) e2)).mul ψ.h1.continuous).mul l8
    exact this.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right.mul_left.mul_left
  simp_rw [first_fourier hf hint hx hσ', second_fourier ψ.h1.continuous.measurable hint hx hσ',
    ← integral_const_mul, ← integral_sub l4 l5]
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  field_simp [e2]; norm_cast; simp [mul_assoc, ← rpow_add hx]

theorem limiting_fourier_lim2_gt_zero (A : ℝ) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
      ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
        (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  refine Tendsto.mul ?_ (tendsto_integral_filter_of_dominated_convergence _
    (.of_forall fun _ ↦ (by continuity : Continuous _).aestronglyMeasurable) ?_
    (limiting_fourier_lim2_aux x C) (.of_forall fun u ↦ ?_))
  · suffices Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) by
      simpa using ((continuous_ofReal.tendsto 1).comp this).const_mul ↑A
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_id.tendsto (1 : ℝ)).const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl hx.ne')
  · refine eventually_of_mem (Ioo_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun σ' hσ' ↦ ?_
    obtain ⟨h1, h2⟩ := hσ'
    rw [ae_restrict_iff' measurableSet_Ici]
    refine .of_forall fun t ht ↦ ?_
    simp only [norm_mul, neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      norm_exp, neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im,
      sub_self, mul_zero, sub_zero]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) ((abs_nonneg x).trans (le_max_left _ _))
    have hα0 : 0 ≤ σ' - 1 := by linarith
    have hα1 : σ' - 1 ≤ 1 := by linarith
    have hmul1 : (-x.log) * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht hα0
    calc Real.exp (-(t * (σ' - 1)))
        ≤ Real.exp (x.log * (σ' - 1)) := Real.exp_monotone (by linarith)
      _ ≤ max |x| 1 := by
          by_cases hx1 : 1 ≤ x
          · calc _ ≤ Real.exp x.log :=
                Real.exp_monotone (mul_le_of_le_one_right (Real.log_nonneg hx1) hα1)
              _ = |x| := by rw [Real.exp_log hx, abs_of_pos hx]
              _ ≤ _ := le_max_left _ _
          · calc _ ≤ 1 := (Real.exp_monotone (mul_nonpos_of_nonpos_of_nonneg
                  ((Real.log_neg_iff hx).2 (by linarith)).le hα0)).trans_eq Real.exp_zero
              _ ≤ _ := le_max_right _ _
  · suffices Tendsto (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by simpa using this.mul_const _
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have : Continuous (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) := by continuity
    simpa using this.tendsto 1

theorem limiting_fourier_lim3_gt_zero
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by
  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh
  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_Icc.reProdIm (isClosed_tsupport ψ), (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded⟩
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩ (hG.mono l2).norm
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun a ↦ ‖G z‖ * ‖ψ a‖)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      ((hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous).mul
        (by simpa using Continuous.const_cpow (by fun_prop) (Or.inl hxC)) |>.aestronglyMeasurable)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      .of_forall fun v ↦ ?_)
    ((continuous_const.mul ψ.h1.continuous.norm).integrable_of_hasCompactSupport ψ.h2.norm.mul_left)
    (.of_forall fun t ↦ ?_)
  · by_cases h : v ∈ tsupport ψ
    · simp_rw [norm_mul, norm_x_cpow_it x v hx, mul_one]
      exact mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hmax _ (by simp [S, mem_reProdIm, hu.1, hu.2, h])) (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp [Function.notMem_support.mp this]
  · exact ((hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr
      ⟨((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds,
       eventually_nhdsWithin_of_forall fun _ hx' ↦ by simp [(Set.mem_Ioi.mp hx').le]⟩).mul_const _ |>.mul_const _

lemma tendsto_tsum_of_monotone_convergence
    {β : Type*} {f : ℕ → β → ENNReal} {g : β → ENNReal}
    (hmono : ∀ k, Monotone (fun n => f n k))
    (hlim : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) := by
  let : MeasurableSpace β := ⊤
  let μ : Measure β := Measure.count
  have hg_iSup (k : β) : (⨆ n : ℕ, f n k) = g k := iSup_eq_of_tendsto (hmono k) (hlim k)
  have h_tend_lint : Tendsto (fun n => ∫⁻ k, f n k ∂μ) atTop (𝓝 (∫⁻ k, (⨆ n, f n k) ∂μ)) := by
    have hmeas : ∀ n, Measurable fun k : β => f n k := fun _ _ _ ↦ trivial
    have hmono_fn : Monotone (fun n => fun k : β => f n k) := fun _ _ hnm k ↦ hmono k hnm
    simpa [lintegral_iSup hmeas hmono_fn] using
      tendsto_atTop_iSup fun _ _ hmn ↦ lintegral_mono fun k ↦ hmono k hmn
  simpa [μ, lintegral_count, hg_iSup] using h_tend_lint

lemma tendsto_tsum_of_monotone_convergence_nhdsGT_one
    {F : ℝ → ℕ → ℝ}
    (hF_nonneg : ∀ σ n, 0 ≤ F σ n)
    (hF_antitone : ∀ n, AntitoneOn (fun σ : ℝ => F σ n) (Set.Ioi (1 : ℝ)))
    (hF_tend : ∀ n, Tendsto (fun σ : ℝ => F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (F 1 n)))
    (hSumm : ∀ σ, 1 < σ → Summable (fun n : ℕ => F σ n))
    (hbounded :
      BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => (∑' n : ℕ, F σ n))) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (∑' n : ℕ, F 1 n)) := by
  let T : ℝ → ℝ := fun σ => ∑' n : ℕ, F σ n
  have hT_antitone : AntitoneOn T (Set.Ioi (1 : ℝ)) := fun a ha b hb hab ↦
    (hSumm b hb).tsum_le_tsum_of_inj (fun n ↦ n) (fun _ _ h ↦ h) (fun c hc ↦ (hc ⟨c, rfl⟩).elim)
      (fun n ↦ hF_antitone n ha hb hab) (hSumm a ha)
  have hT_bdd : BddAbove (T '' Set.Ioi (1 : ℝ)) := by
    obtain ⟨C, hC⟩ := isBigO_iff.1 hbounded
    have hC' : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), T σ ≤ C := by
      filter_upwards [hC] with σ hσ
      calc T σ ≤ |T σ| := le_abs_self _
        _ = ‖T σ‖ := (Real.norm_eq_abs _).symm
        _ ≤ C * ‖(1 : ℝ → ℝ) σ‖ := hσ
        _ = C := by simp
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_inf_iff_superset.1 hC'
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    have hIoi_sub : Set.Ioi (1 : ℝ) ⊆ V := Filter.mem_principal.mp hV
    have hUsub : U ∩ Set.Ioi (1 : ℝ) ⊆ {σ : ℝ | T σ ≤ C} := fun σ hσ ↦ hUV ⟨hσ.1, hIoi_sub hσ.2⟩
    have hσ0_Ioi : 1 + ε / 2 ∈ Set.Ioi (1 : ℝ) := by simp [half_pos hε]
    have hσ0_leC : T (1 + ε / 2) ≤ C :=
      hUsub ⟨hball (by simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos (half_pos hε)]; exact half_lt_self hε), hσ0_Ioi⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨σ, hσIoi, rfl⟩
    by_cases hσlt : σ < 1 + ε / 2
    · exact hUsub ⟨hball (by
        simp only [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_pos (sub_pos.2 (Set.mem_Ioi.mp hσIoi))]
        linarith [half_lt_self hε]), hσIoi⟩
    · exact (hT_antitone hσ0_Ioi hσIoi (le_of_not_gt hσlt)).trans hσ0_leC
  have hT_tend_sup : Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (sSup (T '' Set.Ioi (1 : ℝ)))) :=
    hT_antitone.tendsto_nhdsGT hT_bdd
  let σseq : ℕ → ℝ := fun k => 1 + 1 / (k + 1 : ℝ)
  have hσseq_mem (k) : σseq k ∈ Set.Ioi (1 : ℝ) := by
    simp only [σseq, Set.mem_Ioi, lt_add_iff_pos_right]
    positivity
  have hσseq_tend_nhds : Tendsto σseq atTop (𝓝 (1 : ℝ)) := by
    have : Tendsto (fun k : ℕ => (1 : ℝ) + ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
    simp only [add_zero] at this
    convert this using 1; ext k; simp [σseq, one_div]
  have hσseq_tend_nhdsWithin : Tendsto σseq atTop (𝓝[>] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσseq_tend_nhds
      (.of_forall hσseq_mem)
  have hσseq_antitone : Antitone σseq := fun k₁ k₂ hk ↦ by simp only [σseq]; gcongr
  have hmono_seq (n) : Monotone (fun k => F (σseq k) n) := fun k₁ k₂ hk ↦
    hF_antitone n (hσseq_mem k₂) (hσseq_mem k₁) (hσseq_antitone hk)
  have htend_seq (n) : Tendsto (fun k => F (σseq k) n) atTop (𝓝 (F 1 n)) :=
    (hF_tend n).comp hσseq_tend_nhdsWithin
  have hTseq : Tendsto (fun k : ℕ => T (σseq k)) atTop (𝓝 (T 1)) := by
    have hsum1 : Summable (fun n : ℕ => F (1 : ℝ) n) := by
      obtain ⟨C, hC⟩ := hT_bdd
      refine summable_of_sum_range_le (hF_nonneg 1) fun m ↦ le_of_tendsto
        (tendsto_finsetSum _ fun i _ ↦ hF_tend i)
        (eventually_of_mem self_mem_nhdsWithin fun σ hσ ↦
          ((hSumm σ hσ).sum_le_tsum _ (fun n _ ↦ hF_nonneg σ n)).trans (hC ⟨σ, hσ, rfl⟩))
    have hg_ne_top : (∑' n : ℕ, ENNReal.ofReal (F 1 n)) ≠ ⊤ := hsum1.tsum_ofReal_ne_top
    have hENN : Tendsto (fun k => ∑' n, ENNReal.ofReal (F (σseq k) n)) atTop
        (𝓝 (∑' n, ENNReal.ofReal (F 1 n))) :=
      tendsto_tsum_of_monotone_convergence (fun n _ _ hk ↦ ENNReal.ofReal_le_ofReal (hmono_seq n hk))
        (fun n ↦ ENNReal.tendsto_ofReal (htend_seq n))
    have hrew (σ) : (∑' n, ENNReal.ofReal (F σ n)).toReal = ∑' n, F σ n := by
      rw [ENNReal.tsum_toReal_eq (fun n ↦ by simp)]
      exact tsum_congr fun n ↦ by simp [hF_nonneg σ n]
    simp only [T, ← hrew]; exact (ENNReal.tendsto_toReal hg_ne_top).comp hENN
  have hsSup_eq : sSup (T '' Set.Ioi (1 : ℝ)) = T 1 :=
    tendsto_nhds_unique (hT_tend_sup.comp hσseq_tend_nhdsWithin) hTseq
  simpa [T, hsSup_eq] using hT_tend_sup

lemma limiting_fourier_variant_lim1_aux
    {f : ℕ → ℝ} {x : ℝ} (ψ : CS 2 ℂ)
    (hpos : 0 ≤ f)
    (hf : ∀ (σ : ℝ), 1 < σ → Summable (nterm f σ))
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∀ (σ : ℝ), 1 < σ →
      Summable (fun n : ℕ =>
        (if n = 0 then 0 else f n / ((n : ℝ) ^ σ)) *
          (𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))).re) := by
  intro σ hσ
  let y : ℕ → ℝ := fun n => (1 / (2 * π)) * Real.log ((n : ℝ) / x)
  let W : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re
  let base : ℕ → ℝ := fun n => if n = 0 then 0 else f n / ((n : ℝ) ^ σ)
  obtain ⟨C, hC⟩ := decay_bounds_cor (W21.ofCS2 ψ)
  have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans (by simp))
  have hW_nonneg (n : ℕ) : 0 ≤ W n := (hψpos (y n)).1
  have hnorm_four (n : ℕ) : ‖𝓕 ψ.toFun (y n)‖ = W n := by
    have him0 : (𝓕 ψ.toFun (y n)).im = 0 := (hψpos (y n)).2
    rw [show 𝓕 ψ.toFun (y n) = W n by exact Complex.ext rfl him0]
    simp [abs_of_nonneg (hW_nonneg n)]
  have hW_le_C (n : ℕ) : W n ≤ C := by
    rw [← hnorm_four]; exact (hC (y n)).trans (div_le_self hC_nonneg (by nlinarith [sq_nonneg (y n)]))
  have hbase_summ : Summable base := by
    convert hf σ hσ using 1; ext n
    by_cases hn : n = 0 <;> simp [nterm, base, hn, Real.norm_eq_abs, abs_of_nonneg (hpos n)]
  refine (hbase_summ.mul_left C).of_norm_bounded fun n ↦ ?_
  by_cases hn : n = 0
  · simp [base, hn]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hbase_nonneg : 0 ≤ base n := by
      simp only [base, hn, if_false]
      exact div_nonneg (hpos n) (Real.rpow_pos_of_pos hnpos σ).le
    calc |base n * W n| = base n * W n := abs_of_nonneg (mul_nonneg hbase_nonneg (hW_nonneg n))
      _ ≤ base n * C := mul_le_mul_of_nonneg_left (hW_le_C n) hbase_nonneg
      _ = C * base n := mul_comm _ _


theorem limiting_fourier_variant_lim1
    {f : ℕ → ℝ} {x : ℝ} {ψ : CS 2 ℂ}
    (hpos : 0 ≤ f)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (S : ℝ → ℂ)
    (hSdef :
      ∀ σ' : ℝ,
        S σ' =
          ∑' n : ℕ,
            term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
              𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
    (hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖))
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) :
    Tendsto
      (fun σ' : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
      (𝓝[>] (1 : ℝ))
      (𝓝
        (∑' n : ℕ,
          (f n : ℂ) / (n : ℂ) *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))) := by

  let y : ℕ → ℝ := fun n => (π⁻¹ * 2⁻¹) * Real.log ((n : ℝ) / x)
  let w : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re

  have hw_nonneg : ∀ n, 0 ≤ w n := by
    intro n
    exact (hψpos (y n)).1

  have hFour_eq_ofReal : ∀ n, 𝓕 ψ.toFun (y n) = Complex.ofReal (w n) := by
    intro n
    have h := hψpos (y n)
    refine Complex.ext ?_ ?_
    · simp [w]
    · simp [w, h.2]

  let rterm : ℝ → ℕ → ℝ :=
    fun σ n =>
      if h0 : n = 0 then 0 else (f n) / ((n : ℝ) ^ σ) * (w n)

  have summand_eq_ofReal :
      ∀ (σ : ℝ) (n : ℕ),
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
          = Complex.ofReal (rterm σ n) := by
    intro σ n
    by_cases hn : n = 0
    · subst hn
      simp [rterm, y]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn0 : 0 ≤ (n : ℝ) := le_of_lt hnpos
      have hcpow :
          ( (n : ℂ) ^ ((σ : ℝ) : ℂ) ) = ( ( (n : ℝ) ^ σ : ℝ) : ℂ ) := by
        simpa using (Complex.ofReal_cpow hn0 σ).symm
      have hpow_ne : ((n : ℝ) ^ σ) ≠ 0 := by
        exact (ne_of_gt (Real.rpow_pos_of_pos hnpos σ))
      calc
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
            =
          ((f n : ℂ) / ((n : ℂ) ^ ((σ : ℝ) : ℂ))) * ( (w n : ℝ) : ℂ ) := by
            simp [term, LSeries.term, hn, hFour_eq_ofReal]
        _ =
          ((f n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp [hcpow]
        _ =
          (( (f n : ℝ) : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) : ℝ) : ℂ ) * ((w n : ℝ) : ℂ) := by
            simp [Complex.ofReal_div]
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) * (w n) : ℝ ) : ℂ ) := by
            simp [Complex.ofReal_mul]
        _ =
          Complex.ofReal (rterm σ n) := by
            simp [rterm, hn]

  let T : ℝ → ℝ := fun σ => ∑' n, rterm σ n

  have tsum_eq_ofReal_T : ∀ σ : ℝ,
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = Complex.ofReal (T σ) := by
    intro σ
    have hcongr :
        (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := by
      refine tsum_congr ?_
      intro n
      simpa using (summand_eq_ofReal σ n)

    calc
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := hcongr
      _ = Complex.ofReal (∑' n : ℕ, rterm σ n) := by
            simpa using (Complex.ofReal_tsum (fun n : ℕ => rterm σ n)).symm
      _ = Complex.ofReal (T σ) := by rfl

  have hS_ofReal_T : ∀ σ : ℝ, S σ = Complex.ofReal (T σ) := by
    intro σ
    simpa [hSdef σ, y] using (tsum_eq_ofReal_T σ)

  have rterm_nonneg : ∀ σ n, 0 ≤ rterm σ n := by
    intro σ n
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hden : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
      have : 0 ≤ (f n) / ((n : ℝ) ^ σ) := div_nonneg hf (le_of_lt hden)
      simp [rterm, hn, mul_nonneg this hw]

  have T_nonneg : ∀ σ, 0 ≤ T σ := by
    intro σ
    exact tsum_nonneg (fun n => rterm_nonneg σ n)

  have hT_eq_normS : ∀ σ, T σ = ‖S σ‖ := by
    intro σ
    have := hS_ofReal_T σ
    calc
      T σ = ‖Complex.ofReal (T σ)‖ := by simp [abs_of_nonneg (T_nonneg σ)]
      _ = ‖S σ‖ := by simp [this]

  have hboundedT : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => T σ) := by
    have : (fun σ : ℝ => T σ) = (fun σ : ℝ => ‖S σ‖) := by
      funext σ; exact hT_eq_normS σ
    simpa [this] using hbounded

  have rterm_antitone : ∀ n, AntitoneOn (fun σ => rterm σ n) (Set.Ioi 1) := by
    intro n σ₁ hσ₁ σ₂ hσ₂ hσ₁₂
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hpow : (n : ℝ) ^ σ₁ ≤ (n : ℝ) ^ σ₂ :=
        Real.rpow_le_rpow_of_exponent_le hn1 hσ₁₂
      have hinv :
      (1 / ((n : ℝ) ^ σ₂)) ≤ (1 / ((n : ℝ) ^ σ₁)) := by
        have hpos1 : 0 < (n : ℝ) ^ σ₁ := Real.rpow_pos_of_pos hnpos σ₁
        exact one_div_le_one_div_of_le hpos1 hpow
      have hinv_inv : ((n : ℝ) ^ σ₂)⁻¹ ≤ ((n : ℝ) ^ σ₁)⁻¹ := by
        simpa [one_div] using hinv
      have hmul1 :
          (f n) * (((n : ℝ) ^ σ₂)⁻¹) ≤ (f n) * (((n : ℝ) ^ σ₁)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv_inv hf
      have hmul2 :
          ((f n) * (((n : ℝ) ^ σ₂)⁻¹)) * (w n)
            ≤ ((f n) * (((n : ℝ) ^ σ₁)⁻¹)) * (w n) :=
        mul_le_mul_of_nonneg_right hmul1 hw
      simpa [rterm, hn, div_eq_mul_inv, mul_assoc] using hmul2

  have rterm_tend : ∀ n, Tendsto (fun σ : ℝ => rterm σ n) (𝓝[>] (1 : ℝ)) (𝓝 (rterm 1 n)) := by
    intro n
    have hterm :
        Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
          (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
      by_cases hn : n = 0
      · subst hn
        simp [term, LSeries.term]
      · have hden :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 ((n : ℂ) ^ (1 : ℂ))) := by
          simpa using ((continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).const_cpow

        have hden' :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 (n : ℂ)) := by
          simpa using hden

        have hnC : (n : ℂ) ≠ 0 := by
          exact_mod_cast hn

        have hterm :
            Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
              (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
          have hnC : (n : ℂ) ≠ 0 := by
            exact_mod_cast hn
          simpa [term, LSeries.term, hn] using!
            (tendsto_const_nhds.div hden' hnC)
        exact hterm

    have hsummand :
        Tendsto
          (fun σ : ℝ =>
            term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          (𝓝[>] (1 : ℝ))
          (𝓝 (((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n))) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hterm.mul_const (𝓕 ψ.toFun (y n)))

    have hre : ∀ σ, rterm σ n =
        (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re := by
      intro σ
      have := congrArg Complex.re (summand_eq_ofReal σ n)
      simpa [Complex.ofReal_re] using this.symm

    have hRe : Tendsto
        (fun σ : ℝ =>
          (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re)
        (𝓝[>] (1 : ℝ))
        (𝓝 ((((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n)).re)) :=
      (continuous_re.tendsto _).comp hsummand

    have hlimit_re :
      (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re = rterm 1 n := by
      have h0 :
          (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re = rterm 1 n := by
        have := congrArg Complex.re (summand_eq_ofReal (σ := (1 : ℝ)) n)
        simpa [Complex.ofReal_re] using this

      by_cases hn : n = 0
      · subst hn
        simp [rterm, y]
      · have h1 :
            (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re
              = (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re := by
          simp [Complex.mul_re, term, LSeries.term, hn, y,
                (hψpos (y n)).2]

        exact (h1.symm.trans h0)

    simpa [hre, hlimit_re] using hRe

  have hSumm_rterm : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => rterm σ n) := by
    simpa [rterm] using limiting_fourier_variant_lim1_aux (ψ := ψ)
      (f := f) (x := x) hpos hf hψpos

  have hT_tend :
      Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (T 1)) := by
    have :
        Tendsto (fun σ : ℝ => ∑' n : ℕ, rterm σ n)
          (𝓝[>] (1 : ℝ))
          (𝓝 (∑' n : ℕ, rterm (1 : ℝ) n)) := by
      refine tendsto_tsum_of_monotone_convergence_nhdsGT_one
        (F := rterm)
        (hF_nonneg := rterm_nonneg)
        (hF_antitone := rterm_antitone)
        (hF_tend := rterm_tend)
        (hSumm := hSumm_rterm)
        (hbounded := hboundedT)

    simpa [T] using this

  have hToReal :
      Tendsto (fun σ => Complex.ofReal (T σ)) (𝓝[>] (1 : ℝ)) (𝓝 (Complex.ofReal (T 1))) :=
    (continuous_ofReal.tendsto _).comp hT_tend

  have hsource :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = fun σ : ℝ => Complex.ofReal (T σ) := by
    funext σ
    exact (tsum_eq_ofReal_T σ)

  have hσ1 :
    (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (↑(1:ℝ)) n * 𝓕 ψ.toFun (y n))
      = (↑(T 1) : ℂ) :=
    by simpa using (tsum_eq_ofReal_T (σ := (1:ℝ)))
  have hterm1 :
      ∀ n : ℕ, term (fun n ↦ (f n : ℂ)) (1 : ℂ) n = (f n : ℂ) / (n : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [term, LSeries.term]
    · simp [term, LSeries.term, hn]

  have hrewrite :
      (∑' n : ℕ,
        term (fun n ↦ (f n : ℂ)) (1 : ℂ) n * 𝓕 ψ.toFun (y n))
        =
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n)) := by
    refine tsum_congr ?_
    intro n
    simp [hterm1 n]

  have htarget :
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n))
        = (↑(T 1) : ℂ) := by
    exact (hrewrite.symm.trans hσ1)

  simpa [hsource, htarget, y] using hToReal







lemma limiting_fourier_variant
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (hx : 0 < x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l2 := limiting_fourier_lim2_gt_zero (A := A) (x := x) ψ hx
  have l3 := limiting_fourier_lim3_gt_zero (G := G) (x := x) hG ψ hx

  let S : ℝ → ℂ := fun σ' =>
    ∑' n : ℕ,
      term (fun n ↦ (f n : ℂ)) σ' n *
        𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))
  let Pole : ℝ → ℂ := fun σ' =>
    (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
      ∫ u in Set.Ici (-Real.log x),
        (rexp (-u * (σ' - 1)) : ℂ) *
          𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' =>
    ∫ t : ℝ, G (σ' + t * I) * ψ.toFun t * (x : ℂ) ^ (t * I)


  have haux :
    (fun σ' ↦
        ∑' (n : ℕ),
          term (fun n ↦ (f n : ℂ)) (σ' : ℂ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x))
        - (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
          ∫ (u : ℝ) in Ici (-Real.log x),
            cexp (-( (u : ℂ) * ((σ' : ℂ) - 1))) *
              𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π)))
      =ᶠ[𝓝[>] (1 : ℝ)]
    (fun σ' ↦
      ∫ (t : ℝ), G ((σ' : ℂ) + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)) := by
    rw [Filter.EventuallyEq]

    refine eventually_nhdsWithin_of_forall ?_
    intro σ' hσ'
    have hσ' : (1 : ℝ) < σ' := by
      simpa [Set.mem_Ioi] using hσ'
    simpa using! (limiting_fourier_aux_gt_zero (G := G) (f := f) (A := A) hG' hf ψ hx σ' hσ')

  have haux' :
    (fun σ' : ℝ => S σ') =ᶠ[𝓝[>] (1 : ℝ)] (fun σ' : ℝ => RHS σ' + Pole σ') := by
    rw [Filter.EventuallyEq] at haux ⊢
    filter_upwards [haux] with σ' hσ'
    have hσ'' : S σ' - Pole σ' = RHS σ' := by
      simpa [S, Pole, RHS] using hσ'
    have hadd : (S σ' - Pole σ') + Pole σ' = RHS σ' + Pole σ' :=
      congrArg (fun z : ℂ => z + Pole σ') hσ''
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

  let Pole₁ : ℂ := (A : ℂ) * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS₁ : ℂ := ∫ t : ℝ, G (1 + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)

  have hRHS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖RHS σ'‖ ≤ ‖RHS₁‖ + 1 := by
    have hball : Metric.ball RHS₁ (1 : ℝ) ∈ 𝓝 RHS₁ := by
      simpa using (Metric.ball_mem_nhds (x := RHS₁) (ε := (1 : ℝ)) (by norm_num))
    have hpre : {σ' : ℝ | RHS σ' ∈ Metric.ball RHS₁ (1 : ℝ)} ∈ (𝓝[>] (1 : ℝ)) :=
      l3 hball
    filter_upwards [hpre] with σ' hmem
    have hdist' : dist (RHS σ') RHS₁ < (1 : ℝ) := by
      simpa [Metric.mem_ball] using hmem
    have hdist : ‖RHS σ' - RHS₁‖ < (1 : ℝ) := by
      simpa [dist_eq_norm] using hdist'
    have htri : ‖RHS σ'‖ ≤ ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ := by
      have h := norm_add_le (RHS σ' - RHS₁) RHS₁
      simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using h
    have hle : ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ ≤ ‖RHS₁‖ + (1 : ℝ) := by
      exact add_le_add_right (le_of_lt hdist) ‖RHS₁‖
    exact htri.trans hle

  have hPole_le :
    ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖Pole σ'‖ ≤ ‖Pole₁‖ + 1 := by
    have hball : Metric.ball Pole₁ 1 ∈ 𝓝 Pole₁ := by
      simpa using (Metric.ball_mem_nhds Pole₁ (by norm_num : (0 : ℝ) < 1))
    have hpre : {σ' : ℝ | Pole σ' ∈ Metric.ball Pole₁ 1} ∈ (𝓝[>] (1 : ℝ)) := l2 hball
    filter_upwards [hpre] with σ' hmem
    have hdist : ‖Pole σ' - Pole₁‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hmem
    have htri : ‖Pole σ'‖ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := by
      have hdecomp : Pole σ' = Pole₁ + (Pole σ' - Pole₁) := by abel
      have hnorm_eq : ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := by
        simp [congrArg (fun z : ℂ => ‖z‖) hdecomp]
      calc
        ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := hnorm_eq
        _ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := norm_add_le _ _
    have hdist_le : ‖Pole σ' - Pole₁‖ ≤ 1 := le_of_lt hdist
    have hsum : ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ ≤ ‖Pole₁‖ + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hdist_le ‖Pole₁‖)
    exact htri.trans hsum

  have hS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ),
        ‖S σ'‖ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
    rw [Filter.EventuallyEq] at haux'
    filter_upwards [haux', hRHS_le, hPole_le] with σ' hEq hR hP
    calc
      ‖S σ'‖ = ‖RHS σ' + Pole σ'‖ := by simp [hEq]
      _ ≤ ‖RHS σ'‖ + ‖Pole σ'‖ := norm_add_le _ _
      _ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
        exact add_le_add hR hP

  have hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖) := by
    let C : ℝ := ‖RHS₁‖ + 1 + (‖Pole₁‖ + 1)
    simp only [BoundedAtFilter, Asymptotics.IsBigO, Asymptotics.IsBigOWith]
    refine ⟨C, ?_⟩
    filter_upwards [hS_le] with σ' hσ'
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (S σ'))] using hσ'

  have hcoef : (1 / (2 * π) : ℝ) = (π⁻¹ * 2⁻¹ : ℝ) := by field_simp [pi_ne_zero]

  have l1 :=
    limiting_fourier_variant_lim1
      (f := f) (x := x) (ψ := ψ)
      hpos hψpos
      (S := S)
      (hSdef := by
        intro σ
        simp [S, hcoef] )
      hbounded
      hf
  have l1S :
    Tendsto S (𝓝[>] (1 : ℝ))
      (𝓝 (∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x)))) := by
    simpa [S, hcoef] using l1

  have l12 : Tendsto (fun σ' : ℝ => S σ' - Pole σ') (𝓝[>] (1 : ℝ))
    (𝓝 ((∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x))) - Pole₁)) :=
  l1S.sub l2

  have hPole : (Pole : ℝ → ℂ) =ᶠ[𝓝[>] (1 : ℝ)] Pole := by simp
  have haux_sub :
    (fun σ' : ℝ => S σ' - Pole σ') =ᶠ[𝓝[>] (1 : ℝ)] RHS := by
    filter_upwards [haux'] with σ' hσ'
    calc
      S σ' - Pole σ'
          = (RHS σ' + Pole σ') - Pole σ' := by simp [hσ']
      _   = RHS σ' := by simp
  have hlim :=
    tendsto_nhds_unique_of_eventuallyEq (l1S.sub l2) l3 haux_sub

  simpa [Pole₁, RHS₁] using! hlim


lemma norm_mul_integral_Ici_le_integral_norm
    (A : ℂ) (F : ℝ → ℂ) (a : ℝ)
    (hF : IntegrableOn F (Set.Ici a))
    (hnorm : Integrable (fun u : ℝ => ‖F u‖)) :
    ‖A * (∫ u in Set.Ici a, F u)‖ ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) := by
  have hmul : ‖A * (∫ u in Set.Ici a, F u)‖ = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := by
    simp
  have hnormI :
      ‖∫ u in Set.Ici a, F u‖ ≤ ∫ u in Set.Ici a, ‖F u‖ := by
    have _ : Integrable F (Measure.restrict volume (Set.Ici a)) := hF
    have h :
        ‖∫ u, F u ∂Measure.restrict volume (Set.Ici a)‖
          ≤ ∫ u, ‖F u‖ ∂Measure.restrict volume (Set.Ici a) :=
      norm_integral_le_integral_norm (μ := Measure.restrict volume (Set.Ici a)) (f := F)
    simpa using h

  have hdom :
      (∫ u in Set.Ici a, ‖F u‖) ≤ ∫ u : ℝ, ‖F u‖ := by
    have hEq :
        (∫ u in Set.Ici a, ‖F u‖) =
          ∫ u : ℝ, Set.indicator (Set.Ici a) (fun u => ‖F u‖) u := by
      have h := (integral_indicator (μ := (volume : Measure ℝ))
        (s := Set.Ici a) (f := fun u => ‖F u‖))
      have h' := h measurableSet_Ici
      simpa using h'.symm
    have hind_int :
        Integrable (Set.indicator (Set.Ici a) (fun u => ‖F u‖)) :=
      hnorm.indicator measurableSet_Ici
    have hpoint :
        Set.indicator (Set.Ici a) (fun u => ‖F u‖)
            ≤ᵐ[volume] (fun u : ℝ => ‖F u‖) := by
      filter_upwards with u
      by_cases hu : u ∈ Set.Ici a
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    have hmono :=
        integral_mono_ae (μ := (volume : Measure ℝ))
          hind_int hnorm hpoint
    simpa [hEq] using hmono

  calc
    ‖A * (∫ u in Set.Ici a, F u)‖
        = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := hmul
    _   ≤ ‖A‖ * (∫ u in Set.Ici a, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hnormI (by simp)
    _   ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hdom (by simp)

lemma fourier_decay_of_CS2
    (ψ : CS 2 ℂ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  let ψ' : W21 := (ψ : W21)
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ' : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
    simpa using (decay_bounds_cor (ψ := ψ'))
  refine ⟨C, ?_⟩
  intro u
  simpa [ψ'] using! (hC u)

lemma integrable_norm_fourier_scaled_of_CS2
    (ψ : CS 2 ℂ) :
    Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
  obtain ⟨C, hdecay⟩ := fourier_decay_of_CS2 (ψ := ψ)
  have hC_nonneg : 0 ≤ C := by
    have h0 := hdecay 0
    have hnorm : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) 0‖ := norm_nonneg _
    have hC' : ‖𝓕 (ψ : ℝ → ℂ) 0‖ ≤ C := by simpa using h0
    exact hnorm.trans hC'
  have hmaj_int : Integrable (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    have hbase : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq
    have hscale :
        Integrable (fun u : ℝ => (1 + (u / (2 * Real.pi)) ^ 2)⁻¹) :=
      hbase.comp_div (by nlinarith [Real.pi_pos])
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, pow_two] using
      hscale.const_mul C
  have hle :
      (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖)
        ≤ᵐ[volume]
      (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    refine Filter.Eventually.of_forall ?_
    intro u
    simpa using (hdecay (u / (2 * Real.pi)))
  have hle_norm :
      (fun u : ℝ => ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖)
        ≤ᵐ[volume]
      (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) := by
    refine hle.mono ?_
    intro u hu
    have hden_pos : 0 < 1 + (u / (2 * Real.pi)) ^ 2 := by nlinarith
    have hnonneg : 0 ≤ (C : ℝ) / (1 + (u / (2 * Real.pi))^2) :=
      div_nonneg hC_nonneg hden_pos.le
    have hleft_nonneg : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖ := norm_nonneg _
    have hbound : ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖ ≤
        (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg] using hu
    have hC_abs : |C| = C := abs_of_nonneg hC_nonneg
    have hden_abs : |1 + (u / (2 * Real.pi))^2| = 1 + (u / (2 * Real.pi))^2 := by
      have : 0 ≤ 1 + (u / (2 * Real.pi))^2 := by nlinarith
      simpa using abs_of_nonneg this
    have hnorm :
        ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
          (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      have hrec :
          ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
            |C| / |1 + (u / (2 * Real.pi))^2| := by
        simp [Real.norm_eq_abs]
      simp [hC_abs, hden_abs, hrec]
    simpa [hnorm] using hbound
  have hmaj_int_norm :
      Integrable (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) :=
    hmaj_int.norm
  have hmeas :
      AEStronglyMeasurable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using! continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable.norm
  exact hmaj_int_norm.mono' hmeas hle_norm

lemma exists_bound_norm_G_on_tsupport
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (ψ : CS 2 ℂ) :
    ∃ K : ℝ, ∀ t : ℝ, t ∈ tsupport (ψ : ℝ → ℂ) →
      ‖G (1 + t * Complex.I)‖ ≤ K := by
  let s : Set ℝ := tsupport (ψ : ℝ → ℂ)
  have hscompact : IsCompact s := by
    simpa [s] using (ψ.h2.isCompact : IsCompact (tsupport (ψ : ℝ → ℂ)))
  have hphi_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by continuity
  have hphi_maps :
      Set.MapsTo (fun t : ℝ => (1 : ℂ) + t * Complex.I) s {z : ℂ | 1 ≤ z.re} := by
    intro t ht
    simp
  have hGcomp : ContinuousOn (fun t : ℝ => G ((1 : ℂ) + t * Complex.I)) s :=
    hG.comp hphi_cont.continuousOn hphi_maps
  have hnorm_contOn : ContinuousOn (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) s := hGcomp.norm
  have hbdd : BddAbove ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s) :=
    (hscompact.image_of_continuousOn hnorm_contOn).bddAbove
  refine ⟨sSup ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s), ?_⟩
  intro t ht
  have : ‖G ((1 : ℂ) + t * Complex.I)‖ ∈
      (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s := ⟨t, ht, rfl⟩
  exact le_csSup hbdd this

lemma norm_integrand_le_K_mul_norm_psi
    {x K : ℝ}
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
    ∀ t : ℝ,
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ ≤ K * ‖ψ t‖ := by
  intro t
  by_cases ht : t ∈ Function.support ψ
  · have hxnorm : ‖((x : ℂ) ^ (t * Complex.I))‖ = 1 := norm_x_cpow_it x t hx
    calc
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
          = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * ‖((x : ℂ) ^ (t * Complex.I))‖ := by
              simp [mul_left_comm, mul_comm]
      _   = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * 1 := by simp [hxnorm]
      _   ≤ K * ‖ψ t‖ := by
            have hGle : ‖G (1 + t * Complex.I)‖ ≤ K := hK t ht
            have : ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ ≤ K * ‖ψ t‖ :=
              mul_le_mul_of_nonneg_right hGle (norm_nonneg _)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · have hψ0 : ψ t = 0 := by
      by_contra hψ0
      exact ht (by simpa [Function.support] using hψ0)
    simp [hψ0, mul_comm]


lemma norm_error_integral_le
    (ψ : ℝ → ℂ) (x K : ℝ)
    (hGline_meas : Measurable (fun t : ℝ => G (1 + t * I)))
    (hψ_meas : AEStronglyMeasurable ψ)
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K)
    (hψ : Integrable (fun t : ℝ => ‖ψ t‖) ) :
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
      ≤ K * (∫ t : ℝ, ‖ψ t‖) := by
  have h1 : ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := by
    simpa using (norm_integral_le_integral_norm
        (f := fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))))
  have hmeas_main : AEStronglyMeasurable
        (fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) := by
    have hG' : AEMeasurable fun t : ℝ => G (1 + t * Complex.I) := hGline_meas.aemeasurable
    have hψ_meas' : AEMeasurable ψ := hψ_meas.aemeasurable
    have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hx_ne' : NeZero (x : ℂ) := ⟨hx_ne⟩
    have hxpow_meas : AEMeasurable fun t : ℝ => ((x : ℂ) ^ (t * Complex.I)) := by
      have hcontℂ : Continuous fun z : ℂ => ((x : ℂ) ^ z) :=
        continuous_const_cpow (z := (x : ℂ))
      have hcont : Continuous fun t : ℝ => ((x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
        hcontℂ.comp (by
          have h : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
            simpa using! (continuous_ofReal.mul continuous_const)
          simpa [mul_comm] using h)
      exact hcont.measurable.aemeasurable
    have hGψ_meas : AEMeasurable fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) := hG'.mul hψ_meas'
    have htotal : AEMeasurable (fun t : ℝ =>
            (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) :=
      hGψ_meas.mul hxpow_meas
    exact htotal.aestronglyMeasurable
  have hpt : (fun t : ℝ =>
          ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := by
    refine Eventually.of_forall ?_
    intro t
    exact norm_integrand_le_K_mul_norm_psi (hx := hx) (hK := hK) t
  have hR : Integrable (fun t : ℝ => K * ‖ψ t‖) := hψ.const_mul K
  have hL : Integrable (fun t : ℝ =>
        ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖) := by
      have hpt_norm :
          (fun t : ℝ => ‖‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖‖)
            ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := hpt.mono (by
          intro t ht
          simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using ht)
      exact hR.mono' hmeas_main.norm hpt_norm
  have h2 : (∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ ∫ t : ℝ, K * ‖ψ t‖ := integral_mono_ae (μ := (volume : Measure ℝ)) hL hR hpt
  have h3 : (∫ t : ℝ, K * ‖ψ t‖) = K * (∫ t : ℝ, ‖ψ t‖) := by
    simp [integral_const_mul]
  calc
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := h1
    _   ≤ ∫ t : ℝ, K * ‖ψ t‖ := h2
    _   = K * (∫ t : ℝ, ‖ψ t‖) := h3




lemma crude_upper_bound
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤ B := by

  -- Integrability of ψ
  have hψ_int : MeasureTheory.Integrable (ψ : ℝ → ℂ) := by
    simpa using (ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2)
  have hψ_norm_int : MeasureTheory.Integrable (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖) :=
    hψ_int.norm
  have hψ_meas : MeasureTheory.AEStronglyMeasurable (ψ : ℝ → ℂ) :=
    hψ_int.aestronglyMeasurable

  -- Uniform bound K for ‖G(1+it)‖ on support ψ
  rcases exists_bound_norm_G_on_tsupport (G := G) hG ψ with ⟨K, hK_ts⟩
  have hK_support :
      ∀ t : ℝ, t ∈ Function.support (ψ : ℝ → ℂ) → ‖G (1 + t * Complex.I)‖ ≤ K := by
    have hbnG (hKts : ∀ t : ℝ, t ∈ tsupport ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
      ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K := by
      intro t ht
      exact hKts t ((subset_tsupport ψ) ht)
    exact hbnG hK_ts

  -- Measurability of the line restriction t ↦ G(1 + t I) from continuity-on
  have hGline_meas : Measurable (fun t : ℝ => G (1 + t * Complex.I)) := by
    have hline_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by
      continuity
    have hmem : ∀ t : ℝ, ((1 : ℂ) + t * Complex.I) ∈ {s : ℂ | 1 ≤ s.re} := by
      intro t
      simp
    have hcont : Continuous (G ∘ fun t : ℝ => (1 : ℂ) + t * Complex.I) :=
      hG.comp_continuous hline_cont hmem
    simpa [Function.comp] using! hcont.measurable

  -- L¹ bound for the scaled Fourier transform norm
  have hF_norm_int :
      MeasureTheory.Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
    integrable_norm_fourier_scaled_of_CS2 ψ
  have hF_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using! continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable
  have hF_int :
      MeasureTheory.Integrable (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) :=
    by
      have hfin_norm :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
        hF_norm_int.hasFiniteIntegral
      have hfin :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
        simpa [MeasureTheory.hasFiniteIntegral_iff_norm] using hfin_norm
      exact ⟨hF_meas, hfin⟩
  refine ⟨K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
            + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖), ?_⟩
  intro x hx
  set I : ℂ := ∫ u in Set.Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) with hI

  -- Lemma 12
  have hlim :=
    limiting_fourier_variant (f := f) (A := A) (G := G)
      hpos hG hG' hf ψ hψpos hx
  have hlim' :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
        - A * I
      = ∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I) := by
    simpa [hI] using hlim

  -- express the tsum as RHS + A*I
  have htsum :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
      = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    have h' :
        (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
          = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I :=
      eq_add_of_sub_eq hlim'
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h'

  -- bound the RHS integral
  have hRHS_bound :
      ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖) :=
    norm_error_integral_le (G := G) (ψ := (ψ : ℝ → ℂ)) (x := x) (K := K)
      hGline_meas hψ_meas hx hK_support hψ_norm_int

  -- bound the A * I term
  have hA_bound :
      ‖A * I‖ ≤ ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hF_on : MeasureTheory.IntegrableOn
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (Set.Ici (-Real.log x)) :=
      hF_int.integrableOn
    simpa [hI] using
      norm_mul_integral_Ici_le_integral_norm (A := A)
        (F := fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (a := -Real.log x) hF_on hF_norm_int

  -- combine bounds
  have htsum_std :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)))
        = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using htsum

  -- bound in the normalized form
  have hbound :
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hnorm :
        ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
            (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖ =
          ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ :=
      congrArg norm htsum_std
    calc
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
          = ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ := hnorm
      _ ≤ ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖ + ‖A * I‖ :=
            norm_add_le _ _
      _ ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
            add_le_add hRHS_bound hA_bound
  exact hbound

set_option backward.isDefEq.respectTransparency false in
lemma Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) = 𝓕 f * 𝓕 g := by
  ext y
  simp only [Pi.mul_apply, FourierTransform.fourier, MeasureTheory.convolution,
    VectorFourier.fourierIntegral, ContinuousLinearMap.mul_apply']
  have h_int : Integrable (fun p : ℝ × ℝ ↦ 𝐞 (-(y * p.1)) • (f p.2 * g (p.1 - p.2))) := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine (Integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf hg).bdd_mul
      (c := 1) ?_ ?_
    · exact (by continuity : Continuous _).aestronglyMeasurable
    · filter_upwards with p; simp
  calc ∫ v, 𝐞 (-(y * v)) • ∫ t, f t * g (v - t)
      = ∫ v, ∫ t, 𝐞 (-(y * v)) • (f t * g (v - t)) := by
        simp only [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    _ = ∫ t, ∫ v, 𝐞 (-(y * v)) • (f t * g (v - t)) := integral_integral_swap h_int
    _ = ∫ t, f t • ∫ v, 𝐞 (-(y * v)) • g (v - t) := by
        simp only [Circle.smul_def, smul_eq_mul, mul_left_comm, integral_const_mul]
    _ = ∫ t, f t • ∫ u, 𝐞 (-(y * (u + t))) • g u := by
        congr 1; ext t
        rw [← integral_add_right_eq_self (fun v ↦ 𝐞 (-(y * v)) • g (v - t)) t]; simp
    _ = ∫ t, f t • ∫ u, (𝐞 (-(y * t)) * 𝐞 (-(y * u))) • g u := by
        congr 2 with t; congr 1
        simp only [mul_add, neg_add, mul_comm, Real.fourierChar.map_add_eq_mul]
    _ = ∫ t, 𝐞 (-(y * t)) • f t • ∫ u, 𝐞 (-(y * u)) • g u := by
        congr 1; ext t
        simp only [mul_smul, Circle.smul_def, smul_eq_mul, integral_const_mul]; ring
    _ = (∫ t, 𝐞 (-(y * t)) • f t) * ∫ u, 𝐞 (-(y * u)) • g u := by
        simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]

lemma Real.fourierIntegral_conj_neg {f : ℝ → ℂ} (y : ℝ) :
    𝓕 (fun x ↦ conj (f (-x))) y = conj (𝓕 f y) := by
  simp only [fourier_real_eq]
  have h_conj : ∀ x, 𝐞 (-(x * y)) • conj (f (-x)) = conj (𝐞 (x * y) • f (-x)) := fun x ↦ by
    simp only [Circle.smul_def, Real.fourierChar_apply, map_mul, smul_eq_mul, neg_mul,
      Complex.ofReal_neg, mul_neg]
    congr 1
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg]
  calc ∫ x, 𝐞 (-(x * y)) • conj (f (-x))
      = ∫ x, conj (𝐞 (x * y) • f (-x)) := by congr 1; ext x; exact h_conj x
    _ = conj (∫ x, 𝐞 (x * y) • f (-x)) := integral_conj
    _ = conj (∫ x, 𝐞 (-(x * y)) • f x) := by
        rw [← integral_neg_eq_self (fun x => 𝐞 (-(x * y)) • f x)]
        congr 2 with x; ring_nf

/-- Smooth compactly supported function with non-negative Fourier transform via self-convolution. -/
lemma auto_cheby_exists_smooth_nonneg_fourier_kernel :
    ∃ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) ∧ 0 < (𝓕 ψ 0).re := by
  obtain ⟨φ_real, hφSmooth, hφCompact, hφIcc, _, hφsupp⟩ :=
    smooth_urysohn_support_Ioo (a := 1/2) (b := 1) (c := 1) (d := 2) (by norm_num) (by norm_num)
  let φ : ℝ → ℂ := Complex.ofReal ∘ φ_real
  let φ_rev : ℝ → ℂ := fun x ↦ conj (φ (-x))
  let ψ_fun : ℝ → ℂ := convolution φ φ_rev (ContinuousLinearMap.mul ℂ ℂ) volume
  have hφSmooth' : ContDiff ℝ ∞ φ := contDiff_ofReal.comp hφSmooth
  have hφCompact' : HasCompactSupport φ := hφCompact.comp_left rfl
  have hφRevSmooth : ContDiff ℝ ∞ φ_rev := Complex.conjCLE.contDiff.comp (hφSmooth'.comp contDiff_neg)
  have hφRevCompact : HasCompactSupport φ_rev := (hφCompact'.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (by simp)
  have hφInt : Integrable φ := hφSmooth'.continuous.integrable_of_hasCompactSupport hφCompact'
  have hφRevInt : Integrable φ_rev := hφRevSmooth.continuous.integrable_of_hasCompactSupport hφRevCompact
  have hψSmooth : ContDiff ℝ ∞ ψ_fun := by
    convert! hφRevCompact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hφSmooth'.continuous.locallyIntegrable (μ := volume)) hφRevSmooth
  have hψCompact : HasCompactSupport ψ_fun :=
    HasCompactSupport.convolution (ContinuousLinearMap.mul ℂ ℂ) hφCompact' hφRevCompact
  refine ⟨ψ_fun, hψSmooth, hψCompact, fun y ↦ ?_, ?_⟩
  · rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg y, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact ⟨Complex.normSq_nonneg _, rfl⟩
  · have hφ_nonneg : ∀ x, 0 ≤ φ_real x := fun x ↦ by
      have hx := hφIcc x; by_cases h : x ∈ Set.Icc (1:ℝ) 1
      · simp only [Set.indicator_of_mem h, Pi.one_apply] at hx; linarith
      · simp only [Set.indicator_of_notMem h] at hx; exact hx
    have hvol_supp : (1 : ENNReal) ≤ volume (Function.support φ_real) := by
      have hsub : Set.Ico (1:ℝ) 2 ⊆ Function.support φ_real := fun x hx ↦
        hφsupp.symm ▸ Set.mem_Ioo.mpr ⟨by linarith [hx.1], hx.2⟩
      calc _ = volume (Set.Ico (1:ℝ) 2) := by simp [Real.volume_Ico]; norm_num
           _ ≤ _ := volume.mono hsub
    have hφint_pos : 0 < ∫ x, φ_real x :=
      (integral_pos_iff_support_of_nonneg_ae (.of_forall hφ_nonneg)
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact)).2
        (lt_of_lt_of_le (by simp) hvol_supp)
    have hFφ0_re : 0 < (𝓕 φ 0).re := by
      simp only [φ, fourier_real_eq, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul,
        Function.comp_apply]
      have hint : Integrable (fun x => (φ_real x : ℂ)) :=
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact).ofReal
      calc (∫ x, (φ_real x : ℂ)).re = ∫ x, (φ_real x : ℂ).re := (integral_re hint).symm
        _ = ∫ x, φ_real x := by simp only [Complex.ofReal_re]
        _ > 0 := hφint_pos
    rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg 0, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.normSq_pos.2 (fun h ↦ (ne_of_gt hFφ0_re) (by simp [h]))


/-- The series `∑ f(n)/n · 𝓕ψ(log(n/x)/(2π))` is summable for `x ≥ 1`. -/
lemma auto_cheby_fourier_summable (hpos : 0 ≤ f) (hf : ∀ σ', 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (x : ℝ) (hx : 1 ≤ x) :
    Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) := by
  let ψCS : CS 2 ℂ := ⟨ψ, hψSmooth.of_le (by norm_cast), hψCompact⟩
  let S : ℝ → ℂ := fun σ' ↦ ∑' n, term (f · : ℕ → ℂ) σ' n * 𝓕 ψCS.toFun (1 / (2 * π) * Real.log (n / x))
  let Pole : ℝ → ℂ := fun σ' ↦ (A : ℂ) * (x ^ (1 - σ') : ℝ) *
    ∫ u in Set.Ici (-Real.log x), (rexp (-u * (σ' - 1)) : ℂ) * 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' ↦ ∫ t : ℝ, G (σ' + t * I) * ψCS.toFun t * (x : ℂ) ^ (t * I)
  have l2 := limiting_fourier_lim2 (A := A) (x := x) ψCS hx
  have l3 := limiting_fourier_lim3 (G := G) hG ψCS hx
  have haux : (fun σ' ↦ S σ' - Pole σ') =ᶠ[𝓝[>] 1] RHS := eventually_nhdsWithin_of_forall fun σ' hσ' ↦ by
    simpa [S, Pole, RHS] using! limiting_fourier_aux hG' hf ψCS hx σ' hσ'
  have hS_tendsto : Tendsto S (𝓝[>] 1) (𝓝 (RHS 1 + A * ∫ u in Set.Ici (-Real.log x),
      𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π)))) := by
    convert! (l3.congr' haux.symm).add l2 using 1; ext σ'; simp [S, Pole]
  have hbounded : BoundedAtFilter (𝓝[>] 1) (fun σ' ↦ ‖S σ'‖) := by
    simp only [BoundedAtFilter]
    let L := ‖RHS 1 + A * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))‖
    have : ∀ᶠ σ' in 𝓝[>] 1, ‖S σ'‖ < L + 1 :=
      hS_tendsto.norm.eventually_lt tendsto_const_nhds (lt_add_one L)
    exact Asymptotics.IsBigO.of_bound (L + 1) (by filter_upwards [this] with σ h; simpa using h.le)
  let y : ℕ → ℝ := fun n ↦ (1 / (2 * π)) * Real.log (n / x)
  let w : ℕ → ℝ := fun n ↦ (𝓕 ψCS.toFun (y n)).re
  have hw : ∀ n, 0 ≤ w n := fun n ↦ (hψpos (y n)).1
  let rt : ℝ → ℕ → ℝ := fun σ n ↦ if n = 0 then 0 else f n / (n : ℝ) ^ σ * w n
  have rt_nn σ n : 0 ≤ rt σ n := by
    simp only [rt]; split_ifs with hn
    · rfl
    · exact mul_nonneg (div_nonneg (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero hn)) σ).le) (hw n)
  have hS_eq σ' (hσ' : 1 < σ') : S σ' = ↑(∑' n, rt σ' n) := by
    rw [Complex.ofReal_tsum]; apply tsum_congr; intro n
    simp only [rt, term, LSeries.term, y, w, one_div, mul_inv_rev]
    split_ifs with hn <;> simp only [hn, CharP.cast_eq_zero, Complex.ofReal_zero, zero_mul,
      Complex.ofReal_mul, Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; congr 1
    exact Complex.ext rfl (hψpos _).2
  have hMono n : AntitoneOn (fun σ ↦ rt σ n) (Set.Ioi 1) := fun σ₁ _ σ₂ _ h ↦ by
    simp only [rt]; split_ifs with hn; · rfl
    apply mul_le_mul_of_nonneg_right _ (hw n)
    apply div_le_div_of_nonneg_left (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero hn)) σ₁)
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)) h
  have hT_bdd : BoundedAtFilter (𝓝[>] 1) fun σ ↦ ∑' n, rt σ n := by
    rw [BoundedAtFilter, Asymptotics.isBigO_iff] at hbounded ⊢
    obtain ⟨C, hC⟩ := hbounded
    refine ⟨C, ?_⟩
    filter_upwards [hC, self_mem_nhdsWithin] with σ hnorm hσ
    rw [hS_eq σ hσ] at hnorm; simpa using hnorm
  have hSumm σ (hσ : 1 < σ) : Summable (rt σ ·) := by
    simpa [rt, w, y] using limiting_fourier_variant_lim1_aux ψCS hpos hf hψpos σ hσ
  have hSumm_1 : Summable (rt 1 ·) := by
    let σ_seq : ℕ → ℝ := fun k ↦ 1 + 1 / ((k : ℝ) + 1)
    have hσ_gt k : 1 < σ_seq k := by simp only [σ_seq, lt_add_iff_pos_right, one_div]; positivity
    have h_tendsto : Tendsto σ_seq atTop (𝓝[>] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, by filter_upwards with k; exact hσ_gt k⟩
      have : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        simp only [one_div]; exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
      simpa [σ_seq] using tendsto_const_nhds.add this
    have h_ptwise n : Tendsto (fun k ↦ rt (σ_seq k) n) atTop (𝓝 (rt 1 n)) := by
      simp only [rt]; split_ifs with hn; · exact tendsto_const_nhds
      refine ((tendsto_const_nhds.rpow (tendsto_nhdsWithin_iff.mp h_tendsto).1 (Or.inl ?_)).inv₀
        (by simp [hn])).const_mul (f n) |>.mul_const (w n)
      exact (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (hT_bdd.comp_tendsto h_tendsto)
    refine summable_of_sum_range_le (c := C) (rt_nn 1) fun m ↦ le_of_tendsto (tendsto_finsetSum _
        fun i _ ↦ h_ptwise i) ?_
    filter_upwards [h_tendsto.eventually self_mem_nhdsWithin, hC] with k hk hCk
    calc ∑ i ∈ Finset.range m, rt (σ_seq k) i
        ≤ ∑' n, rt (σ_seq k) n := (hSumm _ hk).sum_le_tsum _ fun n _ ↦ rt_nn _ n
      _ ≤ |∑' n, rt (σ_seq k) n| := le_abs_self _
      _ ≤ C := by simpa using hCk
  rw [show (fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))) =
      Complex.ofRealCLM ∘ (rt 1 ·) from ?_]
  · exact hSumm_1.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  ext n; simp only [rt, Real.rpow_one, one_div, w, y, Function.comp_apply]
  split_ifs with hn; · simp [hn]
  have him0 : (𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).im = 0 := (hψpos _).2
  have hre_eq : 𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x)) =
      Complex.ofReal ((𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).re) := by
    rw [← Complex.re_add_im (𝓕 ψCS.toFun _), him0]; simp
  conv_lhs => rw [show ψ = ψCS.toFun from rfl, hre_eq]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]

/-- Short interval bound from global filtered bound: if `∑ f(n)/n · 𝓕ψ(log(n/x)) ≤ B`,
then `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for some `ε, C > 0`. -/
lemma auto_cheby_short_interval_bound (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (B : ℝ) (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (hψ0 : 0 < (𝓕 ψ 0).re)
    (hB_bound : ∀ x ≥ 1, ‖∑' n, f n / n * 𝓕 ψ (1 / (2 * Real.pi) * Real.log (n / x))‖ ≤ B) :
    ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x := by
  have hF : Continuous (𝓕 ψ) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by continuity) (hψSmooth.continuous.integrable_of_hasCompactSupport hψCompact)
  have hg : Continuous fun y ↦ (𝓕 ψ y).re := Complex.continuous_re.comp hF
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.1 <|
    hg.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi (half_lt_self hψ0))
  let c := (𝓕 ψ 0).re / 2
  have hcpos : 0 < c := by dsimp only [c]; linarith
  have h_psi_ge_c : ∀ y, |y| < δ → c ≤ (𝓕 ψ y).re := fun y hy ↦ (hball (mem_ball_zero_iff.mpr hy)).le
  let ε := 1 - Real.exp (-2 * π * δ)
  have hε : 0 < ε ∧ ε < 1 := by
    have h1 : Real.exp (-2 * π * δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    exact ⟨by simp only [ε]; linarith, by simp only [ε]; linarith [Real.exp_pos (-2 * π * δ)]⟩
  have hB_nonneg : 0 ≤ B := (norm_nonneg _).trans (hB_bound 1 le_rfl)
  refine ⟨ε, B / c + 1, hε.1, hε.2, by positivity, fun x hx ↦ ?_⟩
  have h_summable : Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) :=
    auto_cheby_fourier_summable hpos hf hG hG' ψ hψSmooth hψCompact hψpos x hx
  have hx_pos : 0 < x := by linarith
  have h_sum_lower : c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      ≤ ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ ?_
    · by_cases hn : (n : ℝ) ∈ Set.Ioc ((1 - ε) * x) x
      · rw [Set.indicator_of_mem hn, Pi.one_apply, mul_one]
        have hn_pos : 0 < (n : ℝ) := by nlinarith [hn.1, hε.2]
        let y := (1 / (2 * π)) * Real.log (n / x)
        have h_arg_small : |y| < δ := by
          have h2pi : 0 < 2 * π := by linarith [Real.pi_pos]
          simp only [y, abs_mul, abs_div, abs_one, abs_of_pos h2pi]
          field_simp [ne_of_gt h2pi]; rw [mul_comm, abs_lt]
          have h_log_lower : -2 * π * δ < Real.log (n / x) := by
            rw [← Real.log_exp (-2 * π * δ), Real.log_lt_log_iff (Real.exp_pos _) (by positivity)]
            have : Real.exp (-2 * π * δ) = 1 - ε := by simp only [ε]; ring
            rw [this]; field_simp; exact hn.1
          have h_log_upper : Real.log (n / x) ≤ 0 :=
            Real.log_nonpos (by positivity) (div_le_one_of_le₀ hn.2 hx_pos.le)
          constructor <;> nlinarith [Real.pi_pos]
        have h1 : x⁻¹ ≤ (n : ℝ)⁻¹ := by rw [inv_le_inv₀ hx_pos hn_pos]; exact hn.2
        have h2 : c ≤ (𝓕 ψ y).re := h_psi_ge_c y h_arg_small
        have hfn : 0 ≤ f n := hpos n
        have hre : 0 ≤ (𝓕 ψ y).re := (hψpos y).1
        have hn_inv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
        calc c / x * f n = c * x⁻¹ * f n := by rw [div_eq_mul_inv]
          _ ≤ c * (n : ℝ)⁻¹ * f n := by gcongr
          _ ≤ (𝓕 ψ y).re * (n : ℝ)⁻¹ * f n := by gcongr
          _ = (n : ℝ)⁻¹ * (𝓕 ψ y).re * f n := by ring
          _ = f n / n * (𝓕 ψ y).re := by ring
      · rw [Set.indicator_of_notMem hn, mul_zero, mul_zero]
        exact mul_nonneg (div_nonneg (hpos n) (Nat.cast_nonneg n)) (hψpos _).1
    · refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun n hn ↦ ?_
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hn
      exact Nat.le_floor hn.2.2.1.2
    · rw [← Complex.summable_ofReal]; convert h_summable using 1; ext n
      rw [Complex.ofReal_mul, Complex.ofReal_div]
      norm_cast
      rw [Complex.ofReal_mul]
      congr 1
      apply Complex.ext
      · simp only [Complex.ofReal_re]
      · simp only [Complex.ofReal_im]; exact (hψpos _).2.symm
  have h_real_eq : ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re =
      (∑' n, (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [Complex.re_tsum h_summable]; congr with n
    rw [Complex.mul_re]; norm_cast; simp only [zero_mul, sub_zero]
  calc ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      = x / c * (c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)) := by
        field_simp [ne_of_gt hcpos, ne_of_gt hx_pos]
    _ ≤ x / c * B := by
        gcongr; rw [h_real_eq] at h_sum_lower
        exact h_sum_lower.trans ((Complex.re_le_norm _).trans (hB_bound x hx))
    _ = (B / c) * x := by field_simp [ne_of_gt hcpos]
    _ ≤ (B / c + 1) * x := by nlinarith

/-- Bootstraps short interval bounds to global Chebyshev bound via strong induction.
If `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for all `x ≥ 1`, then `∑_{n ≤ x} f(n) = O(x)`. -/
lemma auto_cheby_bootstrap_induction (hpos : 0 ≤ f)
    (h_short : ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x) :
    cheby f := by
  obtain ⟨ε, C₀, hε, hε1, hC₀, h_bound⟩ := h_short
  let C := C₀ / ε + f 0 + 1
  have hf0 : (0 : ℝ) ≤ f 0 := hpos 0
  have hdiv : 0 ≤ C₀ / ε := div_nonneg hC₀.le hε.le
  have hC : 0 ≤ C := by linarith
  refine ⟨C, fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with | h n ih =>
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [cumsum]
    · simp only [cumsum, Finset.sum_range_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf0,
        Nat.cast_one, mul_one, C]
      linarith
  let x := (n : ℝ) - 1
  have hx : x ≥ 1 := by simp only [x, ge_iff_le, le_sub_iff_add_le]; norm_cast
  let m := ⌊(1 - ε) * x⌋₊ + 1
  have hm_lt : m < n := by
    simp only [m, x]
    have h1 : (1 - ε) * (n - 1 : ℝ) < (n - 1 : ℕ) := by
      calc (1 - ε) * (↑n - 1) < 1 * (↑n - 1) := by gcongr; linarith
        _ = ↑n - 1 := by ring
        _ = ↑(n - 1) := by simp [Nat.cast_sub (by omega : 1 ≤ n)]
    have h2 : ⌊(1 - ε) * (n - 1 : ℝ)⌋₊ < n - 1 :=
      (Nat.floor_lt (mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ n - 1))).mpr h1
    omega
  have hm_gt : (m : ℝ) > (1 - ε) * x := by
    simp only [m, Nat.cast_add, Nat.cast_one, gt_iff_lt]
    exact Nat.lt_floor_add_one ((1 - ε) * x)
  have h_decomp : cumsum (fun k ↦ ‖(f k : ℂ)‖) n = cumsum (fun k ↦ ‖(f k : ℂ)‖) m + ∑ k ∈ Finset.Ico m n, f k := by
    simp only [cumsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _),
      Finset.sum_range_add_sum_Ico _ (by omega : m ≤ n)]
  have h_Ico : ∑ k ∈ Finset.Ico m n, f k ≤ C₀ * x := by
    calc ∑ k ∈ Finset.Ico m n, f k
        = ∑ k ∈ Finset.Ico m n, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          have ⟨hkm, hkn⟩ := Finset.mem_Ico.mp hk
          have hk_gt : (k : ℝ) > (1 - ε) * x := by linarith [hm_gt, (Nat.cast_le (α := ℝ)).mpr hkm]
          have hk_le : (k : ℝ) ≤ x := by
            have h1 : k ≤ n - 1 := Nat.le_pred_of_lt hkn
            have h2 : (k : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast h1
            simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, x] at h2 ⊢; exact h2
          simp only [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hk_gt, hk_le⟩), Pi.one_apply, mul_one]
      _ ≤ ∑' k, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Summable.sum_le_tsum _ (fun k _ ↦ mul_nonneg (hpos k) (Set.indicator_nonneg (by simp) _)) ?_
          refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun k hk ↦ ?_
          simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hk
          exact Nat.le_floor hk.2.1.2
      _ ≤ C₀ * x := h_bound x hx
  have hm_le : (m : ℝ) ≤ (1 - ε) * x + 1 := by
    have hpos' : 0 ≤ (1 - ε) * x := mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ x)
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le hpos']
  have hnorm : ∀ k, ‖(f k : ℂ)‖ = f k := fun k ↦ by simp [abs_of_nonneg (hpos k)]
  simp only [hnorm] at h_decomp ih ⊢
  calc cumsum f n = cumsum f m + ∑ k ∈ Finset.Ico m n, f k := h_decomp
    _ ≤ C * m + C₀ * x := by linarith [ih m hm_lt, h_Ico]
    _ ≤ C * ((1 - ε) * x + 1) + C₀ * x := by nlinarith [hC]
    _ = (C * (1 - ε) + C₀) * x + C := by ring
    _ ≤ C * x + C := by
        have : C₀ ≤ C * ε := by
          calc C₀ = (C₀ / ε) * ε := by field_simp [ne_of_gt hε]
            _ ≤ (C₀ / ε + f 0 + 1) * ε := by gcongr; linarith [hpos 0]
            _ = C * ε := by simp only [C]
        nlinarith [hε, hε1, hx]
    _ ≤ C * n := by simp only [x]; ring_nf; linarith [hC]


lemma auto_cheby (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) : cheby f := by
  obtain ⟨ψ_fun, hψSmooth, hψCompact, hψpos, hψ0⟩ := auto_cheby_exists_smooth_nonneg_fourier_kernel
  obtain ⟨B, hB⟩ := crude_upper_bound hpos hG hG' hf ⟨ψ_fun, hψSmooth.of_le ENat.LEInfty.out, hψCompact⟩ hψpos
  exact auto_cheby_bootstrap_induction hpos <| auto_cheby_short_interval_bound hpos hf hG hG' B ψ_fun
    hψSmooth hψCompact hψpos hψ0 fun x hx ↦ hB x (by linarith)


theorem WienerIkeharaTheorem'' (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) :=
  WienerIkeharaTheorem' hpos hf (auto_cheby (f := f) (A := A) (G := G) hpos hf hG hG') hG hG'

end auto_cheby




theorem WeakPNT_character
    {q a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ if n % q = a then Λ n else 0) s =
      - (∑' χ : DirichletCharacter ℂ q,
          ((starRingEnd ℂ) (χ a) * ((deriv (LSeries (fun n:ℕ ↦ χ n)) s)) /
          (LSeries (fun n:ℕ ↦ χ n) s))) / (Nat.totient q : ℂ) := by
  have : NeZero q := ⟨by omega⟩
  convert vonMangoldt.LSeries_residueClass_eq ((ZMod.isUnit_iff_coprime a q).mpr ha) hs using 1
  · congr with n
    have : n % q = a ↔ (n : ZMod q) = a := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
    simp [this]
    split_ifs <;> simp [*]
  · rw [div_eq_inv_mul, neg_mul_comm, tsum_fintype]
    congr 3 with χ
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs,
      DirichletCharacter.LFunction_eq_LSeries _ hs, mul_div]
    congr 2
    rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply_eq_inv',
      ← ZMod.coe_unitOfCoprime a ha, ZMod.inv_coe_unit, map_units_inv]



theorem WeakPNT_AP_prelim {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) :
    ∃ G: ℂ → ℂ, (ContinuousOn G {s | 1 ≤ s.re}) ∧
    (Set.EqOn G (fun s ↦ LSeries (fun n ↦ if n % q = a then Λ n else 0) s - 1 /
      ((Nat.totient q) * (s - 1))) {s | 1 < s.re}) := by
  have : NeZero q := NeZero.of_pos hq
  have hG : ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ if (n : ZMod q) = a then Λ n else 0) s - (q.totient : ℂ)⁻¹ / (s - 1)) {s | 1 < s.re} := by
    use vonMangoldt.LFunctionResidueClassAux (a : ZMod q), vonMangoldt.continuousOn_LFunctionResidueClassAux (q := q) (a := a)
    have := vonMangoldt.eqOn_LFunctionResidueClassAux ((ZMod.isUnit_iff_coprime a q).mpr ha)
    convert this using 6; split <;> simp_all
  convert hG using 6
  · simp [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
  · rw [inv_eq_one_div, div_div]

/-- The von Mangoldt function divided by `n ^ s` is summable for `s > 1`. -/
lemma summable_vonMangoldt_div_rpow {s : ℝ} (hs : 1 < s) : Summable (fun n ↦ Λ n / n ^ s) := by
  have h_log_bound : ∀ n : ℕ, (Λ n : ℝ) ≤ Real.log n := fun n ↦ vonMangoldt_le_log
  suffices h_log_sum : Summable fun n : ℕ ↦ Real.log n / (n : ℝ) ^ s by
    exact .of_nonneg_of_le (fun n ↦ div_nonneg vonMangoldt_nonneg (by positivity))
      (fun n ↦ div_le_div_of_nonneg_right (h_log_bound n) (by positivity)) h_log_sum
  have h_log_le_n_eps : ∀ ε > 0, ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ (ε - s) := by
    intro ε hε_pos
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n ≤ C * (n : ℝ) ^ ε := by
      refine ⟨1 / ε, by positivity, fun n hn ↦ ?_⟩
      have := log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) ^ ε)
      rw [log_rpow (by positivity)] at this
      nlinarith [rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) ε, mul_div_cancel₀ 1 hε_pos.ne']
    refine ⟨C, hC_pos, fun n hn ↦ ?_⟩
    rw [rpow_sub (by positivity)]
    exact le_trans (div_le_div_of_nonneg_right (hC n hn) (by positivity)) (by rw [div_eq_mul_inv]; ring_nf; norm_num)
  obtain ⟨C, _, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ ((s - 1) / 2 - s) :=
    h_log_le_n_eps ((s - 1) / 2) (by linarith)
  rw [← summable_nat_add_iff 2]
  exact Summable.of_nonneg_of_le (fun n ↦ div_nonneg (log_nonneg (by norm_cast; omega))
    (rpow_nonneg (by positivity) _)) (fun n ↦ hC _ (by omega)) (Summable.mul_left _ <| by
      simpa using summable_nat_add_iff 2 |>.2 <| summable_nat_rpow.2 <| by linarith)


theorem WeakPNT_AP {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun N ↦ cumsum (fun n ↦ if n % q = a then Λ n else 0) N / N) atTop (𝓝 (1 / q.totient)) := by
  have h_summable : ∀ s : ℝ, 1 < s → Summable (fun n ↦ (if n % q = a then Λ n else 0) / n ^ s) := by
    intro s hs
    refine .of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) (summable_vonMangoldt_div_rpow hs)
    · split_ifs <;> positivity
    · split_ifs <;> norm_num; exact div_nonneg vonMangoldt_nonneg (by positivity)
  obtain ⟨G, hG₁, hG₂⟩ := WeakPNT_AP_prelim hq ha ha'
  convert WienerIkeharaTheorem'' _ _ _ _ using 1
  · use G
  · intro n
    simp_all only [ge_iff_le, one_div, mul_inv_rev, Pi.ofNat_apply]
    split
    next h => subst h; simp_all only [vonMangoldt_nonneg]
    next h => simp_all only [le_refl]
  · intro σ' hσ'
    specialize h_summable σ' hσ'
    simp_all only [ge_iff_le, one_div, mul_inv_rev]
    convert h_summable using 1
    ext
    simp only [nterm, norm_real, norm_eq_abs]
    ring_nf
    split_ifs <;> simp [*, mul_comm]
  · assumption
  · convert hG₂ using 3
    · exact tsum_congr fun n ↦ by cases n <;> aesop
    · norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]




























































end Campaign180File13

/- Source module: PrimeNumberTheoremAnd.Consequences -/
section Campaign180File14



open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  intro z hz
  have hz' := Set.Ico_subset_Icc_self.trans h hz
  have hcd : c ≤ d := by
    contrapose! hz'
    rw [Icc_eq_empty_of_lt hz']
    exact notMem_empty _
  simp only [mem_Ico, mem_Icc] at *
  refine ⟨hz'.1, hz'.2.eq_or_lt.resolve_left ?_⟩
  rintro rfl
  apply hz.2.not_ge
  have := h <| right_mem_Icc.mpr (hz.1.trans hz.2.le)
  simp only [mem_Icc] at this
  exact this.2

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx


lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R}
    (x : ℝ) : ∑ᶠ (n : ℕ) (_ : n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero


lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_le_two]
  exact one_lt_two


/-- If u ~ v and w-u = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← add_sub_cancel u w]
  exact add_isLittleO huv hwu

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

/-- `(⌊x⌋₊ + 1) / x → 1` as `x → ∞`. -/
lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  rwa [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx a; simp only [_root_.id] at a; linarith)] at h'

/-- `x =Θ x / c` for nonzero constant `c`. -/
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm

/-- Filtered sum over `Iic n` equals filtered sum over `Icc 1 n` for primes. -/
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩

/-- `Icc 0 n = insert 0 (Icc 1 n)` -/
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega


theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), log p) ~[atTop] fun x ↦ x := by
  have hReal :
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ~[atTop]
        fun x ↦ x := by
    have h x : ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ) = θ x := by
      rw [Chebyshev.theta_eq_sum_Icc]
      have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
        (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr (Nat.le_floor hpx)
      calc ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)
          = ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), log (p : ℝ) :=
            finsum_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
        _ = ∑ p ∈ hfin.toFinset, log (p : ℝ) := finsum_mem_eq_finite_toFinset_sum _ hfin
        _ = _ := sum_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
            mem_filter, mem_Icc, and_congr_left_iff]; exact fun hp ↦
            ⟨fun hpx ↦ ⟨Nat.zero_le _, Nat.le_floor hpx⟩, fun ⟨_, hpn⟩ ↦
              (le_or_gt 0 x).elim
                (fun hx ↦ (Nat.floor_le hx).trans' (Nat.cast_le.mpr hpn)) fun hx ↦
                absurd (Nat.le_zero.mp (Nat.floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
                  hp.ne_zero⟩) (fun _ _ ↦ rfl)
    have heq :
        (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) =ᶠ[atTop] θ :=
      Filter.Eventually.of_forall h
    exact chebyshev_asymptotic.congr_left heq.symm
  simp only [IsEquivalent,
    show (fun n : ℕ ↦ ∑ᶠ (p : ℕ) (_ : p ≤ n) (_ : p.Prime), log (p : ℝ)) =
      (fun x : ℝ ↦ ∑ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), log (p : ℝ)) ∘ Nat.cast
    from funext fun _ ↦ finsum_congr fun _ ↦ by simp]
  exact hReal.isLittleO.comp_tendsto tendsto_natCast_atTop_atTop

theorem chebyshev_asymptotic' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun t ↦ ε * t)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ (x : ℝ), θ x = x + f x := by
  have H := chebyshev_asymptotic
  rw [IsEquivalent, isLittleO_iff] at H
  let f := (fun x ↦ θ x - x)
  have integrable (x : ℝ) (hx : 2 ≤ x) : IntegrableOn f (Set.Icc 2 x) := by
    rw [IntegrableOn]
    refine Integrable.sub ?_ (ContinuousOn.integrableOn_Icc (continuousOn_id' _))
    refine Chebyshev.integrableOn_theta_div_id_mul_log_sq x |>.mul_continuousOn (g' := fun t => t * log t ^ 2)
      (ContinuousOn.mul (continuousOn_id' _) (ContinuousOn.pow (continuousOn_log |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) 2)) isCompact_Icc |>.congr_fun_ae ?_
    simp only [measurableSet_Icc, ae_restrict_eq, EventuallyEq, eventually_inf_principal]
    refine .of_forall fun t ⟨ht1, _⟩ => ?_
    rw [div_mul_cancel₀]
    simpa only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      log_eq_zero, or_self_left, not_or] using ⟨by linarith, by linarith, by linarith⟩
  refine ⟨f, fun ε hε ↦ ?_, integrable, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    specialize @H (c * ε) (mul_pos hc hε)
    simp only [Pi.sub_apply, norm_eq_abs, mul_assoc, eventually_atTop, norm_mul,
      abs_of_pos hε, f] at H ⊢
    exact H
  refine fun r => by simp [f]

theorem chebyshev_asymptotic'' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun _ ↦ ε)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ x > (0 : ℝ), θ x = x + x * (f x) := by
  obtain ⟨f, hf1, inte, hf2⟩ := chebyshev_asymptotic'
  refine ⟨fun t => f t / t, fun ε hε ↦ ?_, ?_, ?_⟩
  · simp only [isLittleO_iff, norm_eq_abs, norm_mul, eventually_atTop,
      norm_div] at hf1 ⊢
    intro r hr
    replace hf1 := hf1 ε hε
    obtain ⟨N, hN⟩ := hf1 hr
    use |N| + 1
    intro x hx
    have hx' : |N| + 1 ≤ |x| := by rwa [abs_of_nonneg (a := x) (le_trans (by positivity) hx)]
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx'), mul_assoc]
    exact hN x (le_trans (le_trans (le_abs_self N) (by linarith)) hx)

  · intro x hx
    refine inte x hx |>.mul_continuousOn (g' := fun t : ℝ => t⁻¹)
      (continuousOn_inv₀ |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) isCompact_Icc |>.congr_fun_ae <| .of_forall <| by simp [div_eq_mul_inv]
  intro x hx
  rw [hf2, mul_div_cancel₀]
  linarith

-- one could also consider adding a version with p < x instead of p \leq x



theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, p = exp (x + E x) := by
  use (fun x ↦ ∑ p ∈ (filter Nat.Prime (Iic ⌊x⌋₊)), log p - x)
  constructor
  · exact Asymptotics.IsEquivalent.isLittleO chebyshev_asymptotic
  intro x
  simp only [cast_prod, add_sub_cancel, exp_sum]
  apply Finset.prod_congr rfl
  intros x hx
  rw[Real.exp_log]
  rw[Finset.mem_filter] at hx
  norm_cast
  exact Nat.Prime.pos hx.right

theorem primorial_bounds_finprod :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), p = exp (x + E x) := by
  obtain ⟨E, hE, hprod⟩ := primorial_bounds
  refine ⟨E, hE, fun x ↦ ?_⟩
  have hfin : {p : ℕ | (p : ℝ) ≤ x ∧ p.Prime}.Finite :=
    (Iic ⌊x⌋₊).finite_toSet.subset fun p ⟨hpx, _⟩ ↦ mem_Iic.mpr <| le_floor hpx
  have heq : ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p =
      ∏ p ∈ (Iic ⌊x⌋₊).filter Prime, p := by
    calc ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x) (_ : p.Prime), p
        = ∏ᶠ (p : ℕ) (_ : (p : ℝ) ≤ x ∧ p.Prime), p :=
      finprod_congr fun p ↦ by by_cases hp : p.Prime <;> simp [hp]
      _ = ∏ p ∈ hfin.toFinset, p := finprod_mem_eq_finite_toFinset_prod _ hfin
      _ = _ := prod_congr (by ext p; simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
          mem_filter, mem_Iic, and_congr_left_iff]; exact fun hp ↦
          ⟨le_floor, fun hpn ↦ (le_or_gt 0 x).elim
          (fun hx ↦ (Nat.floor_le hx).trans' (cast_le.mpr hpn)) fun hx ↦
          absurd (le_zero.mp (floor_eq_zero.mpr (hx.trans_le zero_le_one) ▸ hpn))
          hp.ne_zero⟩) (fun _ _ ↦ rfl)
  simp only [heq, hprod]

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  rw [le_iff_lt_or_eq] at hb
  rcases hb with hb | rfl; swap
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]
  · have := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (log x)⁻¹)
      (u' := fun x => -1 / (x * (log x)^2))
      (v := fun x => x)
      (v' := fun _ => 1) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (lt_iff_not_ge |>.1 hb), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := fun t => t⁻¹) (x := x)
        · simpa using! HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
            (hasDerivAt_id' (log x))
            (by simp only [ne_eq, log_eq_zero, not_or]; refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply hasDerivAt_log; linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hb)]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_log0.mono fun x hx ↦ ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;>
        apply MeasureTheory.integrable_const)
    simp only [mul_one] at this
    rw [this]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le (le_of_lt hb),
      intervalIntegral.integral_of_le (le_of_lt hb),
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    · rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
      · refine .of_forall fun x hx => ?_
        simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
        rw [inv_mul_cancel₀, mul_one]
        linarith
      exact measurableSet_Ioc

lemma integral_log_inv' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  have := integral_log_inv a b ha hb
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos hb, Set.uIoc_of_le hb,
    smul_eq_mul, one_mul] at this
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [this]

lemma integral_log_inv'' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (log a)⁻¹ * a + ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) + ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  rw [integral_log_inv' a b ha hb]
  group

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  classical
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp only [Function.support_inv, measurableSet_Icc, Measure.restrict_apply']
    rw [show Function.support log ∩ Set.Icc 2 x = Set.Icc 2 x by
      rw [Set.inter_eq_right]
      intro t ht
      simp only [Set.mem_Icc, Function.mem_support, ne_eq, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩]
    simpa
  · simp only [measurableSet_Icc, ae_restrict_eq, EventuallyLE, eventually_inf_principal]
    refine .of_forall fun t (ht : _ ∧ _) => ?_
    simpa only [Pi.zero_apply, inv_nonneg] using log_nonneg (by linarith)
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀
    · exact (continuousOn_log).mono <| by aesop

    · rintro t ⟨ht, -⟩
      simp only [ne_eq, log_eq_zero, not_or]
      exact ⟨by linarith, by linarith, by linarith⟩

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  have := integral_log_inv_pos x hx
  linarith

lemma pi_asymp_aux (x : ℝ) (hx : 2 ≤ x) : Nat.primeCounting ⌊x⌋₊ =
    (log x)⁻¹ * θ x + ∫ t in Set.Icc 2 x, θ t * (t * log t ^ 2)⁻¹ := by
  rw [th43_b _ hx]
  simp_rw [div_eq_mul_inv, Chebyshev.theta_eq_sum_Icc]
  ring_nf!

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  obtain ⟨f, hf, f_int, hf'⟩ := chebyshev_asymptotic''
  have eq1 : ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      (∫ t in Set.Icc 2 x,
        (t + t * f t) * (t * log t ^ 2)⁻¹) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [pi_asymp_aux x hx, hf' x (by linarith)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hf' t (by grind)]

  replace eq1 :
    ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      ((∫ t in Set.Icc 2 x, (log t ^ 2)⁻¹) +
        (∫ t in Set.Icc 2 x, (f t) * (log t ^ 2)⁻¹)) := by
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1]
    congr
    simp_rw [mul_inv_rev, add_mul]
    rw [MeasureTheory.integral_add]
    · congr 1
      all_goals
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        field [show t ≠ 0 by grind]
    · apply IntegrableOn.mul_continuousOn
        (hg := ContinuousOn.integrableOn_Icc <| continuousOn_id' _)
        (hK := isCompact_Icc)
      apply continuousOn_log1.mono ?_
      intro y h
      simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [show (fun t ↦ t * f t * ((log t ^ 2)⁻¹ * t⁻¹)) =
        fun t ↦ f t * (t * (log t ^ 2)⁻¹ * t⁻¹) by ext; ring]
      apply IntegrableOn.mul_continuousOn (hK := isCompact_Icc)
      · apply f_int x (by linarith)
      · simp_rw [mul_assoc]
        refine ContinuousOn.mul (continuousOn_id' (Set.Icc 2 x)) ?_
        apply continuousOn_log1.mono ?_
        intro y h
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at h ⊢
        exact ⟨by linarith, by linarith, by linarith⟩

  simp_rw [mul_add] at eq1
  simp_rw [show ∀ (x : ℝ),
    (log x)⁻¹ * x + (log x)⁻¹ * (x * f x) +
    ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) =
    ((log x)⁻¹ * x + (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
    ((log x)⁻¹ * (x * f x) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)
    by intros; ring] at eq1

  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
      ((log x)⁻¹ * (x * f x) +
        ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) +
      C := by
    use ((log 2)⁻¹ * 2)
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1, ← integral_log_inv'' _ _ (by rfl) hx]
    ring
  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      (⌊x⌋₊.primeCounting / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - 1 =
      ((log x)⁻¹ * (x * f x) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) +
      C / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
    obtain ⟨C, hC⟩ := eq1
    use C
    filter_upwards [hC, eventually_gt_atTop 2] with x hC hx
    rw [hC]
    field [integral_log_inv_ne_zero]
  simp_rw [isLittleO_iff] at hf
  choose C hC using eq1
  simp_rw [← one_div] at hC
  apply isLittleO_congr hC (by rfl) |>.mpr
  have ineq1 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c) : ∀ᶠ(x : ℝ) in atTop,
    (log x)⁻¹ * x * |f x| ≤ c * ε * ((log x)⁻¹ * x) := by
    filter_upwards [eventually_ge_atTop 2, hf ε hε hc] with x hx hM
    simp only [norm_eq_abs] at hM
    rw [abs_of_pos hε] at hM
    rw [mul_comm (c * ε)]
    gcongr
    bound
  have int_flog {a b : ℝ} (ha: 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ |f t| * (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    apply IntegrableOn.mul_continuousOn
    · apply Integrable.abs <| f_int b hb |>.mono (Set.Icc_subset_Icc_left ha) (by rfl)
    · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
      · simp
        grind
      · intro t ht
        simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
        exact ⟨by linarith, by linarith, by linarith⟩
    · exact isCompact_Icc
  have int_inv_log_sq {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    refine ContinuousOn.integrableOn_Icc <|
      ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
    · grind
    · intro t ht
      simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
  simp_rw [eventually_atTop] at hf
  choose M hM using hf
  have ineq2 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c)  :
    ∃ (D : ℝ),
      ∀ᶠ (x : ℝ) in atTop,
      |∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹| ≤
      c * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) + D := by
    use (((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), |f t| * (log t ^ 2)⁻¹) -
              c * ε * ∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹) +
            c * ε * ((log 2)⁻¹ * 2))
    filter_upwards [eventually_gt_atTop (max 2 (M ε hε hc))] with x hx
    calc _
      _ ≤ ∫ (t : ℝ) in Set.Icc 2 x, |f t * (log t ^ 2)⁻¹| :=
        norm_integral_le_integral_norm fun a ↦ f a * (log a ^ 2)⁻¹
      _ = ∫ (t : ℝ) in Set.Icc 2 x, |f t| * (log t ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [abs_mul, abs_of_nonneg (a := (log t ^ 2)⁻¹)]
        norm_num
        apply pow_nonneg
        exact log_nonneg <| by grind
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          |f t| * (log t ^ 2)⁻¹) := by
        rw [← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
        · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le, volume_singleton]
        · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
        · apply int_flog (by rfl) (le_max_left ..)
        · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ ≤ (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          (c * ε) * (log t ^ 2)⁻¹) := by
          gcongr 1
          apply setIntegral_mono_on
          · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
          · rw [IntegrableOn, integrable_const_mul_iff]
            · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
            · simp only [isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, not_or]
              exact ⟨by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ht
            simp only [Set.mem_Icc, sup_le_iff] at ht
            apply mul_le_mul_of_nonneg_right
            · refine hM ε hε hc t ht.1.2 |>.trans ?_
              simp only [norm_eq_abs, abs_of_pos hε, le_refl]
            · norm_num
              refine pow_nonneg (log_nonneg <| by linarith) 2
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) * ∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) := by
          congr 1
          exact integral_const_mul (c * ε) _
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) +
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) -
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
        ring
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) -
              ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
          congr 3
          rw [add_comm, ← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
          · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le,
              volume_singleton]
          · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
          · apply int_inv_log_sq (by rfl) (le_max_left ..)
          · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ = ((c * ε) * (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        ring
      _ = ((c * ε) * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
            ((log 2)⁻¹ * 2) - ((log x)⁻¹ * x))) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        congr 2
        rw [integral_log_inv' _ _ (by rfl)]
        · ring
        · simp only [max_lt_iff] at hx
          linarith
      _ = _ := by ring
  choose D hD using ineq2

  have ineq4 (const : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |const / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| ≤ 1/2 * ε := by
    obtain rfl|hconst := eq_or_ne const 0
    · filter_upwards with x
      simp[hε.le]
    have ineq (x : ℝ) (hx : 2 < x) :=
      calc (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)
        _ ≥ (∫ (_ : ℝ) in Set.Icc 2 x, (log x)⁻¹) := by
          apply setIntegral_mono_on (integrable_const _)
          · refine ContinuousOn.integrableOn_Icc <|
              ContinuousOn.inv₀ (continuousOn_log |>.mono ?_) ?_
            · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le,
              isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
            · intro t ht
              simp only [Set.mem_Icc, ne_eq, log_eq_zero, not_or] at ht ⊢
              exact ⟨by linarith, by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ⟨ht1, ht2⟩
            gcongr
            bound
        _ = (x - 2) * (log x)⁻¹ := by
          rw [MeasureTheory.integral_const]
          simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, volume_Icc,
            smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff, sub_nonneg,
            inv_eq_zero, log_eq_zero, Measure.real]
          refine Or.inl (le_of_lt hx)

    simp_rw [abs_div]
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| / ((x - 2) * (log x)⁻¹) := by
      apply div_le_div₀ (abs_nonneg _) (by rfl)
      · apply mul_pos
        · linarith
        · norm_num
          rw [Real.log_pos_iff]
          · linarith
          · linarith
      · rw [abs_of_pos (integral_log_inv_pos _ hx)]
        exact ineq x hx
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| * (log x / ((x - 2))) := by
      refine ineq x hx |>.trans <| le_of_eq ?_
      field_simp
    have lim := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 (by norm_num)
    simp only [pow_one, one_mul, ← sub_eq_add_neg] at lim
    rw [tendsto_atTop_nhds] at lim
    specialize lim (Metric.ball 0 ((1/2) * ε / |const| : ℝ)) (by
      simp only [Metric.mem_ball, dist_self]
      apply _root_.div_pos
      · linarith
      · simpa only [abs_pos, ne_eq]) Metric.isOpen_ball
    obtain ⟨M, hM⟩ := lim
    rw [eventually_atTop]
    refine ⟨max 3 M, ?_⟩
    intro x hx
    simp only [Metric.mem_ball, dist_zero_right, max_le_iff, norm_eq_abs] at hM hx
    refine ineq x (by linarith) |>.trans ?_
    specialize hM x hx.2
    rw [abs_of_nonneg (by
      apply div_nonneg
      · refine log_nonneg (by linarith)
      · linarith)] at hM
    have ineq' : |const| * (log x / (x - 2)) < |const| * ((1/2) * ε / |const|) := by
      rw [mul_lt_mul_iff_right₀]
      · exact hM
      · simpa only [abs_pos, ne_eq]
    rw [mul_div_cancel₀] at ineq'
    · refine le_of_lt ineq'
    · simpa only [ne_eq, abs_eq_zero]
  rw [isLittleO_iff]
  intro ε hε
  specialize ineq4 (|D ε hε (1/2) (by linarith)| + |C|) ε hε
  simp only [one_div, norm_eq_abs, norm_one, mul_one]
  filter_upwards [eventually_gt_atTop 2, ineq4, ineq1 ε hε (1 / 2) (by norm_num),
      hD ε hε (1 / 2) (by norm_num)] with x hx hB ineq1 hD
  have := integral_log_inv_pos x (by linarith) |>.le
  calc _
    _ ≤ |((log x)⁻¹ * (x * f x) / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      apply abs_add_three
    _ = |(log x)⁻¹ * (x * f x)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      rw [abs_div, abs_div, abs_div]
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        repeat rw [abs_of_pos <| integral_log_inv_pos _ (by linarith)]
    _ = ((log x)⁻¹ * x * |f x|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        congr
        rw [abs_mul, abs_mul, abs_of_nonneg (by bound), abs_of_nonneg (by linarith), mul_assoc]
    _ ≤ ((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        ((1/2) * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) +
          D ε hε (1/2) (by linarith)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        gcongr
    _ = ((1/2) * ε * (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      ring
    _ = (1/2) * ε + (D ε hε (1/2) (by linarith) + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      congr 1
      rw [mul_div_assoc, div_self, mul_one]
      apply integral_log_inv_ne_zero
      linarith
    _ ≤ (1/2) * ε + (|D ε hε (1/2) (by linarith)| + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      gcongr
      apply le_abs_self
    _ ≤ (1/2) * ε + (1/2) * ε := by
      rw [abs_div, abs_of_nonneg, abs_of_pos (a := ∫ _ in _, _)] at hB
      · gcongr
      · apply integral_log_inv_pos; linarith
      · positivity
    _ = ε := by
      field


theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']

lemma inv_div_log_asy : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  have := Chebyshev.integral_one_div_log_sq_isBigO
  rw [isBigO_iff] at this
  obtain ⟨c, hc⟩ := this
  use c
  filter_upwards [hc, eventually_ge_atTop 2] with x hc hx
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  apply le_trans (by apply le_norm_self)
  nth_rewrite 2 [norm_of_nonneg (by positivity)] at hc
  exact hc

lemma integral_log_inv_pialt (x : ℝ) (hx : 4 ≤ x) : ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t =
    x / log x - 2 / log 2 + ∫ (t : ℝ) in Set.Icc 2 x, 1 / (log t) ^ 2 := by
  have := integral_log_inv 2 x (by norm_num) (by linarith)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx]),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx]),
    ← mul_one_div, one_div, ← mul_one_div, one_div]
  simp only [one_div, this, mul_comm]

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  obtain ⟨c, hc⟩ := inv_div_log_asy
  use fun x => ((∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2) - 2 / log 2) * log x / x
  constructor
  · simp_rw [mul_div_assoc, mul_comm]
    apply isLittleO_mul_iff_isLittleO_div _|>.mpr
    · simp_rw [one_div_div]
      apply IsLittleO.sub
      · apply IsBigO.trans_isLittleO (g := (fun x ↦ x / log x ^ 2))
        · rw [isBigO_iff]
          use c
          filter_upwards [eventually_ge_atTop 2, hc] with x hx hc
          simp only [norm_eq_abs]
          rwa [abs_of_nonneg, abs_of_nonneg]
          · bound
          · apply setIntegral_nonneg measurableSet_Icc fun t ht ↦ (by bound)
        apply isLittleO_of_tendsto
        · simp
        apply tendsto_log_atTop.inv_tendsto_atTop.congr'
        filter_upwards [eventually_ne_atTop 0] with x hx
        simp only [Pi.inv_apply]
        field
      apply isLittleO_mul_iff_isLittleO_div _|>.mp
      · conv => arg 2; ext; rw [mul_comm]
        apply IsLittleO.const_mul_left isLittleO_log_id_atTop
      · filter_upwards [eventually_ge_atTop 2] with x hx
        simp; grind
    filter_upwards [eventually_ge_atTop 2] with x hx
    simp
    grind
  · filter_upwards [eventually_ge_atTop 4] with x hx
    rw [integral_log_inv_pialt x hx]
    field [show log x ≠ 0 by simp; grind]


theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨f, hf, h⟩ := pi_asymp
  obtain ⟨f', hf', h'⟩ := integral_div_log_asymptotic
  use (fun x => (log x / x) * ⌊x⌋₊.primeCounting - 1)
  constructor
  · apply IsLittleO.congr' (f₁ := (fun x ↦ f x + f x * f' x + f' x)) _ _ (by rfl)
    · apply IsLittleO.add _ hf'
      apply IsLittleO.add hf
      convert! hf.mul hf'
      ring
    · filter_upwards [eventually_ge_atTop 2, h, h'] with x hx h h'
      rw [h, intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc, h']
      have : log x ≠ 0 := by simp; grind
      field
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

theorem pi_alt' :
    (fun (x : ℝ) ↦ (primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / log x) := by
  obtain ⟨f, ⟨hf1, hf2⟩⟩ := pi_alt
  simp_rw [hf2, IsEquivalent]
  have : ((fun x ↦ (1 + f x) * x / log x) - fun x ↦ x / log x) =
      (fun x ↦ f x * x / log x) := by
    ext
    simp
    ring
  rw [this]
  convert hf1.mul_isBigO (f₂ := (fun x ↦ x / log x)) (g₂ := (fun x ↦ x /log x))
      (isBigO_refl ..) using 2
  all_goals first | ring | rfl


lemma pi_nth_prime (n : ℕ) :
    primeCounting (nth_prime n) = n + 1 := by
  rw [primeCounting, primeCounting', count_nth_succ_of_infinite infinite_setOfPred_prime]

lemma tendsto_nth_prime_atTop : Tendsto nth_prime atTop atTop :=
  nth_strictMono infinite_setOfPred_prime |>.tendsto_atTop

lemma pi_nth_prime_asymp :
    (fun n ↦ (nth_prime n) / (log (nth_prime n))) ~[atTop] (fun (n : ℕ) ↦ (n : ℝ)) := by
  trans (fun (n : ℕ) ↦ ( n + 1 : ℝ))
  · have : Tendsto (fun n ↦ ((nth_prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr tendsto_nth_prime_atTop
    convert! pi_alt'.comp_tendsto this |>.symm
    simp only [Function.comp_apply, floor_natCast]
    rw [pi_nth_prime]
    norm_cast
  · apply IsEquivalent.add_isLittleO (by rfl)
    exact isLittleO_const_id_atTop (1 : ℝ) |>.natCast_atTop

lemma log_nth_prime_asymp : (fun n ↦ log (nth_prime n)) ~[atTop] (fun n ↦ log n) := by
  have := pi_nth_prime_asymp.log tendsto_natCast_atTop_atTop
  · apply IsEquivalent.trans _ this
    apply IsEquivalent.congr_right (v := (fun n ↦ log (nth_prime n) - log (log (nth_prime n))))
    swap
    · filter_upwards with n
      rw [log_div]
      · exact_mod_cast prime_nth_prime n |>.ne_zero
      · apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
        <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
    symm
    apply IsEquivalent.sub_isLittleO (by rfl)
    apply IsLittleO.comp_tendsto isLittleO_log_id_atTop
    have : Tendsto (fun n ↦ ((nth_prime n) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_iff.mpr tendsto_nth_prime_atTop
    apply tendsto_log_atTop.comp this

lemma nth_prime_asymp : (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ n * log n) := by
  have := pi_nth_prime_asymp.mul log_nth_prime_asymp
  convert! this using 1
  ext n
  simp only [Pi.mul_apply]
  have : log (nth_prime n) ≠ 0 :=by
    apply log_ne_zero.mpr ⟨?_, ?_, ?_⟩
      <;> norm_cast<;> linarith [prime_nth_prime n |>.two_le]
  field


theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, n > 1 → nth_prime n = (1 + c n) * n * log n := by
  let c : ℕ → ℝ := fun n ↦ (nth_prime n) / (n * log n) - 1
  refine ⟨c, ?_, ?_⟩
  swap
  · intro n hn
    have : log n ≠ 0 := by rw [Real.log_ne_zero]; rify at hn; grind
    simp [c]
    field_simp
  apply isLittleO_of_tendsto
  · simp
  simp only [div_one]
  unfold c
  have := isEquivalent_iff_tendsto_one ?_|>.mp nth_prime_asymp
  swap
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simp
    norm_cast
    grind
  convert! this.add_const (-1 : ℝ) using 2
  norm_num



theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, nth_prime (n + 1) - nth_prime n = (c n) * nth_prime n := by
  use (fun n => (nth_prime (n+1) - nth_prime n) / nth_prime n)
  refine ⟨?_, ?_⟩
  · obtain ⟨k, k_o1, p_n_eq⟩ := pn_asymptotic
    simp only [isLittleO_one_iff]
    rw [Filter.tendsto_congr' (f₂ := fun n ↦
        ((1 + k (n+1))*(n+1)*log (n+1) - (1 + k n)*n*log n) / ((1 + k n)*n*log n))]
    swap
    · simp only [EventuallyEq, eventually_atTop]
      use 2; intro n hn
      rw [p_n_eq n (by linarith), p_n_eq (n+1) (by linarith)]
      grind
    simp_rw [sub_div]
    have zero_eq_minus: (0 : ℝ) = 1 - 1 := by
      simp
    rw [zero_eq_minus]
    apply Filter.Tendsto.sub
    · conv =>
        arg 1
        intro n
        equals ((1 + k (n + 1)) / (1 + k n) ) * ((↑n + 1) * log (↑n + 1) / (↑n * log ↑n)) =>
          field_simp
      nth_rw 6 [← (one_mul 1)]
      apply Filter.Tendsto.mul
      · have one_div: nhds 1 = nhds ((1: ℝ) / 1) := by simp
        rw [one_div]
        apply Filter.Tendsto.div
        · nth_rw 3 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · simp
          · rw [Filter.tendsto_add_atTop_iff_nat]
            rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
            · simp only [div_one] at k_o1
              exact k_o1
            · simp
        · nth_rw 2 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · simp
          · rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
            · simp only [div_one] at k_o1
              exact k_o1
            · simp

        simp
      · conv =>
          arg 1
          intro x
          equals ((↑x + 1) / x) * (log (↑x + 1) / (log ↑x)) =>
            field_simp
        nth_rw 3 [← (one_mul 1)]
        apply Filter.Tendsto.mul
        · simp_rw [add_div]
          nth_rw 2 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · rw [← Filter.tendsto_add_atTop_iff_nat 1]
            field_simp
            simp
          · simp only [one_div]
            exact tendsto_inv_atTop_nhds_zero_nat
        · have log_eq: ∀ (n: ℕ), log (↑n + 1) = log ↑n + log (1 + 1/n) := by
            intro n
            by_cases n_eq_zero: n = 0
            · simp [n_eq_zero]
            · calc
                _ = log (n * (1 + 1 / n)) := by field_simp
                _ = log n + log (1 + 1/n) := by
                  rw [Real.log_mul]
                  · simpa
                  · simp only [one_div, ne_eq]
                    positivity

          simp_rw [log_eq]
          simp_rw [add_div]
          nth_rw 3 [← (AddMonoid.add_zero 1)]
          apply Filter.Tendsto.add
          · rw [← Filter.tendsto_add_atTop_iff_nat 2]
            have log_not_zero: ∀ n: ℕ, log (n + 2) ≠ 0 := by
              intro n
              simp only [ne_eq, log_eq_zero, not_or]
              refine ⟨?_, ?_, ?_⟩
              · norm_cast
              · norm_cast
                simp
              · norm_cast
            simp [log_not_zero]
          · rw [← Filter.tendsto_add_atTop_iff_nat 2]
            apply squeeze_zero (g := fun (n: ℕ) => (log 2 / log (n + 2)))
            · intro n
              have log_plus_nonzero: 0 ≤ log (1 + 1 / ↑(n + 2)) := by
                apply log_nonneg
                simp only [cast_add, cast_ofNat, one_div, le_add_iff_nonneg_right, inv_nonneg]
                norm_cast
                simp only [le_add_iff_nonneg_left, _root_.zero_le]
              exact div_nonneg log_plus_nonzero (log_natCast_nonneg (n + 2))
            · intro n
              norm_cast
              have log_le_2: log (1 + 1 / ↑(n + 2)) ≤ log 2 := by
                apply Real.log_le_log
                · positivity
                · have two_eq_one_plus_one: (2 : ℝ) = 1 + 1 := by
                    norm_num
                  rw [two_eq_one_plus_one]
                  simp only [cast_add, cast_ofNat, one_div, add_le_add_iff_left, ge_iff_le]
                  apply inv_le_one_of_one_le₀
                  linarith

              rw [div_le_div_iff_of_pos_right]
              · exact log_le_2
              · apply Real.log_pos
                norm_cast
                simp
            · apply Filter.Tendsto.div_atTop (l := atTop) (a := log 2)
              · simp
              · norm_cast
                have shift_fn :=
                  Filter.tendsto_add_atTop_iff_nat (f := fun n => log (n)) (l := atTop) 2
                rw [shift_fn]
                apply Filter.Tendsto.comp Real.tendsto_log_atTop
                exact tendsto_natCast_atTop_atTop

    · have eventually_nonzero: ∃ t, t > 2 ∧ ∀ n, 1 + k (n + t) ≠ 0 := by
        rw [Asymptotics.isLittleO_iff_tendsto] at k_o1
        · rw [NormedAddGroup.tendsto_nhds_zero] at k_o1
          specialize k_o1 ((1 : ℝ) / 2)
          simp only [one_div, gt_iff_lt, inv_pos, ofNat_pos, div_one, norm_eq_abs, eventually_atTop, forall_const] at k_o1
          obtain ⟨a, ha⟩ := k_o1
          use (a + 3)
          refine ⟨by simp, ?_⟩
          intro n
          specialize ha (n + (a + 3))
          have a_le_plus: a ≤ n + (a + 3) := by omega
          simp only [a_le_plus, forall_const] at ha

          by_contra!
          rw [add_eq_zero_iff_eq_neg] at this
          rw [← abs_neg] at ha
          rw [← this] at ha
          simp only [abs_one] at ha
          have two_inv_lt := inv_lt_one_of_one_lt₀ (a := (2 : ℝ)) (by simp)
          linarith
        · simp

      obtain ⟨t, t_gt_2, ht⟩ := eventually_nonzero
      rw [← Filter.tendsto_add_atTop_iff_nat t]
      have denom_nonzero: ∀ n, ((1 + k (n + t)) * ↑(n + t) * log ↑(n + t)) ≠ 0 := by
        intro n
        simp only [cast_add, ne_eq, _root_.mul_eq_zero, log_eq_zero, not_or]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · exact ht n
        · norm_cast
          omega
        · norm_cast
          omega
        · refine ⟨?_, by norm_cast⟩
          norm_cast
          omega
      conv =>
        arg 1
        intro n
        rw [div_self (denom_nonzero n)]
      simp
  · intro n
    have nth_nonzero: nth_prime n ≠ 0 := by
      exact Nat.Prime.ne_zero (prime_nth_prime n)
    simp [nth_nonzero]



lemma prime_in_gap' (a b : ℕ) (h : a.primeCounting < b.primeCounting)
    : ∃ (p : ℕ), p.Prime ∧ (a + 1) ≤ p ∧ p < (b + 1) := by
  obtain ⟨p, hp, pp⟩ := exists_of_count_lt_count h
  exact ⟨p, pp, hp.left, hp.right⟩

lemma prime_in_gap (a b : ℝ) (ha : 0 < a)
    (h : ⌊a⌋₊.primeCounting < ⌊b⌋₊.primeCounting)
    : ∃(p : ℕ), p.Prime ∧ a < p ∧ p ≤ b := by

  have hab : ⌊a⌋₊ < ⌊b⌋₊ := Monotone.reflect_lt Nat.monotone_primeCounting h
  obtain ⟨w, h, ha, hb⟩ := prime_in_gap' ⌊a⌋₊ ⌊b⌋₊ h
  refine ⟨w, h, lt_of_floor_lt ha, ?_⟩
  have : a < b := by
    by_contra h
    cases lt_or_eq_of_le <| le_of_not_gt h with
    | inl hh => linarith [floor_le_floor <| le_of_lt hh]
    | inr hh =>
      rw [hh] at hab
      rwa [←lt_self_iff_false ⌊a⌋₊]
  by_contra h
  have : ⌊b⌋₊ < w := floor_lt (by linarith) |>.mpr (lt_of_not_ge h)
  have : ⌊b⌋₊ + 1 ≤ w := by linarith
  linarith

lemma bound_f_second_term (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 + f x) < (1 + δ) := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) < 1 + z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p

  rw [Filter.eventually_atTop]

  use a
  intro b hb
  exact bound_one_plus_f b δ (ha b (by linarith))


lemma bound_f_first_term {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + f ((1 + ε) * x)) > (1 - δ)  := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) > 1 - z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p


  rw [Filter.eventually_atTop]

  use a
  intro b hb

  have a_pos: 0 < a := by
    simp [a]

  have pos_mul: ∀ x y z : ℝ, 0 < x → 0 < y → 1 < z → x ≤ y → x < y * z := by
    intro x y z _ hy hz hlt
    have y_lt: y < y * z := by
      exact (lt_mul_iff_one_lt_right hy).mpr hz
    linarith

  have mul_increase: a ≤ (1 + ε) * b := by
    simp only [ a] at hb
    have a_le := pos_mul a b (1 + ε) a_pos (by linarith) (by linarith) (by linarith)
    linarith

  exact bound_one_plus_f ((1 + ε) * b) δ (ha ((1 + ε) * b) mul_increase)

lemma smaller_terms {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ)
    (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 - δ) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) <
      (1 + f ((1 + ε) * x)) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) := by
  have first_term := bound_f_first_term hε f hf δ hδ
  simp only [gt_iff_lt, eventually_atTop] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [eventually_atTop]
  let a := max p 1
  have ha: ∀ (b : ℝ), a ≤ b → 1 - δ < 1 + f ((1 + ε) * b) := by
    intro b hb
    have a_ge_p: p ≤ a := by
      simp [a]
    specialize hp b (by linarith)
    exact hp
  use a
  intro b hb
  rw [mul_lt_mul_iff_left₀]
  · exact ha b hb
  · simp only [sup_le_iff, a] at hb
    have b_ge_one: 1 ≤ b := hb.2
    have log_pos: Real.log ((1 + ε) *b) > 0 := by
      have one_pplus_pos: 1 < (1 + ε) := by linarith
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · exact one_lt_mul_of_lt_of_le one_pplus_pos b_ge_one

    positivity

lemma second_smaller_terms (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop,
      (1 + δ) * (x / Real.log x) > (1 + f x) * (x / Real.log x) := by
  have first_term := bound_f_second_term f hf δ hδ

  simp only [_root_.add_lt_add_iff_left, eventually_atTop] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [gt_iff_lt, eventually_atTop]
  let a := max p 2
  have ha: ∀ (b : ℝ), a ≤ b → 1 + δ > 1 + f ( b) := by
    intro b hb
    have a_ge_p: p <= a := by simp [a]
    specialize hp b (by linarith)
    linarith
  use a
  intro b hb
  specialize ha b hb
  have rhs_nonzero:  b / log ( b) > 0 := by
    simp only [sup_le_iff, a] at hb
    obtain ⟨_, hb2⟩ := hb
    have log_pos: Real.log (b) > 0 := by
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · linarith
    positivity
  rw [mul_lt_mul_iff_left₀]
  · exact ha
  · linarith

lemma x_log_x_atTop : Filter.Tendsto (fun x => x / Real.log x) Filter.atTop Filter.atTop := by
  have inv_log_x_div := Filter.Tendsto.comp (f := fun x => Real.log x / x) (g := fun x => x⁻¹)
    (x := Filter.atTop) (y := (nhdsWithin 0 (Set.Ioi 0))) (z := Filter.atTop) ?_ ?_
  · simp_rw [Function.comp_def, inv_div] at inv_log_x_div
    exact inv_log_x_div
  · exact tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have log_div_x := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
      simp only [pow_one, one_mul, add_zero] at log_div_x
      exact log_div_x
    · simp only [Set.mem_Ioi, eventually_atTop]
      use 2
      intro x hx
      have log_pos: 0 < Real.log x := by
        refine (Real.log_pos_iff ?_).mpr ?_ <;> linarith
      positivity


lemma tendsto_by_squeeze (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun (x : ℝ) => (Nat.primeCounting ⌊(1 + ε) * x⌋₊ : ℝ) -
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop := by
  obtain ⟨c, hc, pi_x_eq⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  conv =>
    arg 1
    intro x
    rw [pi_x_eq]
    rw [pi_x_eq]
  simp only [div_one] at hc

  -- (1 + δ) * (( x / (Real.log (x)))) > (1 + f ( x)) * ( x / (Real.log (x)))

  let d: ℝ := ε/(2*(2 + ε))
  have hd: 0 < d := by positivity
  have first_helper := smaller_terms hε c hc (d) hd
  have second_helper := second_smaller_terms c hc d hd

  apply Filter.tendsto_atTop_mono' (f₁ := fun x => (
      ((1 - d) * ((1 + ε) * x / log ((1 + ε) * x)))
      -
      ((1 + d) * (x / log x)))
    )
  · rw [Filter.EventuallyLE]

    simp only [eventually_atTop] at first_helper
    simp only [gt_iff_lt, eventually_atTop] at second_helper

    obtain ⟨a1, ha1⟩ := first_helper
    obtain ⟨a2, ha2⟩ := second_helper

    simp only [eventually_atTop]

    use (max a1 a2)
    intro b hb

    have lt_compare: ∀ a b c d : ℝ, a < c ∧ b > d → a - b ≤ c - d := by
      intro a b c d h_lt
      obtain ⟨a_lt, b_gt⟩ := h_lt
      linarith

    apply lt_compare
    simp only [ sup_le_iff] at hb
    specialize ha1 b hb.1
    specialize ha2 b hb.2
    field_simp
    field_simp at ha1 ha2
    exact ⟨ha1, ha2⟩
  · rw [← Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
    have log_split: ∀ x: Set.Ioi 1, x.val / log ((1 + ε) * x.val) =
      x.val / (log (1 + ε) + log (x.val)) := by
      intro x
      have x_ge_one: 1 < x.val := Set.mem_Ioi.mp x.property
      rw [Real.log_mul (by linarith) (by linarith)]

    have log_factor: ∀ x: Set.Ioi 1, x.val / (log (1 + ε) + log (x.val)) =
      x.val / ((1 + (log (1 + ε)/(log x.val))) * (log x.val)) := by
      intro x
      have : log (x.val) ≠ 0 := by
        have pos := Real.log_pos x.property
        linarith
      field_simp
      rw [add_comm]

    conv at log_factor =>
      intro x
      rhs
      rw [div_mul_eq_div_mul_one_div]

    conv =>
      arg 1
      intro x
      lhs
      rw [mul_div_assoc]
      rw [log_split x]

    conv =>
      arg 1
      intro x
      lhs
      rw [log_factor]

    suffices Tendsto (fun x : Set.Ioi (1 : ℝ) ↦ (1 - d) * ((1 + ε) * x) /
      ((1 + log (1 + ε) / log x) * log x) - (1 + d) * x / log x) atTop atTop by
      field_simp at this ⊢
      exact this
    conv =>
      arg 1
      intro x
      rw [sub_eq_add_neg]
      rw [← neg_div]
      rw [div_add_div]
      · skip
      tactic =>
        simp only [ne_eq, _root_.mul_eq_zero, log_eq_zero, not_or]
        have x_pos := x.property
        simp_rw [Set.Ioi, Set.mem_ofPred_eq] at x_pos
        refine ⟨?_, by linarith, by linarith, by linarith⟩
        have log_num_pos: 0 < log (1 + ε) := by
          exact Real.log_pos (by linarith)
        have log_denom_pos: 0 < log x := by
          exact Real.log_pos x.property
        positivity
      tactic =>
        have pos := Real.log_pos (x.property)
        linarith

    conv =>
      arg 1
      intro x
      equals ↑x * (log ↑x * ((1 + ε) * (1 - d)) -
          (1 + log (1 + ε) / log ↑x) * ((1 + d) * log ↑x)) /
        (log ↑x * ((1 + log (1 + ε) / log ↑x) * log ↑x)) =>
        ring

    simp only [mul_div_mul_comm]
    conv =>
      arg 1
      intro x
      rw [mul_comm]

    apply Filter.Tendsto.pos_mul_atTop (C := (1 + ε) * (1 - d) - (1 + d))
    · simp only [d, sub_pos]
      field_simp
      ring_nf
      rw [add_assoc]
      rw [add_lt_add_iff_left]
      apply lt_of_sub_pos
      ring_nf
      positivity
    · conv =>
        arg 1
        intro x
        lhs
        rhs
        equals (log x.val) * ((1 + log (1 + ε) / log ↑x) * ((1 + d))) =>
          ring

      simp_rw [← mul_sub]
      conv =>
        arg 1
        intro x
        rhs
        rw [mul_comm]

      simp only [mul_div_mul_comm]
      conv =>
        arg 1
        intro x
        lhs
        equals 1 =>
          have log_pos := Real.log_pos x.property
          field_simp

      simp only [one_mul]
      conv =>
        arg 3
        equals nhds (((1 + ε) * (1 - d) - (1 + d)) / 1) => simp

      apply Filter.Tendsto.div
      · apply Filter.Tendsto.sub
        · simp
        · conv =>
            arg 3
            equals nhds (1 * (1 + d)) => simp
          apply Filter.Tendsto.mul
          · conv =>
              arg 3
              equals nhds (1 + 0) => simp
            apply Filter.Tendsto.add
            · simp
            · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
              · simp
              · simp only [tendsto_comp_val_Ioi_atTop]
                exact tendsto_log_atTop
          · simp
      · conv =>
          arg 3
          equals nhds (1 + 0) => simp
        apply Filter.Tendsto.add
        · simp
        · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
          · simp
          · simp only [tendsto_comp_val_Ioi_atTop]
            exact tendsto_log_atTop
      · simp
    · let x_div_log (x: ℝ) := x / Real.log x
      conv =>
        arg 1
        equals (fun (x : Set.Ioi 1) => x_div_log x.val) => rfl

      rw [Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
      exact x_log_x_atTop


theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  have squeeze := tendsto_by_squeeze (ε/2) (by linarith)
  rw [Filter.tendsto_iff_forall_eventually_mem] at squeeze
  specialize squeeze (Set.Ici 1) (by exact Ici_mem_atTop 1)
  simp only [Set.mem_Ici, eventually_atTop] at squeeze
  obtain ⟨a, ha⟩ := squeeze
  rw [eventually_atTop]
  use (max a 1)
  intro b hb
  rw [sup_le_iff] at hb
  specialize ha b hb.1

  have val_lt : (⌊b⌋₊.primeCounting : ℝ) < ⌊(1 + ε/2) * b⌋₊.primeCounting := by linarith
  norm_cast at val_lt

  have jump := prime_in_gap b ((1 + ε/2) * b) (by linarith) val_lt
  obtain ⟨p, hp, b_lt_p, p_le⟩ := jump
  have p_lt: p < (1 + ε) * b := by
    linarith
  use p



theorem sum_mobius_div_self_le (N : ℕ) : |∑ n ∈ range N, μ n / (n : ℚ)| ≤ 1 := by
  cases N with
  | zero => simp only [range_zero, sum_empty, abs_zero, zero_le_one]
  | succ N =>
  /- simple cases -/
  obtain rfl | hN := N.eq_zero_or_pos
  · simp
  /- annoying case -/
  have h_sum : 1 = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
      μ d * Int.fract (N / d : ℚ) := calc
    (1 : ℚ) = ∑ m ∈ Ioc 0 N, ∑ d ∈ m.divisors, μ d := by
      have (x : ℕ) (hx : x ∈ Ioc 0 N) : ∑ d ∈ divisors x, μ d = if x = 1 then 1 else 0 := by
        rw [mem_Ioc] at hx
        rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
      rw [sum_congr rfl this]
      simp [hN.ne']
    _ = ∑ d ∈ range (N + 1), μ d * (N / d : ℕ) := by
      simp_rw [← coe_mul_zeta_apply, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (add_one_pos _),
        sum_insert (by simp), Ico_add_one_add_one_eq_Ioc]
      simp
    _ = ∑ d ∈ range (N + 1), (μ d : ℚ) * ⌊(N / d : ℚ)⌋ := by
      simp_rw [Rat.floor_natCast_div_natCast]
      simp [← Int.natCast_ediv]
    _ = (∑ d ∈ range (N + 1), (μ d / d : ℚ)) * N - ∑ d ∈ range (N + 1),
        μ d * Int.fract (N / d : ℚ) := by
      simp_rw [sum_mul, ← sum_sub_distrib, mul_comm_div, ← mul_sub, Int.self_sub_fract]
  rw [eq_sub_iff_add_eq, eq_comm, ← eq_div_iff (by norm_num [Nat.pos_iff_ne_zero.mp hN])] at h_sum

  /- Next, we establish bounds for the error term -/
  have hf' (d : ℕ) : |Int.fract ((N : ℚ) / d)| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact Int.fract_lt_one _
  have h_bound : |∑ d ∈ range (N + 1), μ d * Int.fract ((N : ℚ) / d)| ≤ N - 1 := by
    /- range (N + 1) → Icc 1 N + part that evals to 0 -/
    rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (by simp), sum_insert (by simp),
      ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, zero_add,
      Finset.Ico_add_one_right_eq_Icc, zero_add]
    /- Ico 1 (N + 1) → Ico 1 N ∪ {N + 1} that evals to 0 -/
    rw [← Ico_insert_right hN, sum_insert (by simp), div_self (by simp; grind), Int.fract_one,
      mul_zero, zero_add]
    /- bound sum -/
    have (d : ℕ) : |μ d * Int.fract ((N : ℚ) / d)| ≤ 1 := by
      rw [abs_mul, ← one_mul 1]
      refine mul_le_mul ?_ (hf' _).le (abs_nonneg _) zero_le_one
      norm_cast
      exact abs_moebius_le_one
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum fun d _ ↦ this d).trans
    simp [cast_sub (one_le_iff_ne_zero.mpr hN.ne')]

  rw [h_sum, abs_le]
  rw [abs_le, neg_sub] at h_bound
  constructor
  <;> simp only [le_div_iff₀, div_le_iff₀, cast_pos.mpr hN]
  <;> linarith [h_bound.left]



lemma sum_mobius_mul_floor (x : ℝ) (hx : 1 ≤ x) :
  ∑ n ∈ Iic ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) * (⌊x/n⌋ : ℝ) = 1 := by
  norm_cast
  convert ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum μ ⌊x⌋₊ |>.symm using 1
  · rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp)]
    simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, div_zero, Int.floor_zero, mul_zero,
      zero_add, Int.natCast_ediv]
    refine sum_congr rfl fun n hn ↦ ?_
    congr
    norm_cast
    rw [← floor_div_natCast, Int.natCast_floor_eq_floor]
    positivity
  · simpa [moebius_mul_coe_zeta, one_apply]


noncomputable def mu_log : ArithmeticFunction ℝ :=
    ⟨(fun n ↦ μ n * ArithmeticFunction.log n), (by simp)⟩

lemma mu_log_apply (n : ℕ) : mu_log n = μ n * ArithmeticFunction.log n := by
  rfl

lemma mu_log_mul_zeta : mu_log * ArithmeticFunction.zeta = -Λ := by
  ext n
  rw [coe_mul_zeta_apply]
  simp_rw [mu_log_apply]
  rw [sum_moebius_mul_log_eq]
  rfl

lemma mu_log_eq_mu_mul_neg_lambda : mu_log = μ * -Λ := by
  rw [← mu_log_mul_zeta, mul_comm, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

lemma sum_mu_Lambda (x : ℝ) : ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) * log n = - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x/k) := by
  rw [Iic_eq_Icc, bot_eq_zero, ← add_sum_Ioc_eq_sum_Icc (by simp), ← add_sum_Ioc_eq_sum_Icc (by simp)]
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, CharP.cast_eq_zero, log_zero, mul_zero,
    zero_add, div_zero, zero_mul]
  simp_rw [← log_apply, ← mu_log_apply, mu_log_eq_mu_mul_neg_lambda]
  rw [sum_Ioc_mul_eq_sum_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [ArithmeticFunction.neg_apply, sum_neg_distrib]
  ring_nf
  congr 2
  unfold Psi
  congr
  rw [← floor_div_natCast]
  rfl

lemma M_log_identity (x : ℝ) (hx : 1 ≤ x) : M x * log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (log (x/k) - Psi (x/k)) := by
  have h_log_identity : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k) = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    rw [Finset.sum_mul _ _ _]
    rw [← Finset.sum_sub_distrib] ; refine Finset.sum_congr rfl fun i hi => ?_ ; by_cases hi' : i = 0 <;> simp +decide [*, Real.log_div, ne_of_gt (zero_lt_one.trans_le hx)] ; ring
  generalize_proofs at *
  have h_log_identity' : ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k = -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
    convert sum_mu_Lambda x using 1
  have h_psi_identity :
      (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k)) =
        -∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k := by
    simpa [neg_neg] using (congrArg Neg.neg h_log_identity').symm
  unfold M
  symm
  calc
    (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k))) =
        (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [mul_sub, Finset.sum_sub_distrib]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x / k) := by
          simp [h_log_identity]
    _ = ((∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x -
          ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) -
          (-∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log k) := by
          simp [h_psi_identity]
    _ = (∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ)) * Real.log x := by ring

noncomputable def R (x : ℝ) : ℝ := Psi x - x

lemma R_isLittleO : R =o[atTop] id := by
  have h_pnt : (fun x => Psi x - x) =o[atTop] (fun x => x) := by
    have h_psi : (fun x => Psi x) ~[atTop] (fun x => x) := by
      simpa [Psi] using! WeakPNT''
    exact h_psi
  convert! h_pnt using 1

lemma sum_mobius_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
  have h_abs : ∀ x : ℝ, 1 ≤ x → |∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) / n| ≤ 1 := by
    intros x hx
    have h_sum : ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ) / n = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n := by
      rw [Finset.range_eq_Ico] ; rfl
    have := sum_mobius_div_self_le (⌊x⌋₊ + 1) ; simp_all +decide [Finset.sum_range_succ']
    norm_cast at *
  rw [Asymptotics.isBigO_iff]
  use 1; filter_upwards [Filter.eventually_ge_atTop 1] with x hx; simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm]
  simpa only [← Finset.mul_sum _ _ _, abs_mul] using mul_le_of_le_one_right (abs_nonneg x) (h_abs x hx)

lemma sum_log_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, log (x / k)) =O[atTop] id := by
  have h_sum_log : ∀ x : ℝ, 1 ≤ x → |∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k)| ≤ 2 * x := by
    have h_sum_log_le_x : ∀ x : ℝ, 1 ≤ x → ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) ≤ x := by
      intro x hx
      have h_sum_log : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (k : ℝ)) ≤ Real.log (x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊) := by
        rw [← Real.log_prod]
        · norm_num [Finset.prod_div_distrib]
          erw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
        · exact fun n hn => div_ne_zero (by positivity) (Nat.cast_ne_zero.mpr <| by linarith [Finset.mem_Icc.mp hn])
      have h_exp_bound : x ^ ⌊x⌋₊ / Nat.factorial ⌊x⌋₊ ≤ Real.exp x := by
        have h_term : x ^ ⌊x⌋₊ / (⌊x⌋₊! : ℝ) ≤ ∑' k : ℕ, x ^ k / (k ! : ℝ) := by
          exact Summable.le_tsum (show Summable _ from Real.summable_pow_div_factorial x) ⌊x⌋₊ (fun _ _ => by positivity)
        simpa [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using h_term
      exact h_sum_log.trans (Real.log_le_iff_le_exp (by positivity) |>.2 h_exp_bound)
    intros x hx
    have h_sum_eq : ∑ k ∈ Finset.Iic ⌊x⌋₊, Real.log (x / k) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) := by
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
      erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num
    rw [abs_of_nonneg] <;> linarith [h_sum_log_le_x x hx, show 0 ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k) from Finset.sum_nonneg fun _ _ => Real.log_nonneg <| by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| by linarith [Finset.mem_Icc.mp ‹_›]] ; linarith [Nat.floor_le <| show 0 ≤ x by linarith, show (↑‹ℕ› : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp ‹_› |>.2]]
  rw [Asymptotics.isBigO_iff]
  exact ⟨2, Filter.eventually_atTop.mpr ⟨1, fun x hx => le_trans (h_sum_log x hx) (by norm_num [abs_of_nonneg (by linarith : 0 ≤ x)])⟩⟩

lemma R_locally_bounded (K : ℝ) (hK : 0 ≤ K) : ∃ C, ∀ y ∈ Set.Icc 0 K, |R y| ≤ C := by
  have hR_bounded : BddAbove (Set.image (fun y => |R y|) (Set.Icc 0 K)) := by
    have hR_bounded : ∀ y ∈ Set.Icc 0 K, |R y| ≤ ∑ p ∈ Iic ⌊K⌋₊, log p + K := by
      intro y hy
      simp only [R, Psi, Chebyshev.psi_eq_sum_Icc]
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · refine le_trans (sub_le_self _ hy.1) ?_
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr <| Nat.floor_mono hy.2) fun ?_ ?_ ?_ => ?_) ?_
        · exact vonMangoldt_nonneg
        · refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi => ?_) hK
          exact vonMangoldt_le_log
      · refine le_trans ?_ (le_add_of_nonneg_left ?_)
        · exact le_trans (sub_le_self _ <| Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg) hy.2
        · exact Finset.sum_nonneg fun _ _ => Real.log_natCast_nonneg _
    exact ⟨_, Set.forall_mem_image.2 hR_bounded⟩
  exact ⟨hR_bounded.choose, fun y hy => hR_bounded.choose_spec <| Set.mem_image_of_mem _ hy⟩

lemma sum_bounded_of_linear_bound {f : ℝ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (h : ∀ y, 1 ≤ y → |f y| ≤ ε * y + C) (x : ℝ) (hx : 1 ≤ x) :
  ∑ k ∈ Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * (log x + 1) + C * x := by
    have h_sum_bound : ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) + C * ⌊x⌋₊ := by
      have h_sum_bound : ∀ k ∈ Finset.Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x / k + C := by
        exact fun k hk => by simpa only [mul_div_assoc] using! h (x / k) (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| Finset.mem_Icc.mp hk |>.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), show (k : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast Finset.mem_Icc.mp hk |>.2])
      convert! Finset.sum_le_sum h_sum_bound using 1 ; norm_num [div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_comm]
    have h_harmonic : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) ≤ Real.log n + 1 := by
      intro n _hn
      have h := harmonic_le_one_add_log n
      simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        one_div, add_comm, add_left_comm, add_assoc] using h
    have h_harmonic_x :
        ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ)) ≤ Real.log x + 1 := by
      refine (h_harmonic _ <| Nat.floor_pos.mpr hx).trans ?_
      have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
        refine Real.log_le_log (Nat.cast_pos.mpr <| Nat.floor_pos.mpr hx) ?_
        exact Nat.floor_le (by positivity)
      simpa using add_le_add_right hlog 1
    have h_term1 : ε * x * (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 / (k : ℝ))) ≤ ε * x * (Real.log x + 1) := by
      refine mul_le_mul_of_nonneg_left h_harmonic_x ?_
      exact mul_nonneg hε (by positivity)
    have h_term2 : C * (⌊x⌋₊ : ℝ) ≤ C * x := by
      refine mul_le_mul_of_nonneg_left ?_ hC
      exact Nat.floor_le (by positivity)
    exact h_sum_bound.trans (add_le_add h_term1 h_term2)

lemma sum_abs_R_isLittleO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  have h_eps : ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ ε * x * Real.log x := by
    intro ε hε_pos
    obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y ≥ A, |R y| ≤ (ε / 2) * y := by
      have := R_isLittleO
      rw [Asymptotics.isLittleO_iff] at this
      norm_num at *
      exact Exists.elim (this (half_pos hε_pos)) fun A hA => ⟨Max.max A 1, by positivity, fun y hy => by simpa only [abs_of_nonneg (by linarith [le_max_right A 1] : 0 ≤ y)] using hA y (le_trans (le_max_left A 1) hy)⟩
    obtain ⟨C_A, hC_A⟩ : ∃ C_A : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ C_A := by
      exact ⟨_, fun y hy => R_locally_bounded A hA.1.le |> Classical.choose_spec |> fun h => h y hy⟩
    have h_sum_bound : ∀ x ≥ max A 2, (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) ≤ (ε / 2) * x * (Real.log x + 1) + C_A * x := by
      intros x hx
      have h_sum_bound : ∀ y ≥ 1, |R y| ≤ (ε / 2) * y + C_A := by
        intros y hy
        by_cases hyA : y ≥ A
        · exact le_add_of_le_of_nonneg (hA.right y hyA) (by
          exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩))
        · exact le_add_of_nonneg_of_le (by
          positivity) (hC_A y ⟨by
          linarith, by
            linarith⟩)
      have := sum_bounded_of_linear_bound (show 0 ≤ ε / 2 by positivity) (show 0 ≤ C_A by exact le_trans (abs_nonneg _) (hC_A 0 ⟨by norm_num, by linarith⟩)) (fun y hy => h_sum_bound y hy) x (by linarith [le_max_right A 2]) ; aesop
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x ≥ x₀, (ε / 2) * (Real.log x + 1) + C_A ≤ ε * Real.log x := by
      exact ⟨Real.exp (2 * (C_A / ε + 1)), fun x hx => by nlinarith [Real.log_exp (2 * (C_A / ε + 1)), Real.log_le_log (by positivity) hx, mul_div_cancel₀ C_A hε_pos.ne']⟩
    exact ⟨Max.max x₀ (Max.max A 2), fun x hx => le_trans (h_sum_bound x (le_trans (le_max_right _ _) hx)) (by nlinarith [hx₀ x (le_trans (le_max_left _ _) hx), le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2, Real.log_nonneg (show x ≥ 1 by linarith [le_max_right x₀ (Max.max A 2), le_max_left x₀ (Max.max A 2), le_max_right A 2, le_max_left A 2])])⟩
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h_sum_eq : ∀ x : ℝ, x ≥ 1 → (∑ k ∈ Finset.Iic ⌊x⌋₊, |R (x / k)|) = (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |R (x / k)|) := by
      intro x hx
      have h0 : (0 : ℕ) ∈ Finset.Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
      have hI : (Finset.Iic ⌊x⌋₊).erase 0 = Finset.Icc 1 ⌊x⌋₊ := by
        ext n
        simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
      rw [← Finset.sum_erase_add (Finset.Iic ⌊x⌋₊) (fun k => |R (x / k)|) h0]
      simp [hI, R, Psi, Chebyshev.psi_eq_sum_Icc]
    rw [Metric.tendsto_nhds]
    simp +zetaDelta only [gt_iff_lt, ge_iff_le, dist_zero_right, norm_div, norm_eq_abs, norm_mul,
    eventually_atTop] at *
    intro ε hε; obtain ⟨x₀, hx₀⟩ := h_eps (ε / 2) (half_pos hε) ; use Max.max x₀ 2; intro x hx; rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), abs_of_nonneg (by linarith [le_max_right x₀ 2]), abs_of_nonneg (Real.log_nonneg (by linarith [le_max_right x₀ 2]))] ; rw [div_lt_iff₀] <;> nlinarith [hx₀ x (le_trans (le_max_left x₀ 2) hx), Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x), mul_pos (by linarith [le_max_right x₀ 2] : 0 < x) (Real.log_pos (by linarith [le_max_right x₀ 2] : 1 < x)), h_sum_eq x (by linarith [le_max_right x₀ 2])]
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' (by nlinarith [Real.log_pos hx])

lemma R_linear_bound (ε : ℝ) (hε : 0 < ε) : ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y → |R y| ≤ ε * y + C := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, A ≤ y → |R y| ≤ ε * y := by
    have := R_isLittleO.def hε
    rw [Filter.eventually_atTop] at this; rcases this with ⟨A, hA⟩ ; exact ⟨Max.max A 1, by positivity, fun y hy => by simpa [abs_of_nonneg (show 0 ≤ y by linarith [le_max_right A 1])] using hA y (le_trans (le_max_left A 1) hy)⟩
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, ∀ y ∈ Set.Icc 0 A, |R y| ≤ CA := by
    exact R_locally_bounded A hA.1.le |> fun ⟨CA, hCA⟩ => ⟨CA, fun y hy => hCA y hy⟩
  exact ⟨Max.max CA 0, by positivity, fun y hy => if hy' : y ≤ A then le_trans (hCA y ⟨by linarith, by linarith⟩) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith]) else le_trans (hA.2 y (by linarith)) (by linarith [le_max_left CA 0, le_max_right CA 0, show 0 ≤ ε * y by nlinarith])⟩

lemma sum_abs_R_isLittleO' : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  apply sum_abs_R_isLittleO

lemma M_isLittleO : M =o[atTop] id := by
  have h_identity : ∀ x ≥ 1, M x * Real.log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (Real.log (x / k) - Psi (x / k)) := by
    exact fun x a => M_log_identity x a
  have h_term1 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) =O[atTop] id := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k) := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * Real.log (x / k)| ≤ Real.log (x / k) := by
        intros k hk
        have h_abs : |(μ k : ℝ)| ≤ 1 := by
          norm_num [ArithmeticFunction.moebius]
          split_ifs <;> norm_num
        by_cases hk0 : k = 0
        · rw [hk0] ; norm_num [ArithmeticFunction.map_zero, Nat.cast_zero, Real.log_zero, div_zero, abs_zero]
        · have hx_pos : 0 < x := by positivity
          have hk_pos : 0 < (k : ℝ) := by positivity
          rw [Real.log_div hx_pos.ne' hk_pos.ne']
          simp only [abs_mul, ge_iff_le]
          simp_all only [ge_iff_le, mem_Iic]
          exact le_trans (mul_le_of_le_one_left (abs_nonneg _) h_abs) (by rw [abs_of_nonneg] ; exact sub_nonneg_of_le <| Real.log_le_log hk_pos (Nat.cast_le.mpr hk |>.trans (Nat.floor_le hx_pos.le)))
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_log : (fun x => ∑ k ∈ Iic ⌊x⌋₊, Real.log (x / k)) =O[atTop] id := by
      convert sum_log_div_isBigO using 1
    rw [Asymptotics.isBigO_iff] at *
    exact ⟨h_sum_log.choose, by filter_upwards [h_sum_log.choose_spec, Filter.eventually_ge_atTop 1] with x hx₁ hx₂ using le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)⟩
  have h_term2 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
    convert sum_mobius_div_isBigO using 1
  have h_term3 : (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) =o[atTop] (fun x => x * Real.log x) := by
    have h_abs : ∀ x ≥ 1, |∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)| ≤ ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)| := by
      intros x hx
      have h_abs : ∀ k ∈ Iic ⌊x⌋₊, |(μ k : ℝ) * R (x / k)| ≤ |R (x / k)| := by
        norm_num [abs_mul]
        intro k hk; exact mul_le_of_le_one_left (abs_nonneg _) (mod_cast by exact abs_moebius_le_one)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_abs)
    have h_sum_abs_R : (fun x => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * Real.log x) := by
      exact sum_abs_R_isLittleO
    rw [Asymptotics.isLittleO_iff] at *
    intro c hc; filter_upwards [h_sum_abs_R hc, Filter.eventually_ge_atTop 1] with x hx₁ hx₂; exact le_trans (h_abs x hx₂) (le_trans (le_abs_self _) hx₁)
  have h_combined : (fun x => M x * Real.log x) =o[atTop] (fun x => x * Real.log x) := by
    have h_combined : (fun x => M x * Real.log x) = (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Real.log (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) - (fun x => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * R (x / k)) := by
      ext x; by_cases hx : 1 ≤ x <;> simp_all +decide only [ge_iff_le, mul_sub, sum_sub_distrib, not_le, Pi.sub_apply]
      · simp +decide [sub_sub, mul_sub, Finset.sum_sub_distrib, Psi, R]
      · unfold M R; norm_num [Nat.floor_eq_zero.mpr hx]
        norm_num [Finset.Iic_eq_Icc]
    rw [h_combined]
    refine Asymptotics.IsLittleO.sub ?_ h_term3
    refine Asymptotics.IsLittleO.sub ?_ ?_
    · refine h_term1.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> norm_num at hx⟩
    · refine h_term2.trans_isLittleO ?_
      rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
      · norm_num [← div_div]
        exact le_trans (Filter.Tendsto.div_atTop (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (Real.tendsto_log_atTop)) (by norm_num)
      · exact ⟨2, by rintro x hx (rfl | rfl | rfl) <;> linarith⟩
  rw [Asymptotics.isLittleO_iff_tendsto'] at *
  · refine h_combined.congr' (by filter_upwards [Filter.eventually_gt_atTop 1] with x hx using by rw [mul_div_mul_right _ _ (ne_of_gt <| Real.log_pos hx)] ; rfl)
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using absurd hx' <| ne_of_gt <| mul_pos (by positivity) <| Real.log_pos hx
  · filter_upwards [Filter.eventually_gt_atTop 1] with x hx hx' using by nlinarith [Real.log_pos hx]
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'

lemma M_isLittleO' : M =o[atTop] id := by
  exact M_isLittleO



theorem mu_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, μ n) =o[atTop] fun x ↦ x := by
  have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
    have h_bound : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
      have h_sum : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        have h_moebius_sum : (fun x : ℝ => ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x : ℝ => x) := by
          convert! M_isLittleO using 1
        simpa only [Finset.range_eq_Ico] using! h_moebius_sum
      have h_mu_floor : (fun x : ℝ => (μ ⌊x⌋₊ : ℝ)) =o[atTop] (fun x : ℝ => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
        · refine squeeze_zero_norm (a := fun x : ℝ => 1 / |x|) ?_ ?_
          · intro x; norm_num [abs_div]
            exact mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)
          · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
        · exact ⟨1, by intros; linarith⟩
      simpa [Finset.sum_range_succ] using h_sum.sub h_mu_floor
    convert h_bound using 1
  rw [Asymptotics.isLittleO_iff] at *
  simp_all +decide [Norm.norm]


lemma lambda_eq_sum_sq_dvd_mu (n : ℕ) (hn : n ≠ 0) :
    ((-1 : ℝ) ^ (Ω n)) = ∑ d ∈ (Icc 1 n).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
      set a : ℕ → ℕ := fun p => Nat.factorization n p with ha
      have hn_factor : n = ∏ p ∈ Nat.primeFactors n, p ^ a p := by
        exact Eq.symm ( Nat.prod_factorization_pow_eq_self hn );
      have h_sum_factor : (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (μ (n / d^2) : ℝ)) = (∏ p ∈ Nat.primeFactors n, (∑ d ∈ Finset.range (a p / 2 + 1), (μ (p^(a p - 2 * d)) : ℝ))) := by
        have h_mult : ∀ {m n : ℕ}, Nat.gcd m n = 1 → (∑ d ∈ Finset.filter (fun d => d^2 ∣ m * n) (Finset.Icc 1 (m * n)), (μ (m * n / d^2) : ℝ)) = (∑ d ∈ Finset.filter (fun d => d^2 ∣ m) (Finset.Icc 1 m), (μ (m / d^2) : ℝ)) * (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (μ (n / d^2) : ℝ)) := by
          intros m n h_coprime
          have h_filter : Finset.filter (fun d => d^2 ∣ m * n) (Finset.Icc 1 (m * n)) = Finset.image (fun (d : ℕ × ℕ) => d.1 * d.2) (Finset.filter (fun d => d^2 ∣ m) (Finset.Icc 1 m) ×ˢ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n)) := by
            ext d
            simp only [mem_filter, mem_Icc, mem_image, mem_product, Prod.exists]
            constructor
            · intro h
              obtain ⟨d1, d2, hd1, hd2, hd⟩ : ∃ d1 d2 : ℕ, d1^2 ∣ m ∧ d2^2 ∣ n ∧ d = d1 * d2 := by
                have h_factor : d^2 ∣ m * n → ∃ d1 d2 : ℕ, d1^2 ∣ m ∧ d2^2 ∣ n ∧ d = d1 * d2 := by
                  intro h_div
                  obtain ⟨d1, d2, hd1, hd2, hd⟩ : ∃ d1 d2 : ℕ, d1 ∣ m ∧ d2 ∣ n ∧ d = d1 * d2 := by
                    exact Exists.imp ( by tauto ) ( Nat.dvd_mul.mp ( dvd_of_mul_left_dvd h_div ) );
                  refine ⟨ d1, d2, ?_, ?_, hd ⟩
                  · apply Nat.Coprime.dvd_of_dvd_mul_right
                    · exact Nat.Coprime.pow_left 2 (Nat.Coprime.coprime_dvd_left hd1 h_coprime)
                    · exact dvd_trans (pow_dvd_pow_of_dvd (hd.symm ▸ dvd_mul_right _ _) 2) h_div
                  · subst hd
                    apply Nat.Coprime.dvd_of_dvd_mul_left
                    · exact Nat.Coprime.pow_left _ (Nat.Coprime.symm <| Nat.Coprime.coprime_dvd_right hd2 h_coprime)
                    · exact dvd_trans ⟨d1 ^ 2, by ring⟩ h_div
                exact h_factor h.2;
              refine ⟨ d1, d2, ?_, ?_ ⟩ <;> norm_num [ hd ]
              exact ⟨ ⟨ ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by rintro rfl; linarith ) ) ( dvd_of_mul_left_dvd hd1 ) ⟩, hd1 ⟩, ⟨ Nat.pos_of_ne_zero ( by rintro rfl; linarith ), Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by rintro rfl; linarith ) ) ( dvd_of_mul_left_dvd hd2 ) ⟩, hd2 ⟩;
            · intro h
              rcases h with ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃ ⟩ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith, by nlinarith ⟩, by convert Nat.mul_dvd_mul ha₃ hb₃ using 1 ; ring ⟩ ;
          rw [ h_filter, Finset.sum_image ];
          · rw [ Finset.sum_product, Finset.sum_mul ];
            simp +decide only [Finset.mul_sum _ _ _];
            refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
            rw [show m * n / (x * y) ^ 2 = (m / x ^ 2) * (n / y ^ 2) by
              have hx' : x ^ 2 ∣ m := by
                simpa only [sq] using (Finset.mem_filter.mp hx).2
              have hy' : y ^ 2 ∣ n := by
                simpa only [sq] using (Finset.mem_filter.mp hy).2
              simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
                (Nat.div_mul_div_comm (a := m) (b := x ^ 2) (c := n) (d := y ^ 2) hx' hy').symm]
            norm_cast
            apply ArithmeticFunction.IsMultiplicative.map_mul_of_coprime;
            · exact ArithmeticFunction.isMultiplicative_moebius;
            · exact Nat.Coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd <| Finset.mem_filter.mp hx |>.2 ) <| Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd <| Finset.mem_filter.mp hy |>.2 ) h_coprime;
          · intros x hx y hy; simp +contextual only [ne_eq, coe_product, coe_filter, mem_Icc, Set.mem_prod, Set.mem_ofPred_eq] at *;
            intro hxy
            have h_eq1 : x.1 = y.1 := by
              exact Nat.dvd_antisymm ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( x.1 ) ( y.2 ) from Nat.Coprime.coprime_dvd_left ( dvd_of_mul_left_dvd hx.1.2 ) <| Nat.Coprime.coprime_dvd_right ( dvd_of_mul_left_dvd hy.2.2 ) h_coprime ) <| hxy.symm ▸ dvd_mul_right _ _ ) ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( y.1 ) ( x.2 ) from Nat.Coprime.coprime_dvd_left ( dvd_of_mul_left_dvd hy.1.2 ) <| Nat.Coprime.coprime_dvd_right ( dvd_of_mul_left_dvd hx.2.2 ) h_coprime ) <| hxy.symm ▸ dvd_mul_right _ _ )
            have h_eq2 : x.2 = y.2 := by
              nlinarith
            exact Prod.ext h_eq1 h_eq2;
        have h_prod : (∑ d ∈ Finset.filter (fun d => d^2 ∣ n) (Finset.Icc 1 n), (μ (n / d^2) : ℝ)) = (∏ p ∈ Nat.primeFactors n, (∑ d ∈ Finset.filter (fun d => d^2 ∣ p^(a p)) (Finset.Icc 1 (p^(a p))), (μ (p^(a p) / d^2) : ℝ))) := by
          have h_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → (∑ d ∈ Finset.filter (fun d => d^2 ∣ ∏ p ∈ S, p^(a p)) (Finset.Icc 1 (∏ p ∈ S, p^(a p))), (μ ((∏ p ∈ S, p^(a p)) / d^2) : ℝ)) = (∏ p ∈ S, (∑ d ∈ Finset.filter (fun d => d^2 ∣ p^(a p)) (Finset.Icc 1 (p^(a p))), (μ (p^(a p) / d^2) : ℝ))) := by
            intro S hS; induction S using Finset.induction <;> norm_num at *;
            · norm_num [ Finset.sum_filter ];
            · rw [ Finset.prod_insert ‹_›, h_mult ];
              · rw [ Finset.prod_insert ‹_›, ‹ ( ∀ p ∈ _, Nat.Prime p ) → ∑ d ∈ Finset.Icc 1 ( ∏ p ∈ _, p ^ a p ) with d ^ 2 ∣ ∏ p ∈ _, p ^ a p, ( μ ( ( ∏ p ∈ _, p ^ a p ) / d ^ 2 ) : ℝ ) = ∏ p ∈ _, ∑ d ∈ Finset.Icc 1 ( p ^ a p ) with d ^ 2 ∣ p ^ a p, ( μ ( p ^ a p / d ^ 2 ) : ℝ ) › hS.2 ];
              · exact Nat.Coprime.prod_right fun p hp => Nat.coprime_pow_primes _ _ hS.1 ( hS.2 p hp ) <| by rintro rfl; exact ‹¬_› hp;
          convert h_prod fun p hp => Nat.prime_of_mem_primeFactors hp;
        have h_divisors : ∀ p ∈ Nat.primeFactors n, Finset.filter (fun d => d^2 ∣ p^(a p)) (Finset.Icc 1 (p^(a p))) = Finset.image (fun k => p^k) (Finset.Icc 0 (a p / 2)) := by
          intro p hp
          ext d
          simp only [mem_filter, mem_Icc, mem_image, _root_.zero_le, true_and]
          constructor;
          · intro hd;
            have : d ∣ p ^ a p := dvd_of_mul_left_dvd hd.2; ( rw [ Nat.dvd_prime_pow ( Nat.prime_of_mem_primeFactors hp ) ] at this; obtain ⟨ k, hk ⟩ := this; use k; simp +decide only [ hk, and_true ] at hd ⊢; );
            rw [ Nat.le_div_iff_mul_le zero_lt_two ] ; rw [ ← pow_mul ] at hd ; exact Nat.le_of_not_lt fun h => absurd ( Nat.le_of_dvd ( pow_pos ( Nat.pos_of_mem_primeFactors hp ) _ ) hd.2 ) ( by exact not_le_of_gt ( pow_lt_pow_right₀ ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) ( by linarith ) ) ) ;
          · rintro ⟨ k, hk₁, rfl ⟩ ; exact ⟨ ⟨ Nat.one_le_pow _ _ ( Nat.pos_of_mem_primeFactors hp ), Nat.pow_le_pow_right ( Nat.pos_of_mem_primeFactors hp ) ( by omega ) ⟩, by rw [ ← pow_mul ] ; exact pow_dvd_pow _ ( by omega ) ⟩ ;
        rw [ h_prod, Finset.prod_congr rfl ];
        intro p hp; rw [ show ( Finset.filter ( fun d => d ^ 2 ∣ p ^ a p ) ( Finset.Icc 1 ( p ^ a p ) ) ) = Finset.image ( fun k => p ^ k ) ( Finset.Icc 0 ( a p / 2 ) ) from h_divisors p hp ] ; rw [ Finset.sum_image ] <;> norm_num [ pow_mul', Nat.div_eq_of_lt ] ;
        · rw [Finset.range_eq_Ico, ← Order.succ_eq_add_one, Finset.Ico_succ_right_eq_Icc]
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [← pow_mul', Nat.mul_comm]
          have hx_pos : 0 < p ^ (x * 2) := pow_pos (Nat.pos_of_mem_primeFactors hp) _
          have hx_eq : p ^ a p = p ^ (a p - x * 2) * p ^ (x * 2) := by
            rw [← pow_add, Nat.sub_add_cancel (by linarith [Finset.mem_Icc.mp hx, Nat.div_mul_le_self (a p) 2])]
          rw [Nat.div_eq_of_eq_mul_left hx_pos hx_eq]
        · exact fun x hx y hy hxy => Nat.pow_right_injective ( Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ) hxy;
      have h_inner_sum : ∀ p ∈ Nat.primeFactors n, (∑ d ∈ Finset.range (a p / 2 + 1), (μ (p^(a p - 2 * d)) : ℝ)) = (-1 : ℝ) ^ (a p) := by
        intro p hp
        have h_inner_sum_cases : ∀ d ∈ Finset.range (a p / 2 + 1), (μ (p^(a p - 2 * d)) : ℝ) = if a p - 2 * d = 0 then 1 else if a p - 2 * d = 1 then -1 else 0 := by
          simp +zetaDelta only [ne_eq, mem_primeFactors, mem_range] at *
          intro d hd
          rcases k : (n.factorization p - 2 * d) with (_ | _ | k)
          · simp +decide only [pow_zero, isUnit_iff_eq_one, IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg,
              cardFactors_one, Int.cast_one, ↓reduceIte]
          · simp +decide only [zero_add, pow_one, ↓reduceIte]
            norm_num [hp.1, ArithmeticFunction.moebius]
            exact hp.1.squarefree
          · simp +decide only [Nat.add_eq_zero_iff, and_false, and_self, ↓reduceIte, Nat.add_eq_right, Int.cast_eq_zero]
            exact
              ArithmeticFunction.moebius_eq_zero_of_not_squarefree
                (by rw [Nat.squarefree_pow_iff] <;> norm_num [hp.1.ne_one, hp.1.ne_zero])
        rw [ Finset.sum_congr rfl h_inner_sum_cases ] ; norm_num [ Finset.sum_ite ] ; rcases Nat.even_or_odd' ( a p ) with ⟨ k, hk | hk ⟩ <;> norm_num [ hk, pow_add, pow_mul ]
        · ring_nf
          norm_num [ show ∀ x : ℕ, k * 2 - x * 2 = 0 ↔ x ≥ k by intro x; exact ⟨ fun hx => by contrapose! hx; exact Nat.ne_of_gt <| Nat.sub_pos_of_lt <| by linarith, fun hx => Nat.sub_eq_zero_of_le <| by linarith ⟩ ];
          have h_first :
              Finset.filter (fun x => k ≤ x) (Finset.range (k + 1)) = {k} := by
            ext x
            simp
            omega
          have h_second :
              Finset.filter (fun x => k * 2 - x * 2 = 1)
                (Finset.filter (fun x => ¬2 * k - 2 * x = 0) (Finset.range (k + 1))) = ∅ := by
            ext x
            simp
            omega
          rw [h_first, h_second]
          norm_num
        · ring_nf
          norm_num [ Nat.add_div ];
          rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
          · rw [ Finset.card_eq_one ] ; use k ; ext x ; norm_num ; omega;
          · intros; omega;
      rw [ h_sum_factor, Finset.prod_congr rfl h_inner_sum ];
      rw [ Finset.prod_pow_eq_pow_sum ];
      rw [ ArithmeticFunction.cardFactors_apply ];
      rw [ ← Multiset.coe_card, ← Multiset.toFinset_sum_count_eq ];
      norm_num +zetaDelta

lemma sum_lambda_eq_sum_mu_div_sq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((-1 : ℝ) ^ (Ω n)) =
    ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ) := by
      have h_sum_rewrite : ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Ω n) = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
        have h_sum_rewrite : ∀ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Ω n) = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
          intro n hn
          have h_lambda_eq : ((-1 : ℝ) ^ (Ω n)) = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
            convert lambda_eq_sum_sq_dvd_mu n ( by linarith [ Finset.mem_Icc.mp hn ] ) using 1;
          rw [ h_lambda_eq, Finset.sum_subset ];
          · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2, Finset.mem_Icc.mp hn |>.2 ] ⟩, Finset.mem_filter.mp hx |>.2 ⟩;
          · simp +zetaDelta only [mem_Icc, mem_filter, not_and, and_imp, Int.cast_eq_zero] at *
            exact fun x hx₁ hx₂ hx₃ hx₄ => False.elim <| hx₄ hx₁ ( by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₃ ] ) hx₃;
        exact Finset.sum_congr rfl h_sum_rewrite;
      rw [ h_sum_rewrite, Finset.sum_sigma' ];
      have h_reindex : ∑ x ∈ (Finset.Icc 1 N).sigma fun (n : ℕ) => {d ∈ Finset.Icc 1 N | d ^ 2 ∣ n}, (μ (x.fst / x.snd ^ 2) : ℝ) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d ^ 2), (μ k : ℝ) := by
        have : Finset.filter (fun x => x.snd ^ 2 ∣ x.fst) (Finset.Icc 1 N ×ˢ Finset.Icc 1 N) = Finset.biUnion (Finset.Icc 1 (Nat.sqrt N)) (fun d => Finset.image (fun k => (d ^ 2 * k, d)) (Finset.Icc 1 (N / d ^ 2))) := by
          ext ⟨n, d⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
          constructor
          · intro ⟨⟨⟨hn1, hn2⟩, hd1, hd2⟩, hdiv⟩
            exact ⟨d, ⟨hd1, by rw [Nat.le_sqrt]; nlinarith [Nat.le_of_dvd (by linarith) hdiv]⟩, n / d ^ 2, ⟨Nat.div_pos (Nat.le_of_dvd (by linarith) hdiv) (by nlinarith), Nat.div_le_div_right hn2⟩, Nat.mul_div_cancel' hdiv, rfl⟩
          · rintro ⟨a, ⟨ha₁, ha₂⟩, b, ⟨hb₁, hb₂⟩, hn, hd⟩
            rw [← hn, ← hd]
            exact ⟨⟨⟨by nlinarith, by nlinarith [Nat.div_mul_le_self N (a ^ 2)]⟩, ha₁, by nlinarith [Nat.sqrt_le N]⟩, dvd_mul_right _ _⟩
        rw [ Finset.sum_sigma' ];
        apply Finset.sum_bij (fun x _ => ⟨x.snd, x.fst / x.snd ^ 2⟩);
        · simp_all +decide only [Finset.ext_iff, mem_filter, mem_product, mem_Icc, mem_biUnion, mem_image, Prod.forall,
            Prod.mk.injEq, ↓existsAndEq, and_true, exists_and_left, mem_sigma, true_and, and_imp]
          exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ by nlinarith [ Nat.le_of_dvd ( by linarith ) hx₅, Nat.lt_succ_sqrt N ], Nat.div_pos ( Nat.le_of_dvd ( by linarith ) hx₅ ) ( by positivity ), Nat.div_le_div_right hx₂ ⟩;
        · simp +contextual [ Finset.mem_sigma, Finset.mem_filter ];
          aesop;
        · simp +zetaDelta only [mem_sigma, mem_Icc, mem_filter, exists_prop, Sigma.exists, and_imp] at *
          exact fun b hb₁ hb₂ hb₃ hb₄ => ⟨ b.fst ^ 2 * b.snd, b.fst, ⟨ ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self N ( b.fst ^ 2 ) ] ⟩, ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self N ( b.fst ^ 2 ) ] ⟩, by norm_num ⟩, by simp +decide [ Nat.mul_div_cancel_left _ ( by nlinarith : 0 < b.fst ^ 2 ) ] ⟩;
        · aesop;
      convert h_reindex using 1


lemma sum_mu_div_sq_isLittleO : (fun N : ℕ ↦ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ)) =o[atTop] (fun N ↦ (N : ℝ)) := by
  have h_sum_rewrite : ∀ N : ℕ, (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ))) = (∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (M (N / d^2) : ℝ)) := by
    intro N
    simp only [M]
    refine Finset.sum_congr rfl ?_
    intro x hx
    erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
    rw [ show ⌊ ( N : ℝ ) / x ^ 2⌋₊ = N / x ^ 2 from Nat.floor_eq_iff ( by positivity ) |>.2 ⟨ by rw [ le_div_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_mul_le_self N ( x ^ 2 ) ], by rw [ div_lt_iff₀ ( by norm_cast; nlinarith [ Finset.mem_Icc.mp hx ] ) ] ; norm_cast; linarith [ Nat.div_add_mod N ( x ^ 2 ), Nat.mod_lt N ( show x ^ 2 > 0 by nlinarith [ Finset.mem_Icc.mp hx ] ) ] ⟩ ] ; erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ] ;
  have h_bound : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d ∈ Finset.Icc 1 (Nat.sqrt N), |M (N / d^2)| ≤ ε * (N / d^2) + N₀ := by
    have h_bound : ∀ ε > 0, ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |M x| ≤ ε * x + C := by
      have h_bound : ∀ ε > 0, ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |M x| ≤ ε * x + C := by
        intro ε hε
        have := M_isLittleO'
        rw [ Asymptotics.isLittleO_iff ] at this;
        norm_num +zetaDelta at *;
        obtain ⟨ a, ha ⟩ := this hε;
        obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ Set.Icc 1 a, |M x| ≤ C := by
          have h_bounded : BddAbove (Set.image (fun x => |M x|) (Set.Icc 1 a)) := by
            have h_bounded : BddAbove (Set.image (fun x => |∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℝ)|) (Set.Icc 1 a)) := by
              have h_finite : Set.Finite (Set.image (fun x => ⌊x⌋₊) (Set.Icc 1 a)) := by
                exact Set.finite_iff_bddAbove.mpr ⟨ ⌊a⌋₊, Set.forall_mem_image.mpr fun x hx => Nat.floor_mono hx.2 ⟩
              have h_bounded : BddAbove (Set.image (fun n : ℕ => |∑ k ∈ Finset.Iic n, (μ k : ℝ)|) (Set.image (fun x => ⌊x⌋₊) (Set.Icc 1 a))) := by
                exact Set.Finite.bddAbove <| h_finite.image _;
              exact ⟨ h_bounded.choose, Set.forall_mem_image.2 fun x hx => h_bounded.choose_spec <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx ⟩;
            convert! h_bounded using 1;
          exact ⟨ h_bounded.choose, fun x hx => h_bounded.choose_spec ⟨ x, hx, rfl ⟩ ⟩;
        exact ⟨ Max.max C 0, fun x hx => if hx' : x ≤ a then le_trans ( hC x ⟨ hx, hx' ⟩ ) ( le_max_left _ _ ) |> le_trans <| le_add_of_nonneg_left <| by positivity else le_trans ( ha x <| le_of_not_ge hx' ) <| by rw [ abs_of_nonneg <| by linarith ] ; exact le_add_of_nonneg_right <| by positivity ⟩;
      assumption;
    intro ε hε
    obtain ⟨C, hC⟩ := h_bound ε hε
    refine ⟨⌈C⌉₊ + 1, ?_⟩
    intro N hN d hd
    specialize hC (N / d ^ 2)
    rcases eq_or_ne d 0 with rfl | hd0
    · simp_all +decide only [gt_iff_lt, ge_iff_le, mem_Icc, _root_.zero_le, and_true]
    · simp_all +decide only [gt_iff_lt, ge_iff_le, mem_Icc, ne_eq, cast_add, cast_one]
      exact
        le_trans
            (hC <|
              by
                rw [le_div_iff₀ <| by positivity]
                nlinarith [show (d : ℝ) ^ 2 ≤ N by norm_cast; nlinarith [Nat.sqrt_le N]])
          (by linarith [Nat.le_ceil C])
  have h_sum_bound : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |∑ d ∈ Finset.Icc 1 (Nat.sqrt N), M (N / d^2)| ≤ ε * N * (∑' k : ℕ, (1 : ℝ) / (k^2)) + N₀ * Nat.sqrt N := by
    intros ε hε_pos
    obtain ⟨N₀, hN₀⟩ := h_bound ε hε_pos
    use N₀
    intro N hN
    have h_sum_bound : |∑ d ∈ Finset.Icc 1 (Nat.sqrt N), M (N / d^2)| ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), (ε * (N / d^2) + N₀) := by
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun x hx => hN₀ N hN x hx );
    refine le_trans h_sum_bound ?_;
    norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    rw [ ← Finset.mul_sum _ _ _, ← Finset.mul_sum _ _ _ ];
    exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum ( Finset.Icc 1 N.sqrt ) ( fun _ _ => by positivity ) ( by simp ) ) ( Nat.cast_nonneg _ ) ) hε_pos.le;
  rw [ Asymptotics.isLittleO_iff ];
  intro c hc
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε * (∑' k : ℕ, (1 : ℝ) / (k^2)) < c / 2 := by
    exact ⟨ ( c / 2 ) / ( ∑' k : ℕ, 1 / ( k : ℝ ) ^ 2 + 1 ), div_pos ( half_pos hc ) ( add_pos_of_nonneg_of_pos ( tsum_nonneg fun _ => by positivity ) zero_lt_one ), by rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ show 0 ≤ ∑' k : ℕ, 1 / ( k : ℝ ) ^ 2 from tsum_nonneg fun _ => by positivity ] ⟩;
  obtain ⟨ N₀, hN₀ ⟩ := h_sum_bound ε hε_pos;
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N ≥ N₁, N₀ * Nat.sqrt N ≤ (c / 2) * N := by
    have h_sqrt_growth : ∃ N₁ : ℕ, ∀ N ≥ N₁, (N₀ : ℝ) * Real.sqrt N ≤ (c / 2) * N := by
      have h_sqrt_bound : Filter.Tendsto (fun N : ℕ => (N₀ : ℝ) * Real.sqrt N / N) Filter.atTop (nhds 0) := by
        simpa [ mul_div_assoc, Real.sqrt_div_self ] using tendsto_const_nhds.mul ( tendsto_inv_atTop_nhds_zero_nat.sqrt )
      exact Filter.eventually_atTop.mp ( h_sqrt_bound.eventually ( gt_mem_nhds <| show 0 < c / 2 by positivity ) ) |> fun ⟨ N₁, hN₁ ⟩ ↦ ⟨ N₁ + 1, fun N hN ↦ by have := hN₁ N ( by linarith ) ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ show ( N : ℝ ) ≥ N₁ + 1 by exact_mod_cast hN ] ⟩;
    exact ⟨ h_sqrt_growth.choose, fun N hN => le_trans ( mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _ ) <| Nat.cast_nonneg _ ) <| h_sqrt_growth.choose_spec N hN ⟩;
  filter_upwards [ Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop N₁ ] with N hN₀' hN₁' using by rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; rw [ h_sum_rewrite ] ; exact le_trans ( hN₀ _ hN₀' ) ( by nlinarith [ hN₁ _ hN₁', show ( N : ℝ ) ≥ 0 by positivity ] ) ;



theorem lambda_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (-1)^(Ω n)) =o[atTop] fun x ↦ x := by
  have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
    have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
      have h_lambda_pnt : (fun N : ℕ => ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
        exact sum_mu_div_sq_isLittleO
      convert h_lambda_pnt using 2;
      convert sum_lambda_eq_sum_mu_div_sq _;
      exact Eq.symm cardFactors_eq_sum_factorization
    have h_lambda_pnt : (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) := by
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
      · convert h_lambda_pnt.add ( show Filter.Tendsto ( fun x : ℕ => ( 1 : ℝ ) / x ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) using 2 <;> norm_num [ Finset.sum_Ico_eq_sum_range ];
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ; ring_nf;
      · exact ⟨ 1, by aesop ⟩;
      · exact ⟨ 1, by aesop ⟩;
    simp_all +decide only [Finset.sum_range_succ]
    have := h_lambda_pnt.sub ( show ( fun N : ℕ => ( -1 : ℝ ) ^ N.factorization.sum fun p k => k ) =o[Filter.atTop] fun N : ℕ => ( N : ℝ ) from ?_ );
    · aesop;
    · rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
      · exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa using tendsto_inv_atTop_nhds_zero_nat );
      · exact ⟨ 1, fun n hn => by positivity ⟩;
  have h_floor : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (-1 : ℝ) ^ (Nat.factorization n).sum (fun p k => k)) =o[Filter.atTop] (fun x : ℝ => (⌊x⌋₊ : ℝ)) := by
    rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
    · exact h_lambda_pnt.comp <| tendsto_nat_floor_atTop;
    · exact ⟨ 1, by aesop ⟩;
    · exact ⟨ 1, by intros; linarith ⟩;
  rw [ Asymptotics.isLittleO_iff ] at *;
  intro c hc
  filter_upwards [h_floor (half_pos hc), Filter.eventually_gt_atTop 1] with x hx₁ hx₂
  refine le_trans ?_ (le_trans hx₁ ?_)
  · norm_num [ Norm.norm ];
    convert le_rfl using 2;
    congr! 2;
    exact Eq.symm cardFactors_eq_sum_factorization
  · norm_num [ abs_of_nonneg, Nat.floor_le, hx₂.le ];
    rw [ abs_of_nonneg ( by positivity ) ] ; nlinarith [ Nat.floor_le ( by positivity : 0 ≤ x ) ]


lemma sum_mobius_floor (x : ℝ) (hx : 1 ≤ x) : ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = 1 := by
  classical
  have h := sum_mobius_mul_floor x hx
  have h0 : (0 : ℕ) ∈ Iic ⌊x⌋₊ := by simp [Finset.mem_Iic]
  have hI : (Iic ⌊x⌋₊).erase 0 = Icc 1 ⌊x⌋₊ := by
    ext n
    simp [Finset.mem_Iic, Finset.mem_Icc, Nat.one_le_iff_ne_zero, and_comm]
  rw [← Finset.sum_erase_add (Iic ⌊x⌋₊) (fun n => (μ n : ℝ) * (⌊x / n⌋ : ℝ)) h0] at h
  simpa [hI] using h

lemma sum_mobius_floor_tail_isLittleO (K : ℕ) (hK : 0 < K) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)) =o[atTop] fun x => x := by
      have h_group : ∀ x : ℝ, x ≥ 1 → ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, k * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) := by
        intro x hx
        have h_group : ∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = ∑ k ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ) * k := by
          have h_group : Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊ = Finset.biUnion (Finset.Ico 1 K) (fun k => Finset.Ioc (⌊x / (k + 1 : ℝ)⌋₊) (⌊x / (k : ℝ)⌋₊)) := by
            ext n
            simp only [mem_Ioc, mem_biUnion, mem_Ico]
            constructor
            · intro hn
              refine ⟨⌊x / n⌋₊, ?_, ?_, ?_⟩
              all_goals generalize_proofs at *
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [show (n : ℝ) ≥ 1 by norm_cast; linarith]
                exact ⟨by rw [le_div_iff₀ (Nat.cast_pos.mpr <| by linarith)] ; nlinarith [Nat.floor_le (show 0 ≤ x by linarith), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2], by rw [Nat.floor_lt (by positivity)] at *; rw [div_lt_iff₀ (by positivity)] at *; norm_num at *; linarith⟩
              · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;> try linarith [Nat.lt_floor_add_one (x / n)]
                nlinarith [Nat.lt_floor_add_one (x / n), show (n : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (n : ℝ) ≠ 0 by norm_cast; linarith)]
              · refine Nat.le_floor ?_
                rw [le_div_iff₀] <;> norm_num
                · exact le_trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)) (by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr <| by linarith)])
                · exact Nat.floor_pos.mpr (by rw [le_div_iff₀ (Nat.cast_pos.mpr <| pos_of_gt hn.1)] ; nlinarith [Nat.floor_le (show 0 ≤ x by positivity), Nat.lt_floor_add_one x, show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2, div_mul_cancel₀ x (show (K : ℝ) ≠ 0 by positivity)])
            · field_simp
              rintro ⟨a, ⟨ha₁, ha₂⟩, ha₃, ha₄⟩
              refine ⟨lt_of_le_of_lt ?_ ha₃, ha₄.trans ?_⟩
              · gcongr ; norm_cast
              · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast ha₁
          rw [h_group, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun n hn => ?_
            simp +zetaDelta only [ge_iff_le, mem_Ico, mem_Ioc, mul_eq_mul_left_iff, Int.cast_eq_zero] at *
            rw [Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity)] at *
            exact Or.inl <| mod_cast Int.floor_eq_iff.mpr ⟨by rw [le_div_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)], by rw [div_lt_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hn; linarith [show x / (k + 1 : ℝ) > 0 by positivity]] ; norm_num; nlinarith [show (k : ℝ) ≥ 1 by norm_cast; linarith, div_mul_cancel₀ x (show (k : ℝ) ≠ 0 by norm_cast; linarith), div_mul_cancel₀ x (show (k + 1 : ℝ) ≠ 0 by positivity)]⟩
          · intros k hk l hl hkl; simp_all +decide [Finset.disjoint_left]
            field_simp
            intro a ha₁ ha₂ ha₃; contrapose! hkl
            rw [Nat.le_floor_iff (by positivity), Nat.floor_lt (by positivity)] at *
            rw [div_lt_iff₀ (by positivity), le_div_iff₀ (by norm_cast; linarith)] at *
            exact Nat.le_antisymm (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith }) (Nat.le_of_lt_succ <| by { rw [← @Nat.cast_lt ℝ] ; push_cast; nlinarith })
        simpa only [mul_comm, Finset.mul_sum _ _ _] using h_group
      have h_M_x_over_k : ∀ k : ℕ, 1 ≤ k → k < K → (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
        have h_M : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range ⌊x⌋₊, (μ n : ℝ)) =o[atTop] (fun x => x) := by
            refine Asymptotics.IsLittleO.of_norm_left ?_
            simpa only [← Int.norm_cast_real, Int.cast_sum] using mu_pnt.norm_left
          have h_M : (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ)) =o[atTop] (fun x => x) := by
            simp_all +decide only [ge_iff_le, Finset.sum_range_succ]
            refine h_M.add ?_
            rw [Asymptotics.isLittleO_iff_tendsto] <;> norm_num
            refine squeeze_zero_norm' (a := fun x : ℝ => 1 / |x|) ?_ ?_
            · norm_num [abs_div]
              exact ⟨1, fun x hx => mul_le_of_le_one_left (by positivity) (mod_cast by exact abs_moebius_le_one)⟩
            · exact tendsto_const_nhds.div_atTop (tendsto_norm_atTop_atTop)
          convert! h_M.sub (show (fun x : ℝ => (μ 0 : ℝ)) =o[Filter.atTop] fun x : ℝ => x from ?_) using 2 <;> norm_num [Finset.sum_range_succ']
          erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
        intros k hk_pos hk_lt_K
        have h_M_x_over_k : (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) = (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) - (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x / (k + 1 : ℝ)⌋₊, (μ n : ℝ)) := by
          ext x
          simp only [Pi.sub_apply]
          rw [eq_sub_iff_add_eq']
          simp only [show Finset.Icc (1 : ℕ) (⌊x / (↑k + 1)⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / (↑k + 1)⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / (↑k + 1)⌋₊)),
            show Finset.Icc (1 : ℕ) (⌊x / ↑k⌋₊) = Finset.Ioc (0 : ℕ) (⌊x / ↑k⌋₊) by
              simpa using (Finset.Icc_add_one_left_eq_Ioc (a := (0 : ℕ)) (b := ⌊x / ↑k⌋₊))]
          rw [Finset.sum_Ioc_consecutive] <;> norm_num

          by_cases hx : 0 ≤ x <;> simp_all +decide only [ge_iff_le, floor_div_natCast, not_le]
          · rw [Nat.le_div_iff_mul_le (by positivity)]
            exact Nat.le_floor <| by push_cast; nlinarith [Nat.floor_le (show 0 ≤ x / (k + 1) by positivity), Nat.lt_floor_add_one (x / (k + 1)), mul_div_cancel₀ x (by positivity : (k + 1 : ℝ) ≠ 0)]
          · rw [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx.le (by positivity)), Nat.floor_of_nonpos hx.le] ; norm_num
        rw [h_M_x_over_k]
        refine Asymptotics.IsLittleO.sub ?_ ?_
        · field_simp
          refine h_M.comp_tendsto (Filter.tendsto_id.atTop_mul_const (by positivity)) |> fun h => h.trans_isBigO ?_
          exact Asymptotics.isBigO_iff.mpr ⟨(k : ℝ) ⁻¹, Filter.eventually_atTop.mpr ⟨1, fun x hx => by simp +decide ; ring_nf; norm_num [show k ≠ 0 by linarith]⟩⟩
        · have := h_M.comp_tendsto (show Filter.Tendsto (fun x : ℝ => x / (k + 1)) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_div_const (by positivity))
          rw [Asymptotics.isLittleO_iff] at *
          intro c hc; filter_upwards [this (show 0 < c * (k + 1) by positivity), Filter.eventually_gt_atTop 0] with x hx₁ hx₂; simp_all +decide only [ge_iff_le, norm_eq_abs, eventually_atTop, Function.comp_apply, norm_div, cast_nonneg,
    zero_le_one, add_nonneg, abs_of_nonneg]
          exact hx₁.trans (by rw [mul_assoc, mul_div_cancel₀ _ (by positivity)])
      have h_sum_o_x : (fun x : ℝ => ∑ k ∈ Finset.Ico 1 K, (k : ℝ) * (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ))) =o[atTop] (fun x => x) := by
        rw [Asymptotics.isLittleO_iff_tendsto']
        · have h_sum_little_o : ∀ k ∈ Finset.Ico 1 K, Filter.Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, (μ n : ℝ)) / x) Filter.atTop (nhds 0) := by
            intro k hk; specialize h_M_x_over_k k (Finset.mem_Ico.mp hk |>.1) (Finset.mem_Ico.mp hk |>.2) ; rw [Asymptotics.isLittleO_iff_tendsto'] at h_M_x_over_k <;> aesop
          simpa [Finset.sum_div _ _ _, mul_div_assoc] using tendsto_finsetSum _ fun k hk => h_sum_little_o k hk |> Filter.Tendsto.const_mul _
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      exact h_sum_o_x.congr'
        (by filter_upwards [Filter.eventually_ge_atTop 1] with x hx using by rw [h_group x hx])
        (by norm_num)


lemma sum_mobius_div_approx (x : ℝ) (K : ℕ) (hK : 0 < K) (hx : 1 ≤ x) :
  |x * (∑ n ∈ Icc 1 ⌊x/K⌋₊, (μ n : ℝ) / n) - 1| ≤ x/K + |∑ n ∈ Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
    have h_split : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = (∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) + (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋) := by
      erw [Finset.sum_Ioc_consecutive] <;> norm_num
      · rfl
      · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast hK
    have h_floor : ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) / (n : ℝ) - ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋) := by
      rw [Finset.mul_sum _ _ _] ; rw [← Finset.sum_sub_distrib] ; exact Finset.sum_congr rfl fun _ _ => by ring
    have h_bound : |∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, (μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ ⌊x / (K : ℝ)⌋₊ := by
      have h_bound : ∀ n ∈ Finset.Icc 1 ⌊x / (K : ℝ)⌋₊, |(μ n : ℝ) * (x / (n : ℝ) - ⌊x / (n : ℝ)⌋)| ≤ 1 := by
        norm_num [abs_mul]
        exact fun n hn₁ hn₂ => mul_le_one₀ (mod_cast by exact abs_moebius_le_one) (abs_nonneg _) (abs_le.mpr ⟨by linarith [Int.fract_nonneg (x / n)], by linarith [Int.fract_lt_one (x / n)]⟩)
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum h_bound) (by norm_num))
    have h_sum_floor : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ)⌋ = 1 := by
      convert sum_mobius_floor x hx using 1
    cases abs_cases (x * ∑ n ∈ Finset.Icc 1 ⌊x / (K : ℝ) ⌋₊, (μ n : ℝ) / n - 1) <;> cases abs_cases (∑ n ∈ Finset.Ioc ⌊x / (K : ℝ) ⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x / (n : ℝ) ⌋) <;> linarith [abs_le.mp h_bound, Nat.floor_le (show 0 ≤ x / (K : ℝ) by positivity), Nat.lt_floor_add_one (x / (K : ℝ))]




theorem mu_pnt_alt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ) / n) =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [Asymptotics.isLittleO_iff_tendsto'] <;> norm_num
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    set S : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (μ n : ℝ) / n
    have h_bound : ∀ K : ℕ, 0 < K → ∀ x : ℝ, 1 ≤ x → |S (x / K)| ≤ 1 / K + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x := by
      intros K hK x hx
      have h_approx : |x * S (x / K) - 1| ≤ x / K + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
        convert sum_mobius_div_approx x K hK hx using 1
      rw [abs_le] at *
      ring_nf at *
      constructor <;> nlinarith [inv_pos.2 (by positivity : 0 < x), mul_inv_cancel₀ (by positivity : x ≠ 0), abs_nonneg (∑ n ∈ Finset.Ioc ⌊ (K : ℝ) ⁻¹ * x⌋₊ ⌊x⌋₊, (μ n : ℝ) * ⌊x * (n : ℝ) ⁻¹⌋)]
    have h_tail_zero : ∀ K : ℕ, 0 < K → Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
      intro K hK
      have h_tail_zero : Filter.Tendsto (fun x : ℝ => |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds 0) := by
        have := sum_mobius_floor_tail_isLittleO K hK
        rw [Asymptotics.isLittleO_iff_tendsto'] at this
        · simpa [abs_div] using this.abs.congr' (by filter_upwards [Filter.eventually_gt_atTop 0] with x hx using by rw [abs_div, abs_of_nonneg hx.le])
        · filter_upwards [Filter.eventually_gt_atTop 0] with x hx hx' using absurd hx' hx.ne'
      convert h_tail_zero using 1
    have h_eps : ∀ ϵ > 0, ∃ Y : ℝ, ∀ y ≥ Y, |S y| < ϵ := by
      intros ϵ hϵ_pos
      obtain ⟨K, hK_pos, hK⟩ : ∃ K : ℕ, 0 < K ∧ 1 / (K : ℝ) < ϵ / 3 := by
        exact ⟨⌊ϵ⁻¹ * 3⌋₊ + 1, Nat.succ_pos _, by rw [div_lt_iff₀] <;> push_cast <;> nlinarith [Nat.lt_floor_add_one (ϵ⁻¹ * 3), mul_inv_cancel₀ hϵ_pos.ne']⟩
      obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ x ≥ Y, |S (x / K)| < ϵ := by
        have h_tail_zero : Filter.Tendsto (fun x : ℝ => 1 / (K : ℝ) + 1 / x + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| / x) Filter.atTop (nhds (1 / (K : ℝ))) := by
          simpa using Filter.Tendsto.add (tendsto_const_nhds.add (tendsto_inv_atTop_zero)) (h_tail_zero K hK_pos)
        exact Filter.eventually_atTop.mp (h_tail_zero.eventually (gt_mem_nhds <| by linarith)) |> fun ⟨Y, hY⟩ ↦ ⟨Max.max Y 1, fun x hx ↦ lt_of_le_of_lt (h_bound K hK_pos x <| le_trans (le_max_right _ _) hx) <| hY x <| le_trans (le_max_left _ _) hx⟩
      use Y / K; intros y hy; specialize hY (y * K) (by nlinarith [show (K : ℝ) ≥ 1 by norm_cast, div_mul_cancel₀ Y (by positivity : (K : ℝ) ≠ 0)]) ; simp_all +decide [ne_of_gt]
    exact Metric.tendsto_atTop.mpr fun ε hε => by simpa using h_eps ε hε
  have h_sum_zero : Filter.Tendsto (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (μ n : ℝ) / n) Filter.atTop (nhds 0) := by
    convert h_sum_zero using 2 ; erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
  simpa [Finset.sum_range_succ] using h_sum_zero.sub (show Filter.Tendsto (fun x : ℝ => (μ ⌊x⌋₊ : ℝ) / ⌊x⌋₊) Filter.atTop (nhds 0) from tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => by positivity) (fun x => by simpa using div_le_div_of_nonneg_right (show |(μ ⌊x⌋₊ : ℝ)| ≤ 1 from mod_cast by { unfold ArithmeticFunction.moebius; aesop }) <| Nat.cast_nonneg _) <| tendsto_inv_atTop_zero.comp <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop)





theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
      fun x ↦ x / q.totient := by
  let ψ_aq : ℝ → ℝ := fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else 0
  have htot_pos : (0 : ℝ) < q.totient := cast_pos.mpr (totient_pos.mpr hq)
  have hψ_equiv : ψ_aq ~[atTop] fun x ↦ x / q.totient := by
    have hW := WeakPNT_AP hq ha ha'
    simp only [cumsum, ← Iio_eq_range] at hW
    have hψ_eq x : ψ_aq x = ∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0 := by
      simp only [ψ_aq, show Icc 1 ⌊x⌋₊ = (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
        ext n; simp [mem_Icc, mem_filter]; tauto, sum_filter]
      refine sum_congr rfl fun n _ ↦ ?_
      by_cases hn : 1 ≤ n <;> simp only [hn, ↓reduceIte]
      push Not at hn; interval_cases n; simp
    refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx; exact div_ne_zero (by linarith) htot_pos.ne'
    have hlim1 : Tendsto (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
        (⌊x⌋₊ + 1 : ℝ)) atTop (nhds (1 / q.totient)) := by
      have heq : (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
          (⌊x⌋₊ + 1 : ℝ)) = (fun N ↦ (∑ n ∈ Iio N, if n % q = a then Λ n else 0) / N) ∘
          (fun x : ℝ ↦ ⌊x⌋₊ + 1) := by ext x; simp [Function.comp_apply]
      exact heq ▸ hW.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    have hgoal_eq : (ψ_aq / fun x ↦ x / (q.totient : ℝ)) =
        fun x ↦ ψ_aq x / x * q.totient := by ext x; simp only [Pi.div_apply, div_div_eq_mul_div]; ring
    rw [hgoal_eq, show (1 : ℝ) = 1 / q.totient * 1 * q.totient by field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have heq' : (fun x ↦ ψ_aq x / x) =ᶠ[atTop]
        fun x ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) / (⌊x⌋₊ + 1 : ℝ) * ((⌊x⌋₊ + 1 : ℝ) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [hψ_eq]; field_simp
    exact Tendsto.congr' heq'.symm (hlim1.mul tendsto_floor_add_one_div_self)
  refine hψ_equiv.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, eventually_atTop.mpr ⟨2, fun x hx ↦ ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiff_nonneg : 0 ≤ ψ_aq x - ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0 := by
      simp only [ψ_aq, sub_nonneg]
      calc (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ))
          ≤ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) :=
            sum_le_sum fun p hp ↦ by split_ifs <;> simp [vonMangoldt_apply_prime (mem_filter.mp hp).2]
        _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else (0 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg
              (fun p hp ↦ by simp only [mem_filter, mem_Iic, mem_Icc] at hp ⊢; exact ⟨hp.2.one_lt.le, hp.1⟩)
              (fun n _ _ ↦ by split_ifs <;> [exact vonMangoldt_nonneg; rfl])
    have hdiff_le : ψ_aq x - (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) ≤ ψ x - θ x := by
      simp only [ψ_aq, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
      conv_rhs => rw [Icc_zero_eq_insert, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 ⌊x⌋₊),
        show Λ 0 = 0 by simp only [ArithmeticFunction.map_zero], zero_add,
        show filter Nat.Prime (insert 0 (Icc 1 ⌊x⌋₊)) = filter Nat.Prime (Icc 1 ⌊x⌋₊) by
          simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) =
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) from
          sum_congr rfl fun p hp ↦ by simp only [mem_filter] at hp; split_ifs <;> simp [vonMangoldt_apply_prime hp.2],
        ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p) = ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), log p from
          sum_congr rfl fun p hp ↦ vonMangoldt_apply_prime (mem_filter.mp hp).2]
      have h1 : (∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), if n % q = a then Λ n else (0 : ℝ)) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), Λ n :=
        sum_le_sum fun n _ ↦ by split_ifs <;> [exact le_refl _; exact vonMangoldt_nonneg]
      linarith
    rw [abs_of_nonneg hdiff_nonneg, abs_of_nonneg (by bound)]
    exact hdiff_le.trans ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)))
  · simpa only [mul_assoc] using
      (isLittleO_sqrt_mul_log.const_mul_left 2).trans_isTheta (isTheta_self_div_const htot_pos.ne')


theorem dirichlet_thm {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) :
    Infinite { p // p.Prime ∧ p % q = a } := by
  have : {p | p.Prime ∧ p % q = a}.Infinite := by
    have : {p | p.Prime ∧ p ≡ a [MOD q]}.Infinite := by
      have := @infinite_setOfPred_prime_and_eq_mod
      specialize @this q <| NeZero.of_pos hq
      simp_all only [isUnit_iff_exists_inv, forall_exists_index, ← ZMod.natCast_eq_natCast_iff]
      exact this (IsUnit.exists_right_inv (show IsUnit (a : ZMod q) from by
        rwa [ZMod.isUnit_iff_coprime])).choose (IsUnit.exists_right_inv (show IsUnit (a : ZMod q)
          from by rwa [ZMod.isUnit_iff_coprime])).choose_spec
    exact this.mono fun p hp ↦ ⟨hp.1, by simpa [ModEq, mod_eq_of_lt ha'] using hp.2⟩
  exact Set.infinite_coe_iff.mpr this







end Campaign180File14

/- Source module: ErdosProblems.Erdos730.PNTAP -/
section Campaign180File15
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: fixed-modulus prime number theorem in arithmetic progressions

This file derives the unweighted residue-class prime count used by the
Erdős 730 development from `chebyshev_asymptotic_pnt`, the weighted PNT in
arithmetic progressions proved by `PrimeNumberTheoremAnd`.
-/

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace Erdos730.FullDensity

noncomputable def thetaAP (A a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Icc 0 ⌊x⌋₊).filter Nat.Prime,
    if p % A = a then Real.log p else 0

noncomputable def primeAPCountingReal (A a : ℕ) (x : ℝ) : ℝ :=
  (((Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p % A = a).card : ℝ)

noncomputable def apPrimes (A a : ℕ) (x : ℝ) : Finset ℕ :=
  (Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p % A = a

lemma thetaAP_eq_sum_apPrimes (A a : ℕ) (x : ℝ) :
    thetaAP A a x = ∑ p ∈ apPrimes A a x, Real.log p := by
  rw [thetaAP, apPrimes, ← Finset.sum_filter]
  congr 1
  ext p
  simp [and_assoc]

lemma primeAPCountingReal_eq_card_apPrimes (A a : ℕ) (x : ℝ) :
    primeAPCountingReal A a x = (apPrimes A a x).card := by
  rfl

lemma card_filter_prime_Iic (n : ℕ) :
    ((Iic n).filter Nat.Prime).card = n.primeCounting := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp

lemma thetaAP_nonneg (A a : ℕ) (x : ℝ) : 0 ≤ thetaAP A a x := by
  rw [thetaAP_eq_sum_apPrimes]
  exact Finset.sum_nonneg fun p hp => Real.log_nonneg <| by
    have hprime := (Finset.mem_filter.mp hp).2.1
    exact_mod_cast hprime.one_lt.le

lemma thetaAP_le_count_mul_log (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    thetaAP A a x ≤ primeAPCountingReal A a x * Real.log x := by
  rw [thetaAP_eq_sum_apPrimes, primeAPCountingReal_eq_card_apPrimes]
  calc
    ∑ p ∈ apPrimes A a x, Real.log p
        ≤ ∑ _p ∈ apPrimes A a x, Real.log x := by
          apply Finset.sum_le_sum
          intro p hp
          apply Real.strictMonoOn_log.monotoneOn
          · have hprime := (Finset.mem_filter.mp hp).2.1
            exact (show (0 : ℝ) < p by exact_mod_cast hprime.pos)
          · exact (show (0 : ℝ) < x by linarith)
          · exact (Nat.cast_le.mpr (Finset.mem_Icc.mp
              (Finset.mem_filter.mp hp).1).2).trans (Nat.floor_le (by linarith))
    _ = (apPrimes A a x).card * Real.log x := by simp

lemma integrableOn_thetaAP_div_id_mul_log_sq (A a : ℕ) (x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t => thetaAP A a t / (t * Real.log t ^ 2))
      (Set.Icc 2 x) MeasureTheory.volume := by
  conv => arg 1; ext t
          rw [thetaAP, div_eq_mul_one_div, mul_comm, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have htlog : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 <| by
    simp
    grind
  fun_prop (disch := assumption)

lemma primeAPCountingReal_eq_thetaAP_div_log_add_integral
    (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    primeAPCountingReal A a x =
      thetaAP A a x / Real.log x +
        ∫ t in 2..x, thetaAP A a t / (t * Real.log t ^ 2) := by
  rw [primeAPCountingReal, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  let b : ℕ → ℝ := Set.indicator
    {n : ℕ | n.Prime ∧ n % A = a} (fun n => Real.log n)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * b n
  · refine Finset.sum_congr rfl fun n hn => ?_
    split_ifs with h
    · have hnlog : Real.log n ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (mod_cast h.1.pos) (mod_cast h.1.ne_one)
      simp [b, h, hnlog]
    · simp [b, h]
  rw [sum_mul_eq_sub_integral_mul₁ b (f := fun n => (Real.log n)⁻¹)
      (by simp [b]) (by simp [b]), ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in 2..x, deriv (fun y => (Real.log y)⁻¹) u * f u =
        ∫ u in 2..x, f u * -(u * Real.log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by
        simp [Real.deriv_inv_log, field]
    simp [-Real.deriv_inv_log, int_deriv, b, Set.indicator_apply, Finset.sum_filter, thetaAP]
    grind
  · intro z ⟨hz, _⟩
    have hz0 : z ≠ 0 := by linarith
    have hzlog : Real.log z ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := assumption)
  · refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ =>
      ContinuousWithinAt.congr ?_ (fun _ _ => Real.deriv_inv_log_apply)
        Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith
    have hzlog : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by
      fun_prop (disch := assumption)

lemma thetaAP_le_theta (A a : ℕ) (x : ℝ) :
    thetaAP A a x ≤ Chebyshev.theta x := by
  rw [thetaAP, Chebyshev.theta_eq_sum_Icc]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · exact le_rfl
  · exact Real.log_nonneg <| by
      have hprime := (Finset.mem_filter.mp hp).2
      exact_mod_cast hprime.one_lt.le

lemma integral_thetaAP_div_log_sq_isLittleO (A a : ℕ) :
    (fun x => ∫ t in 2..x, thetaAP A a t / (t * Real.log t ^ 2))
      =o[atTop] (fun x => x / Real.log x) := by
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans_isLittleO
    Chebyshev.integral_theta_div_log_sq_isLittleO
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hapInt : IntervalIntegrable
      (fun t => thetaAP A a t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (integrableOn_thetaAP_div_id_mul_log_sq A a x)
  have hthetaInt : IntervalIntegrable
      (fun t => Chebyshev.theta t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hapNonneg :
      0 ≤ ∫ t in 2..x, thetaAP A a t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      exact div_nonneg (thetaAP_nonneg A a t) <| mul_nonneg
        (by linarith [ht.1]) (sq_nonneg _)
  have hthetaNonneg :
      0 ≤ ∫ t in 2..x, Chebyshev.theta t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      exact div_nonneg (Chebyshev.theta_nonneg t) <| mul_nonneg
        (by linarith [ht.1]) (sq_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hapNonneg,
    abs_of_nonneg hthetaNonneg, one_mul]
  exact intervalIntegral.integral_mono_on hx hapInt hthetaInt fun t ht => by
    exact div_le_div_of_nonneg_right (thetaAP_le_theta A a t) <|
      mul_nonneg (by linarith [ht.1]) (sq_nonneg _)

lemma thetaAP_asymptotic {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A)
    (haA : a < A) :
    thetaAP A a ~[atTop] (fun x : ℝ => x / A.totient) := by
  simpa only [thetaAP] using! chebyshev_asymptotic_pnt hA ha haA

lemma thetaAP_div_id_tendsto {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A)
    (haA : a < A) :
    Tendsto (fun x : ℝ => thetaAP A a x / x) atTop
      (𝓝 ((A.totient : ℝ)⁻¹)) := by
  have htot : (A.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hA).ne'
  have hden : ∀ᶠ x : ℝ in atTop, x / (A.totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx htot
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hden).mp
    (thetaAP_asymptotic hA ha haA)
  convert h.div_const (A.totient : ℝ) using 1
  · funext x
    simp only [Pi.div_apply]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  · field_simp

theorem primeAPCountingReal_normalized_tendsto {A a : ℕ}
    (hA : 0 < A) (ha : a.Coprime A) (haA : a < A) :
    Tendsto
      (fun x : ℝ =>
        primeAPCountingReal A a x / (x / Real.log x))
      atTop (𝓝 ((A.totient : ℝ)⁻¹)) := by
  have hint := (integral_thetaAP_div_log_sq_isLittleO A a).tendsto_div_nhds_zero
  have hsum := (thetaAP_div_id_tendsto hA ha haA).add hint
  simpa only [add_zero] using hsum.congr' <| by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [primeAPCountingReal_eq_thetaAP_div_log_add_integral A a hx]
    have hx0 : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    field

lemma primeAPCount_eq_primeAPCountingReal (A a N : ℕ) (haA : a < A) :
    (primeAPCount A a N : ℝ) = primeAPCountingReal A a N := by
  rw [primeAPCount, primeAPCountingReal, Nat.floor_natCast]
  norm_cast
  apply congrArg Finset.card
  ext p
  simp [Nat.mod_eq_of_lt haA]

theorem pntAPInputAtModulus (A : ℕ) (hA : 0 < A) :
    PNTAPInputAtModulus A := by
  refine ⟨hA, fun a haA ha => ?_⟩
  have h := (primeAPCountingReal_normalized_tendsto hA ha haA).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext N
  rw [primeAPCount_eq_primeAPCountingReal A a N haA]
  rfl

theorem requiredFixedModulusPNTAPInput :
    RequiredFixedModulusPNTAPInput := by
  exact ⟨pntAPInputAtModulus 1 (by norm_num),
    pntAPInputAtModulus 222138 (by norm_num),
    pntAPInputAtModulus 148092 (by norm_num)⟩

end Erdos730.FullDensity

end Campaign180File15

/- Source module: ErdosProblems.Erdos730.Mertens -/
section Campaign180File16
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: reciprocal-prime estimates available in pinned Mathlib

This file isolates the reciprocal-prime input used by the density proof.  It
contains no axiom and does not assume a Mertens theorem.  The main exact
identity is Abel summation:

`sum_{p ≤ x} 1 / p = π(x) / x + ∫₂ˣ π(t) / t² dt`.

Consequently an ordinary prime-number theorem is enough to recover all fixed
prime-band limits.  Pinned Mathlib currently supplies only Chebyshev's upper
bound, not the coefficient-one asymptotic; the unconditional lemmas below
bank the exact Abel bridge and the crude harmonic majorant needed by the
uniform geometric tail.
-/

open Filter Finset MeasureTheory Real
open scoped ArithmeticFunction BigOperators Nat.Prime Topology

namespace Erdos730.FullDensity

/-- The reciprocal-prime sum is nonnegative. -/
theorem reciprocalPrimeSum_nonneg (N : ℕ) :
    0 ≤ reciprocalPrimeSum N := by
  exact sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Dropping the primality restriction embeds the reciprocal-prime sum in the
ordinary harmonic sum.  The endpoint convention agrees exactly: the extra
term at `0` is zero. -/
theorem reciprocalPrimeSum_le_harmonic (N : ℕ) :
    reciprocalPrimeSum N ≤ (harmonic N : ℝ) := by
  rw [reciprocalPrimeSum]
  calc
    (∑ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ)⁻¹)
        ≤ ∑ p ∈ range (N + 1), (p : ℝ)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p _ _
          positivity
    _ = (harmonic N : ℝ) := by
      induction N with
      | zero => simp
      | succ N ih =>
          rw [Finset.sum_range_succ, harmonic_succ, Rat.cast_add, Rat.cast_inv,
            Rat.cast_natCast, ih]

/-- A completely unconditional logarithmic majorant.  This is much weaker
than Mertens, but is already sufficient after multiplication by the geometric
depth factor in the uniform tail. -/
theorem reciprocalPrimeSum_le_one_add_log (N : ℕ) :
    reciprocalPrimeSum N ≤ 1 + Real.log N :=
  (reciprocalPrimeSum_le_harmonic N).trans (harmonic_le_one_add_log N)

/-- The elementary linear majorant used to discharge geometric-depth tails.
It is intentionally proved without any prime-counting estimate. -/
theorem reciprocalPrimeSum_le_natCast (N : ℕ) :
    reciprocalPrimeSum N ≤ (N : ℝ) := by
  refine (reciprocalPrimeSum_le_harmonic N).trans ?_
  induction N with
  | zero => simp
  | succ N ih =>
      rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
        Nat.cast_add, Nat.cast_one]
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hone : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      exact add_le_add ih ((inv_le_one₀ hpos).2 hone)

/-- Any fixed geometric depth factor kills the reciprocal-prime partial sum.
This unconditional lemma is the analytic content needed for the deepest-band
tail after the depth cutoff has been converted to a natural parameter. -/
theorem tendsto_geom_mul_reciprocalPrimeSum_atTop
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun N : ℕ => q ^ N * reciprocalPrimeSum N) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro N
    exact mul_nonneg (pow_nonneg hq0 N) (reciprocalPrimeSum_nonneg N)
  · intro N
    calc
      q ^ N * reciprocalPrimeSum N ≤ q ^ N * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (reciprocalPrimeSum_le_natCast N) (pow_nonneg hq0 N)
      _ = (N : ℝ) * q ^ N := mul_comm _ _
  · exact tendsto_self_mul_const_pow_of_lt_one hq0 hq1

/-- Abel summation for reciprocal primes.  This is the exact bridge from the
ordinary prime-counting function to the Mertens-type band estimates needed by
the density proof. -/
theorem reciprocalPrimeSum_eq_primeCounting_div_add_integral
    {N : ℕ} (hN : 2 ≤ N) :
    reciprocalPrimeSum N =
      (Nat.primeCounting N : ℝ) / N +
        ∫ t in (2 : ℝ)..N, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) N,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (zero_lt_two.trans_le ht.1))
  have hint : IntegrableOn (deriv fun x : ℝ => x⁻¹) (Set.Icc (2 : ℝ) N) := by
    rw [deriv_inv']
    refine ContinuousOn.integrableOn_Icc ?_
    exact ((continuous_id.pow 2).continuousOn.inv₀ fun t ht hzero =>
      (zero_lt_two.trans_le ht.1).ne' (eq_zero_of_pow_eq_zero hzero)).neg
  rw [reciprocalPrimeSum, Nat.range_succ_eq_Icc_zero, sum_filter]
  let a : ℕ → ℝ := Set.indicator {p | p.Prime} (fun _ => 1)
  trans ∑ k ∈ Icc 0 N, (k : ℝ)⁻¹ * a k
  · refine sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · simp [a, hk]
    · simp [a, hk]
  have hab :
      ∑ k ∈ Icc 0 N, (k : ℝ)⁻¹ * a k =
        (N : ℝ)⁻¹ * ∑ k ∈ Icc 0 N, a k -
          ∫ t in Set.Ioc (2 : ℝ) N,
            deriv (fun x : ℝ => x⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, a k := by
    simpa using sum_mul_eq_sub_integral_mul₁ a (f := fun x : ℝ => x⁻¹)
      (by simp [a, Nat.not_prime_zero]) (by simp [a, Nat.not_prime_one]) N hdiff hint
  rw [hab, ← intervalIntegral.integral_of_le (mod_cast hN)]
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have int_deriv (f : ℝ → ℝ) :
      ∫ u in (2 : ℝ)..N,
          deriv (fun x : ℝ => x⁻¹) u * f u =
        ∫ u in (2 : ℝ)..N, f u * -(u ^ 2)⁻¹ :=
    intervalIntegral.integral_congr fun u _ => by rw [deriv_inv']; ring
  rw [int_deriv]
  simp [a, Set.indicator_apply, Nat.range_succ_eq_Icc_zero, div_eq_mul_inv]
  ring

/-!
## The unconditional weighted Mertens estimate

The following factorial argument is adapted from
`math-inc/Erdos1196`, commit
`02fba13be7487cc51315f68d8fa7ef277633d3c8`, file
`PrimitiveSetsAboveX/PreliminariesMertens.lean` (Apache-2.0).  The source
targets Lean `v4.30.0-rc1`; the proof below has been ported and checked against
this repository's pinned Lean `v4.33.0` and Mathlib `db584cd6`.

This is the classical first Mertens theorem for the von Mangoldt weight.  It
is strictly weaker than the reciprocal-prime asymptotic, but it is the
standard unconditional input from which that asymptotic follows after (i)
bounding the contribution of proper prime powers and (ii) a second Abel
summation with weight `1 / log`.
-/

/-- Partial sums of `Λ(m) / m`. -/
noncomputable def vonMangoldtReciprocalSum (t : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 t, Λ m / (m : ℝ)

/-- The fractional-part correction in the factorial proof. -/
private noncomputable def vonMangoldtFractionalError (t : ℕ) : ℝ :=
  (1 / t) * ∑ m ∈ Icc 1 t, Λ m * ((t : ℝ) / m - ((t / m : ℕ) : ℝ))

private lemma one_div_mul_mul_natCast_div {a : ℝ} {t m : ℕ} (ht : t ≠ 0) :
    (1 / (t : ℝ)) * (a * ((t : ℝ) / m)) = a / (m : ℝ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  grind only

private lemma truncation_eq_mod_div {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = ↑(t % m) / m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    apply (eq_div_iff hmR).2
    have hdecomp : (↑(t % m) : ℝ) + ↑(t / m) * m = t := by
      have h : (↑(t % m + m * (t / m)) : ℝ) = t := by
        exact_mod_cast (Nat.mod_add_div t m)
      simpa [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h
    grind only

private lemma truncation_eq_fract {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = Int.fract ((t : ℝ) / m) := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  exact truncation_eq_mod_div

private lemma sum_vonMangoldt_mul_div_eq_log_factorial (N : ℕ) :
    (Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
      Real.log (Nat.factorial N) := by
  have hI : Icc 1 N = Ioc 0 N := by
    ext n
    simp [mem_Icc, mem_Ioc, Nat.succ_le_iff]
  have hlogsum :
      (Icc 1 N).sum (fun n => Real.log (n : ℝ)) =
        Real.log (∏ n ∈ Icc 1 N, (n : ℝ)) := by
    symm
    refine Real.log_prod ?_
    intro n hn
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (Nat.succ_le_iff.mp (mem_Icc.mp hn).1))
  have hprodRange :
      (∏ i ∈ range N, ((i + 1 : ℕ) : ℝ)) = Nat.factorial N := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial N
  have hprod : (∏ n ∈ Icc 1 N, (n : ℝ)) = Nat.factorial N := by
    rw [← Ico_add_one_right_eq_Icc 1 N, prod_Ico_eq_prod_range]
    simpa [Nat.succ_eq_add_one, add_comm] using hprodRange
  calc
    (Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
        ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by rw [hI]
    _ = ∑ n ∈ Ioc 0 N,
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) n := by
          simpa using
            (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
              ArithmeticFunction.vonMangoldt N).symm
    _ = ∑ n ∈ Ioc 0 N, Real.log (n : ℝ) := by
          simp [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log]
    _ = ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by rw [← hI]
    _ = Real.log (Nat.factorial N) := by rw [hlogsum, hprod]

private lemma log_factorial_eq_sum_range (N : ℕ) :
    Real.log (Nat.factorial N) =
      ∑ i ∈ range N, Real.log ((i + 1 : ℕ) : ℝ) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, Real.log_prod]
  grind only

private lemma integral_log_le_log_factorial {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x ≤ Real.log (Nat.factorial N) := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  calc
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x
      ≤ ∑ i ∈ Ico 1 N, Real.log ((i + 1 : ℕ) : ℝ) :=
        MonotoneOn.integral_le_sum_Ico (f := Real.log) hN hmono
    _ = ∑ i ∈ range N, Real.log ((i + 1 : ℕ) : ℝ) := by
        have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
        rw [sum_Ico_eq_sum_range]
        rw [← hpred, sum_range_succ']
        simp [Nat.cast_add, add_left_comm, add_comm]
    _ = Real.log (Nat.factorial N) := (log_factorial_eq_sum_range N).symm

private lemma log_factorial_le_log_add_integral_log {N : ℕ} (hN : 1 ≤ N) :
    Real.log (Nat.factorial N) ≤
      Real.log N + ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  have hsum :
      ∑ i ∈ Ico 1 N, Real.log (i : ℝ) ≤
        ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x :=
    MonotoneOn.sum_le_integral_Ico (f := Real.log) hN hmono
  have hsum' :
      ∑ i ∈ Ico 1 N, Real.log (i : ℝ) =
        Real.log (Nat.factorial (N - 1)) := by
    rw [sum_Ico_eq_sum_range]
    simpa [Nat.cast_add, add_comm] using
      (log_factorial_eq_sum_range (N - 1)).symm
  have hfacNat : Nat.factorial N = N * Nat.factorial (N - 1) := by
    have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
    simpa [Nat.succ_eq_add_one, hpred] using Nat.factorial_succ (N - 1)
  have hfac :
      Real.log (Nat.factorial N) =
        Real.log N + Real.log (Nat.factorial (N - 1)) := by
    rw [hfacNat, Nat.cast_mul, Real.log_mul]
    · exact_mod_cast Nat.ne_of_gt hN
    · exact_mod_cast Nat.factorial_ne_zero (N - 1)
  grind only

private lemma abs_log_factorial_div_sub_log_le_one {N : ℕ} (hN : 1 ≤ N) :
    |Real.log (Nat.factorial N) / N - Real.log N| ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hint :
      ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x =
        (N : ℝ) * Real.log N - N + 1 := by
    simp [integral_log]
  have hlower : Real.log N - 1 ≤ Real.log (Nat.factorial N) / N := by
    apply (le_div_iff₀ hNpos).2
    have hcomp :
        (N : ℝ) * Real.log N - N + 1 ≤ Real.log (Nat.factorial N) := by
      simpa [hint] using integral_log_le_log_factorial hN
    linarith
  have hupper : Real.log (Nat.factorial N) / N ≤ Real.log N := by
    apply (div_le_iff₀ hNpos).2
    have hcomp :
        Real.log (Nat.factorial N) ≤
          Real.log N + ((N : ℝ) * Real.log N - N + 1) := by
      simpa [hint] using log_factorial_le_log_add_integral_log hN
    have hlog : Real.log N ≤ N - 1 := by
      simpa using Real.log_le_sub_one_of_pos hNpos
    linarith
  grind only [= abs.eq_1, = max_def]

private lemma vonMangoldtReciprocalSum_eq_log_factorial_div_add_fractional
    (t : ℕ) :
    vonMangoldtReciprocalSum t =
      Real.log (Nat.factorial t) / t + vonMangoldtFractionalError t := by
  by_cases ht : t = 0
  · subst ht
    simp [vonMangoldtReciprocalSum, vonMangoldtFractionalError]
  · rw [vonMangoldtReciprocalSum, vonMangoldtFractionalError]
    calc
      ∑ m ∈ Icc 1 t, Λ m / (m : ℝ) =
          ∑ m ∈ Icc 1 t,
            ((1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
              (1 / (t : ℝ)) *
                (Λ m * ((t : ℝ) / m - ↑(t / m)))) := by
            refine sum_congr rfl ?_
            intro m _
            calc
              Λ m / (m : ℝ) =
                  (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m)) := by
                symm
                exact one_div_mul_mul_natCast_div (a := Λ m) ht
              _ = (1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
                    (1 / (t : ℝ)) *
                      (Λ m * ((t : ℝ) / m - ↑(t / m))) := by ring
      _ = (1 / (t : ℝ)) *
              ∑ m ∈ Icc 1 t, Λ m * (((t / m : ℕ) : ℝ)) +
            (1 / (t : ℝ)) *
              ∑ m ∈ Icc 1 t,
                Λ m * ((t : ℝ) / m - ↑(t / m)) := by
            rw [sum_add_distrib, mul_sum, mul_sum]
      _ = Real.log (Nat.factorial t) / t + vonMangoldtFractionalError t := by
            rw [sum_vonMangoldt_mul_div_eq_log_factorial]
            rw [vonMangoldtFractionalError]
            ring_nf

private lemma vonMangoldtFractionalError_nonneg {t : ℕ} (ht : 1 ≤ t) :
    0 ≤ vonMangoldtFractionalError t := by
  rw [vonMangoldtFractionalError]
  refine mul_nonneg ?_ (sum_nonneg ?_)
  · exact one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity)
  · intro m _
    rw [truncation_eq_fract]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Int.fract_nonneg _)

private lemma vonMangoldtFractionalError_le {t : ℕ} (ht : 2 ≤ t) :
    vonMangoldtFractionalError t ≤ Real.log 4 + 4 := by
  rw [vonMangoldtFractionalError]
  have hsum :
      ∑ m ∈ Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m)) ≤
        ∑ m ∈ Icc 1 t, Λ m := by
    refine sum_le_sum ?_
    intro m _
    rw [truncation_eq_fract]
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := m),
      (Int.fract_lt_one ((t : ℝ) / m)).le]
  have hcheb : Chebyshev.psi t ≤ (Real.log 4 + 4) * t := by
    simpa using Chebyshev.psi_le_const_mul_self (x := (t : ℝ))
      (show 0 ≤ (t : ℝ) by positivity)
  have hI : Icc 1 t = Ioc 0 t := by
    ext n
    simp [mem_Icc, mem_Ioc, Nat.succ_le_iff]
  calc
    (1 / t : ℝ) *
        ∑ m ∈ Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m))
      ≤ (1 / t : ℝ) * ∑ m ∈ Icc 1 t, Λ m :=
        mul_le_mul_of_nonneg_left hsum
          (one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity))
    _ = Chebyshev.psi t / t := by
        simp [hI, Chebyshev.psi, Nat.floor_natCast, div_eq_mul_inv, mul_comm]
    _ ≤ Real.log 4 + 4 := by
        have htR : 0 < (t : ℝ) := by positivity
        exact (div_le_iff₀ htR).mpr hcheb

/-- Unconditional bounded-error first Mertens theorem:
`∑_{m ≤ t} Λ(m) / m = log t + O(1)` with an explicit bound. -/
theorem vonMangoldtReciprocalSum_bounded_error :
    ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |vonMangoldtReciprocalSum t - Real.log (t : ℝ)| ≤ Real.log 4 + 5 := by
  intro t ht
  have ht1 : 1 ≤ t := by omega
  rw [vonMangoldtReciprocalSum_eq_log_factorial_div_add_fractional t]
  calc
    |Real.log (Nat.factorial t) / t + vonMangoldtFractionalError t -
        Real.log (t : ℝ)| =
      |(Real.log (Nat.factorial t) / t - Real.log (t : ℝ)) +
        vonMangoldtFractionalError t| := by
          congr
          ring
    _ ≤ |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| +
          |vonMangoldtFractionalError t| := abs_add_le _ _
    _ = |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| +
          vonMangoldtFractionalError t := by
        rw [abs_of_nonneg (vonMangoldtFractionalError_nonneg ht1)]
    _ ≤ 1 + (Real.log 4 + 4) := by
        gcongr
        · exact abs_log_factorial_div_sub_log_le_one ht1
        · exact vonMangoldtFractionalError_le ht
    _ = Real.log 4 + 5 := by ring

/-- Proper prime powers make an absolutely summable contribution to the
von-Mangoldt reciprocal series.  This specializes Mathlib's residue-class
lemma to the unique class modulo `1`; unlike the prime-number theorem in
progressions, this summability theorem is already present in pinned Mathlib. -/
theorem summable_nonprime_vonMangoldt_div :
    Summable fun n : ℕ => (if n.Prime then 0 else Λ n) / n := by
  have h :=
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
      (a := (0 : ZMod 1))
  refine h.congr fun n => ?_
  have hn : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [ArithmeticFunction.vonMangoldt.residueClass, hn]

/-- The logarithmically weighted reciprocal-prime partial sum. -/
noncomputable def logWeightedPrimeSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p

/-- The summable proper-prime-power contribution. -/
noncomputable def nonprimeVonMangoldtConstant : ℝ :=
  ∑' n : ℕ, (if n.Prime then 0 else Λ n) / n

theorem nonprimeVonMangoldtConstant_nonneg : 0 ≤ nonprimeVonMangoldtConstant := by
  exact tsum_nonneg fun n => by
    split_ifs
    · simp
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

/-- Exact separation of prime and proper-prime-power terms. -/
theorem vonMangoldtReciprocalSum_eq_logWeightedPrimeSum_add (N : ℕ) :
    vonMangoldtReciprocalSum N =
      logWeightedPrimeSum N +
        ∑ n ∈ Icc 1 N, (if n.Prime then 0 else Λ n) / n := by
  rw [vonMangoldtReciprocalSum, logWeightedPrimeSum, sum_filter,
    ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · simp [hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [hn]

/-- Every finite proper-prime-power contribution is bounded by its convergent
total mass. -/
theorem sum_nonprime_vonMangoldt_div_le_constant (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if n.Prime then 0 else Λ n) / n ≤
      nonprimeVonMangoldtConstant := by
  exact summable_nonprime_vonMangoldt_div.sum_le_tsum (Icc 1 N)
    (fun n _ => by
      split_ifs
      · simp
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))

/-- The floor/log discrepancy on a unit interval is at most `log 2`. -/
private lemma abs_log_floor_sub_log_le_log_two {t : ℝ} (ht : 2 ≤ t) :
    |Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t| ≤ Real.log 2 := by
  have hfloor_pos : 0 < ((⌊t⌋₊ : ℕ) : ℝ) := by
    have hfloor_one : (1 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_lt_two (Nat.le_floor ht)
    linarith
  have ht_pos : 0 < t := by linarith
  have hfloor_le : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht_pos.le
  have htwo : t ≤ ((⌊t⌋₊ : ℕ) : ℝ) * 2 := by
    have hlt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    grind only
  have habs : Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t ≤ 0 := by
    exact sub_nonpos.mpr (Real.log_le_log hfloor_pos hfloor_le)
  rw [abs_of_nonpos habs, neg_sub, ← Real.log_div
    (show t ≠ 0 by linarith)
    (show (((⌊t⌋₊ : ℕ) : ℝ) ≠ 0) by positivity)]
  have hratio_pos : 0 < t / (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
  refine Real.log_le_log hratio_pos ?_
  exact (div_le_iff₀' hfloor_pos).mpr htwo

/-- Continuous-endpoint bounded error for the von-Mangoldt sum. -/
theorem vonMangoldtReciprocalSum_floor_bounded_error {x : ℝ} (hx : 2 ≤ x) :
    |vonMangoldtReciprocalSum ⌊x⌋₊ - Real.log x| ≤
      Real.log 4 + 5 + Real.log 2 := by
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  calc
    |vonMangoldtReciprocalSum ⌊x⌋₊ - Real.log x|
      ≤ |vonMangoldtReciprocalSum ⌊x⌋₊ - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| +
          |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              abs_sub_le (vonMangoldtReciprocalSum ⌊x⌋₊)
                (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) (Real.log x)
    _ ≤ (Real.log 4 + 5) + Real.log 2 :=
      add_le_add (vonMangoldtReciprocalSum_bounded_error hfloor)
        (abs_log_floor_sub_log_le_log_two hx)

/-- Real-endpoint error for the weighted prime sum. -/
noncomputable def logWeightedPrimeError (x : ℝ) : ℝ :=
  logWeightedPrimeSum ⌊x⌋₊ - Real.log x

/-- The prime-weighted first Mertens error is bounded unconditionally.  The
constant is deliberately not optimized; finiteness, rather than its numerical
value, is what the second Abel summation requires. -/
theorem logWeightedPrimeError_abs_le {x : ℝ} (hx : 2 ≤ x) :
    |logWeightedPrimeError x| ≤
      Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant := by
  let R : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (if n.Prime then 0 else Λ n) / n
  have hR0 : 0 ≤ R := by
    exact sum_nonneg fun n _ => by
      split_ifs
      · simp
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hRC : R ≤ nonprimeVonMangoldtConstant :=
    sum_nonprime_vonMangoldt_div_le_constant ⌊x⌋₊
  have hA := vonMangoldtReciprocalSum_floor_bounded_error hx
  have hdecomp := vonMangoldtReciprocalSum_eq_logWeightedPrimeSum_add ⌊x⌋₊
  rw [abs_le] at hA ⊢
  constructor
  · dsimp [logWeightedPrimeError]
    rw [hdecomp] at hA
    dsimp [R] at hR0 hRC ⊢
    linarith
  · dsimp [logWeightedPrimeError]
    rw [hdecomp] at hA
    dsimp [R] at hR0 hRC ⊢
    linarith

private lemma sum_Ioc_one_eq_sum_Ioc_zero_aux {f : ℕ → ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hf1 : f 1 = 0) :
    ∑ n ∈ Ioc 1 N, f n = ∑ n ∈ Ioc 0 N, f n := by
  calc
    ∑ n ∈ Ioc 1 N, f n = f 1 + ∑ n ∈ Ioc 1 N, f n := by rw [hf1, zero_add]
    _ = ∑ n ∈ Icc 1 N, f n := add_sum_Ioc_eq_sum_Icc hN
    _ = ∑ n ∈ Ioc 0 N, f n := by congr 1

private lemma sum_Ioc_one_eq_sum_Icc_zero_aux {f : ℕ → ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 N, f n = ∑ n ∈ Icc 0 N, f n := by
  calc
    ∑ n ∈ Ioc 1 N, f n = f 1 + ∑ n ∈ Ioc 1 N, f n := by rw [hf1, zero_add]
    _ = ∑ n ∈ Icc 1 N, f n := add_sum_Ioc_eq_sum_Icc hN
    _ = ∑ n ∈ Ioc 0 N, f n := by
      congr 1
    _ = ∑ n ∈ Icc 0 N, f n := by
      rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le N), hf0, zero_add]

/-- Abel summation with inverse-log weight. -/
private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊x⌋₊, f n / Real.log n =
      (∑ n ∈ Ioc 1 ⌊x⌋₊, f n) / Real.log x +
        ∫ t in 2..x,
          (∑ n ∈ Ioc 1 ⌊t⌋₊, f n) / (t * Real.log t ^ 2) := by
  let g : ℕ → ℝ := fun n => if n < 2 then 0 else f n
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
      (by simp) (by simp)]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : ¬n ≤ 1 := by simp_all
    simp [g, hn1]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := fun n => (Real.log n)⁻¹)
    (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv,
      ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
        (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      have hn1 : ¬n ≤ 1 := by linarith
      simp [g, hn1]
    · rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht => ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
        (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      have hn1 : ¬n ≤ 1 := by linarith
      simp [g, hn1]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : Real.log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext y; rw [deriv_inv_log]
    have : Real.log t ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (fun t => c / (t * Real.log t ^ 2)) (Set.Ioi x) volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply Integrable.const_mul
  refine integrableOn_Ioi_deriv_of_nonneg' ?_ ?_
    Real.tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have hlog : Real.log t ≠ 0 := by simp; grind
    have hdiff : DifferentiableAt ℝ (fun y => -(Real.log y)⁻¹) t := by
      fun_prop (disch := grind)
    refine hdiff.hasDerivAt.congr_deriv ?_
    simp [deriv_inv_log_apply]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem integrable_logWeightedPrimeError_div_mul_log_sq
    {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn
      (fun t => logWeightedPrimeError t / (t * Real.log t ^ 2))
      (Set.Ioi x) volume := by
  let C := Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant
  have hC : 0 < C := by
    dsimp [C]
    positivity [nonprimeVonMangoldtConstant_nonneg]
  apply Integrable.mono (integrable_const_div_mul_log_sq C hx)
  · exact Measurable.aestronglyMeasurable (by
      unfold logWeightedPrimeError logWeightedPrimeSum
      fun_prop)
  · filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, Real.norm_eq_abs, norm_mul, norm_pow, sq_abs,
      abs_of_pos hC]
    gcongr
    exact logWeightedPrimeError_abs_le (by linarith)

private lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t => Real.log (Real.log t)) x = 1 / (x * Real.log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

private lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * Real.log t) =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub
    (f := fun t => Real.log (Real.log t))]
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : Real.log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := fun t => 1 / (t * Real.log t))
    · refine fun t ht => ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : Real.log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

private lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => 1 / (t * Real.log t)) volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht =>
    ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : Real.log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

private theorem integral_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * Real.log t ^ 2) = c / Real.log x := by
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0)
    (f := fun y => -c / Real.log y) ?_
    (integrable_const_div_mul_log_sq c hx) ?_ using 1
  · grind
  · intro t ht
    simp at ht
    refine (HasDerivAt.fun_div (hasDerivAt_const _ (-c))
      (hasDerivAt_log (by linarith)) ?_).congr_deriv ?_
    · simp
      grind
    · grind
  · have h := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c)
    simpa [div_eq_mul_inv] using! h

/-- Reciprocal-prime partial sums with a real cutoff. -/
noncomputable def reciprocalPrimeSumReal (x : ℝ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)⁻¹

private lemma sum_Ioc_logWeighted_eq (x : ℝ) :
    ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p =
      logWeightedPrimeSum ⌊x⌋₊ := by
  rw [logWeightedPrimeSum]
  congr 2

private lemma sum_Icc_logWeighted_eq (x : ℝ) :
    ∑ p ∈ (Icc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p =
      logWeightedPrimeSum ⌊x⌋₊ := by
  rw [logWeightedPrimeSum]
  congr 1

/-- The Meissel-Mertens constant produced by the bounded first-error
integral. -/
noncomputable def reciprocalPrimeMertensConstant : ℝ :=
  (∫ t in Set.Ioi 2,
      logWeightedPrimeError t / (t * Real.log t ^ 2)) +
    1 - Real.log (Real.log 2)

/-- The continuous second Mertens error. -/
noncomputable def reciprocalPrimeMertensError (x : ℝ) : ℝ :=
  reciprocalPrimeSumReal x - Real.log (Real.log x) -
    reciprocalPrimeMertensConstant

/-- Exact tail-integral representation of the reciprocal-prime Mertens
error. -/
theorem reciprocalPrimeMertensError_eq {x : ℝ} (hx : 2 ≤ x) :
    reciprocalPrimeMertensError x =
      logWeightedPrimeError x / Real.log x -
        ∫ t in Set.Ioi x,
          logWeightedPrimeError t / (t * Real.log t ^ 2) := by
  unfold reciprocalPrimeMertensError reciprocalPrimeSumReal
  rw [sum_filter,
    ← sum_Ioc_one_eq_sum_Ioc_zero_aux (Nat.le_floor (by grind))
      (by simp [Nat.not_prime_one])]
  have hterm (n : ℕ) :
      (if n.Prime then (n : ℝ)⁻¹ else 0) =
        (if n.Prime then Real.log n / n else 0) / Real.log n := by
    split_ifs with hn
    · have hlog : Real.log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · simp
  simp_rw [hterm]
  rw [sum_div_log_eq hx,
    sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
      (by simp) (by simp), ← sum_filter, sum_Icc_logWeighted_eq]
  have hmain :
      ∫ t in 2..x,
          (∑ n ∈ Ioc 1 ⌊t⌋₊,
            if n.Prime then Real.log n / n else 0) /
              (t * Real.log t ^ 2) =
        ∫ t in 2..x,
          (1 / (t * Real.log t) +
            logWeightedPrimeError t / (t * Real.log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
      (by simp) (by simp), ← sum_filter, sum_Icc_logWeighted_eq]
    unfold logWeightedPrimeError
    field
  rw [hmain, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx,
      show logWeightedPrimeSum ⌊x⌋₊ =
        Real.log x + logWeightedPrimeError x by
          unfold logWeightedPrimeError
          ring,
      add_div,
      div_self (by simp; grind)]
    unfold reciprocalPrimeMertensConstant
    calc
      _ = logWeightedPrimeError x / Real.log x +
          (∫ t in 2..x,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) -
          (∫ t in Set.Ioi 2,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) := by ring
      _ = _ := by
        rw [← intervalIntegral.integral_interval_add_Ioi
          (integrable_logWeightedPrimeError_div_mul_log_sq (by rfl))
          (integrable_logWeightedPrimeError_div_mul_log_sq hx)]
        ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact (integrable_logWeightedPrimeError_div_mul_log_sq
      (x := 2) (by rfl)).mono (by grind) (by rfl)

/-- A concrete (not optimized) coefficient for the reciprocal-prime Mertens
error. -/
noncomputable def reciprocalPrimeMertensErrorConstant : ℝ :=
  2 * (Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant)

theorem reciprocalPrimeMertensErrorConstant_pos :
    0 < reciprocalPrimeMertensErrorConstant := by
  unfold reciprocalPrimeMertensErrorConstant
  positivity [nonprimeVonMangoldtConstant_nonneg]

/-- Unconditional reciprocal-prime Mertens estimate with an explicit formal
coefficient.  No prime number theorem is used. -/
theorem reciprocalPrimeMertensError_abs_le {x : ℝ} (hx : 2 ≤ x) :
    |reciprocalPrimeMertensError x| ≤
      reciprocalPrimeMertensErrorConstant / Real.log x := by
  let C := Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant
  have hC : 0 < C := by
    dsimp [C]
    positivity [nonprimeVonMangoldtConstant_nonneg]
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [reciprocalPrimeMertensError_eq hx, abs_le']
  constructor
  · have hE : logWeightedPrimeError x ≤ C := by
      simpa [C] using (abs_le.mp (logWeightedPrimeError_abs_le hx)).2
    have htail :
        ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2) ≥
          (-C) / Real.log x := calc
      _ ≥ ∫ t in Set.Ioi x, (-C) / (t * Real.log t ^ 2) := by
        apply setIntegral_mono_on
          (integrable_const_div_mul_log_sq (-C) hx)
          (integrable_logWeightedPrimeError_div_mul_log_sq hx)
          (by measurability)
        intro y hy
        simp only [Set.mem_Ioi] at hy
        have hden : 0 ≤ y * Real.log y ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ hden
        simpa [C] using (abs_le.mp
          (logWeightedPrimeError_abs_le (x := y) (by linarith))).1
      _ = _ := integral_const_div_mul_log_sq (-C) hx
    have hEdiv := div_le_div_of_nonneg_right hE hlog.le
    calc
      logWeightedPrimeError x / Real.log x -
          ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2) ≤
          C / Real.log x - (-C / Real.log x) :=
        sub_le_sub hEdiv htail
      _ = reciprocalPrimeMertensErrorConstant / Real.log x := by
        simp only [reciprocalPrimeMertensErrorConstant, C]
        ring
  · have hE : -C ≤ logWeightedPrimeError x := by
      simpa [C] using (abs_le.mp (logWeightedPrimeError_abs_le hx)).1
    have htail :
        ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2) ≤
          C / Real.log x := calc
      _ ≤ ∫ t in Set.Ioi x, C / (t * Real.log t ^ 2) := by
        apply setIntegral_mono_on
          (integrable_logWeightedPrimeError_div_mul_log_sq hx)
          (integrable_const_div_mul_log_sq C hx)
          (by measurability)
        intro y hy
        simp only [Set.mem_Ioi] at hy
        have hden : 0 ≤ y * Real.log y ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ hden
        simpa [C] using (abs_le.mp
          (logWeightedPrimeError_abs_le (x := y) (by linarith))).2
      _ = _ := integral_const_div_mul_log_sq C hx
    have hEdiv := div_le_div_of_nonneg_right hE hlog.le
    calc
      -(logWeightedPrimeError x / Real.log x -
          ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) =
          (∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) -
              logWeightedPrimeError x / Real.log x := by ring
      _ ≤ C / Real.log x - (-C / Real.log x) :=
        sub_le_sub htail hEdiv
      _ = reciprocalPrimeMertensErrorConstant / Real.log x := by
        simp only [reciprocalPrimeMertensErrorConstant, C]
        ring

theorem reciprocalPrimeSumReal_natCast (N : ℕ) :
    reciprocalPrimeSumReal (N : ℝ) = reciprocalPrimeSum N := by
  rw [reciprocalPrimeSumReal, reciprocalPrimeSum, Nat.floor_natCast,
    Nat.range_succ_eq_Icc_zero]
  congr 1

/-- Full unconditional closure of the reciprocal-prime analytic input, with a
non-optimized coefficient. -/
theorem mertensReciprocalPrimeInput : MertensReciprocalPrimeInput := by
  refine ⟨reciprocalPrimeMertensConstant,
    reciprocalPrimeMertensErrorConstant,
    reciprocalPrimeMertensErrorConstant_pos, ?_⟩
  intro N hN
  have h := reciprocalPrimeMertensError_abs_le
    (x := (N : ℝ)) (by exact_mod_cast (show 2 ≤ N by omega))
  unfold reciprocalPrimeMertensError at h
  rw [reciprocalPrimeSumReal_natCast] at h
  exact h

end Erdos730.FullDensity

end Campaign180File16

/- Source module: ErdosProblems.Erdos730.PrimeBands -/
section Campaign180File17
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: reciprocal-prime bands

This file isolates the Mertens component of the first-power argument.  It
contains no digit or Fourier counting: only reciprocal-prime sums over the
fixed-depth bands and over the transition band.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.FullDensity

/-- Lower endpoint `X^(1/(r+2))` of the depth-`r` prime band. -/
noncomputable def fixedDepthPrimeBandLower (r : ℕ) (X : ℝ) : ℝ :=
  X ^ (((r + 2 : ℕ) : ℝ)⁻¹)

/-- Upper endpoint `X^(1/(r+1))` of the depth-`r` prime band. -/
noncomputable def fixedDepthPrimeBandUpper (r : ℕ) (X : ℝ) : ℝ :=
  X ^ (((r + 1 : ℕ) : ℝ)⁻¹)

/-- Reciprocal-prime mass in the depth-`r` band.  The real-cutoff sum uses
natural floors, so this is exactly the sum over
`X^(1/(r+2)) < p ≤ X^(1/(r+1))`. -/
noncomputable def fixedDepthReciprocalPrimeBand (r : ℕ) (X : ℝ) : ℝ :=
  reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
    reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X)

/-- The limiting reciprocal-prime mass of the depth-`r` band. -/
noncomputable def fixedDepthPrimeBandMainTerm (r : ℕ) : ℝ :=
  Real.log (((r + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ))

lemma fixedDepthPrimeBandLower_pos (r : ℕ) {X : ℝ} (hX : 0 < X) :
    0 < fixedDepthPrimeBandLower r X := by
  exact Real.rpow_pos_of_pos hX _

lemma fixedDepthPrimeBandUpper_pos (r : ℕ) {X : ℝ} (hX : 0 < X) :
    0 < fixedDepthPrimeBandUpper r X := by
  exact Real.rpow_pos_of_pos hX _

lemma log_fixedDepthPrimeBandLower (r : ℕ) {X : ℝ} (hX : 0 < X) :
    Real.log (fixedDepthPrimeBandLower r X) =
      (((r + 2 : ℕ) : ℝ)⁻¹) * Real.log X := by
  exact Real.log_rpow hX _

lemma log_fixedDepthPrimeBandUpper (r : ℕ) {X : ℝ} (hX : 0 < X) :
    Real.log (fixedDepthPrimeBandUpper r X) =
      (((r + 1 : ℕ) : ℝ)⁻¹) * Real.log X := by
  exact Real.log_rpow hX _

lemma fixedDepthPrimeBandLower_le_upper (r : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    fixedDepthPrimeBandLower r X ≤ fixedDepthPrimeBandUpper r X := by
  apply Real.rpow_le_rpow_of_exponent_le hX
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  norm_num

/-- The logarithmic main terms telescope to the paper's band constant. -/
theorem fixedDepthPrimeBand_loglog_sub_eq (r : ℕ) {X : ℝ} (hX : 1 < X) :
    Real.log (Real.log (fixedDepthPrimeBandUpper r X)) -
        Real.log (Real.log (fixedDepthPrimeBandLower r X)) =
      fixedDepthPrimeBandMainTerm r := by
  rw [log_fixedDepthPrimeBandUpper r (zero_lt_one.trans hX),
    log_fixedDepthPrimeBandLower r (zero_lt_one.trans hX)]
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hr1 : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hr2 : (((r + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [← Real.log_div (mul_ne_zero (inv_ne_zero hr1) hlog)
    (mul_ne_zero (inv_ne_zero hr2) hlog)]
  unfold fixedDepthPrimeBandMainTerm
  congr 1
  field_simp

/-- Quantitative fixed-depth band estimate from an arbitrary reciprocal-prime
Mertens coefficient `C`.  The factor `2r+3` is the exact sum of the two
endpoint factors `r+1` and `r+2`. -/
theorem fixedDepthReciprocalPrimeBand_sub_main_abs_le_of_bound
    (r : ℕ) {M C X : ℝ} (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X)
    (hMertens : ∀ x : ℝ, 2 ≤ x →
      |reciprocalPrimeSumReal x - Real.log (Real.log x) - M| ≤
        C / Real.log x) :
    |fixedDepthReciprocalPrimeBand r X -
        fixedDepthPrimeBandMainTerm r| ≤
      C * (((2 * r + 3 : ℕ) : ℝ)) / Real.log X := by
  have hupper : 2 ≤ fixedDepthPrimeBandUpper r X :=
    hlower.trans (fixedDepthPrimeBandLower_le_upper r hX.le)
  have hlowError := hMertens (fixedDepthPrimeBandLower r X) hlower
  have huppError := hMertens (fixedDepthPrimeBandUpper r X) hupper
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hr1 : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hr2 : (((r + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hrewrite :
      fixedDepthReciprocalPrimeBand r X -
          fixedDepthPrimeBandMainTerm r =
        (reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
            Real.log (Real.log (fixedDepthPrimeBandUpper r X)) - M) -
          (reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X) -
            Real.log (Real.log (fixedDepthPrimeBandLower r X)) - M) := by
    unfold fixedDepthReciprocalPrimeBand
    rw [← fixedDepthPrimeBand_loglog_sub_eq r hX]
    ring
  rw [hrewrite]
  calc
    |(reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
          Real.log (Real.log (fixedDepthPrimeBandUpper r X)) - M) -
        (reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X) -
          Real.log (Real.log (fixedDepthPrimeBandLower r X)) - M)| ≤
        |reciprocalPrimeSumReal (fixedDepthPrimeBandUpper r X) -
          Real.log (Real.log (fixedDepthPrimeBandUpper r X)) - M| +
        |reciprocalPrimeSumReal (fixedDepthPrimeBandLower r X) -
          Real.log (Real.log (fixedDepthPrimeBandLower r X)) - M| :=
      abs_sub _ _
    _ ≤ C / Real.log (fixedDepthPrimeBandUpper r X) +
        C / Real.log (fixedDepthPrimeBandLower r X) :=
      add_le_add huppError hlowError
    _ = C * (((2 * r + 3 : ℕ) : ℝ)) / Real.log X := by
      rw [log_fixedDepthPrimeBandUpper r (zero_lt_one.trans hX),
        log_fixedDepthPrimeBandLower r (zero_lt_one.trans hX)]
      field_simp
      push_cast
      ring

/-- Uniform upper bound in the rounded form used in equation (44): replacing
the paper's numerical Mertens coefficient `4` by an arbitrary positive `C`
replaces `8(r+2)/log X` by `2C(r+2)/log X`. -/
theorem fixedDepthReciprocalPrimeBand_le_of_bound
    (r : ℕ) {M C X : ℝ} (hC : 0 ≤ C) (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X)
    (hMertens : ∀ x : ℝ, 2 ≤ x →
      |reciprocalPrimeSumReal x - Real.log (Real.log x) - M| ≤
        C / Real.log x) :
    fixedDepthReciprocalPrimeBand r X ≤
      fixedDepthPrimeBandMainTerm r +
        2 * C * (((r + 2 : ℕ) : ℝ)) / Real.log X := by
  have habs := fixedDepthReciprocalPrimeBand_sub_main_abs_le_of_bound
    r hX hlower hMertens
  have hsub := (le_abs_self
    (fixedDepthReciprocalPrimeBand r X -
      fixedDepthPrimeBandMainTerm r)).trans habs
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hcoeff :
      C * (((2 * r + 3 : ℕ) : ℝ)) / Real.log X ≤
        2 * C * (((r + 2 : ℕ) : ℝ)) / Real.log X := by
    apply div_le_div_of_nonneg_right _ hlog.le
    push_cast
    nlinarith
  linarith

/-- Unconditional quantitative form of the fixed-depth band estimate. -/
theorem fixedDepthReciprocalPrimeBand_le
    (r : ℕ) {X : ℝ} (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X) :
    fixedDepthReciprocalPrimeBand r X ≤
      fixedDepthPrimeBandMainTerm r +
        2 * reciprocalPrimeMertensErrorConstant *
          (((r + 2 : ℕ) : ℝ)) / Real.log X := by
  refine fixedDepthReciprocalPrimeBand_le_of_bound
    (M := reciprocalPrimeMertensConstant)
    (C := reciprocalPrimeMertensErrorConstant) r
    reciprocalPrimeMertensErrorConstant_pos.le hX hlower ?_
  intro x hx
  simpa only [reciprocalPrimeMertensError] using
    reciprocalPrimeMertensError_abs_le hx

/-- The Mertens error itself tends to zero. -/
theorem tendsto_reciprocalPrimeMertensError_atTop :
    Tendsto reciprocalPrimeMertensError atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    exact reciprocalPrimeMertensError_abs_le hX
  · simpa [div_eq_mul_inv] using
      Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul
        reciprocalPrimeMertensErrorConstant

/-- Fixed-depth Mertens component of equation (42). -/
theorem tendsto_fixedDepthReciprocalPrimeBand (r : ℕ) :
    Tendsto (fixedDepthReciprocalPrimeBand r) atTop
      (𝓝 (fixedDepthPrimeBandMainTerm r)) := by
  have hlowerTop : Tendsto (fixedDepthPrimeBandLower r) atTop atTop := by
    exact tendsto_rpow_atTop (by positivity)
  have hupperTop : Tendsto (fixedDepthPrimeBandUpper r) atTop atTop := by
    exact tendsto_rpow_atTop (by positivity)
  have hlowerError := tendsto_reciprocalPrimeMertensError_atTop.comp hlowerTop
  have hupperError := tendsto_reciprocalPrimeMertensError_atTop.comp hupperTop
  have hlim := (hupperError.sub hlowerError).add
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ ↦ fixedDepthPrimeBandMainTerm r) atTop
      (𝓝 (fixedDepthPrimeBandMainTerm r)))
  have hlim' : Tendsto
      (fun X : ℝ ↦
        reciprocalPrimeMertensError (fixedDepthPrimeBandUpper r X) -
          reciprocalPrimeMertensError (fixedDepthPrimeBandLower r X) +
            fixedDepthPrimeBandMainTerm r)
      atTop (𝓝 (fixedDepthPrimeBandMainTerm r)) := by
    simpa only [Function.comp_apply, sub_zero, zero_add] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  unfold fixedDepthReciprocalPrimeBand reciprocalPrimeMertensError
  rw [← fixedDepthPrimeBand_loglog_sub_eq r hX]
  ring

/-- Natural-parameter form of the fixed-depth band limit. -/
theorem tendsto_fixedDepthReciprocalPrimeBand_nat (r : ℕ) :
    Tendsto (fun X : ℕ ↦ fixedDepthReciprocalPrimeBand r (X : ℝ))
      atTop (𝓝 (fixedDepthPrimeBandMainTerm r)) :=
  (tendsto_fixedDepthReciprocalPrimeBand r).comp
    tendsto_natCast_atTop_atTop

/-! ## Transition band -/

/-- Lower endpoint `sqrt X` of the transition band. -/
noncomputable def transitionPrimeBandLower (X : ℝ) : ℝ :=
  Real.sqrt X

/-- Upper endpoint `Y = sqrt X * (log X)^2` of the transition band. -/
noncomputable def transitionPrimeBandUpper (X : ℝ) : ℝ :=
  Real.sqrt X * Real.log X ^ 2

/-- Reciprocal-prime mass in `sqrt X < p ≤ sqrt X * (log X)^2`. -/
noncomputable def transitionReciprocalPrimeBand (X : ℝ) : ℝ :=
  reciprocalPrimeSumReal (transitionPrimeBandUpper X) -
    reciprocalPrimeSumReal (transitionPrimeBandLower X)

lemma log_transitionPrimeBandLower {X : ℝ} (hX : 0 ≤ X) :
    Real.log (transitionPrimeBandLower X) = Real.log X / 2 := by
  exact Real.log_sqrt hX

lemma log_transitionPrimeBandUpper {X : ℝ} (hX : 1 < X) :
    Real.log (transitionPrimeBandUpper X) =
      Real.log X / 2 + 2 * Real.log (Real.log X) := by
  have hsqrt : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 (zero_lt_one.trans hX)).ne'
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  rw [transitionPrimeBandUpper, Real.log_mul hsqrt (pow_ne_zero 2 hlog),
    Real.log_sqrt (zero_lt_one.trans hX).le, Real.log_pow]
  norm_num

/-- Exact transition-band logarithmic ratio, stated in the eventual range
where both inner logarithms are positive. -/
theorem transitionPrimeBand_loglog_sub_eq {X : ℝ}
    (hX : Real.exp 1 < X) :
    Real.log (Real.log (transitionPrimeBandUpper X)) -
        Real.log (Real.log (transitionPrimeBandLower X)) =
      Real.log
        (1 + 4 * Real.log (Real.log X) / Real.log X) := by
  have hexp : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1))
  have hX1 : 1 < X := hexp.trans hX
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have honeLog : 1 < Real.log X := by
    apply Real.exp_lt_exp.mp
    simpa [Real.exp_log (zero_lt_one.trans hX1)] using hX
  have hlowerLog : 0 < Real.log (transitionPrimeBandLower X) := by
    rw [log_transitionPrimeBandLower (zero_lt_one.trans hX1).le]
    positivity
  have hupperLog : 0 < Real.log (transitionPrimeBandUpper X) := by
    rw [log_transitionPrimeBandUpper hX1]
    have hloglog : 0 < Real.log (Real.log X) := Real.log_pos honeLog
    positivity
  rw [← Real.log_div hupperLog.ne' hlowerLog.ne',
    log_transitionPrimeBandUpper hX1,
    log_transitionPrimeBandLower (zero_lt_one.trans hX1).le]
  congr 1
  field_simp [hlog.ne']
  ring

private theorem tendsto_log_log_div_log_atTop :
    Tendsto (fun X : ℝ ↦ Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) := by
  simpa using!
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      Real.tendsto_log_atTop

/-- The logarithmic main term of the transition band tends to zero. -/
theorem tendsto_transitionPrimeBand_loglog_sub :
    Tendsto (fun X : ℝ ↦
      Real.log (Real.log (transitionPrimeBandUpper X)) -
        Real.log (Real.log (transitionPrimeBandLower X)))
      atTop (𝓝 0) := by
  have hinside : Tendsto
      (fun X : ℝ ↦
        1 + 4 * Real.log (Real.log X) / Real.log X)
      atTop (𝓝 1) := by
    simpa only [mul_div_assoc, mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).add
        (tendsto_log_log_div_log_atTop.const_mul 4)
  have hlog : Tendsto
      (fun X : ℝ ↦
        Real.log (1 + 4 * Real.log (Real.log X) / Real.log X))
      atTop (𝓝 0) := by
    simpa using! (Real.continuousAt_log one_ne_zero).tendsto.comp hinside
  apply hlog.congr'
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with X hX
  exact (transitionPrimeBand_loglog_sub_eq hX).symm

/-- The reciprocal-prime transition band for
`Y = sqrt X * (log X)^2` has asymptotically zero mass. -/
theorem tendsto_transitionReciprocalPrimeBand :
    Tendsto transitionReciprocalPrimeBand atTop (𝓝 0) := by
  have hlowerTop : Tendsto transitionPrimeBandLower atTop atTop := by
    exact Real.tendsto_sqrt_atTop
  have hlogSqTop : Tendsto (fun X : ℝ ↦ Real.log X ^ 2)
      atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  have hupperTop : Tendsto transitionPrimeBandUpper atTop atTop := by
    exact hlowerTop.atTop_mul_atTop₀ hlogSqTop
  have hlowerError := tendsto_reciprocalPrimeMertensError_atTop.comp hlowerTop
  have hupperError := tendsto_reciprocalPrimeMertensError_atTop.comp hupperTop
  have hlim := (hupperError.sub hlowerError).add
    tendsto_transitionPrimeBand_loglog_sub
  have hlim' : Tendsto
      (fun X : ℝ ↦
        reciprocalPrimeMertensError (transitionPrimeBandUpper X) -
          reciprocalPrimeMertensError (transitionPrimeBandLower X) +
            (Real.log (Real.log (transitionPrimeBandUpper X)) -
              Real.log (Real.log (transitionPrimeBandLower X))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_zero, zero_add] using hlim
  apply hlim'.congr'
  filter_upwards with X
  unfold transitionReciprocalPrimeBand reciprocalPrimeMertensError
  ring

/-- Natural-parameter transition-band limit used by the counting argument. -/
theorem tendsto_transitionReciprocalPrimeBand_nat :
    Tendsto (fun X : ℕ ↦ transitionReciprocalPrimeBand (X : ℝ))
      atTop (𝓝 0) :=
  tendsto_transitionReciprocalPrimeBand.comp tendsto_natCast_atTop_atTop

end Erdos730.FullDensity

end Campaign180File17

/- Source module: ErdosProblems.Erdos730.TransitionDensity -/
section Campaign180File18
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: transition-range event count

This file closes the range
`sqrt X < p ≤ sqrt X * (log X)^2` for the exact local branch-event ledger.
The finite argument forgets the unique exact cofactor, counts at most one
root class per prime and branch, and then invokes the reciprocal-prime band
limit and the ordinary prime-counting consequence of PNT in modulus one.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.TransitionDensity

open BranchEvents DensityEvents FullDensityCore ConsecutiveTransition
open FullDensity

/-! ## Exact endpoints -/

/-- Natural upper cutoff `floor(sqrt X * (log X)^2)`. -/
noncomputable def transitionTopCut (X : ℕ) : ℕ :=
  ⌊transitionPrimeBandUpper (X : ℝ)⌋₊

/-- The primes in the exact transition interval. -/
noncomputable def transitionPrimeSet (X : ℕ) : Finset ℕ :=
  (Ioc (Nat.sqrt X) (transitionTopCut X)).filter Nat.Prime

/-! ## One root progression per branch and prime -/

def branchSlope : Branch → ℕ
  | .P => 222138
  | .Q => 380808
  | .R => 148092
  | .S => 380808

def branchOffset : Branch → ℕ
  | .P => 11
  | .Q => 13
  | .R => 5
  | .S => 19

theorem branchValue_eq_slope_mul_add (L : Branch) (x : ℕ) :
    branchValue L x = branchSlope L * x + branchOffset L := by
  cases L with
  | P => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).1
  | Q => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.1
  | R => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.1
  | S => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.2

theorem branchSlope_pos (L : Branch) : 0 < branchSlope L := by
  cases L <;> norm_num [branchSlope]

theorem branchSlope_le_max (L : Branch) : branchSlope L ≤ 380808 := by
  cases L <;> norm_num [branchSlope]

noncomputable def branchDivisibilityParameters
    (L : Branch) (p X : ℕ) : Finset ℕ :=
  (parameterRange X).filter fun x => p ∣ branchValue L x

theorem branchRoots_modEq
    {L : Branch} {p x y : ℕ} (hp : p.Prime)
    (hslope : branchSlope L < p)
    (hx : p ∣ branchValue L x) (hy : p ∣ branchValue L y) :
    x ≡ y [MOD p] := by
  have hvalues : branchValue L x ≡ branchValue L y [MOD p] :=
    hx.modEq_zero_nat.trans hy.modEq_zero_nat.symm
  rw [branchValue_eq_slope_mul_add, branchValue_eq_slope_mul_add] at hvalues
  have hmul : branchSlope L * x ≡ branchSlope L * y [MOD p] :=
    (Nat.ModEq.refl (branchOffset L)).add_right_cancel hvalues
  have hnot : ¬p ∣ branchSlope L :=
    Nat.not_dvd_of_pos_of_lt (branchSlope_pos L) hslope
  have hcop : Nat.Coprime p (branchSlope L) :=
    (hp.coprime_iff_not_dvd).2 hnot
  exact Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hmul

/-- A finite set contained in one residue class modulo `p` and in `[1,X]`
has at most `X/p+1` elements. -/
theorem card_le_div_add_one_of_modEq
    {S : Finset ℕ} {p v X : ℕ}
    (hbound : ∀ x ∈ S, x ≤ X)
    (hmod : ∀ x ∈ S, x ≡ v [MOD p]) :
    S.card ≤ X / p + 1 := by
  have hcard := Finset.card_le_card_of_injOn
    (fun x : ℕ => x / p)
    (s := S) (t := Finset.range (X / p + 1))
    (fun x hx => by
      simpa using Nat.lt_succ_of_le
        (Nat.div_le_div_right (hbound x hx)))
    (fun x hx y hy hdiv => by
      change x / p = y / p at hdiv
      have hxy : x ≡ y [MOD p] :=
        (hmod x hx).trans (hmod y hy).symm
      unfold Nat.ModEq at hxy
      calc
        x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
        _ = p * (y / p) + y % p := by rw [hdiv, hxy]
        _ = y := Nat.div_add_mod y p)
  simpa using hcard

theorem branchDivisibilityParameters_card_le
    {L : Branch} {p X : ℕ} (hp : p.Prime)
    (hslope : branchSlope L < p) :
    (branchDivisibilityParameters L p X).card ≤ X / p + 1 := by
  classical
  by_cases hempty : branchDivisibilityParameters L p X = ∅
  · simp [hempty]
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    apply card_le_div_add_one_of_modEq
    · intro x hx
      exact (mem_parameterRange.mp
        (Finset.mem_filter.mp hx).1).2
    · intro x hx
      exact branchRoots_modEq hp hslope
        (Finset.mem_filter.mp hx).2
        (Finset.mem_filter.mp hv).2

/-! ## Injecting transition witnesses into branch-prime-root triples -/

abbrev TransitionKey := Σ _L : Branch, Σ _p : ℕ, ℕ

def transitionWitnessKey (w : LocalBranchWitness) : TransitionKey :=
  ⟨localWitnessBranch w,
    ⟨localWitnessPrime w, localWitnessParameter w⟩⟩

noncomputable def transitionDivisibilityKeys (X : ℕ) : Finset TransitionKey :=
  (Finset.univ : Finset Branch).sigma fun L =>
    (transitionPrimeSet X).sigma fun p =>
      branchDivisibilityParameters L p X

theorem transitionWitnessKey_mapsTo (X : ℕ) :
    Set.MapsTo transitionWitnessKey
      (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X) (transitionTopCut X) :
        Set LocalBranchWitness)
      (transitionDivisibilityKeys X : Set TransitionKey) := by
  intro w hw
  change w ∈ localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
    (transitionTopCut X) at hw
  change transitionWitnessKey w ∈ transitionDivisibilityKeys X
  have htrans := Finset.mem_filter.mp hw
  have hlocal := mem_localBranchWitnessesUpTo.mp htrans.1
  rw [transitionDivisibilityKeys]
  simp only [transitionWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · rw [transitionPrimeSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨htrans.2.2.1, htrans.2.2.2⟩, hlocal.2.1⟩
  · rw [branchDivisibilityParameters, Finset.mem_filter]
    exact ⟨(mem_witnessBox.mp hlocal.1).1,
      prime_dvd_factor_of_exactPrimePowerCofactor hlocal.2.2.2.1⟩

theorem transitionWitnessKey_injOn (X : ℕ) :
    Set.InjOn transitionWitnessKey
      (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X) (transitionTopCut X) :
        Set LocalBranchWitness) := by
  rintro ⟨L, x, p, a, d⟩ hw ⟨K, y, q, b, e⟩ hv hkey
  simp only [transitionWitnessKey, localWitnessBranch, localWitnessPrime,
    localWitnessParameter, Sigma.mk.injEq] at hkey
  rcases hkey with ⟨rfl, rfl, rfl⟩
  have hwa := (Finset.mem_filter.mp hw).2.1
  have hvb := (Finset.mem_filter.mp hv).2.1
  change a = 1 at hwa
  change b = 1 at hvb
  subst a
  subst b
  have hwd := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.2.2.1.2.1
  have hve := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hv).1).2.2.2.1.2.1
  change branchValue L x = p ^ 1 * d at hwd
  change branchValue L x = p ^ 1 * e at hve
  have hp : 0 < p := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.1.pos
  have hde : d = e := by
    apply Nat.mul_left_cancel (pow_pos hp 1)
    rw [← hwd, ← hve]
  subst e
  rfl

theorem transitionWitnesses_card_le_keys (X : ℕ) :
    (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card ≤
        (transitionDivisibilityKeys X).card :=
  Finset.card_le_card_of_injOn transitionWitnessKey
    (transitionWitnessKey_mapsTo X) (transitionWitnessKey_injOn X)

theorem transitionDivisibilityKeys_card (X : ℕ) :
    (transitionDivisibilityKeys X).card =
      ∑ L : Branch, ∑ p ∈ transitionPrimeSet X,
        (branchDivisibilityParameters L p X).card := by
  simp [transitionDivisibilityKeys, Finset.card_sigma]

/-- Exact finite transition count before casting to the analytic bound. -/
theorem transitionWitnesses_card_le_sum (X : ℕ)
    (hroot : 380808 ≤ Nat.sqrt X) :
    (localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card ≤
        4 * ∑ p ∈ transitionPrimeSet X, (X / p + 1) := by
  calc
    _ ≤ (transitionDivisibilityKeys X).card :=
      transitionWitnesses_card_le_keys X
    _ = ∑ L : Branch, ∑ p ∈ transitionPrimeSet X,
        (branchDivisibilityParameters L p X).card :=
      transitionDivisibilityKeys_card X
    _ ≤ ∑ _L : Branch, ∑ p ∈ transitionPrimeSet X,
        (X / p + 1) := by
      apply Finset.sum_le_sum
      intro L _hL
      apply Finset.sum_le_sum
      intro p hp
      have hpMem := Finset.mem_filter.mp hp
      exact branchDivisibilityParameters_card_le hpMem.2
        ((branchSlope_le_max L).trans_lt
          (hroot.trans_lt (Finset.mem_Ioc.mp hpMem.1).1))
    _ = _ := by
      have hcard : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
      norm_num

/-! ## Reciprocal-prime mass of the exact natural interval -/

noncomputable def transitionPrimeMass (X : ℕ) : ℝ :=
  ∑ p ∈ transitionPrimeSet X, (p : ℝ)⁻¹

theorem transitionPrimeMass_eq_band {X : ℕ}
    (hcut : Nat.sqrt X ≤ transitionTopCut X) :
    transitionPrimeMass X = transitionReciprocalPrimeBand (X : ℝ) := by
  have hdis : Disjoint
      ((Ioc 0 (Nat.sqrt X)).filter Nat.Prime)
      ((Ioc (Nat.sqrt X) (transitionTopCut X)).filter Nat.Prime) :=
    Finset.disjoint_filter_filter
      (Finset.Ioc_disjoint_Ioc_of_le (le_refl (Nat.sqrt X)))
  have hunion :
      (Ioc 0 (Nat.sqrt X)).filter Nat.Prime ∪
          (Ioc (Nat.sqrt X) (transitionTopCut X)).filter Nat.Prime =
        (Ioc 0 (transitionTopCut X)).filter Nat.Prime := by
    rw [← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hcut]
  have hsum := Finset.sum_union hdis
    (f := fun p : ℕ ↦ (p : ℝ)⁻¹)
  rw [hunion] at hsum
  unfold transitionPrimeMass transitionPrimeSet
  rw [transitionReciprocalPrimeBand, reciprocalPrimeSumReal,
    reciprocalPrimeSumReal, transitionPrimeBandLower, transitionTopCut,
    Real.nat_floor_real_sqrt_eq_nat_sqrt]
  unfold transitionTopCut at hsum
  linarith

theorem eventually_sqrt_le_transitionTopCut :
    ∀ᶠ X : ℕ in atTop, Nat.sqrt X ≤ transitionTopCut X := by
  filter_upwards [eventually_ge_atTop 3] with X hX
  rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
  apply Nat.floor_mono
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hexp : Real.exp 1 < (X : ℝ) :=
    Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
  have hlog : 1 < Real.log (X : ℝ) := by
    apply Real.exp_lt_exp.mp
    simpa [Real.exp_log hXpos] using hexp
  have hsqrt : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  unfold transitionPrimeBandUpper
  nlinarith [sq_nonneg (Real.log (X : ℝ) - 1)]

theorem tendsto_transitionPrimeMass :
    Tendsto transitionPrimeMass atTop (𝓝 0) := by
  apply tendsto_transitionReciprocalPrimeBand_nat.congr'
  filter_upwards [eventually_sqrt_le_transitionTopCut] with X hcut
  exact (transitionPrimeMass_eq_band hcut).symm

/-! ## Real form of the finite event bound -/

theorem transitionWitnesses_cast_card_le (X : ℕ)
    (hroot : 380808 ≤ Nat.sqrt X) :
    ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card : ℝ) ≤
        4 * ((X : ℝ) * transitionPrimeMass X +
          (transitionPrimeSet X).card) := by
  have hnat := transitionWitnesses_card_le_sum X hroot
  calc
    ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
      (transitionTopCut X)).card : ℝ) ≤
        ((4 * ∑ p ∈ transitionPrimeSet X, (X / p + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = 4 * ∑ p ∈ transitionPrimeSet X,
        (((X / p + 1 : ℕ) : ℝ)) := by push_cast; ring
    _ ≤ 4 * ∑ p ∈ transitionPrimeSet X,
        ((X : ℝ) / (p : ℝ) + 1) := by
      gcongr with p hp
      simpa only [Nat.cast_add, Nat.cast_one] using
        add_le_add (Nat.cast_div_le (m := X) (n := p) (α := ℝ)) le_rfl
    _ = 4 * ((X : ℝ) * transitionPrimeMass X +
        (transitionPrimeSet X).card) := by
      unfold transitionPrimeMass
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

theorem normalized_transitionWitnesses_le (X : ℕ)
    (hX : 0 < X) (hroot : 380808 ≤ Nat.sqrt X) :
    ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
        (transitionTopCut X)).card : ℝ) / (X : ℝ) ≤
      4 * transitionPrimeMass X +
        4 * (transitionPrimeSet X).card / (X : ℝ) := by
  calc
    _ ≤ (4 * ((X : ℝ) * transitionPrimeMass X +
        (transitionPrimeSet X).card)) / (X : ℝ) :=
      div_le_div_of_nonneg_right (transitionWitnesses_cast_card_le X hroot)
        (Nat.cast_nonneg X)
    _ = _ := by
      have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
      field_simp

/-! ## The prime-counting endpoint term -/

theorem tendsto_transitionPrimeBandUpper_atTop :
    Tendsto transitionPrimeBandUpper atTop atTop := by
  have hlogSq : Tendsto (fun X : ℝ ↦ Real.log X ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  exact Real.tendsto_sqrt_atTop.atTop_mul_atTop₀ hlogSq

theorem tendsto_transitionPrimeBandUpper_nat_atTop :
    Tendsto (fun X : ℕ ↦ transitionPrimeBandUpper (X : ℝ))
      atTop atTop :=
  tendsto_transitionPrimeBandUpper_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_transitionPrimeBandUpper_div :
    Tendsto (fun X : ℝ ↦ transitionPrimeBandUpper X / X)
      atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun X : ℝ ↦ Real.log (Real.sqrt X) ^ 2 / Real.sqrt X)
      atTop (𝓝 0) := by
    simpa using!
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
        Real.tendsto_sqrt_atTop
  have hscaled : Tendsto
      (fun X : ℝ ↦
        4 * (Real.log (Real.sqrt X) ^ 2 / Real.sqrt X))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul 4
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hsqrt0 : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 hX).ne'
  unfold transitionPrimeBandUpper
  rw [Real.log_sqrt hX.le]
  field_simp
  nlinarith [Real.sq_sqrt hX.le]

theorem tendsto_transitionPrimeBandUpper_div_nat :
    Tendsto (fun X : ℕ ↦
      transitionPrimeBandUpper (X : ℝ) / (X : ℝ))
      atTop (𝓝 0) :=
  tendsto_transitionPrimeBandUpper_div.comp tendsto_natCast_atTop_atTop

private theorem tendsto_transitionPrimeCounting_normalized :
    Tendsto (fun X : ℕ ↦
      primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) /
        (transitionPrimeBandUpper (X : ℝ) /
          Real.log (transitionPrimeBandUpper (X : ℝ))))
      atTop (𝓝 1) := by
  have h := (primeAPCountingReal_normalized_tendsto
    (A := 1) (a := 0) (by norm_num) (by norm_num) (by norm_num)).comp
      tendsto_transitionPrimeBandUpper_nat_atTop
  simpa using! h

private theorem tendsto_transitionPNTScale :
    Tendsto (fun X : ℕ ↦
      (transitionPrimeBandUpper (X : ℝ) /
        Real.log (transitionPrimeBandUpper (X : ℝ))) / (X : ℝ))
      atTop (𝓝 0) := by
  have hinvLog : Tendsto (fun X : ℕ ↦
      (Real.log (transitionPrimeBandUpper (X : ℝ)))⁻¹)
      atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp
      tendsto_transitionPrimeBandUpper_nat_atTop).inv_tendsto_atTop
  have hmul := tendsto_transitionPrimeBandUpper_div_nat.mul hinvLog
  have hmul' : Tendsto (fun X : ℕ ↦
      (transitionPrimeBandUpper (X : ℝ) / (X : ℝ)) *
        (Real.log (transitionPrimeBandUpper (X : ℝ)))⁻¹)
      atTop (𝓝 0) := by simpa using hmul
  apply hmul'.congr'
  exact Eventually.of_forall fun X ↦ by ring

theorem tendsto_transitionPrimeCounting_div :
    Tendsto (fun X : ℕ ↦
      primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hprod := tendsto_transitionPrimeCounting_normalized.mul
    tendsto_transitionPNTScale
  have hprod' : Tendsto (fun X : ℕ ↦
      (primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) /
        (transitionPrimeBandUpper (X : ℝ) /
          Real.log (transitionPrimeBandUpper (X : ℝ)))) *
      ((transitionPrimeBandUpper (X : ℝ) /
        Real.log (transitionPrimeBandUpper (X : ℝ))) / (X : ℝ)))
      atTop (𝓝 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards
      [tendsto_transitionPrimeBandUpper_nat_atTop.eventually_gt_atTop
        (Real.exp 1), eventually_gt_atTop (0 : ℕ)] with X hupper hX
  have hu0 : transitionPrimeBandUpper (X : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.exp_pos 1 |>.trans hupper)
  have hlog0 : Real.log (transitionPrimeBandUpper (X : ℝ)) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact Real.exp_pos 1 |>.trans hupper
    · linarith [Real.exp_one_gt_two]
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  field_simp

theorem transitionPrimeSet_card_le_primeCounting (X : ℕ) :
    ((transitionPrimeSet X).card : ℝ) ≤
      primeAPCountingReal 1 0 (transitionPrimeBandUpper (X : ℝ)) := by
  unfold primeAPCountingReal
  norm_cast
  apply Finset.card_le_card
  intro p hp
  rw [transitionPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨Nat.zero_le p, ?_⟩, hp.2, Nat.mod_one p⟩
  simpa [transitionTopCut] using hp.1.2

theorem tendsto_transitionPrimeSet_card_div :
    Tendsto (fun X : ℕ ↦
      ((transitionPrimeSet X).card : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ by positivity
  · exact Eventually.of_forall fun X ↦
      div_le_div_of_nonneg_right
        (transitionPrimeSet_card_le_primeCounting X) (Nat.cast_nonneg X)
  · exact tendsto_transitionPrimeCounting_div

/-! ## Transition density closure -/

/-- The normalized exact transition-range local witness count. -/
noncomputable def normalizedTransitionWitnessCount (X : ℕ) : ℝ :=
  ((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
    (transitionTopCut X)).card : ℝ) / (X : ℝ)

/-- The transition-range contribution is `o(X)`. -/
theorem tendsto_normalizedTransitionWitnessCount :
    Tendsto normalizedTransitionWitnessCount atTop (𝓝 0) := by
  have hmajorant : Tendsto (fun X : ℕ ↦
      4 * transitionPrimeMass X +
        4 * (transitionPrimeSet X).card / (X : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, mul_div_assoc] using
      (tendsto_transitionPrimeMass.const_mul 4).add
        (tendsto_transitionPrimeSet_card_div.const_mul 4)
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ by
      unfold normalizedTransitionWitnessCount
      positivity
  · filter_upwards
      [eventually_ge_atTop (380808 * 380808)] with X hX
    unfold normalizedTransitionWitnessCount
    apply normalized_transitionWitnesses_le X
    · omega
    · exact Nat.le_sqrt.mpr hX
  · exact hmajorant

end Erdos730.TransitionDensity

end Campaign180File18

/- Source module: ErdosProblems.Erdos730.FullDensityBudget -/
section Campaign180File19
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: exact logarithmic density budget

This module formalizes the final infinite-series and rational-arithmetic
certificate in the proposed positive-density proof of Erdős 730.  It does not
formalize the preceding analytic counting argument; its sole input is the
explicit series appearing in that argument.
-/

namespace Erdos730

/-- The rational function used to majorize
`log ((1+x)/(1-x))` on `0 < x < 1`. -/
noncomputable def atanhLogUpper (x : ℝ) : ℝ :=
  2 * (x + x ^ 3 / 3) + 2 * x ^ 5 / (5 * (1 - x ^ 2))

/-- Equation (123): a strict, completely explicit upper bound for the
logarithmic ratio. -/
theorem log_one_add_div_one_sub_lt_atanhLogUpper
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) < atanhLogUpper x := by
  let f : ℕ → ℝ := fun k ↦
    2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1)
  let g : ℕ → ℝ := fun k ↦
    (2 / 5) * x ^ 5 * (x ^ 2) ^ k
  have habs : |x| < 1 := by simpa [abs_of_pos hx0] using hx1
  have hf : HasSum f (Real.log (1 + x) - Real.log (1 - x)) := by
    simpa [f, Nat.cast_add, Nat.cast_mul] using
      (Real.hasSum_log_sub_log_of_abs_lt_one habs)
  have hratio :
      Real.log ((1 + x) / (1 - x)) =
        Real.log (1 + x) - Real.log (1 - x) := by
    rw [Real.log_div (by linarith) (by linarith)]
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0.le).2 hx1
  have hgeom : Summable (fun k : ℕ ↦ (x ^ 2) ^ k) :=
    summable_geometric_of_lt_one hx2_nonneg hx2_lt
  have hg : Summable g := (hgeom.mul_left ((2 / 5) * x ^ 5))
  have hpow (k : ℕ) : x ^ (2 * (k + 2) + 1) = x ^ 5 * (x ^ 2) ^ k := by
    rw [show 2 * (k + 2) + 1 = 5 + 2 * k by omega, pow_add, pow_mul]
  have hle (k : ℕ) : f (k + 2) ≤ g k := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hden : (5 : ℝ) ≤ 2 * (k : ℝ) + 5 := by linarith
    have hinv : 1 / (2 * (k : ℝ) + 5) ≤ (1 : ℝ) / 5 := by
      exact one_div_le_one_div_of_le (by norm_num) hden
    dsimp only [f, g]
    rw [show 2 * ((k + 2 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 5 by
      push_cast
      ring, hpow]
    have hxpow : 0 ≤ x ^ 5 := (pow_nonneg hx0.le 5)
    have hxgeom : 0 ≤ (x ^ 2) ^ k := pow_nonneg hx2_nonneg k
    calc
      2 * (1 / (2 * (k : ℝ) + 5)) * (x ^ 5 * (x ^ 2) ^ k) ≤
          2 * ((1 : ℝ) / 5) * (x ^ 5 * (x ^ 2) ^ k) := by
        gcongr
      _ = 2 / 5 * x ^ 5 * (x ^ 2) ^ k := by ring
  have hlt : f (1 + 2) < g 1 := by
    dsimp only [f, g]
    rw [show 2 * ((1 + 2 : ℕ) : ℝ) + 1 = 7 by norm_num, hpow]
    have hx5 : 0 < x ^ 5 := pow_pos hx0 5
    have hx2 : 0 < x ^ 2 := pow_pos hx0 2
    norm_num
    nlinarith [mul_pos hx5 hx2]
  have htail : (∑' k : ℕ, f (k + 2)) < ∑' k : ℕ, g k := by
    exact Summable.tsum_lt_tsum hle hlt
      ((summable_nat_add_iff 2).2 hf.summable) hg
  have hsplit := hf.summable.sum_add_tsum_nat_add 2
  have hg_sum :
      (∑' k : ℕ, g k) = (2 / 5) * x ^ 5 / (1 - x ^ 2) := by
    rw [show (∑' k : ℕ, g k) = (2 / 5) * x ^ 5 *
        (∑' k : ℕ, (x ^ 2) ^ k) by
      simp only [g, tsum_mul_left]]
    rw [tsum_geometric_of_lt_one hx2_nonneg hx2_lt]
    field_simp
  rw [hg_sum] at htail
  have hhead :
      (∑ k ∈ Finset.range 2, f k) = 2 * x + 2 * x ^ 3 / 3 := by
    norm_num [f, Finset.sum_range_succ]
    ring
  calc
    Real.log ((1 + x) / (1 - x)) =
        (∑ k ∈ Finset.range 2, f k) + ∑' k : ℕ, f (k + 2) := by
      rw [hratio, ← hf.tsum_eq, hsplit]
    _ < (2 * x + 2 * x ^ 3 / 3) +
        (2 / 5) * x ^ 5 / (1 - x ^ 2) := by
      rw [hhead]
      linarith
    _ = atanhLogUpper x := by
      rw [atanhLogUpper]
      field_simp

/-- Equation (124), written as a specialization of `atanhLogUpper`. -/
noncomputable def U (d : ℕ) : ℝ := atanhLogUpper (1 / (d : ℝ))

/-- Equation (125). -/
theorem log_succ_div_pred_lt_U {d : ℕ} (hd : 3 ≤ d) :
    Real.log (((d + 1 : ℕ) : ℝ) / (d - 1 : ℕ)) < U d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hx0 : (0 : ℝ) < 1 / d := one_div_pos.mpr hd0
  have hx1 : (1 : ℝ) / d < 1 := (div_lt_one hd0).2 (by linarith)
  have h := log_one_add_div_one_sub_lt_atanhLogUpper hx0 hx1
  have hd1 : 1 ≤ d := by omega
  have hratio :
      (((d + 1 : ℕ) : ℝ) / (d - 1 : ℕ)) =
        (1 + 1 / (d : ℝ)) / (1 - 1 / (d : ℝ)) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hd1, Nat.cast_one]
    field_simp
  rw [hratio, U]
  exact h

/-! ## Exact specializations of the logarithmic majorant -/

theorem U_three : U 3 = (1123 : ℝ) / 1620 := by
  norm_num [U, atanhLogUpper]

theorem U_five : U 5 = (3041 : ℝ) / 7500 := by
  norm_num [U, atanhLogUpper]

theorem U_seven : U 7 = (3947 : ℝ) / 13720 := by
  norm_num [U, atanhLogUpper]

theorem U_nine : U 9 = (97603 : ℝ) / 437400 := by
  norm_num [U, atanhLogUpper]

theorem U_eleven : U 11 = (24267 : ℝ) / 133100 := by
  norm_num [U, atanhLogUpper]

theorem U_thirteen : U 13 = (142241 : ℝ) / 922740 := by
  norm_num [U, atanhLogUpper]

theorem U_fifteen : U 15 = (757123 : ℝ) / 5670000 := by
  norm_num [U, atanhLogUpper]

/-- The logarithm in the `r`th density-series term is the specialization
`d = 2r+3` of equation (125). -/
theorem log_density_ratio_lt_U (r : ℕ) :
    Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) < U (2 * r + 3) := by
  have h := log_succ_div_pred_lt_U (d := 2 * r + 3) (by omega)
  convert h using 1
  congr 1
  push_cast
  field_simp
  ring

/-! ## The infinite density series -/

/-- The `r=0` term is set to zero, so this is exactly the series over
integers `r >= 1` from equation (103). -/
noncomputable def densityBudgetTerm (r : ℕ) : ℝ :=
  if r = 0 then 0
  else (1 / 4 : ℝ) ^ r * Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ))

/-- The series `S` in the density budget. -/
noncomputable def densityBudgetSeries : ℝ :=
  ∑' r : ℕ, densityBudgetTerm r

theorem densityBudgetTerm_nonneg (r : ℕ) : 0 ≤ densityBudgetTerm r := by
  by_cases hr : r = 0
  · simp [densityBudgetTerm, hr]
  · have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
    have hratio : (1 : ℝ) ≤ (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) := by
      rw [le_div_iff₀ hden]
      push_cast
      linarith
    simp only [densityBudgetTerm, hr, if_false]
    exact mul_nonneg (pow_nonneg (by norm_num) r) (Real.log_nonneg hratio)

/-- The elementary upper bound `log ((r+2)/(r+1)) <= 1/(r+1)`. -/
theorem log_density_ratio_le_inv_succ (r : ℕ) :
    Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤ 1 / (r + 1 : ℕ) := by
  have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hpos : (0 : ℝ) < (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) := by positivity
  calc
    Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤
        (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) - 1 :=
      Real.log_le_sub_one_of_pos hpos
    _ = 1 / (r + 1 : ℕ) := by
      field_simp
      push_cast
      ring

theorem densityBudgetTerm_le_geometric (r : ℕ) :
    densityBudgetTerm r ≤ (1 / 4 : ℝ) ^ r := by
  by_cases hr : r = 0
  · simp [densityBudgetTerm, hr]
  · have hlog := log_density_ratio_le_inv_succ r
    have hinv : (1 : ℝ) / (r + 1 : ℕ) ≤ 1 := by
      rw [div_le_one]
      · norm_num
      · positivity
    simp only [densityBudgetTerm, hr, if_false]
    calc
      (1 / 4 : ℝ) ^ r *
          Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤
          (1 / 4 : ℝ) ^ r * 1 := by
        gcongr
        exact hlog.trans hinv
      _ = (1 / 4 : ℝ) ^ r := mul_one _

theorem densityBudgetTerm_summable : Summable densityBudgetTerm := by
  exact Summable.of_nonneg_of_le densityBudgetTerm_nonneg
    densityBudgetTerm_le_geometric
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- For `r >= 7`, the logarithm is at most `1/8`. -/
theorem densityBudgetTerm_le_eighth_geometric {r : ℕ} (hr : 7 ≤ r) :
    densityBudgetTerm r ≤ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ r := by
  have hr0 : r ≠ 0 := by omega
  have hden : (8 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast (show 8 ≤ r + 1 by omega)
  have hinv : (1 : ℝ) / (r + 1 : ℕ) ≤ 1 / 8 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hlog :
      Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤ 1 / 8 :=
    (log_density_ratio_le_inv_succ r).trans hinv
  simp only [densityBudgetTerm, hr0, if_false]
  calc
    (1 / 4 : ℝ) ^ r *
        Real.log (((r + 2 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤
        (1 / 4 : ℝ) ^ r * (1 / 8) := by
      gcongr
    _ = (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ r := by ring

/-- Equation (126): the entire tail beginning at `r=7`. -/
theorem densityBudget_tail_le :
    (∑' n : ℕ, densityBudgetTerm (n + 7)) ≤ (1 : ℝ) / 98304 := by
  let g : ℕ → ℝ := fun n ↦ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ (n + 7)
  have hg : HasSum g ((1 : ℝ) / 98304) := by
    have hgeom := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    have hscaled := hgeom.mul_left ((1 / 8 : ℝ) * (1 / 4 : ℝ) ^ 7)
    have hfun : g = fun i ↦ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ 7 * (1 / 4 : ℝ) ^ i := by
      funext n
      simp only [g, pow_add]
      ring
    have hval : (1 : ℝ) / 98304 = (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ 7 * (1 - 1 / 4)⁻¹ := by
      norm_num
    rw [hfun, hval]
    exact hscaled
  calc
    (∑' n : ℕ, densityBudgetTerm (n + 7)) ≤ ∑' n : ℕ, g n := by
      exact ((summable_nat_add_iff 7).2 densityBudgetTerm_summable).tsum_le_tsum
        (fun n ↦ densityBudgetTerm_le_eighth_geometric (by omega)) hg.summable
    _ = (1 : ℝ) / 98304 := hg.tsum_eq

/-- The finite majorant used for indices `0,...,6`. -/
noncomputable def densityBudgetFiniteMajorant (r : ℕ) : ℝ :=
  if r = 0 then 0 else (1 / 4 : ℝ) ^ r * U (2 * r + 3)

theorem densityBudgetTerm_le_finiteMajorant (r : ℕ) :
    densityBudgetTerm r ≤ densityBudgetFiniteMajorant r := by
  by_cases hr : r = 0
  · simp [densityBudgetTerm, densityBudgetFiniteMajorant, hr]
  · simp only [densityBudgetTerm, densityBudgetFiniteMajorant, hr, if_false]
    exact (mul_lt_mul_of_pos_left (log_density_ratio_lt_U r)
      (pow_pos (by norm_num) r)).le

theorem densityBudgetTerm_one_lt_finiteMajorant :
    densityBudgetTerm 1 < densityBudgetFiniteMajorant 1 := by
  simp only [densityBudgetTerm, densityBudgetFiniteMajorant, one_ne_zero, if_false]
  exact mul_lt_mul_of_pos_left (log_density_ratio_lt_U 1) (by norm_num)

/-- The exact rational evaluation of the six finite majorants together with
the geometric tail. -/
theorem densityBudget_finite_and_tail_certificate :
    (∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r) + (1 : ℝ) / 98304 =
      (11117760449158646497 : ℝ) / 89848527388139520000 := by
  norm_num [densityBudgetFiniteMajorant, U, atanhLogUpper, Finset.sum_range_succ]

/-- Equation (127): the exact strict upper bound for the series `S`. -/
theorem densityBudgetSeries_lt_certificate :
    densityBudgetSeries <
      (11117760449158646497 : ℝ) / 89848527388139520000 := by
  have hfinite :
      (∑ r ∈ Finset.range 7, densityBudgetTerm r) <
        ∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r := by
    exact Finset.sum_lt_sum
      (fun r _ ↦ densityBudgetTerm_le_finiteMajorant r)
      ⟨1, by simp, densityBudgetTerm_one_lt_finiteMajorant⟩
  have hsplit := densityBudgetTerm_summable.sum_add_tsum_nat_add 7
  rw [densityBudgetSeries, ← hsplit]
  calc
    (∑ r ∈ Finset.range 7, densityBudgetTerm r) +
        ∑' n : ℕ, densityBudgetTerm (n + 7) <
        (∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r) +
          ∑' n : ℕ, densityBudgetTerm (n + 7) := by
      gcongr
    _ ≤ (∑ r ∈ Finset.range 7, densityBudgetFiniteMajorant r) +
          (1 : ℝ) / 98304 := by
      gcongr
      exact densityBudget_tail_le
    _ = (11117760449158646497 : ℝ) / 89848527388139520000 :=
      densityBudget_finite_and_tail_certificate

/-! ## Final exact density budget -/

/-- Equation (128): the same logarithmic majorant at `d=3` bounds `log 2`. -/
theorem log_two_lt_U_three : Real.log 2 < U 3 := by
  have h := log_succ_div_pred_lt_U (d := 3) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Exact evaluation of the two rational upper bounds in equation (129). -/
theorem densityBudget_total_upper_identity :
    4 * ((11117760449158646497 : ℝ) / 89848527388139520000) +
        (2 / 3) * ((1123 : ℝ) / 1620) =
      (21498408212212214497 : ℝ) / 22462131847034880000 := by
  norm_num

/-- Equation (129), including both strict analytic inequalities. -/
theorem densityBudget_total_lt_exact :
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 <
      (21498408212212214497 : ℝ) / 22462131847034880000 := by
  have hS := densityBudgetSeries_lt_certificate
  have hlog : Real.log 2 < (1123 : ℝ) / 1620 := by
    rw [← U_three]
    exact log_two_lt_U_three
  calc
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 <
        4 * ((11117760449158646497 : ℝ) / 89848527388139520000) +
          (2 / 3) * ((1123 : ℝ) / 1620) := by
      nlinarith
    _ = (21498408212212214497 : ℝ) / 22462131847034880000 :=
      densityBudget_total_upper_identity

/-- Equation (130): the target-minus-certificate difference, exactly. -/
theorem densityBudget_target_difference :
    (2393 : ℝ) / 2500 -
        (21498408212212214497 : ℝ) / 22462131847034880000 =
      (2344391769572639 : ℝ) / 22462131847034880000 := by
  norm_num

/-- Equation (121): the final logarithmic-series budget is below `2393/2500`. -/
theorem densityBudget_final_lt :
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 < (2393 : ℝ) / 2500 := by
  exact densityBudget_total_lt_exact.trans (by norm_num)

end Erdos730

end Campaign180File19

/- Source module: ErdosProblems.Erdos730.PositiveDensityBridge -/
section Campaign180File20
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: positive lower density implies the upstream infinitude target

This module contains only the general density-to-infinitude bridge.  It does
not assume or claim the analytic positive-density estimate for the explicit
four-linear-form family.
-/

open Filter
open scoped Topology

namespace Erdos730.FullDensity

/-- Number of parameters in `[1, X]` satisfying `good`. -/
def parameterCount (good : ℕ → Prop) [DecidablePred good] (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter good).card

/-- The exact positive-density surface claimed by the supplied proof, with a
generic parameter predicate. -/
def HasCandidatePositiveDensity (good : ℕ → Prop) [DecidablePred good] : Prop :=
  (107 : ℝ) / 2500 <
    liminf (fun X : ℕ => (parameterCount good X : ℝ) / X) atTop

/-- A positive lower density at the candidate's explicit constant forces
infinitely many good parameters. -/
theorem parameterSet_infinite_of_candidatePositiveDensity
    (good : ℕ → Prop) [DecidablePred good]
    (h : HasCandidatePositiveDensity good) :
    Set.Infinite {x : ℕ | good x} := by
  intro hfinite
  let C : ℕ := hfinite.toFinset.card
  have hcount (X : ℕ) : parameterCount good X ≤ C := by
    simp only [parameterCount, C]
    exact Finset.card_le_card (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx
      simpa using hx.2)
  have hbounded : IsBoundedUnder (· ≥ ·) atTop
      (fun X : ℕ => (parameterCount good X : ℝ) / X) := by
    change ∃ b : ℝ, ∀ᶠ X : ℕ in atTop,
      b ≤ (parameterCount good X : ℝ) / X
    refine ⟨0, Eventually.of_forall (fun X : ℕ => ?_)⟩
    exact div_nonneg (by positivity : (0 : ℝ) ≤ parameterCount good X)
      (by positivity : (0 : ℝ) ≤ X)
  have hevent : ∀ᶠ X : ℕ in atTop,
      (107 : ℝ) / 2500 < (parameterCount good X : ℝ) / X :=
    eventually_lt_of_lt_liminf h hbounded
  have hlarge : ∀ᶠ X : ℕ in atTop, C * 2500 < 107 * X := by
    exact eventually_atTop.2 ⟨C * 2500 + 1, fun X hX => by omega⟩
  obtain ⟨X, hratio, hCX, hX⟩ :=
    (hevent.and (hlarge.and (eventually_gt_atTop 0))).exists
  have hcast : (parameterCount good X : ℝ) ≤ C := by
    exact_mod_cast hcount X
  have hden : (0 : ℝ) < X := by
    exact_mod_cast hX
  have hupper : (parameterCount good X : ℝ) / X ≤ C / X :=
    div_le_div_of_nonneg_right hcast hden.le
  have hsmall : (C : ℝ) / X < (107 : ℝ) / 2500 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2500)]
    exact_mod_cast hCX
  linarith

/-- If an injective explicit family maps every good parameter into a target
set, the candidate positive-density estimate proves that target infinite. -/
theorem target_infinite_of_candidatePositiveDensity
    (good : ℕ → Prop) [DecidablePred good]
    {α : Type*} (family : ℕ → α) (target : Set α)
    (h : HasCandidatePositiveDensity good)
    (hinj : Function.Injective family)
    (hmaps : ∀ x, good x → family x ∈ target) :
    target.Infinite := by
  have hgood : Set.Infinite {x : ℕ | good x} :=
    parameterSet_infinite_of_candidatePositiveDensity good h
  have himage : Set.Infinite (family '' {x : ℕ | good x}) :=
    hgood.image hinj.injOn
  exact himage.mono (by
    rintro y ⟨x, hx, rfl⟩
    exact hmaps x hx)


end Erdos730.FullDensity

end Campaign180File20

/- Source module: ErdosProblems.Erdos730.DensityAssembly -/
section Campaign180File21
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: final limsup-to-positive-density assembly

This file is independent of the four analytic range estimates.  It proves
that the strict numerical budget for the normalized bad-event count implies
the exact `107/2500` lower-density claim used by the upstream infinitude
bridge.
-/

open Filter
open scoped Topology

namespace Erdos730
namespace DensityAssembly

open DensityEvents FullDensityCore

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ ↦ Classical.propDecidable _

/-- Normalized finite bad-parameter count. -/
def badDensity (X : ℕ) : ℝ :=
  ((badParametersUpTo X).card : ℝ) / (X : ℝ)

/-- Normalized finite good-parameter count. -/
def goodDensity (X : ℕ) : ℝ :=
  ((goodParametersUpTo X).card : ℝ) / (X : ℝ)

theorem badParameters_card_le (X : ℕ) :
    (badParametersUpTo X).card ≤ X := by
  calc
    (badParametersUpTo X).card ≤ (parameterRange X).card :=
      Finset.card_le_card (by
        intro x hx
        exact (mem_badParametersUpTo.mp hx).1)
    _ = X := parameterRange_card X

theorem badDensity_nonneg (X : ℕ) : 0 ≤ badDensity X := by
  unfold badDensity
  positivity

theorem badDensity_le_one (X : ℕ) : badDensity X ≤ 1 := by
  by_cases hX : X = 0
  · subst X
    simp [badDensity]
  · rw [badDensity, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hX)]
    exact_mod_cast badParameters_card_le X

theorem badDensity_isBoundedUnder_le :
    IsBoundedUnder (· ≤ ·) atTop badDensity := by
  exact isBoundedUnder_of ⟨1, badDensity_le_one⟩

theorem badDensity_isCoboundedUnder_le :
    IsCoboundedUnder (· ≤ ·) atTop badDensity := by
  exact isCoboundedUnder_le_of_le atTop badDensity_nonneg

/-- Exact finite complement identity away from the harmless endpoint `X=0`. -/
theorem goodDensity_eq_one_sub_badDensity {X : ℕ} (hX : 0 < X) :
    goodDensity X = 1 - badDensity X := by
  have hsum := good_card_add_bad_card X
  have hsumR : ((goodParametersUpTo X).card : ℝ) +
      ((badParametersUpTo X).card : ℝ) = (X : ℝ) := by
    exact_mod_cast hsum
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  unfold goodDensity badDensity
  field_simp [hXR]
  linarith [hsumR]

/-- The lower density of good parameters is exactly one minus the upper
density of bad parameters. -/
theorem liminf_goodDensity_eq_one_sub_limsup_badDensity :
    liminf goodDensity atTop = 1 - limsup badDensity atTop := by
  rw [liminf_congr ((eventually_gt_atTop (0 : ℕ)).mono fun X hX ↦
    goodDensity_eq_one_sub_badDensity hX),
    liminf_const_sub atTop badDensity 1 badDensity_isBoundedUnder_le
      badDensity_isCoboundedUnder_le]

theorem parameterCount_eq_good_card (X : ℕ) :
    FullDensity.parameterCount GoodParameter X = (goodParametersUpTo X).card := by
  rfl

/-- Any bad-density limsup within the paper's analytic budget proves the
exact candidate positive-density statement. -/
theorem hasCandidatePositiveDensity_of_limsup_bad_le
    (hbad : limsup badDensity atTop ≤
      4 * densityBudgetSeries + (2 / 3) * Real.log 2) :
    FullDensity.HasCandidatePositiveDensity GoodParameter := by
  unfold FullDensity.HasCandidatePositiveDensity
  simp_rw [parameterCount_eq_good_card]
  change (107 : ℝ) / 2500 < liminf goodDensity atTop
  rw [liminf_goodDensity_eq_one_sub_limsup_badDensity]
  have hbudget := densityBudget_final_lt
  linarith


end

end DensityAssembly
end Erdos730

end Campaign180File21

/- Source module: ErdosProblems.Erdos730.RangeAssembly -/
section Campaign180File22
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: assembly of the four analytic ranges

This file contains only the finite four-range union bound and the topology
needed to add the four normalized estimates.  In particular, the hypotheses
of `limsup_badDensity_le_budget_of_range_estimates` are the concrete
higher-power, small-prime, and top-prime estimates, not a restatement of the
headline density claim.
-/

open Filter
open scoped Topology

namespace Erdos730
namespace RangeAssembly

open BranchEvents DensityAssembly DensityEvents FullDensityCore
  TransitionDensity

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ ↦ Classical.propDecidable _

/-- Normalized count of local witnesses with exponent at least two. -/
def normalizedHigherPowerWitnessCount (X : ℕ) : ℝ :=
  ((localHigherPowerWitnessesUpTo X).card : ℝ) / (X : ℝ)

/-- Normalized count of first-power witnesses with `p ≤ sqrt X`. -/
def normalizedSmallPrimeWitnessCount (X : ℕ) : ℝ :=
  ((localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card : ℝ) / (X : ℝ)

/-- Normalized count of first-power witnesses above the transition cutoff. -/
def normalizedTopPrimeWitnessCount (X : ℕ) : ℝ :=
  ((localTopPrimeWitnessesUpTo X (transitionTopCut X)).card : ℝ) / (X : ℝ)

/-- The exact normalized sum of the four disjoint local ranges. -/
def normalizedFourRangeCount (X : ℕ) : ℝ :=
  normalizedHigherPowerWitnessCount X +
    (normalizedSmallPrimeWitnessCount X +
      (normalizedTransitionWitnessCount X +
        normalizedTopPrimeWitnessCount X))

theorem normalizedHigherPowerWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedHigherPowerWitnessCount X := by
  unfold normalizedHigherPowerWitnessCount
  positivity

theorem normalizedSmallPrimeWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedSmallPrimeWitnessCount X := by
  unfold normalizedSmallPrimeWitnessCount
  positivity

theorem normalizedTransitionWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedTransitionWitnessCount X := by
  unfold normalizedTransitionWitnessCount
  positivity

theorem normalizedTopPrimeWitnessCount_nonneg (X : ℕ) :
    0 ≤ normalizedTopPrimeWitnessCount X := by
  unfold normalizedTopPrimeWitnessCount
  positivity

theorem normalizedFourRangeCount_nonneg (X : ℕ) :
    0 ≤ normalizedFourRangeCount X := by
  unfold normalizedFourRangeCount
  exact add_nonneg (normalizedHigherPowerWitnessCount_nonneg X)
    (add_nonneg (normalizedSmallPrimeWitnessCount_nonneg X)
      (add_nonneg (normalizedTransitionWitnessCount_nonneg X)
        (normalizedTopPrimeWitnessCount_nonneg X)))

/-- The exact finite ledger inequality once the two moving cutoffs are in
their natural order. -/
theorem badDensity_le_normalizedFourRangeCount
    (X : ℕ) (hcut : Nat.sqrt X ≤ transitionTopCut X) :
    badDensity X ≤ normalizedFourRangeCount X := by
  have hcard := bad_card_le_localBranchWitnesses_card X
  rw [localBranchWitnesses_card_fourRange X (Nat.sqrt X)
    (transitionTopCut X) hcut] at hcard
  unfold badDensity normalizedFourRangeCount
  unfold normalizedHigherPowerWitnessCount normalizedSmallPrimeWitnessCount
    normalizedTransitionWitnessCount normalizedTopPrimeWitnessCount
  have hcast :
      ((badParametersUpTo X).card : ℝ) ≤
        ((localHigherPowerWitnessesUpTo X).card : ℝ) +
          (((localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card : ℝ) +
            (((localTransitionPrimeWitnessesUpTo X (Nat.sqrt X)
              (transitionTopCut X)).card : ℝ) +
              ((localTopPrimeWitnessesUpTo X
                (transitionTopCut X)).card : ℝ))) := by
    exact_mod_cast hcard
  simpa only [add_div] using
    (div_le_div_of_nonneg_right hcast (Nat.cast_nonneg X))

theorem eventually_badDensity_le_normalizedFourRangeCount :
    badDensity ≤ᶠ[atTop] normalizedFourRangeCount := by
  filter_upwards [eventually_sqrt_le_transitionTopCut] with X hcut
  exact badDensity_le_normalizedFourRangeCount X hcut

/-- The vanishing higher-power and transition ranges plus the two bounded
limsup estimates imply the paper's complete bad-density budget. -/
theorem limsup_badDensity_le_budget_of_range_estimates
    (hhigher : Tendsto normalizedHigherPowerWitnessCount atTop (𝓝 0))
    (hsmallBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount)
    (hsmall : limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries)
    (htopBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedTopPrimeWitnessCount)
    (htop : limsup normalizedTopPrimeWitnessCount atTop ≤
      (2 / 3) * Real.log 2) :
    limsup badDensity atTop ≤
      4 * densityBudgetSeries + (2 / 3) * Real.log 2 := by
  let vanishing : ℕ → ℝ := fun X ↦
    normalizedHigherPowerWitnessCount X +
      normalizedTransitionWitnessCount X
  let principal : ℕ → ℝ := fun X ↦
    normalizedSmallPrimeWitnessCount X +
      normalizedTopPrimeWitnessCount X
  have hvanishing : Tendsto vanishing atTop (𝓝 0) := by
    simpa only [vanishing, zero_add] using
      hhigher.add tendsto_normalizedTransitionWitnessCount
  have hsmallCob :
      IsCoboundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount :=
    isCoboundedUnder_le_of_le atTop normalizedSmallPrimeWitnessCount_nonneg
  have hsmallLower :
      IsBoundedUnder (· ≥ ·) atTop normalizedSmallPrimeWitnessCount := by
    exact isBoundedUnder_of
      ⟨0, normalizedSmallPrimeWitnessCount_nonneg⟩
  have htopCob :
      IsCoboundedUnder (· ≤ ·) atTop normalizedTopPrimeWitnessCount :=
    isCoboundedUnder_le_of_le atTop normalizedTopPrimeWitnessCount_nonneg
  have htopLower :
      IsBoundedUnder (· ≥ ·) atTop normalizedTopPrimeWitnessCount := by
    exact isBoundedUnder_of
      ⟨0, normalizedTopPrimeWitnessCount_nonneg⟩
  have hprincipalBdd : IsBoundedUnder (· ≤ ·) atTop principal := by
    simpa only [principal] using! isBoundedUnder_le_add hsmallBdd htopBdd
  have hprincipalCob : IsCoboundedUnder (· ≤ ·) atTop principal := by
    exact isCoboundedUnder_le_of_le atTop fun X ↦ by
      dsimp only [principal]
      exact add_nonneg (normalizedSmallPrimeWitnessCount_nonneg X)
        (normalizedTopPrimeWitnessCount_nonneg X)
  have hprincipal : limsup principal atTop ≤
      4 * densityBudgetSeries + (2 / 3) * Real.log 2 := by
    calc
      limsup principal atTop ≤
          limsup normalizedSmallPrimeWitnessCount atTop +
            limsup normalizedTopPrimeWitnessCount atTop := by
        simpa only [principal] using!
          (limsup_add_le (f := atTop)
            (u := normalizedSmallPrimeWitnessCount)
            (v := normalizedTopPrimeWitnessCount)
            (h₁ := hsmallLower) (h₂ := hsmallBdd)
            (h₃ := htopCob) (h₄ := htopBdd))
      _ ≤ 4 * densityBudgetSeries + (2 / 3) * Real.log 2 :=
        add_le_add hsmall htop
  have hrangeBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedFourRangeCount := by
    unfold normalizedFourRangeCount
    exact isBoundedUnder_le_add hhigher.isBoundedUnder_le
      (isBoundedUnder_le_add hsmallBdd
        (isBoundedUnder_le_add
          tendsto_normalizedTransitionWitnessCount.isBoundedUnder_le htopBdd))
  have hbadToRange := limsup_le_limsup
    eventually_badDensity_le_normalizedFourRangeCount
    badDensity_isCoboundedUnder_le hrangeBdd
  calc
    limsup badDensity atTop ≤ limsup normalizedFourRangeCount atTop :=
      hbadToRange
    _ = limsup (vanishing + principal) atTop := by
      apply limsup_congr
      exact Eventually.of_forall fun X ↦ by
        dsimp only [vanishing, principal]
        unfold normalizedFourRangeCount
        change normalizedHigherPowerWitnessCount X +
            (normalizedSmallPrimeWitnessCount X +
              (normalizedTransitionWitnessCount X +
                normalizedTopPrimeWitnessCount X)) =
          (normalizedHigherPowerWitnessCount X +
              normalizedTransitionWitnessCount X) +
            (normalizedSmallPrimeWitnessCount X +
              normalizedTopPrimeWitnessCount X)
        ring
    _ ≤ limsup vanishing atTop + limsup principal atTop := by
      exact limsup_add_le (f := atTop) (u := vanishing) (v := principal)
        (h₁ := hvanishing.isBoundedUnder_ge)
        (h₂ := hvanishing.isBoundedUnder_le)
        (h₃ := hprincipalCob) (h₄ := hprincipalBdd)
    _ ≤ 4 * densityBudgetSeries + (2 / 3) * Real.log 2 := by
      rw [hvanishing.limsup_eq, zero_add]
      exact hprincipal

/-- Once the three remaining concrete range estimates are supplied, the
existing exact numerical certificate yields positive lower density. -/
theorem hasCandidatePositiveDensity_of_range_estimates
    (hhigher : Tendsto normalizedHigherPowerWitnessCount atTop (𝓝 0))
    (hsmallBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount)
    (hsmall : limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries)
    (htopBdd :
      IsBoundedUnder (· ≤ ·) atTop normalizedTopPrimeWitnessCount)
    (htop : limsup normalizedTopPrimeWitnessCount atTop ≤
      (2 / 3) * Real.log 2) :
    FullDensity.HasCandidatePositiveDensity GoodParameter := by
  exact hasCandidatePositiveDensity_of_limsup_bad_le
    (limsup_badDensity_le_budget_of_range_estimates
      hhigher hsmallBdd hsmall htopBdd htop)


end

end RangeAssembly
end Erdos730

end Campaign180File22

/- Source module: ErdosProblems.Erdos730.DivisorSwitching -/
section Campaign180File23
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: top-range divisor switching

This module implements the top-prime classification and the ensuing
fixed-modulus divisor switch for the exact local branch events.
-/

open Filter Finset MeasureTheory
open scoped Topology Chebyshev

namespace Erdos730
namespace DivisorSwitching

open BranchEvents ConsecutiveTransition FullDensityCore KummerTransition
open FullDensity

noncomputable section

def globalBranchBound : ℕ := 380827

def topPrimeScale (X : ℝ) : ℝ :=
  Real.sqrt X * Real.log X ^ 2

def topPrimeCut (X : ℕ) : ℕ :=
  ⌊topPrimeScale X⌋₊

def branchSlope : Branch → ℕ
  | .P => 222138
  | .Q => 380808
  | .R => 148092
  | .S => 380808

def branchIntercept : Branch → ℕ
  | .P => 11
  | .Q => 13
  | .R => 5
  | .S => 19

theorem branchValue_eq_slope_mul_add (L : Branch) (x : ℕ) :
    branchValue L x = branchSlope L * x + branchIntercept L := by
  cases L <;> simp [branchValue, branchSlope, branchIntercept,
    branch_expansions]

theorem branchValue_le_globalBranchBound_mul
    {L : Branch} {x X : ℕ} (hX : 1 ≤ X) (hx : x ≤ X) :
    branchValue L x ≤ globalBranchBound * X := by
  rw [branchValue_eq_slope_mul_add]
  cases L <;> simp only [branchSlope, branchIntercept, globalBranchBound] <;>
    nlinarith

/-- Finite-threshold hypothesis needed by the top digit calculation. -/
def TopCutoffHypothesis (X : ℕ) : Prop :=
  130 * globalBranchBound * X < topPrimeCut X ^ 2

theorem top_ratio_and_square
    {L : Branch} {X x p c : ℕ}
    (hX : 1 ≤ X) (hx : x ≤ X)
    (hcut : TopCutoffHypothesis X)
    (hpCut : topPrimeCut X < p)
    (hbranch : branchValue L x = p * c) :
    130 * c < p ∧ branchValue L x < p ^ 2 := by
  have hL := branchValue_le_globalBranchBound_mul hX hx (L := L)
  have hpSq : topPrimeCut X ^ 2 < p ^ 2 := by nlinarith
  have h130L : 130 * branchValue L x < p ^ 2 := by
    calc
      130 * branchValue L x ≤ 130 * (globalBranchBound * X) :=
        Nat.mul_le_mul_left 130 hL
      _ < topPrimeCut X ^ 2 := by
        simpa [TopCutoffHypothesis, mul_assoc] using hcut
      _ < p ^ 2 := hpSq
  constructor
  · rw [hbranch] at h130L
    have hp0 : 0 < p := by omega
    nlinarith
  · exact (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 130)).trans_lt h130L

lemma cofactor_pos_of_exact_one {p c N : ℕ}
    (hp : p.Prime) (h : ExactPrimePowerCofactor p 1 c N) : 0 < c := by
  rcases h with ⟨_, hN, hpc⟩
  apply Nat.pos_of_ne_zero
  rintro rfl
  exact hpc (dvd_zero p)

lemma least_digit_lower_half
    {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : 0 < t) (hlow : LowerHalfDigits p t) :
    2 * (t % p) ≤ p - 1 := by
  have hdigit : t % p ∈ p.digits t := by
    rw [Nat.digits_eq_cons_digits_div hp.one_lt ht.ne']
    simp
  have h := hlow (t % p) hdigit
  have hpodd := hp.odd_of_ne_two hp2
  have hhalf := two_mul_paperHalf_add_one hpodd
  omega

lemma branchTestValue_pos
    {L : Branch} {x p c : ℕ}
    (hlocal : LocalBranchObstruction L x p 1 c) :
    0 < branchTestValue L x c := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hc := cofactor_pos_of_exact_one hp hexact
  cases L with
  | P =>
      simp only [branchTestValue]
      exact mul_pos hc (branches_positive x).2.1
  | Q =>
      simp only [branchTestValue]
      exact mul_pos hc (branches_positive x).1
  | R =>
      simp only [branchTestValue]
      have hS := (branches_positive x).2.2.2
      have hlarge : 2 < 3 * c * S x := by nlinarith
      omega
  | S =>
      simp only [branchTestValue]
      have hR := (branches_positive x).2.2.1
      have hlarge : 2 < 3 * c * FullDensityCore.R x := by nlinarith
      omega

lemma P_branch_test_cleared {x p c : ℕ}
    (hbranch : P x = p * c) :
    7 * branchTestValue .P x c + 41 * c = 12 * p * c ^ 2 := by
  simp only [branchTestValue]
  have hid := identity_PQ x
  nlinarith

lemma Q_branch_test_cleared {x p c : ℕ}
    (hbranch : Q x = p * c) :
    12 * branchTestValue .Q x c = 7 * p * c ^ 2 + 41 * c := by
  simp only [branchTestValue]
  have hid := identity_PQ x
  nlinarith

lemma R_branch_test_cleared {x p c : ℕ}
    (hbranch : FullDensityCore.R x = p * c) :
    14 * branchTestValue .R x c + 7 =
      54 * p * c ^ 2 + 129 * c := by
  simp only [branchTestValue]
  have hRodd : Odd (FullDensityCore.R x) := by
    refine ⟨14 * T * x + 2, ?_⟩
    simp only [FullDensityCore.R]
    ring
  have hcodd : Odd c := by
    have hprod : Odd (p * c) := hbranch ▸ hRodd
    exact (Nat.odd_mul.mp hprod).2
  have hSodd : Odd (FullDensityCore.S x) := by
    refine ⟨36 * T * x + 9, ?_⟩
    simp only [FullDensityCore.S]
    ring
  have hnum : 2 * ((3 * c * FullDensityCore.S x - 1) / 2) =
      3 * c * FullDensityCore.S x - 1 := by
    rcases hcodd with ⟨u, rfl⟩
    rcases hSodd with ⟨v, hv⟩
    rw [hv]
    have hprod : 3 * (2 * u + 1) * (2 * v + 1) =
        2 * (6 * u * v + 3 * u + 3 * v + 1) + 1 := by ring
    rw [hprod]
    simp
  have hcpos : 0 < c := by
    by_contra hc
    have : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    exact (Nat.ne_of_gt (branches_positive x).2.2.1) hbranch
  have hone : 2 * branchTestValue .R x c + 1 =
      3 * c * FullDensityCore.S x := by
    simp only [branchTestValue]
    have hpos : 0 < 3 * c * FullDensityCore.S x :=
      mul_pos (mul_pos (by norm_num) hcpos) (branches_positive x).2.2.2
    omega
  have hid := identity_RS x
  calc
    14 * branchTestValue .R x c + 7 =
        7 * (2 * branchTestValue .R x c + 1) := by ring
    _ = 7 * (3 * c * FullDensityCore.S x) := by rw [hone]
    _ = 3 * c * (7 * FullDensityCore.S x) := by ring
    _ = 3 * c * (18 * FullDensityCore.R x + 43) := by rw [hid]
    _ = 54 * p * c ^ 2 + 129 * c := by rw [hbranch]; ring

lemma S_branch_test_cleared {x p c : ℕ}
    (hbranch : FullDensityCore.S x = p * c) :
    12 * branchTestValue .S x c + 43 * c + 6 =
      7 * p * c ^ 2 := by
  simp only [branchTestValue]
  have hSodd : Odd (FullDensityCore.S x) := by
    refine ⟨36 * T * x + 9, ?_⟩
    simp only [FullDensityCore.S]
    ring
  have hcodd : Odd c := by
    have hprod : Odd (p * c) := hbranch ▸ hSodd
    exact (Nat.odd_mul.mp hprod).2
  have hRodd : Odd (FullDensityCore.R x) := by
    refine ⟨14 * T * x + 2, ?_⟩
    simp only [FullDensityCore.R]
    ring
  have hnum : 2 * ((3 * c * FullDensityCore.R x - 1) / 2) =
      3 * c * FullDensityCore.R x - 1 := by
    rcases hcodd with ⟨u, rfl⟩
    rcases hRodd with ⟨v, hv⟩
    rw [hv]
    have hprod : 3 * (2 * u + 1) * (2 * v + 1) =
        2 * (6 * u * v + 3 * u + 3 * v + 1) + 1 := by ring
    rw [hprod]
    simp
  have hcpos : 0 < c := by
    by_contra hc
    have : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    exact (Nat.ne_of_gt (branches_positive x).2.2.2) hbranch
  have hone : 2 * branchTestValue .S x c + 1 =
      3 * c * FullDensityCore.R x := by
    simp only [branchTestValue]
    have hpos : 0 < 3 * c * FullDensityCore.R x :=
      mul_pos (mul_pos (by norm_num) hcpos) (branches_positive x).2.2.1
    omega
  have hid := identity_RS x
  calc
    12 * branchTestValue .S x c + 43 * c + 6 =
        6 * (2 * branchTestValue .S x c + 1) + 43 * c := by ring
    _ = 6 * (3 * c * FullDensityCore.R x) + 43 * c := by
      rw [hone]
    _ = c * (18 * FullDensityCore.R x + 43) := by ring
    _ = c * (7 * FullDensityCore.S x) := by rw [hid]
    _ = 7 * p * c ^ 2 := by rw [hbranch]; ring

lemma coprime_mod_left {c m : ℕ} (hc : c.Coprime m) :
    (c % m).Coprime m := by
  rw [Nat.Coprime] at hc ⊢
  rw [Nat.gcd_comm] at hc
  rwa [Nat.gcd_rec] at hc

lemma P_branch_coprime_seven {x p c : ℕ}
    (hbranch : P x = p * c) : c.Coprime 7 := by
  have hPcop : (P x).Coprime 7 := by
    have hmod := (branch_mod_7_fixed x).1
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c) (k := P x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hPcop

lemma Q_branch_coprime_twelve {x p c : ℕ}
    (hbranch : Q x = p * c) : c.Coprime 12 := by
  have hQmod : Q x % 12 = 1 := by
    simp only [Q, T]
    omega
  have hQcop : (Q x).Coprime 12 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hQmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c) (k := Q x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hQcop

lemma R_branch_coprime_fourteen {x p c : ℕ}
    (hbranch : FullDensityCore.R x = p * c) : c.Coprime 14 := by
  have hRmod : FullDensityCore.R x % 14 = 5 := by
    simp only [FullDensityCore.R, T]
    omega
  have hRcop : (FullDensityCore.R x).Coprime 14 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hRmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c)
      (k := FullDensityCore.R x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hRcop

lemma S_branch_coprime_twelve {x p c : ℕ}
    (hbranch : FullDensityCore.S x = p * c) : c.Coprime 12 := by
  have hSmod : FullDensityCore.S x % 12 = 7 := by
    simp only [FullDensityCore.S, T]
    omega
  have hScop : (FullDensityCore.S x).Coprime 12 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hSmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c)
      (k := FullDensityCore.S x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hScop

/-- Exact top classification on the P branch. -/
theorem P_top_local_classification
    {x p c : ℕ} (hlocal : LocalBranchObstruction .P x p 1 c)
    (hratio : 130 * c < p) : c % 7 = 3 ∨ c % 7 = 4 := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : P x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .P x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have hdlt : d < p := Nat.mod_lt _ hp0
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := P_branch_test_cleared hbranch
  have hclearZ :
      (7 : ℤ) * t + 41 * c = 12 * p * (c : ℤ) ^ 2 := by
    exact_mod_cast hclear
  have hrdef :
      ((7 * d + 41 * c : ℕ) : ℤ) =
        (p : ℤ) * (12 * (c : ℤ) ^ 2 - 7 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 12 * (c : ℤ) ^ 2 - 7 * (k : ℤ)
  have hrEq : ((7 * d + 41 * c : ℕ) : ℤ) = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrpos : 0 < r := by
    have hleft : 0 < (7 * d + 41 * c : ℕ) := by omega
    push_cast at hleft
    nlinarith
  have hrlt : r < 4 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    push_cast at hhalf' hratio
    nlinarith
  have hcop := coprime_mod_left (P_branch_coprime_seven hbranch)
  have hcnot : c % 7 ≠ 0 := by
    intro hc0
    rw [Nat.Coprime, hc0] at hcop
    norm_num at hcop
  have hcmodlt : c % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 12 * (c : ℤ) ^ 2 - 7 * (k : ℤ) := rfl
  have hrcong : r ≡ 12 * (c : ℤ) ^ 2 [ZMOD 7] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 7 : ℕ) : ℤ) [ZMOD 7] := by
    exact_mod_cast (Nat.mod_modEq c 7).symm
  have hrsmallcong :
      r ≡ 12 * (((c % 7 : ℕ) : ℤ) ^ 2) [ZMOD 7] :=
    hrcong.trans ((hccong.pow 2).mul_left 12)
  interval_cases hcm : c % 7 <;>
    norm_num [Int.ModEq, hcm] at hrsmallcong ⊢ <;> omega

/-- The Q branch has no exponent-one local obstruction in the top range. -/
theorem Q_top_local_impossible
    {x p c : ℕ} (hlocal : LocalBranchObstruction .Q x p 1 c)
    (hratio : 130 * c < p) : False := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : Q x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .Q x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := Q_branch_test_cleared hbranch
  have hclearZ :
      (12 : ℤ) * t = 7 * p * (c : ℤ) ^ 2 + 41 * c := by
    exact_mod_cast hclear
  have hrdef :
      (12 : ℤ) * d - 41 * c =
        (p : ℤ) * (7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)
  have hrEq : (12 : ℤ) * d - 41 * c = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrnonneg : 0 ≤ r := by
    push_cast at hratio
    have hlower : -(p : ℤ) < (12 : ℤ) * d - 41 * c := by nlinarith
    nlinarith
  have hrlt : r < 6 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    push_cast at hhalf' hratio
    nlinarith
  have hremod : r % 12 = r :=
    Int.emod_eq_of_lt hrnonneg (by omega)
  have hcop := coprime_mod_left (Q_branch_coprime_twelve hbranch)
  have hcmodlt : c % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ) := rfl
  have hrcong : r ≡ 7 * (c : ℤ) ^ 2 [ZMOD 12] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 12 : ℕ) : ℤ) [ZMOD 12] := by
    exact_mod_cast (Nat.mod_modEq c 12).symm
  have hrsmallcong :
      r ≡ 7 * (((c % 12 : ℕ) : ℤ) ^ 2) [ZMOD 12] :=
    hrcong.trans ((hccong.pow 2).mul_left 7)
  interval_cases hcm : c % 12
  all_goals norm_num [Nat.Coprime, hcm] at hcop
  all_goals norm_num [Int.ModEq, hcm, hremod] at hrsmallcong
  all_goals omega

/-- Exact top classification on the R branch. -/
theorem R_top_local_classification
    {x p c : ℕ} (hlocal : LocalBranchObstruction .R x p 1 c)
    (hratio : 130 * c < p) : c % 14 = 5 ∨ c % 14 = 9 := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : FullDensityCore.R x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .R x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := R_branch_test_cleared hbranch
  have hclearZ :
      (14 : ℤ) * t + 7 = 54 * p * (c : ℤ) ^ 2 + 129 * c := by
    exact_mod_cast hclear
  have hrdef :
      (14 : ℤ) * d + 7 - 129 * c =
        (p : ℤ) * (54 * (c : ℤ) ^ 2 - 14 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 54 * (c : ℤ) ^ 2 - 14 * (k : ℤ)
  have hrEq :
      (14 : ℤ) * d + 7 - 129 * c = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrnonneg : 0 ≤ r := by
    push_cast at hratio
    have hlower : -(p : ℤ) < (14 : ℤ) * d + 7 - 129 * c := by
      nlinarith
    nlinarith
  have hrlt : r < 7 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    push_cast at hhalf' hratio
    nlinarith
  have hremod : r % 14 = r :=
    Int.emod_eq_of_lt hrnonneg (by omega)
  have hcop := coprime_mod_left (R_branch_coprime_fourteen hbranch)
  have hcmodlt : c % 14 < 14 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 54 * (c : ℤ) ^ 2 - 14 * (k : ℤ) := rfl
  have hrcong : r ≡ 54 * (c : ℤ) ^ 2 [ZMOD 14] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 14 : ℕ) : ℤ) [ZMOD 14] := by
    exact_mod_cast (Nat.mod_modEq c 14).symm
  have hrsmallcong :
      r ≡ 54 * (((c % 14 : ℕ) : ℤ) ^ 2) [ZMOD 14] :=
    hrcong.trans ((hccong.pow 2).mul_left 54)
  interval_cases hcm : c % 14
  all_goals norm_num [Nat.Coprime, hcm] at hcop
  all_goals norm_num [Int.ModEq, hcm, hremod] at hrsmallcong
  all_goals omega

/-- The S branch has no exponent-one local obstruction in the top range. -/
theorem S_top_local_impossible
    {x p c : ℕ} (hlocal : LocalBranchObstruction .S x p 1 c)
    (hratio : 130 * c < p) : False := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : FullDensityCore.S x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .S x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := S_branch_test_cleared hbranch
  have hclearZ :
      (12 : ℤ) * t + 43 * c + 6 = 7 * p * (c : ℤ) ^ 2 := by
    exact_mod_cast hclear
  have hrdef :
      (12 : ℤ) * d + 43 * c + 6 =
        (p : ℤ) * (7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)
  have hrEq :
      (12 : ℤ) * d + 43 * c + 6 = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrpos : 0 < r := by
    push_cast at hcpos
    nlinarith
  have hrlt : r < 7 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    have haux : 43 * c + 6 < p := by nlinarith
    push_cast at hhalf' haux
    nlinarith
  have hremod : r % 12 = r :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have hcop := coprime_mod_left (S_branch_coprime_twelve hbranch)
  have hcmodlt : c % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ) := rfl
  have hrcong : r ≡ 7 * (c : ℤ) ^ 2 [ZMOD 12] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 12 : ℕ) : ℤ) [ZMOD 12] := by
    exact_mod_cast (Nat.mod_modEq c 12).symm
  have hrsmallcong :
      r ≡ 7 * (((c % 12 : ℕ) : ℤ) ^ 2) [ZMOD 12] :=
    hrcong.trans ((hccong.pow 2).mul_left 7)
  interval_cases hcm : c % 12
  all_goals norm_num [Nat.Coprime, hcm] at hcop
  all_goals norm_num [Int.ModEq, hcm, hremod] at hrsmallcong
  all_goals omega

/-! ## Exact p-first divisor switch -/

lemma P_prime_residue_of_cofactor
    {x p c : ℕ} (hbranch : P x = p * c)
    (hc : c % 7 = 3 ∨ c % 7 = 4) :
    p % 7 = 1 ∨ p % 7 = 6 := by
  have hPmod := (branch_mod_7_fixed x).1
  have hprod : (p % 7) * (c % 7) % 7 = 4 := by
    rw [← Nat.mul_mod, ← hbranch]
    exact hPmod
  have hpmodlt : p % 7 < 7 := Nat.mod_lt _ (by norm_num)
  rcases hc with hc | hc
  · interval_cases hpm : p % 7
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]
  · interval_cases hpm : p % 7
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]

lemma R_prime_residue_of_cofactor
    {x p c : ℕ} (hbranch : FullDensityCore.R x = p * c)
    (hc : c % 14 = 5 ∨ c % 14 = 9) :
    p % 14 = 1 ∨ p % 14 = 13 := by
  have hRmod : FullDensityCore.R x % 14 = 5 := by
    simp only [FullDensityCore.R, T]
    omega
  have hprod : (p % 14) * (c % 14) % 14 = 5 := by
    rw [← Nat.mul_mod, ← hbranch]
    exact hRmod
  have hpmodlt : p % 14 < 14 := Nat.mod_lt _ (by norm_num)
  rcases hc with hc | hc
  · interval_cases hpm : p % 14
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]
  · interval_cases hpm : p % 14
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]

/-- The exact top witnesses on one branch. -/
noncomputable def topBranchWitnessesUpTo (L : Branch) (X : ℕ) :
    Finset LocalBranchWitness :=
  (localTopPrimeWitnessesUpTo X (topPrimeCut X)).filter fun w =>
    localWitnessBranch w = L

/-- Allowed top primes on the P branch, enlarged only by the common exact
linear height bound. -/
noncomputable def PTopPrimeSet (X : ℕ) : Finset ℕ :=
  (Ioc (topPrimeCut X) (globalBranchBound * X)).filter fun p =>
    p.Prime ∧ (p % 7 = 1 ∨ p % 7 = 6)

/-- Allowed top primes on the R branch. -/
noncomputable def RTopPrimeSet (X : ℕ) : Finset ℕ :=
  (Ioc (topPrimeCut X) (globalBranchBound * X)).filter fun p =>
    p.Prime ∧ (p % 14 = 1 ∨ p % 14 = 13)

abbrev PrimeParameterKey := Σ _p : ℕ, ℕ

def topWitnessKey (w : LocalBranchWitness) : PrimeParameterKey :=
  ⟨localWitnessPrime w, localWitnessParameter w⟩

noncomputable def topBranchKeys
    (L : Branch) (primes : Finset ℕ) (X : ℕ) : Finset PrimeParameterKey :=
  primes.sigma fun p =>
    TransitionDensity.branchDivisibilityParameters L p X

theorem topWitnessKey_injOn (L : Branch) (X : ℕ) :
    Set.InjOn topWitnessKey (topBranchWitnessesUpTo L X :
      Set LocalBranchWitness) := by
  rintro ⟨K, x, p, a, d⟩ hw ⟨M, y, q, b, e⟩ hv hkey
  have hK := (Finset.mem_filter.mp hw).2
  have hM := (Finset.mem_filter.mp hv).2
  change K = L at hK
  change M = L at hM
  subst K
  subst M
  simp only [topWitnessKey, localWitnessPrime, localWitnessParameter,
    Sigma.mk.injEq] at hkey
  rcases hkey with ⟨rfl, rfl⟩
  have hwa := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hw).1).2.1
  have hvb := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hv).1).2.1
  change a = 1 at hwa
  change b = 1 at hvb
  subst a
  subst b
  have hwd := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1).2.2.2.1.2.1
  have hve := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).2.2.2.1.2.1
  change branchValue L x = p ^ 1 * d at hwd
  change branchValue L x = p ^ 1 * e at hve
  have hp : 0 < p := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1).2.1.pos
  have hde : d = e := by
    apply Nat.mul_left_cancel (pow_pos hp 1)
    rw [← hwd, ← hve]
  subst e
  rfl

lemma top_witness_prime_le
    {L : Branch} {X : ℕ} {w : LocalBranchWitness}
    (hX : 1 ≤ X) (hw : w ∈ topBranchWitnessesUpTo L X) :
    localWitnessPrime w ≤ globalBranchBound * X := by
  have hwlocal := mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have ha := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2.1
  change localWitnessExponent w = 1 at ha
  have hbranch := hwlocal.2.2.2.1.2.1
  have hexact := hwlocal.2.2.2.1
  rw [ha] at hexact
  have hcpos := cofactor_pos_of_exact_one hwlocal.2.1 hexact
  have hp_le : localWitnessPrime w ≤ branchValue (localWitnessBranch w)
      (localWitnessParameter w) := by
    rw [hbranch, ha, pow_one]
    exact Nat.le_mul_of_pos_right (localWitnessPrime w) hcpos
  have hx := (DensityEvents.mem_witnessBox.mp hwlocal.1).1
  have htag := (Finset.mem_filter.mp hw).2
  change localWitnessBranch w = L at htag
  rw [htag] at hp_le
  exact hp_le.trans (branchValue_le_globalBranchBound_mul hX
    (DensityEvents.mem_parameterRange.mp hx).2)

theorem P_topWitnessKey_mapsTo
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    Set.MapsTo topWitnessKey (topBranchWitnessesUpTo .P X :
      Set LocalBranchWitness) (topBranchKeys .P (PTopPrimeSet X) X :
        Set PrimeParameterKey) := by
  intro w hw
  change topWitnessKey w ∈ topBranchKeys .P (PTopPrimeSet X) X
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.P at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hexact := hlocal.2.2.1
  have hbranch := hexact.2.1
  have hbranch1 : branchValue .P (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hbranch
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch1).1
  have hlocalP : LocalBranchObstruction .P
      (localWitnessParameter w) (localWitnessPrime w) 1
      (localWitnessCofactor w) := by
    simpa [htag, ha] using hlocal
  have hc := P_top_local_classification hlocalP hratio
  have hpResidue : localWitnessPrime w % 7 = 1 ∨
      localWitnessPrime w % 7 = 6 := by
    apply P_prime_residue_of_cofactor
      (x := localWitnessParameter w)
      (c := localWitnessCofactor w)
    · simpa [branchValue] using hbranch1
    · exact hc
  rw [topBranchKeys]
  simp only [topWitnessKey, Finset.mem_sigma]
  constructor
  · rw [PTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hpCut, top_witness_prime_le hX hw⟩, hlocal.1, hpResidue⟩
  · rw [TransitionDensity.branchDivisibilityParameters,
      Finset.mem_filter]
    exact ⟨hxRange,
      ⟨localWitnessCofactor w, by rw [hbranch1]⟩⟩

theorem R_topWitnessKey_mapsTo
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    Set.MapsTo topWitnessKey (topBranchWitnessesUpTo .R X :
      Set LocalBranchWitness) (topBranchKeys .R (RTopPrimeSet X) X :
        Set PrimeParameterKey) := by
  intro w hw
  change topWitnessKey w ∈ topBranchKeys .R (RTopPrimeSet X) X
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.R at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hexact := hlocal.2.2.1
  have hbranch := hexact.2.1
  have hbranch1 : branchValue .R (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hbranch
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch1).1
  have hlocalR : LocalBranchObstruction .R
      (localWitnessParameter w) (localWitnessPrime w) 1
      (localWitnessCofactor w) := by
    simpa [htag, ha] using hlocal
  have hc := R_top_local_classification hlocalR hratio
  have hpResidue : localWitnessPrime w % 14 = 1 ∨
      localWitnessPrime w % 14 = 13 := by
    apply R_prime_residue_of_cofactor
      (x := localWitnessParameter w)
      (c := localWitnessCofactor w)
    · simpa [branchValue] using hbranch1
    · exact hc
  rw [topBranchKeys]
  simp only [topWitnessKey, Finset.mem_sigma]
  constructor
  · rw [RTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hpCut, top_witness_prime_le hX hw⟩, hlocal.1, hpResidue⟩
  · rw [TransitionDensity.branchDivisibilityParameters,
      Finset.mem_filter]
    exact ⟨hxRange,
      ⟨localWitnessCofactor w, by rw [hbranch1]⟩⟩

theorem Q_topBranchWitnesses_eq_empty
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    topBranchWitnessesUpTo .Q X = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨w, hw⟩
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.Q at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hbranch : branchValue .Q (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hlocal.2.2.1.2.1
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch).1
  apply Q_top_local_impossible (p := localWitnessPrime w)
    (c := localWitnessCofactor w) (x := localWitnessParameter w)
    (hratio := hratio)
  simpa [htag, ha] using hlocal

theorem S_topBranchWitnesses_eq_empty
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    topBranchWitnessesUpTo .S X = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨w, hw⟩
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.S at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hbranch : branchValue .S (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hlocal.2.2.1.2.1
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch).1
  apply S_top_local_impossible (p := localWitnessPrime w)
    (c := localWitnessCofactor w) (x := localWitnessParameter w)
    (hratio := hratio)
  simpa [htag, ha] using hlocal

theorem P_topBranchWitnesses_card_le_sum
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X) :
    (topBranchWitnessesUpTo .P X).card ≤
      ∑ p ∈ PTopPrimeSet X, (X / p + 1) := by
  calc
    _ ≤ (topBranchKeys .P (PTopPrimeSet X) X).card :=
      Finset.card_le_card_of_injOn topWitnessKey
        (P_topWitnessKey_mapsTo X hX hcut) (topWitnessKey_injOn .P X)
    _ = ∑ p ∈ PTopPrimeSet X,
        (TransitionDensity.branchDivisibilityParameters .P p X).card := by
      simp [topBranchKeys, Finset.card_sigma]
    _ ≤ ∑ p ∈ PTopPrimeSet X, (X / p + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      have hpCut := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      apply TransitionDensity.branchDivisibilityParameters_card_le hp'
      have hslope := TransitionDensity.branchSlope_le_max Branch.P
      omega

theorem R_topBranchWitnesses_card_le_sum
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X) :
    (topBranchWitnessesUpTo .R X).card ≤
      ∑ p ∈ RTopPrimeSet X, (X / p + 1) := by
  calc
    _ ≤ (topBranchKeys .R (RTopPrimeSet X) X).card :=
      Finset.card_le_card_of_injOn topWitnessKey
        (R_topWitnessKey_mapsTo X hX hcut) (topWitnessKey_injOn .R X)
    _ = ∑ p ∈ RTopPrimeSet X,
        (TransitionDensity.branchDivisibilityParameters .R p X).card := by
      simp [topBranchKeys, Finset.card_sigma]
    _ ≤ ∑ p ∈ RTopPrimeSet X, (X / p + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      have hpCut := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      apply TransitionDensity.branchDivisibilityParameters_card_le hp'
      have hslope := TransitionDensity.branchSlope_le_max Branch.R
      omega

theorem topWitnesses_card_eq_sum_branches (X : ℕ) :
    (localTopPrimeWitnessesUpTo X (topPrimeCut X)).card =
      ∑ L : Branch, (topBranchWitnessesUpTo L X).card := by
  classical
  unfold topBranchWitnessesUpTo
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Exact finite divisor-switch bound for all four branches. -/
theorem topWitnesses_card_le_allowed_sums
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X) :
    (localTopPrimeWitnessesUpTo X (topPrimeCut X)).card ≤
      (∑ p ∈ PTopPrimeSet X, (X / p + 1)) +
        ∑ p ∈ RTopPrimeSet X, (X / p + 1) := by
  rw [topWitnesses_card_eq_sum_branches]
  let pSum := ∑ p ∈ PTopPrimeSet X, (X / p + 1)
  let rSum := ∑ p ∈ RTopPrimeSet X, (X / p + 1)
  calc
    ∑ L : Branch, (topBranchWitnessesUpTo L X).card ≤
        ∑ L : Branch, match L with
          | .P => pSum
          | .Q => 0
          | .R => rSum
          | .S => 0 := by
      apply Finset.sum_le_sum
      intro L _
      cases L with
      | P => exact P_topBranchWitnesses_card_le_sum X hX hcut hlarge
      | Q => rw [Q_topBranchWitnesses_eq_empty X hX hcut]; simp
      | R => exact R_topBranchWitnesses_card_le_sum X hX hcut hlarge
      | S => rw [S_topBranchWitnesses_eq_empty X hX hcut]; simp
    _ = pSum + rSum := by
      have huniv : (Finset.univ : Finset Branch) =
          {.P, .Q, .R, .S} := by decide
      rw [huniv]
      simp
    _ = _ := rfl

/-! ## Reciprocal primes in one fixed arithmetic progression -/

/-- Reciprocal-prime partial sum in the exact class `a mod A`, with a real
cutoff and the same floor convention as `primeAPCountingReal`. -/
noncomputable def reciprocalPrimeAPSumReal (A a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ apPrimes A a x, (p : ℝ)⁻¹

/-- Abel summation for reciprocal primes in one arithmetic progression. -/
theorem reciprocalPrimeAPSumReal_eq_count_div_add_integral
    (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    reciprocalPrimeAPSumReal A a x =
      primeAPCountingReal A a x / x +
        ∫ t in (2 : ℝ)..x, primeAPCountingReal A a t / t ^ 2 := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun y : ℝ => y⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (zero_lt_two.trans_le ht.1))
  have hint : IntegrableOn (deriv fun y : ℝ => y⁻¹)
      (Set.Icc (2 : ℝ) x) := by
    rw [deriv_inv']
    refine ContinuousOn.integrableOn_Icc ?_
    exact ((continuous_id.pow 2).continuousOn.inv₀ fun t ht hzero =>
      (zero_lt_two.trans_le ht.1).ne' (eq_zero_of_pow_eq_zero hzero)).neg
  rw [reciprocalPrimeAPSumReal, apPrimes, Finset.sum_filter]
  let b : ℕ → ℝ := Set.indicator
    {p : ℕ | p.Prime ∧ p % A = a} (fun _ => 1)
  trans ∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ)⁻¹ * b k
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · simp [b, hk]
    · simp [b, hk]
  rw [sum_mul_eq_sub_integral_mul₁ b
      (by simp [b, Nat.not_prime_zero])
      (by simp [b, Nat.not_prime_one]) x hdiff hint,
    ← intervalIntegral.integral_of_le hx]
  have int_deriv (f : ℝ → ℝ) :
      ∫ u in (2 : ℝ)..x,
          deriv (fun y : ℝ => y⁻¹) u * f u =
        ∫ u in (2 : ℝ)..x, f u * -(u ^ 2)⁻¹ :=
    intervalIntegral.integral_congr fun u _ => by rw [deriv_inv']; ring
  rw [int_deriv]
  simp [b, Set.indicator_apply, Finset.sum_filter,
    primeAPCountingReal, div_eq_mul_inv]
  ring

lemma integrableOn_primeAPCountingReal_div_sq
    (A a : ℕ) (x : ℝ) :
    IntegrableOn (fun t => primeAPCountingReal A a t / t ^ 2)
      (Set.Icc 2 x) MeasureTheory.volume := by
  unfold primeAPCountingReal
  conv =>
    arg 1
    ext t
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  conv =>
    arg 1
    ext t
    rw [div_eq_mul_one_div, mul_comm]
  refine integrableOn_mul_sum_Icc
      (a := 2) (b := x) (m := 0)
      (fun p : ℕ => if p.Prime ∧ p % A = a then (1 : ℝ) else 0)
      (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
  have ht0 : t ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [ht.1])
  fun_prop (disch := assumption)

/-! ## Moving top-band endpoints -/

def topPrimeUpper (X : ℕ) : ℝ :=
  (globalBranchBound : ℝ) * (X : ℝ)

def topLogBand (X : ℕ) : ℝ :=
  Real.log (Real.log (topPrimeUpper X)) -
    Real.log (Real.log (topPrimeScale X))

theorem tendsto_topPrimeScale_atTop :
    Tendsto (fun X : ℕ => topPrimeScale X) atTop atTop := by
  simpa [topPrimeScale, FullDensity.transitionPrimeBandUpper] using
    TransitionDensity.tendsto_transitionPrimeBandUpper_nat_atTop

theorem tendsto_topPrimeUpper_atTop :
    Tendsto topPrimeUpper atTop atTop := by
  unfold topPrimeUpper
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by
    norm_num [globalBranchBound])

private theorem tendsto_log_log_div_log_nat :
    Tendsto (fun X : ℕ =>
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ))
      atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun X : ℝ => Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) := by
    simpa using!
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        Real.tendsto_log_atTop
  exact hreal.comp tendsto_natCast_atTop_atTop

theorem tendsto_top_log_ratio :
    Tendsto (fun X : ℕ =>
      Real.log (topPrimeUpper X) / Real.log (topPrimeScale X))
      atTop (𝓝 2) := by
  have hinvLog : Tendsto (fun X : ℕ =>
      (Real.log (X : ℝ))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hnum : Tendsto (fun X : ℕ =>
      1 + Real.log (globalBranchBound : ℝ) / Real.log (X : ℝ))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).add
        (hinvLog.const_mul (Real.log (globalBranchBound : ℝ)))
    simpa [div_eq_mul_inv] using h
  have hden : Tendsto (fun X : ℕ =>
      (1 / 2 : ℝ) +
        2 * (Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_log_log_div_log_nat.const_mul 2))
  have hquot := hnum.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hquot' : Tendsto (fun X : ℕ =>
      (1 + Real.log (globalBranchBound : ℝ) / Real.log (X : ℝ)) /
        ((1 / 2 : ℝ) +
          2 * (Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ))))
      atTop (𝓝 2) := by
    norm_num at hquot ⊢
    exact hquot
  apply hquot'.congr'
  filter_upwards [eventually_gt_atTop (Nat.ceil (Real.exp 1))] with X hX
  have hXreal : Real.exp 1 < (X : ℝ) := by
    exact (Nat.le_ceil (Real.exp 1)).trans_lt (by exact_mod_cast hX)
  have hX1 : 1 < (X : ℝ) := (by
    have : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr zero_lt_one
    exact this.trans hXreal)
  have hlogX : Real.log (X : ℝ) ≠ 0 := (Real.log_pos hX1).ne'
  have hscaleEq : Real.log (topPrimeScale X) =
      Real.log (X : ℝ) / 2 +
        2 * Real.log (Real.log (X : ℝ)) := by
    simpa [topPrimeScale, FullDensity.transitionPrimeBandUpper] using
      (FullDensity.log_transitionPrimeBandUpper hX1)
  have hscaleLog : Real.log (topPrimeScale X) ≠ 0 := by
    rw [hscaleEq]
    have hloglog : 0 < Real.log (Real.log (X : ℝ)) := by
      have : 1 < Real.log (X : ℝ) := by
        apply Real.exp_lt_exp.mp
        simpa [Real.exp_log (by positivity)] using hXreal
      exact Real.log_pos this
    positivity
  rw [topPrimeUpper, Real.log_mul (by norm_num [globalBranchBound])
    (by positivity), hscaleEq]
  field_simp
  ring

theorem tendsto_topLogBand :
    Tendsto topLogBand atTop (𝓝 (Real.log 2)) := by
  have hlogRatio := (tendsto_top_log_ratio.log (by norm_num : (2 : ℝ) ≠ 0))
  apply hlogRatio.congr'
  filter_upwards
      [tendsto_topPrimeScale_atTop.eventually_gt_atTop (Real.exp 1),
       tendsto_topPrimeUpper_atTop.eventually_gt_atTop (Real.exp 1)]
      with X hscale hupper
  unfold topLogBand
  have hslog : Real.log (topPrimeScale X) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact (Real.exp_pos 1).trans hscale
    · linarith [Real.exp_one_gt_two]
  have hulog : Real.log (topPrimeUpper X) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact (Real.exp_pos 1).trans hupper
    · linarith [Real.exp_one_gt_two]
  rw [← Real.log_div hulog hslog]

theorem eventually_topPrimeScale_le_upper :
    ∀ᶠ X : ℕ in atTop, topPrimeScale X ≤ topPrimeUpper X := by
  have hdiv := TransitionDensity.tendsto_transitionPrimeBandUpper_div_nat
  have hlt := (tendsto_order.1 hdiv).2
    (globalBranchBound : ℝ) (by norm_num [globalBranchBound])
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with X hratio hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have h := (div_lt_iff₀ hXreal).mp hratio
  simpa [topPrimeScale, FullDensity.transitionPrimeBandUpper,
    topPrimeUpper] using h.le

private lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t => Real.log (Real.log t)) x =
      1 / (x * Real.log x) := by
  rw [deriv.log (Real.differentiableAt_log (by linarith))
    (by simp; grind), Real.deriv_log]
  field

lemma integral_one_div_mul_log_between
    {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z) :
    ∫ t in y..z, 1 / (t * Real.log t) =
      Real.log (Real.log z) - Real.log (Real.log y) := by
  rw [← intervalIntegral.integral_deriv_eq_sub
    (f := fun t => Real.log (Real.log t))]
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
    have htlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := fun t => 1 / (t * Real.log t))
    · refine fun t ht => ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
      have htlog : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

noncomputable def reciprocalPrimeAPTopBand
    (A a : ℕ) (X : ℕ) : ℝ :=
  reciprocalPrimeAPSumReal A a (topPrimeUpper X) -
    reciprocalPrimeAPSumReal A a (topPrimeScale X)

/-- Pointwise PNT control on the moving interval gives the exact reciprocal
prime-band upper bound needed by the p-first switch. -/
theorem reciprocalPrimeAPTopBand_le_of_normalized
    (A a X : ℕ) (C : ℝ)
    (hscale : 2 ≤ topPrimeScale X)
    (hle : topPrimeScale X ≤ topPrimeUpper X)
    (hnorm : ∀ t : ℝ, topPrimeScale X ≤ t → t ≤ topPrimeUpper X →
      primeAPCountingReal A a t / (t / Real.log t) ≤ C) :
    reciprocalPrimeAPTopBand A a X ≤
      primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X +
        C * topLogBand X := by
  let f : ℝ → ℝ := fun t => primeAPCountingReal A a t / t ^ 2
  have hupper : 2 ≤ topPrimeUpper X := hscale.trans hle
  have hi2s : IntervalIntegrable f MeasureTheory.volume 2
      (topPrimeScale X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hscale]
    exact integrableOn_primeAPCountingReal_div_sq A a _
  have hi2u : IntervalIntegrable f MeasureTheory.volume 2
      (topPrimeUpper X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hupper]
    exact integrableOn_primeAPCountingReal_div_sq A a _
  have hisu : IntervalIntegrable f MeasureTheory.volume
      (topPrimeScale X) (topPrimeUpper X) := by
    apply hi2u.mono_set
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le hupper]
    intro t ht
    exact ⟨hscale.trans ht.1, ht.2⟩
  have hband : reciprocalPrimeAPTopBand A a X =
      primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X -
        primeAPCountingReal A a (topPrimeScale X) / topPrimeScale X +
          ∫ t in topPrimeScale X..topPrimeUpper X, f t := by
    unfold reciprocalPrimeAPTopBand
    rw [reciprocalPrimeAPSumReal_eq_count_div_add_integral A a hupper,
      reciprocalPrimeAPSumReal_eq_count_div_add_integral A a hscale]
    rw [← intervalIntegral.integral_add_adjacent_intervals hi2s hisu]
    dsimp [f]
    ring
  have hbaseInt : IntervalIntegrable
      (fun t : ℝ => C * (1 / (t * Real.log t)))
      MeasureTheory.volume (topPrimeScale X) (topPrimeUpper X) := by
    refine ContinuousOn.intervalIntegrable fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at ht
    have htlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := grind)
  have hintLe :
      (∫ t in topPrimeScale X..topPrimeUpper X, f t) ≤
        ∫ t in topPrimeScale X..topPrimeUpper X,
          C * (1 / (t * Real.log t)) := by
    apply intervalIntegral.integral_mono_on hle hisu hbaseInt
    intro t ht
    have ht1 : 1 < t := (by linarith [hscale, ht.1])
    have htpos : 0 < t := zero_lt_one.trans ht1
    have htlog : 0 < Real.log t := Real.log_pos ht1
    have hn := hnorm t ht.1 ht.2
    have hid : f t =
        (primeAPCountingReal A a t / (t / Real.log t)) *
          (1 / (t * Real.log t)) := by
      dsimp [f]
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_right hn (by positivity)
  rw [hband]
  have hpiNonneg : 0 ≤
      primeAPCountingReal A a (topPrimeScale X) / topPrimeScale X := by
    exact div_nonneg (by unfold primeAPCountingReal; positivity)
      (by linarith)
  have hbase :
      (∫ t in topPrimeScale X..topPrimeUpper X,
        C * (1 / (t * Real.log t))) = C * topLogBand X := by
    rw [intervalIntegral.integral_const_mul,
      integral_one_div_mul_log_between (by linarith) hle]
    rfl
  rw [hbase] at hintLe
  linarith

theorem eventually_reciprocalPrimeAPTopBand_le
    {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A) (haA : a < A)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      reciprocalPrimeAPTopBand A a X ≤
        primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X +
          ((A.totient : ℝ)⁻¹ + ε) * topLogBand X := by
  have hpnt := primeAPCountingReal_normalized_tendsto hA ha haA
  have hpntUpper : ∀ᶠ t : ℝ in atTop,
      primeAPCountingReal A a t / (t / Real.log t) ≤
        (A.totient : ℝ)⁻¹ + ε := by
    have hlt := (tendsto_order.1 hpnt).2
      ((A.totient : ℝ)⁻¹ + ε) (by linarith)
    exact hlt.mono fun _ h => h.le
  obtain ⟨M, hM⟩ := (eventually_atTop.1 hpntUpper)
  filter_upwards
      [tendsto_topPrimeScale_atTop.eventually_ge_atTop (max 2 M),
       eventually_topPrimeScale_le_upper]
      with X hscale hle
  apply reciprocalPrimeAPTopBand_le_of_normalized A a X
    ((A.totient : ℝ)⁻¹ + ε) ((le_max_left 2 M).trans hscale) hle
  intro t hst _htz
  exact hM t (le_trans (le_max_right 2 M) (hscale.trans hst))

theorem tendsto_primeAP_top_endpoint
    {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A) (haA : a < A) :
    Tendsto (fun X : ℕ =>
      primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X)
      atTop (𝓝 0) := by
  have hpnt := (primeAPCountingReal_normalized_tendsto hA ha haA).comp
    tendsto_topPrimeUpper_atTop
  have hinvLog : Tendsto (fun X : ℕ =>
      (Real.log (topPrimeUpper X))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_topPrimeUpper_atTop).inv_tendsto_atTop
  have hprod := hpnt.mul hinvLog
  have hprod' : Tendsto (fun X : ℕ =>
      (primeAPCountingReal A a (topPrimeUpper X) /
        (topPrimeUpper X / Real.log (topPrimeUpper X))) *
          (Real.log (topPrimeUpper X))⁻¹)
      atTop (𝓝 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards
      [tendsto_topPrimeUpper_atTop.eventually_gt_atTop (Real.exp 1)]
      with X hupper
  have hu0 : topPrimeUpper X ≠ 0 :=
    ne_of_gt ((Real.exp_pos 1).trans hupper)
  have hlog0 : Real.log (topPrimeUpper X) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact (Real.exp_pos 1).trans hupper
    · linarith [Real.exp_one_gt_two]
  field_simp

noncomputable def topAPPrimeSet (A a X : ℕ) : Finset ℕ :=
  (Ioc (topPrimeCut X) (globalBranchBound * X)).filter fun p =>
    p.Prime ∧ p % A = a

theorem reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet
    (A a X : ℕ) (hle : topPrimeScale X ≤ topPrimeUpper X) :
    reciprocalPrimeAPTopBand A a X =
      ∑ p ∈ topAPPrimeSet A a X, (p : ℝ)⁻¹ := by
  have hfloorUpper : ⌊topPrimeUpper X⌋₊ = globalBranchBound * X := by
    rw [topPrimeUpper, ← Nat.cast_mul, Nat.floor_natCast]
  have hfloorScale : ⌊topPrimeScale X⌋₊ = topPrimeCut X := rfl
  have hsubset : apPrimes A a (topPrimeScale X) ⊆
      apPrimes A a (topPrimeUpper X) := by
    intro p hp
    rw [apPrimes, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hle)⟩, hp.2⟩
  have hdiff : apPrimes A a (topPrimeUpper X) \
      apPrimes A a (topPrimeScale X) = topAPPrimeSet A a X := by
    ext p
    simp only [apPrimes, topAPPrimeSet, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    rw [hfloorUpper, hfloorScale]
    constructor
    · rintro ⟨⟨⟨_, hpU⟩, hprime, hmod⟩, hnot⟩
      refine ⟨⟨?_, hpU⟩, hprime, hmod⟩
      by_contra hn
      apply hnot
      exact ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hn⟩, hprime, hmod⟩
    · rintro ⟨⟨hpL, hpU⟩, hprime, hmod⟩
      refine ⟨⟨⟨Nat.zero_le p, hpU⟩, hprime, hmod⟩, ?_⟩
      rintro ⟨⟨_, hpLe⟩, _, _⟩
      omega
  unfold reciprocalPrimeAPTopBand reciprocalPrimeAPSumReal
  rw [← hdiff]
  have hsum := Finset.sum_sdiff (f := fun p : ℕ => (p : ℝ)⁻¹) hsubset
  linarith

theorem PTopPrimeSet_eq_union (X : ℕ) :
    PTopPrimeSet X = topAPPrimeSet 7 1 X ∪ topAPPrimeSet 7 6 X := by
  ext p
  simp only [PTopPrimeSet, topAPPrimeSet, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_union]
  aesop

theorem RTopPrimeSet_eq_union (X : ℕ) :
    RTopPrimeSet X = topAPPrimeSet 14 1 X ∪ topAPPrimeSet 14 13 X := by
  ext p
  simp only [RTopPrimeSet, topAPPrimeSet, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_union]
  aesop

lemma topAPPrimeSet_disjoint
    {A a b X : ℕ} (hab : a ≠ b) :
    Disjoint (topAPPrimeSet A a X) (topAPPrimeSet A b X) := by
  rw [Finset.disjoint_left]
  intro p hpa hpb
  have ha := (Finset.mem_filter.mp hpa).2.2
  have hb := (Finset.mem_filter.mp hpb).2.2
  exact hab (ha.symm.trans hb)

theorem sum_PTopPrimeSet_eq_bands
    (X : ℕ) (hle : topPrimeScale X ≤ topPrimeUpper X) :
    (∑ p ∈ PTopPrimeSet X, (p : ℝ)⁻¹) =
      reciprocalPrimeAPTopBand 7 1 X +
        reciprocalPrimeAPTopBand 7 6 X := by
  rw [PTopPrimeSet_eq_union,
    Finset.sum_union (topAPPrimeSet_disjoint (by norm_num : (1 : ℕ) ≠ 6)),
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 7 1 X hle,
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 7 6 X hle]

theorem sum_RTopPrimeSet_eq_bands
    (X : ℕ) (hle : topPrimeScale X ≤ topPrimeUpper X) :
    (∑ p ∈ RTopPrimeSet X, (p : ℝ)⁻¹) =
      reciprocalPrimeAPTopBand 14 1 X +
        reciprocalPrimeAPTopBand 14 13 X := by
  rw [RTopPrimeSet_eq_union,
    Finset.sum_union (topAPPrimeSet_disjoint (by norm_num : (1 : ℕ) ≠ 13)),
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 14 1 X hle,
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 14 13 X hle]

lemma cast_sum_div_add_one_le
    (S : Finset ℕ) (X : ℕ) :
    ((∑ p ∈ S, (X / p + 1) : ℕ) : ℝ) ≤
      (X : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) + S.card := by
  calc
    ((∑ p ∈ S, (X / p + 1) : ℕ) : ℝ) =
        ∑ p ∈ S, (((X / p : ℕ) : ℝ) + 1) := by norm_cast
    _ ≤ ∑ p ∈ S, ((X : ℝ) * (p : ℝ)⁻¹ + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact add_le_add (by
        simpa [div_eq_mul_inv] using
          (Nat.cast_div_le (m := X) (n := p) (α := ℝ))) le_rfl
    _ = (X : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) + S.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

theorem allowedPrimeSets_card_le_ordinary_count (X : ℕ) :
    ((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card ≤
      2 * primeAPCountingReal 1 0 (topPrimeUpper X) := by
  have hP : ((PTopPrimeSet X).card : ℝ) ≤
      primeAPCountingReal 1 0 (topPrimeUpper X) := by
    unfold primeAPCountingReal
    norm_cast
    apply Finset.card_le_card
    intro p hp
    rw [PTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hfloor : ⌊topPrimeUpper X⌋₊ = globalBranchBound * X := by
      rw [topPrimeUpper, ← Nat.cast_mul, Nat.floor_natCast]
    exact ⟨⟨Nat.zero_le p, by simpa [hfloor] using hp.1.2⟩,
      hp.2.1, Nat.mod_one p⟩
  have hR : ((RTopPrimeSet X).card : ℝ) ≤
      primeAPCountingReal 1 0 (topPrimeUpper X) := by
    unfold primeAPCountingReal
    norm_cast
    apply Finset.card_le_card
    intro p hp
    rw [RTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hfloor : ⌊topPrimeUpper X⌋₊ = globalBranchBound * X := by
      rw [topPrimeUpper, ← Nat.cast_mul, Nat.floor_natCast]
    exact ⟨⟨Nat.zero_le p, by simpa [hfloor] using hp.1.2⟩,
      hp.2.1, Nat.mod_one p⟩
  linarith

theorem tendsto_ordinary_top_count_div_parameter :
    Tendsto (fun X : ℕ =>
      primeAPCountingReal 1 0 (topPrimeUpper X) / (X : ℝ))
      atTop (𝓝 0) := by
  have hend := tendsto_primeAP_top_endpoint
    (A := 1) (a := 0) (by norm_num) (by norm_num) (by norm_num)
  have hscaled := hend.const_mul (globalBranchBound : ℝ)
  have hscaled' : Tendsto (fun X : ℕ =>
      (globalBranchBound : ℝ) *
        (primeAPCountingReal 1 0 (topPrimeUpper X) / topPrimeUpper X))
      atTop (𝓝 0) := by simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hC0 : (globalBranchBound : ℝ) ≠ 0 := by
    norm_num [globalBranchBound]
  unfold topPrimeUpper
  field_simp

noncomputable def topAnalyticMajorant (ε : ℝ) (X : ℕ) : ℝ :=
  primeAPCountingReal 7 1 (topPrimeUpper X) / topPrimeUpper X +
    primeAPCountingReal 7 6 (topPrimeUpper X) / topPrimeUpper X +
    primeAPCountingReal 14 1 (topPrimeUpper X) / topPrimeUpper X +
    primeAPCountingReal 14 13 (topPrimeUpper X) / topPrimeUpper X +
    4 * ((1 / 6 : ℝ) + ε) * topLogBand X +
    2 * primeAPCountingReal 1 0 (topPrimeUpper X) / (X : ℝ)

theorem tendsto_topAnalyticMajorant (ε : ℝ) :
    Tendsto (topAnalyticMajorant ε) atTop
      (𝓝 (4 * ((1 / 6 : ℝ) + ε) * Real.log 2)) := by
  have h71 := tendsto_primeAP_top_endpoint
    (A := 7) (a := 1) (by norm_num) (by norm_num) (by norm_num)
  have h76 := tendsto_primeAP_top_endpoint
    (A := 7) (a := 6) (by norm_num) (by norm_num) (by norm_num)
  have h141 := tendsto_primeAP_top_endpoint
    (A := 14) (a := 1) (by norm_num) (by norm_num) (by norm_num)
  have h1413 := tendsto_primeAP_top_endpoint
    (A := 14) (a := 13) (by norm_num) (by norm_num) (by norm_num)
  have hmain := tendsto_topLogBand.const_mul
    (4 * ((1 / 6 : ℝ) + ε))
  have hcount := tendsto_ordinary_top_count_div_parameter.const_mul 2
  have htotal := (((((h71.add h76).add h141).add h1413).add hmain).add hcount)
  convert htotal using 1
  · funext X
    unfold topAnalyticMajorant
    ring
  · ring

/-- Finite normalized top count bounded by the analytic majorant. -/
theorem normalizedTopPrimeWitnessCount_le_majorant
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X)
    (hle : topPrimeScale X ≤ topPrimeUpper X)
    (ε : ℝ)
    (h71 : reciprocalPrimeAPTopBand 7 1 X ≤
      primeAPCountingReal 7 1 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X)
    (h76 : reciprocalPrimeAPTopBand 7 6 X ≤
      primeAPCountingReal 7 6 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X)
    (h141 : reciprocalPrimeAPTopBand 14 1 X ≤
      primeAPCountingReal 14 1 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X)
    (h1413 : reciprocalPrimeAPTopBand 14 13 X ≤
      primeAPCountingReal 14 13 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X) :
    ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) /
        (X : ℝ) ≤ topAnalyticMajorant ε X := by
  have hcard := topWitnesses_card_le_allowed_sums X hX hcut hlarge
  have hcardCast :
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) ≤
        ((∑ p ∈ PTopPrimeSet X, (X / p + 1) : ℕ) : ℝ) +
          ((∑ p ∈ RTopPrimeSet X, (X / p + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hP := cast_sum_div_add_one_le (PTopPrimeSet X) X
  have hR := cast_sum_div_add_one_le (RTopPrimeSet X) X
  have hmassP := sum_PTopPrimeSet_eq_bands X hle
  have hmassR := sum_RTopPrimeSet_eq_bands X hle
  have hraw :
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) ≤
        (X : ℝ) *
          (reciprocalPrimeAPTopBand 7 1 X +
            reciprocalPrimeAPTopBand 7 6 X +
            reciprocalPrimeAPTopBand 14 1 X +
            reciprocalPrimeAPTopBand 14 13 X) +
          ((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card := by
    rw [hmassP] at hP
    rw [hmassR] at hR
    linarith
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hnormalized :
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) /
          (X : ℝ) ≤
        reciprocalPrimeAPTopBand 7 1 X +
          reciprocalPrimeAPTopBand 7 6 X +
          reciprocalPrimeAPTopBand 14 1 X +
          reciprocalPrimeAPTopBand 14 13 X +
          (((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card) /
            (X : ℝ) := by
    apply (div_le_iff₀ hXreal).2
    calc
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) ≤ _ := hraw
      _ = (reciprocalPrimeAPTopBand 7 1 X +
          reciprocalPrimeAPTopBand 7 6 X +
          reciprocalPrimeAPTopBand 14 1 X +
          reciprocalPrimeAPTopBand 14 13 X +
          (((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card) /
            (X : ℝ)) * (X : ℝ) := by
        field_simp
        ring
  have hcards := allowedPrimeSets_card_le_ordinary_count X
  have hcardsDiv :
      (((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card) /
          (X : ℝ) ≤
        2 * primeAPCountingReal 1 0 (topPrimeUpper X) / (X : ℝ) :=
    div_le_div_of_nonneg_right hcards hXreal.le
  unfold topAnalyticMajorant
  linarith

/-! ## Eventual cutoff verification and limsup closure -/

theorem eventually_large_topPrimeCut :
    ∀ᶠ X : ℕ in atTop, 380808 ≤ topPrimeCut X := by
  filter_upwards
      [tendsto_topPrimeScale_atTop.eventually_ge_atTop (380808 : ℝ)]
      with X hX
  unfold topPrimeCut
  exact Nat.le_floor hX

theorem eventually_topCutoffHypothesis :
    ∀ᶠ X : ℕ in atTop, TopCutoffHypothesis X := by
  have hlogPow : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ 4)
      atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards
      [hlogPow.eventually_gt_atTop
        (4 * (130 * globalBranchBound : ℝ)),
       tendsto_topPrimeScale_atTop.eventually_gt_atTop 2,
       eventually_gt_atTop (0 : ℕ)]
      with X hlog hscale hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hfloor : topPrimeScale X < (topPrimeCut X : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (topPrimeScale X)
  have hhalf : topPrimeScale X / 2 < (topPrimeCut X : ℝ) := by
    nlinarith
  have hscaleSq : topPrimeScale X ^ 2 =
      (X : ℝ) * Real.log (X : ℝ) ^ 4 := by
    unfold topPrimeScale
    rw [mul_pow, Real.sq_sqrt hXreal.le]
    ring
  have hreal :
      ((130 * globalBranchBound * X : ℕ) : ℝ) <
        ((topPrimeCut X ^ 2 : ℕ) : ℝ) := by
    push_cast
    rw [pow_two]
    have hhalfSq : (topPrimeScale X / 2) ^ 2 <
        (topPrimeCut X : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (topPrimeScale X / 2),
        sq_nonneg (topPrimeCut X : ℝ)]
    have hhalfSq' : topPrimeScale X ^ 2 / 4 <
        (topPrimeCut X : ℝ) ^ 2 := by
      nlinarith
    rw [hscaleSq] at hhalfSq'
    nlinarith
  unfold TopCutoffHypothesis
  exact_mod_cast hreal

theorem topPrimeCut_eq_transitionTopCut (X : ℕ) :
    topPrimeCut X = TransitionDensity.transitionTopCut X := by
  rfl

theorem eventually_normalizedTopPrimeWitnessCount_le_majorant
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      RangeAssembly.normalizedTopPrimeWitnessCount X ≤
        topAnalyticMajorant ε X := by
  have h71 := eventually_reciprocalPrimeAPTopBand_le
    (A := 7) (a := 1) (by norm_num) (by norm_num) (by norm_num) hε
  have h76 := eventually_reciprocalPrimeAPTopBand_le
    (A := 7) (a := 6) (by norm_num) (by norm_num) (by norm_num) hε
  have h141 := eventually_reciprocalPrimeAPTopBand_le
    (A := 14) (a := 1) (by norm_num) (by norm_num) (by norm_num) hε
  have h1413 := eventually_reciprocalPrimeAPTopBand_le
    (A := 14) (a := 13) (by norm_num) (by norm_num) (by norm_num) hε
  filter_upwards
      [h71, h76, h141, h1413, eventually_topCutoffHypothesis,
       eventually_large_topPrimeCut, eventually_topPrimeScale_le_upper,
       eventually_ge_atTop (1 : ℕ)]
      with X h71X h76X h141X h1413X hcut hlarge hle hX
  rw [RangeAssembly.normalizedTopPrimeWitnessCount,
    ← topPrimeCut_eq_transitionTopCut]
  apply normalizedTopPrimeWitnessCount_le_majorant X hX hcut hlarge hle ε
  · simpa [show Nat.totient 7 = 6 by decide] using h71X
  · simpa [show Nat.totient 7 = 6 by decide] using h76X
  · simpa [show Nat.totient 14 = 6 by decide] using h141X
  · simpa [show Nat.totient 14 = 6 by decide] using h1413X

theorem eventually_normalizedTopPrimeWitnessCount_lt
    {y : ℝ} (hy : (2 / 3 : ℝ) * Real.log 2 < y) :
    ∀ᶠ X : ℕ in atTop,
      RangeAssembly.normalizedTopPrimeWitnessCount X < y := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε : ℝ := (y - (2 / 3 : ℝ) * Real.log 2) /
    (8 * Real.log 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (sub_pos.mpr hy) (mul_pos (by norm_num) hlog2)
  have hbound := eventually_normalizedTopPrimeWitnessCount_le_majorant hε
  have hlim := tendsto_topAnalyticMajorant ε
  have hlimitLt :
      4 * ((1 / 6 : ℝ) + ε) * Real.log 2 < y := by
    dsimp [ε]
    field_simp
    linarith
  have hmajorLt := (tendsto_order.1 hlim).2 y hlimitLt
  filter_upwards [hbound, hmajorLt] with X hX hM
  exact hX.trans_lt hM

/-- The top-range normalized count is eventually bounded. -/
theorem normalizedTopPrimeWitnessCount_isBoundedUnder :
    IsBoundedUnder (· ≤ ·) atTop
      RangeAssembly.normalizedTopPrimeWitnessCount := by
  have h := eventually_normalizedTopPrimeWitnessCount_lt
    (y := (2 / 3 : ℝ) * Real.log 2 + 1) (by linarith)
  apply isBoundedUnder_of_eventually_le
  exact h.mono fun _ hx => hx.le

/-- Complete top-range closure: P and R each contribute at most
`(1/3) log 2`, while Q and S contribute zero. -/
theorem limsup_normalizedTopPrimeWitnessCount_le :
    limsup RangeAssembly.normalizedTopPrimeWitnessCount atTop ≤
      (2 / 3 : ℝ) * Real.log 2 := by
  apply (limsup_le_iff
    (h₁ := isCoboundedUnder_le_of_le atTop
      RangeAssembly.normalizedTopPrimeWitnessCount_nonneg)
    (h₂ := normalizedTopPrimeWitnessCount_isBoundedUnder)).2
  intro y hy
  exact eventually_normalizedTopPrimeWitnessCount_lt hy

end

end DivisorSwitching
end Erdos730

end Campaign180File23

/- Source module: ErdosProblems.Erdos730.PadicIsometry -/
section Campaign180File24
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: generic p-adic branch-map isometry

This module isolates equations (22)--(28) of the proposed positive-density
proof.  A branch map has a quadratic coefficient divisible by `p`, a linear
coefficient of the form `p*u+b`, and a residual coefficient `b` which is a
unit modulo `p`.  We prove the exact difference factorization, the resulting
isometry modulo every positive power `p^j`, and hence permutation of
`ZMod (p^j)`.

The last section records the finite combinatorics used after the permutation:
the preimage of an allowed set has the same cardinality, removal of one allowed
image removes exactly one residue, and the corresponding depth-`d` digit box
has cardinality `(H-1) * H^(d-1)`.
-/

namespace Erdos730

/-- Generic form of the four branch polynomials in equation (22). -/
def padicBranchMap {R : Type*} [CommRing R]
    (p q u b v k : R) : R :=
  p * q * k ^ 2 + (p * u + b) * k + v

/-- Exact difference factorization underlying equation (26). -/
theorem padicBranchMap_sub_factor {R : Type*} [CommRing R]
    (p q u b v x y : R) :
    padicBranchMap p q u b v x - padicBranchMap p q u b v y =
      (x - y) * (p * q * (x + y) + p * u + b) := by
  simp only [padicBranchMap]
  ring

/-- A multiple of `p` in `ZMod (p^j)` is nilpotent when `j>=1`. -/
theorem zmod_primeMultiple_isNilpotent {p j : ℕ} (z : ZMod (p ^ j)) :
    IsNilpotent ((p : ZMod (p ^ j)) * z) := by
  refine ⟨j, ?_⟩
  rw [mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

/-- The second factor in the branch-map difference is a unit.  This is the
kernel form of the sentence following equation (25). -/
theorem padicBranchMap_differenceFactor_isUnit
    {p j : ℕ} {b : ZMod (p ^ j)} (hb : IsUnit b)
    (q u x y : ZMod (p ^ j)) :
    IsUnit ((p : ZMod (p ^ j)) * q * (x + y) + p * u + b) := by
  have hnil : IsNilpotent
      ((p : ZMod (p ^ j)) * (q * (x + y) + u)) :=
    zmod_primeMultiple_isNilpotent _
  rw [show (p : ZMod (p ^ j)) * q * (x + y) + p * u + b =
      p * (q * (x + y) + u) + b by ring]
  exact hnil.isUnit_add_right_of_commute hb (Commute.all _ _)

/-- Equality after applying the branch map is equivalent to equality before
applying it.  Equality in `ZMod (p^j)` is congruence modulo `p^j`. -/
theorem padicBranchMap_eq_iff
    {p j : ℕ} {b : ZMod (p ^ j)} (hb : IsUnit b)
    (q u v x y : ZMod (p ^ j)) :
    padicBranchMap (p : ZMod (p ^ j)) q u b v x =
        padicBranchMap (p : ZMod (p ^ j)) q u b v y ↔ x = y := by
  constructor
  · intro hxy
    have hunit := padicBranchMap_differenceFactor_isUnit hb q u x y
    have hzero :
        (x - y) * ((p : ZMod (p ^ j)) * q * (x + y) + p * u + b) = 0 := by
      rw [← padicBranchMap_sub_factor]
      rw [hxy, sub_self]
    have hsub : x - y = 0 := hunit.mul_left_injective (by simpa using hzero)
    exact sub_eq_zero.mp hsub
  · exact fun hxy ↦ congrArg (padicBranchMap (p : ZMod (p ^ j)) q u b v) hxy

/-- The branch polynomial permutes every `ZMod (p^j)`. -/
theorem padicBranchMap_bijective
    {p j : ℕ} (hp0 : 0 < p) {b : ZMod (p ^ j)} (hb : IsUnit b)
    (q u v : ZMod (p ^ j)) :
    Function.Bijective (padicBranchMap (p : ZMod (p ^ j)) q u b v) := by
  have hinj : Function.Injective
      (padicBranchMap (p : ZMod (p ^ j)) q u b v) := by
    intro x y hxy
    exact (padicBranchMap_eq_iff hb q u v x y).mp hxy
  letI : NeZero (p ^ j) := ⟨pow_ne_zero j (Nat.ne_of_gt hp0)⟩
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- A natural number not divisible by the prime `p` remains a unit modulo
every power `p^j`. -/
theorem natCast_isUnit_zmod_primePow
    {p j b : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b) :
    IsUnit (b : ZMod (p ^ j)) := by
  exact (ZMod.isUnit_iff_coprime b (p ^ j)).2
    (hp.coprime_pow_of_not_dvd hpb)

/-- Equation (26) stated as an integer congruence equivalence.  The
coefficients `q,u,v` may depend on the branch and on the chosen root. -/
theorem padicBranchMap_int_congr_iff
    {p j b : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (q u v : ZMod (p ^ j)) (x y : ℤ) :
    padicBranchMap (p : ZMod (p ^ j)) q u b v x =
        padicBranchMap (p : ZMod (p ^ j)) q u b v y ↔
      x ≡ y [ZMOD p ^ j] := by
  rw [padicBranchMap_eq_iff (natCast_isUnit_zmod_primePow hp hpb) q u v]
  exact ZMod.intCast_eq_intCast_iff x y (p ^ j)

/-! ## Exact one-class removal and digit-box cardinality -/

/-- Under a permutation of a finite type, the preimage of a finite allowed
set has exactly the cardinality of that set. -/
theorem card_filter_preimage_of_bijective
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : α → α) (hG : Function.Bijective G) (A : Finset α) :
    (Finset.univ.filter fun x ↦ G x ∈ A).card = A.card := by
  exact Finset.card_bijective G hG (by intro x; simp)

/-- If one allowed image `G x0` is removed, exactly one domain residue is
removed.  This is the finite permutation content of the sentence before
equation (28). -/
theorem card_filter_preimage_erase_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : α → α) (hG : Function.Bijective G) (A : Finset α)
    (x0 : α) (hx0 : G x0 ∈ A) :
    (Finset.univ.filter fun x ↦ G x ∈ A.erase (G x0)).card = A.card - 1 := by
  rw [card_filter_preimage_of_bijective G hG]
  exact Finset.card_erase_of_mem hx0

/-- Abstract digit box: the first digit lies in `A` with one endpoint
removed, while each of the remaining `d-1` digits lies in `A`. -/
def RestrictedDigitBox {α : Type*} [DecidableEq α]
    (A : Finset α) (endpoint : α) (d : ℕ) :=
  ↥(A.erase endpoint) × (Fin (d - 1) → ↥A)

instance restrictedDigitBoxFintype {α : Type*} [DecidableEq α]
    (A : Finset α) (endpoint : α) (d : ℕ) :
    Fintype (RestrictedDigitBox A endpoint d) := by
  unfold RestrictedDigitBox
  infer_instance

/-- Equation (28) as an exact finite cardinality identity. -/
theorem restrictedDigitBox_card
    {α : Type*} [DecidableEq α]
    (A : Finset α) (endpoint : α) (d H : ℕ)
    (hendpoint : endpoint ∈ A) (hcard : A.card = H) :
    Fintype.card (RestrictedDigitBox A endpoint d) =
      (H - 1) * H ^ (d - 1) := by
  change Fintype.card (↥(A.erase endpoint) × (Fin (d - 1) → ↥A)) = _
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Fintype.card_coe, Finset.card_erase_of_mem hendpoint, hcard]

end Erdos730

end Campaign180File24

/- Source module: ErdosProblems.Erdos730.HigherPowerCount -/
section Campaign180File25
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: finite higher-power counting

This file isolates the unconditional finite counting statements used in
§5 of the positive-density proof.  There are two independent parts.

* A predicate on residues modulo `q` occurs in an interval of `N`
  consecutive integers at most `(N / q + 1)` times its full-period count.
  Applying this to a bijective p-adic branch map gives the complete/padded
  block bound in (26), including depth `r = 0`.
* The finite set of pairs `(p,a)` with `p` prime, `a ≥ 2`, and `p^a ≤ Z`
  has cardinality at most
  `sqrt Z + cubeRootFloor Z * log 2 Z`.  This is the exact natural-number
  form of (27).

No asymptotic assertion is made here.
-/

namespace Erdos730

/-! ## Consecutive intervals modulo a positive modulus -/

/-- Number of offsets `i < N` for which `start + i` has an allowed residue
modulo `q`. -/
def intervalResidueCount (q start N : ℕ) (P : ZMod q → Prop)
    [DecidablePred P] : ℕ :=
  (Finset.range N).filter (fun i ↦ P ((start + i : ℕ) : ZMod q)) |>.card

/-- A consecutive interval meets an allowed residue set no more often than
the number of offset blocks times the number of allowed residues in one
complete period.  The harmless `+1` is the padded final block.

This theorem is deliberately stated for arbitrary predicates on `ZMod q`;
the p-adic polynomial enters only in the corollary below. -/
theorem intervalResidueCount_le
    {q start N : ℕ} [NeZero q] (P : ZMod q → Prop) [DecidablePred P] :
    intervalResidueCount q start N P ≤
      (N / q + 1) * (Finset.univ.filter P).card := by
  let source : Finset ℕ :=
    (Finset.range N).filter (fun i ↦ P ((start + i : ℕ) : ZMod q))
  let target : Type := Fin (N / q + 1) × ↑(Finset.univ.filter P)
  let encode : ↑source → target := fun i ↦
    (⟨i.1 / q, by
        apply Nat.lt_succ_iff.mpr
        apply Nat.div_le_div_right
        exact (Finset.mem_range.mp (Finset.mem_filter.mp i.2).1).le⟩,
      ⟨((start + i.1 : ℕ) : ZMod q), by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp i.2).2⟩⟩)
  have hencode : Function.Injective encode := by
    intro i j hij
    have hdiv : i.1 / q = j.1 / q := by
      simpa [encode] using congrArg (fun z : target ↦ (z.1 : ℕ)) hij
    have hcast : ((start + i.1 : ℕ) : ZMod q) =
        ((start + j.1 : ℕ) : ZMod q) := by
      simpa [encode] using congrArg (fun z : target ↦ (z.2.1 : ZMod q)) hij
    have hadd : start + i.1 ≡ start + j.1 [MOD q] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have hmod : i.1 % q = j.1 % q := by
      exact Nat.ModEq.add_left_cancel' start hadd
    apply Subtype.ext
    calc
      i.1 = q * (i.1 / q) + i.1 % q := (Nat.div_add_mod i.1 q).symm
      _ = q * (j.1 / q) + j.1 % q := by rw [hdiv, hmod]
      _ = j.1 := Nat.div_add_mod j.1 q
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [intervalResidueCount, source, target, Fintype.card_subtype] using hcard

/-- The count after a bijection of residues is bounded by the number of
padded blocks times the cardinality of the allowed image set. -/
theorem interval_bijective_preimage_count_le
    {q start N : ℕ} [NeZero q]
    (G : ZMod q → ZMod q) (hG : Function.Bijective G)
    (A : Finset (ZMod q)) :
    intervalResidueCount q start N (fun z ↦ G z ∈ A) ≤
      (N / q + 1) * A.card := by
  calc
    intervalResidueCount q start N (fun z ↦ G z ∈ A) ≤
        (N / q + 1) * (Finset.univ.filter fun z ↦ G z ∈ A).card :=
      intervalResidueCount_le _
    _ = (N / q + 1) * A.card := by
      rw [card_filter_preimage_of_bijective G hG A]

/-! ## The p-adic branch-map block bound -/

/-- Count of offsets in a consecutive parameter interval whose image under a
p-adic branch map belongs to `A`. -/
def padicBranchAllowedCount
    (p r start N : ℕ) (q u b v : ZMod (p ^ r))
    (A : Finset (ZMod (p ^ r))) : ℕ :=
  intervalResidueCount (p ^ r) start N
    (fun z ↦ padicBranchMap (p : ZMod (p ^ r)) q u b v z ∈ A)

/-- Complete/padded block form of the first inequality in (26).

If the allowed set has `H^r` residues, an interval of `N` parameters contains
at most `(N / p^r + 1) H^r` allowed branch values.  There is no `r ≥ 1`
hypothesis: at `r = 0`, `ZMod (p^0)` is the one-element ring and the bound is
the intended vacuous digit bound. -/
theorem padicBranchAllowedCount_le
    {p r start N H : ℕ} (hp : p.Prime)
    (q u v : ZMod (p ^ r)) {b : ZMod (p ^ r)} (hb : IsUnit b)
    (A : Finset (ZMod (p ^ r))) (hA : A.card = H ^ r) :
    padicBranchAllowedCount p r start N q u b v A ≤
      (N / p ^ r + 1) * H ^ r := by
  letI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  unfold padicBranchAllowedCount
  calc
    intervalResidueCount (p ^ r) start N
          (fun z ↦ padicBranchMap (p : ZMod (p ^ r)) q u b v z ∈ A)
        ≤ (N / p ^ r + 1) * A.card :=
      interval_bijective_preimage_count_le _
        (padicBranchMap_bijective hp.pos hb q u v) A
    _ = (N / p ^ r + 1) * H ^ r := by rw [hA]

/-- Version used when a root progression has at most `U+1` parameters.
This is the exact finite, floor-valued form of the first bound in (26). -/
theorem padicBranchAllowedCount_le_of_length
    {p r start N H U : ℕ} (hp : p.Prime)
    (q u v : ZMod (p ^ r)) {b : ZMod (p ^ r)} (hb : IsUnit b)
    (A : Finset (ZMod (p ^ r))) (hA : A.card = H ^ r)
    (hN : N ≤ U + 1) :
    padicBranchAllowedCount p r start N q u b v A ≤
      ((U + 1) / p ^ r + 1) * H ^ r := by
  calc
    padicBranchAllowedCount p r start N q u b v A
        ≤ (N / p ^ r + 1) * H ^ r :=
      padicBranchAllowedCount_le hp q u v hb A hA
    _ ≤ ((U + 1) / p ^ r + 1) * H ^ r := by
      exact Nat.mul_le_mul_right _
        (Nat.add_le_add_right (Nat.div_le_div_right hN) 1)

/-! ## Exact finite higher-prime-power pair count -/

/-- Floor cube root, defined without introducing an analytic real root. -/
def cubeRootFloor (Z : ℕ) : ℕ :=
  Nat.findGreatest (fun n ↦ n ^ 3 ≤ Z) Z

/-- The floor cube root really has cube at most `Z`. -/
theorem cubeRootFloor_pow_le (Z : ℕ) : cubeRootFloor Z ^ 3 ≤ Z := by
  unfold cubeRootFloor
  exact Nat.findGreatest_spec (P := fun n ↦ n ^ 3 ≤ Z) (m := 0)
    (Nat.zero_le Z) (by norm_num)

/-- Every natural whose cube is at most `Z` is at most the floor cube root. -/
theorem le_cubeRootFloor {n Z : ℕ} (hnZ : n ≤ Z) (hcube : n ^ 3 ≤ Z) :
    n ≤ cubeRootFloor Z := by
  exact Nat.le_findGreatest hnZ hcube

/-- The finite set counted by `M(Z)` in (27).  The range bounds are redundant
under the filter conditions; they only make the set computationally finite. -/
def higherPrimePowerPairs (Z : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Z + 1)).product (Finset.range (Nat.log 2 Z + 1))).filter
    (fun pa ↦ pa.1.Prime ∧ 2 ≤ pa.2 ∧ pa.1 ^ pa.2 ≤ Z)

/-- The computational range bounds in `higherPrimePowerPairs` lose no pairs:
this is exactly the predicate defining `M(Z)` in the paper. -/
theorem mem_higherPrimePowerPairs_iff {p a Z : ℕ} :
    (p, a) ∈ higherPrimePowerPairs Z ↔
      p.Prime ∧ 2 ≤ a ∧ p ^ a ≤ Z := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hp, ha2, hpow⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
      Finset.mem_range.mpr ?_⟩, ⟨hp, ha2, hpow⟩⟩
    · have hp_le_pow : p ≤ p ^ a := by
        calc
          p = p ^ 1 := by simp
          _ ≤ p ^ a := pow_le_pow_right' hp.one_le (by omega)
      omega
    · have htwoPow : 2 ^ a ≤ Z :=
        (Nat.pow_le_pow_left hp.two_le a).trans hpow
      have haLog : a ≤ Nat.log 2 Z :=
        Nat.le_log_of_pow_le (by norm_num) htwoPow
      omega

/-- Every higher-prime-power pair lies either on the square row below
`sqrt Z`, or in the rectangle below `cubeRootFloor Z` and `log_2 Z`. -/
theorem higherPrimePowerPairs_subset_boxes (Z : ℕ) :
    higherPrimePowerPairs Z ⊆
      ((Finset.Icc 2 (Nat.sqrt Z)).product {2}) ∪
        ((Finset.Icc 2 (cubeRootFloor Z)).product
          (Finset.Icc 3 (Nat.log 2 Z))) := by
  intro pa hpa
  rcases mem_higherPrimePowerPairs_iff.mp hpa with ⟨hp, ha2, hpow⟩
  by_cases hea : pa.2 = 2
  · apply Finset.mem_union_left
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩,
      Finset.mem_singleton.mpr hea⟩
    exact Nat.le_sqrt'.2 (by simpa [hea] using hpow)
  · apply Finset.mem_union_right
    have ha3 : 3 ≤ pa.2 := by omega
    have hpone : 1 ≤ pa.1 := hp.one_le
    have hp3 : pa.1 ^ 3 ≤ Z :=
      (pow_le_pow_right' hpone ha3).trans hpow
    have hp_le_cube : pa.1 ≤ pa.1 ^ 3 := by
      calc
        pa.1 = pa.1 ^ 1 := by simp
        _ ≤ pa.1 ^ 3 := pow_le_pow_right' hpone (by omega)
    have hp_le_Z : pa.1 ≤ Z := hp_le_cube.trans hp3
    have hpCube : pa.1 ≤ cubeRootFloor Z := le_cubeRootFloor hp_le_Z hp3
    have htwoPow : 2 ^ pa.2 ≤ Z :=
      (Nat.pow_le_pow_left hp.two_le pa.2).trans hpow
    have haBound : pa.2 ≤ Nat.log 2 Z :=
      Nat.le_log_of_pow_le (by norm_num) htwoPow
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpCube⟩,
        Finset.mem_Icc.mpr ⟨ha3, haBound⟩⟩

/-- Exact finite inequality behind (27):

`M(Z) ≤ floor(sqrt Z) + floor(cuberoot Z) * floor(log_2 Z)`.

The paper's displayed bound uses the corresponding real quantities, which
are weakly larger. -/
theorem higherPrimePowerPairs_card_le (Z : ℕ) :
    (higherPrimePowerPairs Z).card ≤
      Nat.sqrt Z + cubeRootFloor Z * Nat.log 2 Z := by
  let squares : Finset (ℕ × ℕ) :=
    (Finset.Icc 2 (Nat.sqrt Z)).product {2}
  let higher : Finset (ℕ × ℕ) :=
    (Finset.Icc 2 (cubeRootFloor Z)).product
      (Finset.Icc 3 (Nat.log 2 Z))
  have hsubset : higherPrimePowerPairs Z ⊆ squares ∪ higher := by
    simpa [squares, higher] using higherPrimePowerPairs_subset_boxes Z
  have hsq : squares.card ≤ Nat.sqrt Z := by
    have hcard := Finset.card_product (Finset.Icc 2 (Nat.sqrt Z)) ({2} : Finset ℕ)
    rw [Nat.card_Icc, Finset.card_singleton, mul_one] at hcard
    rw [show squares.card = Nat.sqrt Z + 1 - 2 from hcard]
    omega
  have hhigher : higher.card ≤ cubeRootFloor Z * Nat.log 2 Z := by
    have hcard := Finset.card_product (Finset.Icc 2 (cubeRootFloor Z))
      (Finset.Icc 3 (Nat.log 2 Z))
    rw [Nat.card_Icc, Nat.card_Icc] at hcard
    rw [show higher.card =
      (cubeRootFloor Z + 1 - 2) * (Nat.log 2 Z + 1 - 3) from hcard]
    apply Nat.mul_le_mul <;> omega
  calc
    (higherPrimePowerPairs Z).card ≤ (squares ∪ higher).card :=
      Finset.card_le_card hsubset
    _ ≤ squares.card + higher.card := Finset.card_union_le _ _
    _ ≤ Nat.sqrt Z + cubeRootFloor Z * Nat.log 2 Z :=
      Nat.add_le_add hsq hhigher

end Erdos730

end Campaign180File25

/- Source module: ErdosProblems.Erdos730.DominatedLimit -/
section Campaign180File26
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: dominated limits for the higher-prime-power range

This file supplies the unconditional analytic limit layer behind the finite
higher-power estimates in `Erdos730HigherPowerCount`.

The exponent coordinate in `HigherPowerIndex` is shifted: `(p, k)` represents
the prime power `p^(k+2)`.  The majorant is therefore exactly
`2 / p^(k+2)`.  We prove that this majorant is summable and apply Tannery's
theorem to any nonnegative family converging pointwise to zero.

No claim is made here that a particular event count satisfies these hypotheses;
that specialization still has to instantiate the finite block estimate and its
depth parameter.
-/

open Filter Topology

namespace Erdos730

/-- A prime together with a shifted exponent.  `(p,k)` denotes exponent
`a = k+2`, so every represented exponent is at least two. -/
abbrev HigherPowerIndex := Nat.Primes × ℕ

/-- The summable majorant `2 / p^(k+2)`, written in factored form so its
summability is transparent. -/
noncomputable def higherPowerMajorant (i : HigherPowerIndex) : ℝ :=
  (2 * (i.1 : ℝ)⁻¹ ^ 2) * (i.1 : ℝ)⁻¹ ^ i.2

theorem higherPowerMajorant_eq (i : HigherPowerIndex) :
    higherPowerMajorant i = 2 / (i.1 : ℝ) ^ (i.2 + 2) := by
  rw [higherPowerMajorant, div_eq_mul_inv, inv_pow, pow_add]
  ring

theorem higherPowerMajorant_nonneg (i : HigherPowerIndex) :
    0 ≤ higherPowerMajorant i := by
  unfold higherPowerMajorant
  positivity

private theorem primeInv_le_half (p : Nat.Primes) :
    (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
  rw [inv_le_inv₀ (by exact_mod_cast p.prop.pos) (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast p.prop.two_le

/-- The double series `sum_p sum_(a>=2) 2/p^a` converges. -/
theorem higherPowerMajorant_summable : Summable higherPowerMajorant := by
  have hpNat : Summable (fun n : ℕ ↦ 2 * ((n : ℝ) ^ 2)⁻¹) := by
    exact (Real.summable_nat_pow_inv.mpr (by omega)).mul_left 2
  have hp : Summable (fun p : Nat.Primes ↦ 2 * (p : ℝ)⁻¹ ^ 2) := by
    have h := hpNat.comp_injective (i := fun p : Nat.Primes ↦ (p : ℕ))
      Subtype.val_injective
    simpa [inv_pow] using! h
  have ha : Summable (fun k : ℕ ↦ ((2 : ℝ)⁻¹) ^ k) := by
    exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hprod : Summable (fun i : HigherPowerIndex ↦
      (2 * (i.1 : ℝ)⁻¹ ^ 2) * ((2 : ℝ)⁻¹) ^ i.2) :=
    hp.mul_of_nonneg ha (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  refine hprod.of_nonneg_of_le higherPowerMajorant_nonneg ?_
  intro i
  unfold higherPowerMajorant
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (primeInv_le_half i.1) i.2)
    (by positivity)

/-- Tannery/dominated convergence for the exact higher-power majorant.

This is the countable analytic passage needed after the finite bound has been
normalized: each fixed prime/exponent contribution tends to zero, and every
contribution is bounded by `2/p^a`. -/
theorem tendsto_tsum_higherPower_of_dominated
    (f : ℕ → HigherPowerIndex → ℝ)
    (hpoint : ∀ i, Tendsto (fun X ↦ f X i) atTop (𝓝 0))
    (hnonneg : ∀ X i, 0 ≤ f X i)
    (hbound : ∀ X i, f X i ≤ higherPowerMajorant i) :
    Tendsto (fun X ↦ ∑' i, f X i) atTop (𝓝 0) := by
  have hdom : ∀ᶠ X in atTop, ∀ i, ‖f X i‖ ≤ higherPowerMajorant i :=
    Eventually.of_forall fun X i ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg X i)]
      exact hbound X i
  simpa using tendsto_tsum_of_dominated_convergence
    higherPowerMajorant_summable hpoint hdom

/-- Iterated-sum form of `tendsto_tsum_higherPower_of_dominated`. -/
theorem tendsto_iterated_tsum_higherPower_of_dominated
    (f : ℕ → Nat.Primes → ℕ → ℝ)
    (hpoint : ∀ p k, Tendsto (fun X ↦ f X p k) atTop (𝓝 0))
    (hnonneg : ∀ X p k, 0 ≤ f X p k)
    (hbound : ∀ X p k,
      f X p k ≤ higherPowerMajorant (p, k)) :
    Tendsto (fun X ↦ ∑' p : Nat.Primes, ∑' k : ℕ, f X p k)
      atTop (𝓝 0) := by
  let F : ℕ → HigherPowerIndex → ℝ := fun X i ↦ f X i.1 i.2
  have hFsum (X : ℕ) : Summable (F X) := by
    refine higherPowerMajorant_summable.of_nonneg_of_le ?_ ?_
    · intro i
      exact hnonneg X i.1 i.2
    · intro i
      exact hbound X i.1 i.2
  have hlim : Tendsto (fun X ↦ ∑' i, F X i) atTop (𝓝 0) :=
    tendsto_tsum_higherPower_of_dominated F
      (fun i ↦ hpoint i.1 i.2)
      (fun X i ↦ hnonneg X i.1 i.2)
      (fun X i ↦ hbound X i.1 i.2)
  convert hlim using 1
  ext X
  simpa [F] using (hFsum X).tsum_prod.symm

/-! ## The finite box-count error is sublinear -/

/-- The real comparison function for the cube-root/logarithm term tends to
zero after division by its argument. -/
theorem tendsto_rpow_third_mul_logb_div_atTop :
    Tendsto (fun x : ℝ ↦ x ^ (1 / 3 : ℝ) * Real.logb 2 x / x)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x ^ (2 / 3 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
  have hscaled := hlog.const_mul ((Real.log 2)⁻¹)
  simpa only [mul_zero] using hscaled.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hrpow : x ^ (1 / 3 : ℝ) / x = 1 / x ^ (2 / 3 : ℝ) := by
      calc
        x ^ (1 / 3 : ℝ) / x =
            x ^ (1 / 3 : ℝ) / x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = x ^ ((1 / 3 : ℝ) - 1) := (Real.rpow_sub hx _ _).symm
        _ = x ^ (-(2 / 3 : ℝ)) := by norm_num
        _ = 1 / x ^ (2 / 3 : ℝ) := by
          rw [Real.rpow_neg hx.le]
          simp [one_div]
    rw [Real.logb]
    calc
      (Real.log 2)⁻¹ * (Real.log x / x ^ (2 / 3 : ℝ)) =
          (Real.log x / Real.log 2) * (1 / x ^ (2 / 3 : ℝ)) := by ring
      _ = (Real.log x / Real.log 2) * (x ^ (1 / 3 : ℝ) / x) := by rw [hrpow]
      _ = x ^ (1 / 3 : ℝ) * (Real.log x / Real.log 2) / x := by ring)

/-- The exact natural floor cube root is bounded by the corresponding real
power. -/
theorem cubeRootFloor_cast_le_rpow (Z : ℕ) :
    (cubeRootFloor Z : ℝ) ≤ (Z : ℝ) ^ (1 / 3 : ℝ) := by
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by norm_num : (0 : ℝ) < 3)]
  exact_mod_cast cubeRootFloor_pow_le Z

/-- The natural square/cube-root/logarithm box bound from (27), divided by
`Z`, tends to zero.  This turns the finite cardinality estimate into the
precise `o(Z)` assertion needed for the `+1` and terminal-prime-power terms. -/
theorem tendsto_higherPrimePower_boxBound_div :
    Tendsto (fun Z : ℕ ↦
      ((Nat.sqrt Z + cubeRootFloor Z * Nat.log 2 Z : ℕ) : ℝ) / (Z : ℝ))
      atTop (𝓝 0) := by
  let comparison : ℕ → ℝ := fun Z ↦
    Real.sqrt (Z : ℝ) / (Z : ℝ) +
      ((Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ)) / (Z : ℝ)
  have hsqrt : Tendsto (fun Z : ℕ ↦ Real.sqrt (Z : ℝ) / (Z : ℝ))
      atTop (𝓝 0) := by
    have htop : Tendsto (fun Z : ℕ ↦ Real.sqrt (Z : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [Real.sqrt_div_self] using! htop.inv_tendsto_atTop
  have hcubelog : Tendsto (fun Z : ℕ ↦
      ((Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ)) / (Z : ℝ))
      atTop (𝓝 0) :=
    tendsto_rpow_third_mul_logb_div_atTop.comp tendsto_natCast_atTop_atTop
  have hcomparison : Tendsto comparison atTop (𝓝 0) := by
    simpa only [comparison, zero_add] using hsqrt.add hcubelog
  apply squeeze_zero' (Eventually.of_forall fun Z ↦ by positivity)
    (Eventually.of_forall fun Z ↦ ?_) hcomparison
  have hsqrtLe : (Nat.sqrt Z : ℝ) ≤ Real.sqrt (Z : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hcubeLe : (cubeRootFloor Z : ℝ) ≤ (Z : ℝ) ^ (1 / 3 : ℝ) :=
    cubeRootFloor_cast_le_rpow Z
  have hlogLe : (Nat.log 2 Z : ℝ) ≤ Real.logb 2 (Z : ℝ) :=
    Real.natLog_le_logb Z 2
  have hcubeLogLe :
      (cubeRootFloor Z : ℝ) * (Nat.log 2 Z : ℝ) ≤
        (Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ) := by
    exact mul_le_mul hcubeLe hlogLe (Nat.cast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hnum :
      (Nat.sqrt Z : ℝ) + (cubeRootFloor Z : ℝ) * (Nat.log 2 Z : ℝ) ≤
        Real.sqrt (Z : ℝ) +
          (Z : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Z : ℝ) :=
    add_le_add hsqrtLe hcubeLogLe
  simpa only [comparison, Nat.cast_add, Nat.cast_mul, add_div] using
    div_le_div_of_nonneg_right hnum (Nat.cast_nonneg Z)

/-- Direct consequence for the actual finite set `M(Z)`. -/
theorem tendsto_higherPrimePowerPairs_card_div :
    Tendsto (fun Z : ℕ ↦ ((higherPrimePowerPairs Z).card : ℝ) / (Z : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun Z ↦ by positivity)
    (Eventually.of_forall fun Z ↦ ?_)
    tendsto_higherPrimePower_boxBound_div
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast higherPrimePowerPairs_card_le Z) (Nat.cast_nonneg Z)

end Erdos730

end Campaign180File26

/- Source module: ErdosProblems.Erdos730.FixedDepthParity -/
section Campaign180File27
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: a character-free fixed-depth digit-parity estimate

This file isolates a finite combinatorial shadow of the fixed-depth Fourier
step in the positive-density proof.  Suppose an independent base-`p` digit
has `marked` possible values which toggle a parity bit and `unmarked` possible
values which preserve it.  `digitParityCounts marked unmarked d` is the exact
two-state recurrence for the number of length-`d` strings ending in even and
odd parity.

For the half-digit alphabet used in the Erdős 730 argument, `p = 2*H-1`,
`marked = H`, and `unmarked = H-1`.  The two parity classes then differ by
exactly one string at every depth.  In particular the doubled even count has
absolute error exactly `1` from the uniform main term `p^d`; after
normalization the error is exactly `1/(2*p^d)`.

This is deliberately character-free: it is the order-two finite Fourier
calculation written as an exact integer recurrence.  It does not assert the
quadratic incomplete-sum estimate of Lemma 2 in the paper proof.
-/

namespace Erdos730

/-- Exact even/odd counts for `d` independent digits.  A marked digit toggles
the parity state, while an unmarked digit preserves it. -/
def digitParityCounts (marked unmarked : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | d + 1 =>
      let previous := digitParityCounts marked unmarked d
      (unmarked * previous.1 + marked * previous.2,
        marked * previous.1 + unmarked * previous.2)

/-- Number of digit strings with even marked-digit parity. -/
def evenDigitParityCount (marked unmarked d : ℕ) : ℕ :=
  (digitParityCounts marked unmarked d).1

/-- Number of digit strings with odd marked-digit parity. -/
def oddDigitParityCount (marked unmarked d : ℕ) : ℕ :=
  (digitParityCounts marked unmarked d).2

@[simp] theorem evenDigitParityCount_zero (marked unmarked : ℕ) :
    evenDigitParityCount marked unmarked 0 = 1 := rfl

@[simp] theorem oddDigitParityCount_zero (marked unmarked : ℕ) :
    oddDigitParityCount marked unmarked 0 = 0 := rfl

@[simp] theorem evenDigitParityCount_succ (marked unmarked d : ℕ) :
    evenDigitParityCount marked unmarked (d + 1) =
      unmarked * evenDigitParityCount marked unmarked d +
        marked * oddDigitParityCount marked unmarked d := by
  rfl

@[simp] theorem oddDigitParityCount_succ (marked unmarked d : ℕ) :
    oddDigitParityCount marked unmarked (d + 1) =
      marked * evenDigitParityCount marked unmarked d +
        unmarked * oddDigitParityCount marked unmarked d := by
  rfl

/-- The two parity classes partition all `(marked + unmarked)^d` strings. -/
theorem digitParityCounts_total (marked unmarked d : ℕ) :
    evenDigitParityCount marked unmarked d +
        oddDigitParityCount marked unmarked d =
      (marked + unmarked) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [evenDigitParityCount_succ, oddDigitParityCount_succ, pow_succ]
      calc
        unmarked * evenDigitParityCount marked unmarked d +
              marked * oddDigitParityCount marked unmarked d +
            (marked * evenDigitParityCount marked unmarked d +
              unmarked * oddDigitParityCount marked unmarked d) =
            (marked + unmarked) *
              (evenDigitParityCount marked unmarked d +
                oddDigitParityCount marked unmarked d) := by ring
        _ = (marked + unmarked) * (marked + unmarked) ^ d := by rw [ih]
        _ = (marked + unmarked) ^ d * (marked + unmarked) := by ring

/-- The signed parity imbalance is the `d`-th power of the one-digit
imbalance.  This is the character-free form of the nontrivial order-two
Fourier coefficient. -/
theorem digitParityCounts_intDifference (marked unmarked d : ℕ) :
    (evenDigitParityCount marked unmarked d : ℤ) -
        oddDigitParityCount marked unmarked d =
      ((unmarked : ℤ) - marked) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [evenDigitParityCount_succ, oddDigitParityCount_succ, pow_succ]
      push_cast
      rw [← ih]
      ring

/-- For an odd alphabet of size `2*H-1`, split into `H` marked and `H-1`
unmarked digits, the signed parity discrepancy is exactly `(-1)^d`. -/
theorem halfDigitParity_intDifference (H d : ℕ) (hH : 1 ≤ H) :
    (evenDigitParityCount H (H - 1) d : ℤ) -
        oddDigitParityCount H (H - 1) d = (-1 : ℤ) ^ d := by
  rw [digitParityCounts_intDifference]
  have hcast : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
  rw [hcast]
  ring_nf

/-- The exact total count for the odd half-alphabet specialization. -/
theorem halfDigitParity_total (H d : ℕ) (hH : 1 ≤ H) :
    evenDigitParityCount H (H - 1) d +
        oddDigitParityCount H (H - 1) d =
      (2 * H - 1) ^ d := by
  rw [digitParityCounts_total]
  congr 1
  omega

/-- Explicit absolute-error estimate: twice the even-parity count differs
from its uniform main term `(2*H-1)^d` by exactly one. -/
theorem halfDigitParity_exactAbsoluteError (H d : ℕ) (hH : 1 ≤ H) :
    Int.natAbs
        (2 * (evenDigitParityCount H (H - 1) d : ℤ) -
          ((2 * H - 1) ^ d : ℕ)) = 1 := by
  have htotal := halfDigitParity_total H d hH
  have hdiff := halfDigitParity_intDifference H d hH
  have hrewrite :
      2 * (evenDigitParityCount H (H - 1) d : ℤ) -
          ((2 * H - 1) ^ d : ℕ) =
        (evenDigitParityCount H (H - 1) d : ℤ) -
          oddDigitParityCount H (H - 1) d := by
    have htotalZ :
        (evenDigitParityCount H (H - 1) d : ℤ) +
            oddDigitParityCount H (H - 1) d =
          ((2 * H - 1) ^ d : ℕ) := by
      exact_mod_cast htotal
    rw [← htotalZ]
    ring
  rw [hrewrite, hdiff, Int.natAbs_pow]
  norm_num

/-- Real-valued version of the exact error.  This is often the most useful
form when the finite count is inserted into a density estimate. -/
theorem halfDigitParity_realAbsoluteError (H d : ℕ) (hH : 1 ≤ H) :
    |2 * (evenDigitParityCount H (H - 1) d : ℝ) -
        ((2 * H - 1) ^ d : ℕ)| = 1 := by
  have hdiff := halfDigitParity_intDifference H d hH
  have htotal := halfDigitParity_total H d hH
  have hint :
      2 * (evenDigitParityCount H (H - 1) d : ℤ) -
          ((2 * H - 1) ^ d : ℕ) = (-1 : ℤ) ^ d := by
    calc
      2 * (evenDigitParityCount H (H - 1) d : ℤ) -
            ((2 * H - 1) ^ d : ℕ) =
          (evenDigitParityCount H (H - 1) d : ℤ) -
            oddDigitParityCount H (H - 1) d := by
              have htotalZ :
                  (evenDigitParityCount H (H - 1) d : ℤ) +
                      oddDigitParityCount H (H - 1) d =
                    ((2 * H - 1) ^ d : ℕ) := by
                exact_mod_cast htotal
              rw [← htotalZ]
              ring
      _ = (-1 : ℤ) ^ d := hdiff
  have hreal :
      2 * (evenDigitParityCount H (H - 1) d : ℝ) -
          ((2 * H - 1) ^ d : ℕ) = (-1 : ℝ) ^ d := by
    exact_mod_cast hint
  rw [hreal, abs_pow]
  norm_num

/-- Normalized discrepancy of the even-parity probability from `1/2`.
The denominator is nonzero because `H>=1`. -/
theorem halfDigitParity_probabilityError (H d : ℕ) (hH : 1 ≤ H) :
    |(evenDigitParityCount H (H - 1) d : ℝ) /
          ((2 * H - 1) ^ d : ℕ) - 1 / 2| =
      1 / (2 * ((2 * H - 1) ^ d : ℕ)) := by
  have hbase : 0 < (2 * H - 1 : ℕ) := by omega
  have hden : (0 : ℝ) < ((2 * H - 1) ^ d : ℕ) := by positivity
  have herr := halfDigitParity_realAbsoluteError H d hH
  rw [abs_sub_comm]
  rw [show (1 / 2 : ℝ) -
          (evenDigitParityCount H (H - 1) d : ℝ) /
            ((2 * H - 1) ^ d : ℕ) =
        -((2 * (evenDigitParityCount H (H - 1) d : ℝ) -
              ((2 * H - 1) ^ d : ℕ)) /
            (2 * ((2 * H - 1) ^ d : ℕ))) by field_simp; ring]
  rw [abs_neg, abs_div, herr]
  rw [abs_of_pos (by positivity : (0 : ℝ) <
    2 * ((2 * H - 1) ^ d : ℕ))]


end Erdos730

end Campaign180File27

/- Source module: ErdosProblems.Erdos730.ObstructionMaps -/
section Campaign180File28
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: exact obstruction-map algebra

This file formalizes equations (13)--(17) of the positive-density proof.
Everything here is elementary algebra over `ℤ`; in particular, this module
contains no asymptotic or distributional assertion.

The integer-valued left descriptions are used as the definitions of the
four obstruction maps.  For the `R` and `S` branches, the division by two is
certified from parity before it is used.  The subsequent progression
identities expose the common quadratic coefficient and the four residual
linear coefficients exactly.
-/

namespace Erdos730
namespace ObstructionMaps

open FullDensityCore

/-! ## Integer copies of the four branches -/

def Tz : ℤ := (FullDensityCore.T : ℤ)

def Pz (x : ℤ) : ℤ := 42 * Tz * x + 11
def Qz (x : ℤ) : ℤ := 72 * Tz * x + 13
def Rz (x : ℤ) : ℤ := 28 * Tz * x + 5
def Sz (x : ℤ) : ℤ := 72 * Tz * x + 19

theorem Tz_eq : Tz = 5289 := by
  norm_num [Tz, FullDensityCore.T]

theorem branch_casts (x : ℕ) :
    Pz x = (FullDensityCore.P x : ℤ) ∧
    Qz x = (FullDensityCore.Q x : ℤ) ∧
    Rz x = (FullDensityCore.R x : ℤ) ∧
    Sz x = (FullDensityCore.S x : ℤ) := by
  norm_num [Pz, Qz, Rz, Sz, Tz, FullDensityCore.P,
    FullDensityCore.Q, FullDensityCore.R, FullDensityCore.S,
    FullDensityCore.T]

theorem identity_PQz (x : ℤ) : 12 * Pz x = 7 * Qz x + 41 := by
  simp only [Pz, Qz]
  ring

theorem identity_RSz (x : ℤ) : 18 * Rz x + 43 = 7 * Sz x := by
  simp only [Rz, Sz]
  ring

theorem Rz_odd (x : ℤ) : Odd (Rz x) := by
  refine ⟨14 * Tz * x + 2, ?_⟩
  simp only [Rz]
  ring

theorem Sz_odd (x : ℤ) : Odd (Sz x) := by
  refine ⟨36 * Tz * x + 9, ?_⟩
  simp only [Sz]
  ring

/-! ## Integer-valued left descriptions and cleared formulas -/

/-- `Phi_P(c) = c Q`, the integral left description in (13). -/
def PhiP (x c : ℤ) : ℤ := c * Qz x

/-- `Phi_Q(c) = c P`, the integral left description in (13). -/
def PhiQ (x c : ℤ) : ℤ := c * Pz x

/-- `Phi_R(c) = (3 c S - 1) / 2`, the integral left description in (14). -/
def PhiR (x c : ℤ) : ℤ := (3 * c * Sz x - 1) / 2

/-- `Phi_S(c) = (3 c R - 1) / 2`, the integral left description in (15). -/
def PhiS (x c : ℤ) : ℤ := (3 * c * Rz x - 1) / 2

lemma two_dvd_PhiR_numerator {x c : ℤ} (hc : Odd c) :
    (2 : ℤ) ∣ 3 * c * Sz x - 1 := by
  rcases hc with ⟨d, hd⟩
  rcases Sz_odd x with ⟨e, he⟩
  refine ⟨6 * d * e + 3 * d + 3 * e + 1, ?_⟩
  rw [hd, he]
  ring

lemma two_dvd_PhiS_numerator {x c : ℤ} (hc : Odd c) :
    (2 : ℤ) ∣ 3 * c * Rz x - 1 := by
  rcases hc with ⟨d, hd⟩
  rcases Rz_odd x with ⟨e, he⟩
  refine ⟨6 * d * e + 3 * d + 3 * e + 1, ?_⟩
  rw [hd, he]
  ring

/-- The left description in (14) really is integral. -/
theorem two_mul_PhiR {x c : ℤ} (hc : Odd c) :
    2 * PhiR x c = 3 * c * Sz x - 1 := by
  have h := Int.ediv_mul_cancel (two_dvd_PhiR_numerator (x := x) hc)
  simpa only [PhiR, mul_comm] using h

/-- The left description in (15) really is integral. -/
theorem two_mul_PhiS {x c : ℤ} (hc : Odd c) :
    2 * PhiS x c = 3 * c * Rz x - 1 := by
  have h := Int.ediv_mul_cancel (two_dvd_PhiS_numerator (x := x) hc)
  simpa only [PhiS, mul_comm] using h

lemma R_cofactor_odd {q x c : ℤ} (hbranch : q * c = Rz x) : Odd c := by
  have hprod : Odd (q * c) := by
    rw [hbranch]
    exact Rz_odd x
  exact (Int.odd_mul.mp hprod).2

lemma S_cofactor_odd {q x c : ℤ} (hbranch : q * c = Sz x) : Odd c := by
  have hprod : Odd (q * c) := by
    rw [hbranch]
    exact Sz_odd x
  exact (Int.odd_mul.mp hprod).2

/-- Cleared first formula in (13), under `q c = P(x)`. -/
theorem PhiP_cleared {q x c : ℤ} (hbranch : q * c = Pz x) :
    7 * PhiP x c = 12 * q * c ^ 2 - 41 * c := by
  simp only [PhiP]
  have hid := identity_PQz x
  linear_combination -c * hid - 12 * c * hbranch

/-- Cleared second formula in (13), under `q c = Q(x)`. -/
theorem PhiQ_cleared {q x c : ℤ} (hbranch : q * c = Qz x) :
    12 * PhiQ x c = 7 * q * c ^ 2 + 41 * c := by
  simp only [PhiQ]
  have hid := identity_PQz x
  linear_combination c * hid - 7 * c * hbranch

/-- Cleared formula (14), under `q c = R(x)`.  Oddness of `c`, and hence
integrality of the left description, follows from the branch equation. -/
theorem PhiR_cleared {q x c : ℤ} (hbranch : q * c = Rz x) :
    14 * PhiR x c = 54 * q * c ^ 2 + 129 * c - 7 := by
  have hc := R_cofactor_odd hbranch
  have hhalf := two_mul_PhiR (x := x) hc
  have hid := identity_RSz x
  linear_combination 7 * hhalf - 3 * c * hid - 54 * c * hbranch

/-- Cleared formula (15), under `q c = S(x)`.  Oddness of `c`, and hence
integrality of the left description, follows from the branch equation. -/
theorem PhiS_cleared {q x c : ℤ} (hbranch : q * c = Sz x) :
    12 * PhiS x c = 7 * q * c ^ 2 - 43 * c - 6 := by
  have hc := S_cofactor_odd hbranch
  have hhalf := two_mul_PhiS (x := x) hc
  have hid := identity_RSz x
  linear_combination 6 * hhalf + c * hid - 7 * c * hbranch

/-! ## Root-progression substitution: equations (16)--(17) -/

/-- The four numerator coefficients all reduce to the same quadratic
coefficient after division by their respective clearing denominator. -/
theorem common_quadratic_coefficient :
    12 * (42 * Tz) ^ 2 = 7 * (3024 * Tz ^ 2) ∧
    7 * (72 * Tz) ^ 2 = 12 * (3024 * Tz ^ 2) ∧
    54 * (28 * Tz) ^ 2 = 14 * (3024 * Tz ^ 2) ∧
    7 * (72 * Tz) ^ 2 = 12 * (3024 * Tz ^ 2) := by
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

lemma P_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Pz x0) :
    q * (c0 + 42 * Tz * k) = Pz (x0 + q * k) := by
  simp only [Pz] at hbranch ⊢
  linear_combination hbranch

lemma Q_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Qz x0) :
    q * (c0 + 72 * Tz * k) = Qz (x0 + q * k) := by
  simp only [Qz] at hbranch ⊢
  linear_combination hbranch

lemma R_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Rz x0) :
    q * (c0 + 28 * Tz * k) = Rz (x0 + q * k) := by
  simp only [Rz] at hbranch ⊢
  linear_combination hbranch

lemma S_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Sz x0) :
    q * (c0 + 72 * Tz * k) = Sz (x0 + q * k) := by
  simp only [Sz] at hbranch ⊢
  linear_combination hbranch

lemma R_progression_odd {c0 k : ℤ} (hc0 : Odd c0) :
    Odd (c0 + 28 * Tz * k) := by
  rcases hc0 with ⟨d, hd⟩
  refine ⟨d + 14 * Tz * k, ?_⟩
  rw [hd]
  ring

lemma S_progression_odd {c0 k : ℤ} (hc0 : Odd c0) :
    Odd (c0 + 72 * Tz * k) := by
  rcases hc0 with ⟨d, hd⟩
  refine ⟨d + 36 * Tz * k, ?_⟩
  rw [hd]
  ring

/-- `P` instance of (16), with `u_P = 144 T c₀` and `b_P = -246 T`. -/
theorem PhiP_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Pz x0) (k : ℤ) :
    PhiP (x0 + q * k) (c0 + 42 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (144 * Tz * c0) - 246 * Tz) * k + PhiP x0 c0 := by
  have hbase := PhiP_cleared hbranch
  have hshift := PhiP_cleared (P_shift_branch (k := k) hbranch)
  have hscaled :
      7 * PhiP (x0 + q * k) (c0 + 42 * Tz * k) =
        7 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (144 * Tz * c0) - 246 * Tz) * k + PhiP x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- `Q` instance of (16), with `u_Q = 84 T c₀` and `b_Q = 246 T`. -/
theorem PhiQ_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Qz x0) (k : ℤ) :
    PhiQ (x0 + q * k) (c0 + 72 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (84 * Tz * c0) + 246 * Tz) * k + PhiQ x0 c0 := by
  have hbase := PhiQ_cleared hbranch
  have hshift := PhiQ_cleared (Q_shift_branch (k := k) hbranch)
  have hscaled :
      12 * PhiQ (x0 + q * k) (c0 + 72 * Tz * k) =
        12 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (84 * Tz * c0) + 246 * Tz) * k + PhiQ x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- `R` instance of (16), with `u_R = 216 T c₀` and `b_R = 258 T`. -/
theorem PhiR_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Rz x0) (k : ℤ) :
    PhiR (x0 + q * k) (c0 + 28 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (216 * Tz * c0) + 258 * Tz) * k + PhiR x0 c0 := by
  have hbase := PhiR_cleared hbranch
  have hshift := PhiR_cleared (R_shift_branch (k := k) hbranch)
  have hscaled :
      14 * PhiR (x0 + q * k) (c0 + 28 * Tz * k) =
        14 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (216 * Tz * c0) + 258 * Tz) * k + PhiR x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- `S` instance of (16), with `u_S = 84 T c₀` and `b_S = -258 T`. -/
theorem PhiS_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Sz x0) (k : ℤ) :
    PhiS (x0 + q * k) (c0 + 72 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (84 * Tz * c0) - 258 * Tz) * k + PhiS x0 c0 := by
  have hbase := PhiS_cleared hbranch
  have hshift := PhiS_cleared (S_shift_branch (k := k) hbranch)
  have hscaled :
      12 * PhiS (x0 + q * k) (c0 + 72 * Tz * k) =
        12 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (84 * Tz * c0) - 258 * Tz) * k + PhiS x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- Exact residual tuple from (17). -/
theorem residual_linear_coefficients :
    ((-246 : ℤ) * Tz, 246 * Tz, 258 * Tz, (-258 : ℤ) * Tz) =
      (-1301094, 1301094, 1364562, -1364562) := by
  norm_num [Tz, FullDensityCore.T]

/-! ## Exceptional-prime support -/

theorem exceptional_coefficient_factorizations :
    246 * FullDensityCore.T = 2 * 3 ^ 2 * 41 ^ 2 * 43 ∧
    258 * FullDensityCore.T = 2 * 3 ^ 2 * 41 * 43 ^ 2 := by
  norm_num [FullDensityCore.T]

private lemma prime_eq_of_dvd_prime {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p ∣ q) : p = q := by
  rcases (Nat.dvd_prime hq).mp h with hp1 | hpq
  · exact (hp.ne_one hp1).elim
  · exact hpq

private lemma prime_dvd_four_factors {p a b c d : ℕ} (hp : Nat.Prime p)
    (h : p ∣ a * b * c * d) : p ∣ a ∨ p ∣ b ∨ p ∣ c ∨ p ∣ d := by
  rcases hp.dvd_mul.mp h with habc | hd
  · rcases hp.dvd_mul.mp habc with hab | hc
    · rcases hp.dvd_mul.mp hab with ha | hb
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hd))

/-- Every prime divisor of either residual coefficient lies in the exact
exceptional set `{2,3,41,43}`. -/
theorem prime_dvd_residual_support {p : ℕ} (hp : Nat.Prime p)
    (h : p ∣ 246 * FullDensityCore.T ∨
      p ∣ 258 * FullDensityCore.T) :
    p = 2 ∨ p = 3 ∨ p = 41 ∨ p = 43 := by
  rcases h with h246 | h258
  · rw [exceptional_coefficient_factorizations.1] at h246
    have h' : p ∣ 2 * 3 ^ 2 * 41 ^ 2 * 43 := h246
    rcases prime_dvd_four_factors hp h' with h2 | h3sq | h41sq | h43
    · exact Or.inl (prime_eq_of_dvd_prime hp Nat.prime_two h2)
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h3sq
      exact Or.inr (Or.inl (prime_eq_of_dvd_prime hp Nat.prime_three h3))
    · have h41 : p ∣ 41 := hp.dvd_of_dvd_pow h41sq
      exact Or.inr (Or.inr (Or.inl
        (prime_eq_of_dvd_prime hp (by norm_num) h41)))
    · exact Or.inr (Or.inr (Or.inr
        (prime_eq_of_dvd_prime hp (by norm_num) h43)))
  · rw [exceptional_coefficient_factorizations.2] at h258
    have h' : p ∣ 2 * 3 ^ 2 * 41 * 43 ^ 2 := h258
    rcases prime_dvd_four_factors hp h' with h2 | h3sq | h41 | h43sq
    · exact Or.inl (prime_eq_of_dvd_prime hp Nat.prime_two h2)
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h3sq
      exact Or.inr (Or.inl (prime_eq_of_dvd_prime hp Nat.prime_three h3))
    · exact Or.inr (Or.inr (Or.inl
        (prime_eq_of_dvd_prime hp (by norm_num) h41)))
    · have h43 : p ∣ 43 := hp.dvd_of_dvd_pow h43sq
      exact Or.inr (Or.inr (Or.inr
        (prime_eq_of_dvd_prime hp (by norm_num) h43)))

end ObstructionMaps
end Erdos730

end Campaign180File28

/- Source module: ErdosProblems.Erdos730.FullDensityReduction -/
section Campaign180File29
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: explicit positive-density reduction

This module isolates the explicit quantified density claim and proves, without
any extra axiom, that it implies the exact upstream infinitude target.  The
statement deliberately uses the explicit family from `Erdos730FullDensityCore`;
it is not a theorem-strength placeholder over an arbitrary sequence.

Historically this claim was the final intake boundary.  It is now discharged
unconditionally in `Erdos730FullDensityTheorem`, after formalizing the
Kummer, Mertens, fixed-modulus PNT-in-progressions, and counting arguments.
-/

open Filter

namespace Erdos730
namespace FullDensityReduction

open FullDensityCore

noncomputable section

local instance : DecidablePred GoodParameter :=
  fun _ => Classical.propDecidable _

/-- The explicit quantified density claim used by the historical reduction.

It says that more than `107/2500` of the positive integer parameters in the
four-linear-form family give equal prime support for the two consecutive
central binomial coefficients, in lower-density liminf. -/
def CandidatePositiveDensityClaim : Prop :=
  FullDensity.HasCandidatePositiveDensity GoodParameter

/-- Expanded form of the density claim, useful for hostile audit. -/
theorem candidatePositiveDensityClaim_iff :
    CandidatePositiveDensityClaim ↔
      (107 : ℝ) / 2500 <
        liminf (fun X : ℕ =>
          (((Finset.Icc 1 X).filter GoodParameter).card : ℝ) / X) atTop := by
  rfl

/-- The exact density claim gives infinitely many good parameters. -/
theorem goodParameters_infinite_of_candidatePositiveDensity
    (h : CandidatePositiveDensityClaim) : GoodParameters.Infinite := by
  exact FullDensity.parameterSet_infinite_of_candidatePositiveDensity
    GoodParameter (by simpa [CandidatePositiveDensityClaim] using h)

/-- Kernel-clean final reduction to the exact upstream Erdős 730 set.

No analytic theorem is hidden here: the only hypothesis is the fully expanded
positive-density claim above. -/
theorem pairSet_infinite_of_candidatePositiveDensity
    (h : CandidatePositiveDensityClaim) : PairSet.Infinite := by
  exact pairSet_infinite_of_goodParameters_infinite
    (goodParameters_infinite_of_candidatePositiveDensity h)

/-- The checked numerical node used by the supplied density argument. -/
theorem supplied_density_budget_certificate :
    4 * densityBudgetSeries + (2 / 3) * Real.log 2 < (2393 : ℝ) / 2500 :=
  densityBudget_final_lt


end

end FullDensityReduction
end Erdos730

end Campaign180File29

/- Source module: ErdosProblems.Erdos730.DigitBoxes -/
section Campaign180File30
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: finite lower-half digit boxes

This file supplies the concrete finite set used by the p-adic block counts.
For an odd prime `p`, `halfDigitCount p = (p+1)/2`; the permitted digits are
exactly `0, ..., halfDigitCount p - 1`.  Encoding `r` such digits in base `p`
gives a subset of `ZMod (p^r)` of cardinality `halfDigitCount p ^ r`.

The final membership theorem is the bridge needed by every event count:
`LowerHalfDigits p n` forces the residue of `n` modulo `p^r` to lie in this
finite box.  Leading zeroes are inserted explicitly, so the statement also
covers `n = 0` and `r = 0`.
-/

namespace Erdos730
namespace DigitBoxes

open KummerTransition

/-- Number of permitted base-`p` digits for an odd prime. -/
def halfDigitCount (p : ℕ) : ℕ := (p + 1) / 2

theorem halfDigitCount_eq_succ_half {p : ℕ} (hpodd : p % 2 = 1) :
    halfDigitCount p = (p - 1) / 2 + 1 := by
  unfold halfDigitCount
  omega

theorem halfDigitCount_pos {p : ℕ} (hp : 1 ≤ p) :
    0 < halfDigitCount p := by
  unfold halfDigitCount
  omega

theorem one_lt_halfDigitCount {p : ℕ} (hp : 3 ≤ p) :
    1 < halfDigitCount p := by
  unfold halfDigitCount
  omega

theorem halfDigitCount_le {p : ℕ} (hp : 1 ≤ p) :
    halfDigitCount p ≤ p := by
  unfold halfDigitCount
  omega

/-- Natural encodings of all length-`r` strings of permitted digits. -/
noncomputable def lowerHalfResiduesNat (p r : ℕ) : Finset ℕ := by
  classical
  by_cases hH : 1 < halfDigitCount p
  · exact (List.fixedLengthDigits hH r).image (Nat.ofDigits p)
  · exact ∅

private theorem ofDigits_injective_on_lowerHalf
    {p r : ℕ} (hp : 1 < p) (hH : 1 < halfDigitCount p)
    (hHp : halfDigitCount p ≤ p) :
    Set.InjOn (Nat.ofDigits p) (List.fixedLengthDigits hH r) := by
  intro L hL K hK hEq
  have hLm := (List.mem_fixedLengthDigits_iff hH).mp hL
  have hKm := (List.mem_fixedLengthDigits_iff hH).mp hK
  exact Nat.ofDigits_inj_of_len_eq hp (hLm.1.trans hKm.1.symm)
    (fun d hd ↦ (hLm.2 d hd).trans_le hHp)
    (fun d hd ↦ (hKm.2 d hd).trans_le hHp) hEq

theorem lowerHalfResiduesNat_card
    {p r : ℕ} (hp : 3 ≤ p) :
    (lowerHalfResiduesNat p r).card = halfDigitCount p ^ r := by
  classical
  have hp1 : 1 < p := by omega
  have hH : 1 < halfDigitCount p := one_lt_halfDigitCount hp
  have hHp : halfDigitCount p ≤ p := halfDigitCount_le (by omega)
  rw [lowerHalfResiduesNat, dif_pos hH,
    Finset.card_image_iff.mpr (ofDigits_injective_on_lowerHalf hp1 hH hHp),
    List.card_fixedLengthDigits]

theorem mem_lowerHalfResiduesNat_lt_pow
    {p r n : ℕ} (hp : 3 ≤ p)
    (hn : n ∈ lowerHalfResiduesNat p r) : n < p ^ r := by
  classical
  have hH : 1 < halfDigitCount p := one_lt_halfDigitCount hp
  rw [lowerHalfResiduesNat, dif_pos hH, Finset.mem_image] at hn
  obtain ⟨L, hL, rfl⟩ := hn
  have hLm := (List.mem_fixedLengthDigits_iff hH).mp hL
  rw [← hLm.1]
  exact Nat.ofDigits_lt_base_pow_length (by omega)
    (fun d hd ↦ (hLm.2 d hd).trans_le (halfDigitCount_le (by omega)))

/-- The permitted digit box as residues modulo `p^r`. -/
noncomputable def lowerHalfResidues (p r : ℕ) : Finset (ZMod (p ^ r)) :=
  Finset.image (fun n : ℕ ↦ (n : ZMod (p ^ r)))
    (lowerHalfResiduesNat p r)

private theorem natCast_injective_on_lowerHalf
    {p r : ℕ} (hp : 3 ≤ p) :
    Set.InjOn (fun n : ℕ ↦ (n : ZMod (p ^ r)))
      (lowerHalfResiduesNat p r) := by
  intro m hm n hn hcast
  have hmLt := mem_lowerHalfResiduesNat_lt_pow hp hm
  have hnLt := mem_lowerHalfResiduesNat_lt_pow hp hn
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hmLt,
    Nat.mod_eq_of_lt hnLt] using hval

theorem lowerHalfResidues_card {p r : ℕ} (hp : 3 ≤ p) :
    (lowerHalfResidues p r).card = halfDigitCount p ^ r := by
  classical
  rw [lowerHalfResidues,
    Finset.card_image_iff.mpr (natCast_injective_on_lowerHalf hp),
    lowerHalfResiduesNat_card hp]

private def paddedLowDigits (p r n : ℕ) : List ℕ :=
  let low := (Nat.digits p n).take r
  low ++ List.replicate (r - low.length) 0

private theorem paddedLowDigits_length (p r n : ℕ) :
    (paddedLowDigits p r n).length = r := by
  simp only [paddedLowDigits, List.length_append, List.length_replicate,
    List.length_take]
  omega

private theorem paddedLowDigits_digits_lt_half
    {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : LowerHalfDigits p n) :
    ∀ d ∈ paddedLowDigits p r n, d < halfDigitCount p := by
  intro d hd
  rw [paddedLowDigits, List.mem_append, List.mem_replicate] at hd
  rcases hd with hd | ⟨_hrep, rfl⟩
  · have hdDigits : d ∈ Nat.digits p n :=
      List.mem_of_mem_take hd
    have hdHalf := hn d hdDigits
    rw [halfDigitCount_eq_succ_half
      ((hp.mod_two_eq_one_iff_ne_two).2 hp2)]
    omega
  · exact halfDigitCount_pos hp.one_le

private theorem ofDigits_paddedLowDigits
    {p r n : ℕ} (hp : p.Prime) :
    Nat.ofDigits p (paddedLowDigits p r n) = n % p ^ r := by
  unfold paddedLowDigits
  rw [Nat.ofDigits_append_replicate_zero]
  exact (Nat.self_mod_pow_eq_ofDigits_take r n hp.two_le).symm

/-- Every lower-half integer lands in the finite lower-half residue box at
every depth. -/
theorem natCast_mem_lowerHalfResidues
    {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : LowerHalfDigits p n) :
    (n : ZMod (p ^ r)) ∈ lowerHalfResidues p r := by
  classical
  have hp3 : 3 ≤ p := by
    have hp2le := hp.two_le
    omega
  have hH : 1 < halfDigitCount p := one_lt_halfDigitCount hp3
  let L := paddedLowDigits p r n
  have hLmem : L ∈ List.fixedLengthDigits hH r := by
    rw [List.mem_fixedLengthDigits_iff hH]
    exact ⟨paddedLowDigits_length p r n,
      paddedLowDigits_digits_lt_half hp hp2 hn⟩
  have hNat : Nat.ofDigits p L ∈ lowerHalfResiduesNat p r := by
    rw [lowerHalfResiduesNat, dif_pos hH]
    exact Finset.mem_image.mpr ⟨L, hLmem, rfl⟩
  rw [lowerHalfResidues, Finset.mem_image]
  refine ⟨Nat.ofDigits p L, hNat, ?_⟩
  have hDigits : Nat.ofDigits p L = n % p ^ r := by
    simpa [L] using ofDigits_paddedLowDigits (p := p) (r := r) (n := n) hp
  calc
    ((Nat.ofDigits p L : ℕ) : ZMod (p ^ r)) =
        ((n % p ^ r : ℕ) : ZMod (p ^ r)) := congrArg (fun m : ℕ ↦
          (m : ZMod (p ^ r))) hDigits
    _ = (n : ZMod (p ^ r)) := ZMod.natCast_mod n (p ^ r)


end DigitBoxes
end Erdos730

end Campaign180File30

/- Source module: ErdosProblems.Erdos730.HigherPowerDecay -/
section Campaign180File31
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: pointwise decay at a fixed higher prime power

This module closes the depth/limit subnode needed to specialize the generic
Tannery theorem.  For fixed `p` and `a`, the complete-block depth

`log_p (X / p^a)`

tends to infinity.  Consequently every geometric digit-density factor with
ratio in `[0,1)` tends to zero.  The final theorem instantiates the exact
ratio `(p+1)/(2p)` used by the Erdős 730 higher-power count.
-/

open Filter Topology

namespace Erdos730

/-- Complete-block digit depth at the fixed prime power `p^a`. -/
def higherPowerDepth (p a X : ℕ) : ℕ :=
  Nat.log p (X / p ^ a)

/-- For every fixed base greater than one and fixed exponent, the available
complete-block depth tends to infinity with the interval cutoff. -/
theorem tendsto_higherPowerDepth_atTop
    {p : ℕ} (hp : 1 < p) (a : ℕ) :
    Tendsto (higherPowerDepth p a) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro r
  refine ⟨p ^ (a + r), fun X hX ↦ ?_⟩
  unfold higherPowerDepth
  apply Nat.le_log_of_pow_le hp
  rw [Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < p) a)]
  calc
    p ^ r * p ^ a = p ^ (a + r) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ X := hX

/-- Geometric decay after composing any ratio in `[0,1)` with the increasing
prime-power depth. -/
theorem tendsto_pow_higherPowerDepth_zero
    {p : ℕ} (hp : 1 < p) (a : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun X ↦ ρ ^ higherPowerDepth p a X) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
    (tendsto_higherPowerDepth_atTop hp a)

/-- The exact permitted-digit ratio `rho_p=(p+1)/(2p)`. -/
noncomputable def higherPowerRho (p : ℕ) : ℝ :=
  (p + 1 : ℝ) / (2 * p : ℝ)

theorem higherPowerRho_nonneg (p : ℕ) : 0 ≤ higherPowerRho p := by
  unfold higherPowerRho
  positivity

theorem higherPowerRho_lt_one {p : ℕ} (hp : 1 < p) :
    higherPowerRho p < 1 := by
  unfold higherPowerRho
  rw [div_lt_one (by positivity : (0 : ℝ) < 2 * p)]
  exact_mod_cast (show p + 1 < 2 * p by omega)

/-- Pointwise vanishing of the normalized first term in equation (26), for a
fixed prime and exponent. -/
theorem tendsto_higherPower_normalizedTerm_zero
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Tendsto
      (fun X ↦ (2 / (p : ℝ) ^ a) *
        higherPowerRho p ^ higherPowerDepth p a X)
      atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (tendsto_pow_higherPowerDepth_zero hp.one_lt a
      (higherPowerRho_nonneg p) (higherPowerRho_lt_one hp.one_lt)).const_mul
      (2 / (p : ℝ) ^ a)


end Erdos730

end Campaign180File31

/- Source module: ErdosProblems.Erdos730.HigherPowerDensity -/
section Campaign180File32
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: analytic higher-power envelope

This module specializes the generic Tannery theorem to the exact normalized
term in equation (26).  It also proves that the number of terminal `+1`
payments remains sublinear after replacing the branch cutoff `X` by the
uniform bound `380827 X`.

The only remaining finite-combinatorial input for the actual event ledger is
the pointwise inequality saying that each branch event count is bounded by
this envelope plus one terminal payment.
-/

open Filter Topology

namespace Erdos730

/-- Exact normalized geometric term for the index `(p,k)`, where the true
prime-power exponent is `a=k+2`. -/
noncomputable def higherPowerEnvelope (X : ℕ) (i : HigherPowerIndex) : ℝ :=
  (2 / (i.1 : ℝ) ^ (i.2 + 2)) *
    higherPowerRho i.1 ^ higherPowerDepth i.1 (i.2 + 2) X

theorem higherPowerEnvelope_nonneg (X : ℕ) (i : HigherPowerIndex) :
    0 ≤ higherPowerEnvelope X i := by
  unfold higherPowerEnvelope
  exact mul_nonneg (by positivity)
    (pow_nonneg (higherPowerRho_nonneg (i.1 : ℕ)) _)

theorem higherPowerEnvelope_le_majorant (X : ℕ) (i : HigherPowerIndex) :
    higherPowerEnvelope X i ≤ higherPowerMajorant i := by
  rw [higherPowerMajorant_eq]
  unfold higherPowerEnvelope
  have hρ0 := higherPowerRho_nonneg (i.1 : ℕ)
  have hρ1 := (higherPowerRho_lt_one i.1.prop.one_lt).le
  have hpow : higherPowerRho (i.1 : ℕ) ^
      higherPowerDepth (i.1 : ℕ) (i.2 + 2) X ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hρ0 hρ1
      (higherPowerDepth (i.1 : ℕ) (i.2 + 2) X)
  have hcoef : 0 ≤ 2 / ((i.1 : ℝ) ^ (i.2 + 2)) := by positivity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hcoef

theorem tendsto_higherPowerEnvelope_zero (i : HigherPowerIndex) :
    Tendsto (fun X ↦ higherPowerEnvelope X i) atTop (𝓝 0) := by
  simpa only [higherPowerEnvelope] using
    tendsto_higherPower_normalizedTerm_zero i.1.prop (i.2 + 2)

/-- The complete normalized sum of all geometric higher-power payments tends
to zero. -/
theorem tendsto_tsum_higherPowerEnvelope_zero :
    Tendsto (fun X ↦ ∑' i : HigherPowerIndex, higherPowerEnvelope X i)
      atTop (𝓝 0) :=
  tendsto_tsum_higherPower_of_dominated higherPowerEnvelope
    tendsto_higherPowerEnvelope_zero higherPowerEnvelope_nonneg
    higherPowerEnvelope_le_majorant

/-- Uniform linear height bound used for terminal prime powers in all four
branches. -/
def higherPowerBranchHeight : ℕ := 380827

theorem higherPowerBranchHeight_pos : 0 < higherPowerBranchHeight := by
  norm_num [higherPowerBranchHeight]

theorem tendsto_higherPower_scaledCutoff :
    Tendsto (fun X : ℕ ↦ higherPowerBranchHeight * X) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Eventually.of_forall fun X : ℕ ↦ ?_) tendsto_id
  unfold higherPowerBranchHeight
  simpa only [id_eq, one_mul] using
    Nat.mul_le_mul_right X (show 1 ≤ 380827 by norm_num)

/-- The finite number of `(p,a)` terminal payments is still `o(X)` at the
actual uniform branch cutoff. -/
theorem tendsto_higherPrimePowerPairs_scaled_card_div :
    Tendsto (fun X : ℕ ↦
      ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
        (X : ℝ)) atTop (𝓝 0) := by
  have hbase := tendsto_higherPrimePowerPairs_card_div.comp
    tendsto_higherPower_scaledCutoff
  have hscaled := hbase.const_mul (higherPowerBranchHeight : ℝ)
  have hscaled0 : Tendsto (fun X : ℕ ↦
      (higherPowerBranchHeight : ℝ) *
        (((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          ((higherPowerBranchHeight * X : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hscaled
  apply hscaled0.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hC : (higherPowerBranchHeight : ℝ) ≠ 0 := by
    exact_mod_cast higherPowerBranchHeight_pos.ne'
  simp only [Function.comp_apply, Nat.cast_mul, mul_zero]
  field_simp

/-- Four branches do not change either vanishing assertion. -/
theorem tendsto_four_mul_higherPowerEnvelope_and_terminal_zero :
    Tendsto (fun X : ℕ ↦
      4 * ((∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ))) atTop (𝓝 0) := by
  simpa only [zero_add, mul_zero] using
    (tendsto_tsum_higherPowerEnvelope_zero.add
      tendsto_higherPrimePowerPairs_scaled_card_div).const_mul 4


end Erdos730

end Campaign180File32

/- Source module: ErdosProblems.Erdos730.HigherPowerEvents -/
section Campaign180File33
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: concrete higher-prime-power local events

This module closes the finite-combinatorial bridge left open by
`Erdos730HigherPowerDensity`.  For a fixed branch and prime power `p^a`,
divisibility of the branch value confines the parameter to one root
progression.  Equations (16)--(17) identify the obstruction value along that
progression with the generic p-adic permutation map, while the lower-half
digit condition places its residue in the exact digit box.

The resulting complete/padded block bound is summed over all branches and
higher prime powers.  The geometric part is discharged by Tannery and the
terminal `p^a > X` part by the sublinear prime-power-pair count.  In
particular, the depth-zero case is retained in the finite block theorem.
-/

open Filter Finset Topology

namespace Erdos730.HigherPowerEvents

open BranchEvents ConsecutiveTransition DensityEvents DigitBoxes
open FullDensityCore KummerTransition ObstructionMaps

/-! ## Branch slopes and exceptional-prime exclusions -/

def branchSlope : Branch → ℕ
  | .P => 222138
  | .Q => 380808
  | .R => 148092
  | .S => 380808

def branchOffset : Branch → ℕ
  | .P => 11
  | .Q => 13
  | .R => 5
  | .S => 19

theorem branchValue_eq_slope_mul_add (L : Branch) (x : ℕ) :
    branchValue L x = branchSlope L * x + branchOffset L := by
  cases L with
  | P => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).1
  | Q => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.1
  | R => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.1
  | S => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.2

theorem branchSlope_pos (L : Branch) : 0 < branchSlope L := by
  cases L <;> norm_num [branchSlope]

theorem three_not_dvd_branchValue (L : Branch) (x : ℕ) :
    ¬3 ∣ branchValue L x := by
  rw [Nat.dvd_iff_mod_eq_zero]
  cases L with
  | P => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).1 (by norm_num)
  | Q => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).2.1 (by norm_num)
  | R => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).2.2.1 (by norm_num)
  | S => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).2.2.2 (by norm_num)

theorem fortyOne_not_dvd_branchValue (L : Branch) (x : ℕ) :
    ¬41 ∣ branchValue L x := by
  rcases fixed_primes_do_not_divide_branches x with ⟨h41, _h43⟩
  cases L with
  | P => exact h41.1
  | Q => exact h41.2.1
  | R => exact h41.2.2.1
  | S => exact h41.2.2.2

theorem fortyThree_not_dvd_branchValue (L : Branch) (x : ℕ) :
    ¬43 ∣ branchValue L x := by
  rcases fixed_primes_do_not_divide_branches x with ⟨_h41, h43⟩
  cases L with
  | P => exact h43.1
  | Q => exact h43.2.1
  | R => exact h43.2.2.1
  | S => exact h43.2.2.2

theorem localPrime_avoids_exceptional
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 41 ∧ p ≠ 43 := by
  have hpBranch : p ∣ branchValue L x :=
    prime_dvd_factor_of_exactPrimePowerCofactor hlocal.2.2.1
  refine ⟨hlocal.2.1, ?_, ?_, ?_⟩
  · rintro rfl
    exact three_not_dvd_branchValue L x hpBranch
  · rintro rfl
    exact fortyOne_not_dvd_branchValue L x hpBranch
  · rintro rfl
    exact fortyThree_not_dvd_branchValue L x hpBranch

theorem localPrime_not_dvd_branchSlope
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    ¬p ∣ branchSlope L := by
  intro hpSlope
  have hpValue : p ∣ branchValue L x :=
    prime_dvd_factor_of_exactPrimePowerCofactor hlocal.2.2.1
  have hpProduct : p ∣ branchSlope L * x := dvd_mul_of_dvd_left hpSlope x
  have hpOffset : p ∣ branchOffset L := by
    rw [branchValue_eq_slope_mul_add] at hpValue
    exact (Nat.dvd_add_iff_right hpProduct).mpr hpValue
  cases L with
  | P =>
      have hpEq : p = 11 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope
  | Q =>
      have hpEq : p = 13 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope
  | R =>
      have hpEq : p = 5 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope
  | S =>
      have hpEq : p = 19 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope

theorem localPrimePow_coprime_branchSlope
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    Nat.Coprime (p ^ a) (branchSlope L) := by
  exact (hlocal.1.coprime_iff_not_dvd.mpr
    (localPrime_not_dvd_branchSlope hlocal)).pow_left a

/-- Divisibility by the same exact prime power confines two local events to
one parameter residue class. -/
theorem localBranchRoots_modEq
    {L : Branch} {x y p a d e : ℕ}
    (hx : LocalBranchObstruction L x p a d)
    (hy : LocalBranchObstruction L y p a e) :
    x ≡ y [MOD p ^ a] := by
  have hxDiv : p ^ a ∣ branchValue L x :=
    ⟨d, hx.2.2.1.2.1⟩
  have hyDiv : p ^ a ∣ branchValue L y :=
    ⟨e, hy.2.2.1.2.1⟩
  have hvalues : branchValue L x ≡ branchValue L y [MOD p ^ a] :=
    hxDiv.modEq_zero_nat.trans hyDiv.modEq_zero_nat.symm
  rw [branchValue_eq_slope_mul_add, branchValue_eq_slope_mul_add] at hvalues
  have hmul : branchSlope L * x ≡ branchSlope L * y [MOD p ^ a] :=
    (Nat.ModEq.refl (branchOffset L)).add_right_cancel hvalues
  exact Nat.ModEq.cancel_left_of_coprime
    (localPrimePow_coprime_branchSlope hx).gcd_eq_one hmul

/-- The least nonnegative representative of a witnessed root is again a
root of the branch congruence. -/
theorem branchValue_mod_pow_dvd
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    p ^ a ∣ branchValue L (x % p ^ a) := by
  have hxDiv : p ^ a ∣ branchValue L x :=
    ⟨d, hlocal.2.2.1.2.1⟩
  have hroot : branchValue L (x % p ^ a) ≡
      branchValue L x [MOD p ^ a] := by
    rw [branchValue_eq_slope_mul_add, branchValue_eq_slope_mul_add]
    exact (Nat.mod_modEq x (p ^ a)).mul_left (branchSlope L) |>.add
      (Nat.ModEq.refl (branchOffset L))
  exact Nat.modEq_zero_iff_dvd.mp
    (hroot.trans hxDiv.modEq_zero_nat)

/-! ## The natural branch tests are the four integral obstruction maps -/

theorem localCofactor_pos
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) : 0 < d := by
  have hbranchPos : 0 < branchValue L x := by
    cases L with
    | P => simpa [branchValue] using (branches_positive x).1
    | Q => simpa [branchValue] using (branches_positive x).2.1
    | R => simpa [branchValue] using (branches_positive x).2.2.1
    | S => simpa [branchValue] using (branches_positive x).2.2.2
  have hpPow : 0 < p ^ a := pow_pos hlocal.1.pos a
  have hfac := hlocal.2.2.1.2.1
  nlinarith

theorem branchTestValue_int_eq_phi
    {L : Branch} {x d : ℕ} (hd : 0 < d) :
    (branchTestValue L x d : ℤ) =
      match L with
      | .P => PhiP x d
      | .Q => PhiQ x d
      | .R => PhiR x d
      | .S => PhiS x d := by
  have hbranches := branch_casts x
  cases L with
  | P => simp [branchTestValue, PhiP, hbranches.2.1]
  | Q => simp [branchTestValue, PhiQ, hbranches.1]
  | R =>
      have hle : 1 ≤ 3 * d * S x := by
        have hS := (branches_positive x).2.2.2
        have hpos : 0 < 3 * d * S x := by positivity
        omega
      simp only [branchTestValue, PhiR]
      rw [Int.natCast_ediv]
      rw [Nat.cast_sub hle]
      simp [hbranches.2.2.2]
  | S =>
      have hle : 1 ≤ 3 * d * FullDensityCore.R x := by
        have hR := (branches_positive x).2.2.1
        have hpos : 0 < 3 * d * FullDensityCore.R x := by positivity
        omega
      simp only [branchTestValue, PhiS]
      rw [Int.natCast_ediv]
      rw [Nat.cast_sub hle]
      simp [hbranches.2.2.1]

/-! ## Exact specialization of equations (16)--(17) -/

def commonQuadraticCoefficient : ℤ := 3024 * Tz ^ 2

def branchUCoefficient : Branch → ℤ
  | .P => 144 * Tz
  | .Q => 84 * Tz
  | .R => 216 * Tz
  | .S => 84 * Tz

def branchResidualCoefficient : Branch → ℤ
  | .P => -246 * Tz
  | .Q => 246 * Tz
  | .R => 258 * Tz
  | .S => -258 * Tz

def branchResidualNat : Branch → ℕ
  | .P => 246 * T
  | .Q => 246 * T
  | .R => 258 * T
  | .S => 258 * T

theorem localPrime_not_dvd_branchResidualNat
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    ¬p ∣ branchResidualNat L := by
  intro hdiv
  have hsupp : p = 2 ∨ p = 3 ∨ p = 41 ∨ p = 43 := by
    apply prime_dvd_residual_support hlocal.1
    cases L with
    | P => exact Or.inl (by simpa [branchResidualNat] using hdiv)
    | Q => exact Or.inl (by simpa [branchResidualNat] using hdiv)
    | R => exact Or.inr (by simpa [branchResidualNat] using hdiv)
    | S => exact Or.inr (by simpa [branchResidualNat] using hdiv)
  rcases localPrime_avoids_exceptional hlocal with ⟨hp2, hp3, hp41, hp43⟩
  rcases hsupp with h | h | h | h
  · exact hp2 h
  · exact hp3 h
  · exact hp41 h
  · exact hp43 h

theorem branchResidualCoefficient_isUnit
    {L : Branch} {x p a d r : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    IsUnit (branchResidualCoefficient L : ZMod (p ^ r)) := by
  have hu := natCast_isUnit_zmod_primePow (j := r) hlocal.1
    (localPrime_not_dvd_branchResidualNat hlocal)
  cases L with
  | P => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu.neg
  | Q => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu
  | R => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu
  | S => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu.neg

def branchPadicQuadratic (p a : ℕ) : ℤ :=
  commonQuadraticCoefficient * (p ^ (a - 1) : ℕ)

def branchPadicLinear (L : Branch) (p a c₀ : ℕ) : ℤ :=
  (p ^ (a - 1) : ℕ) * (branchUCoefficient L * c₀)

/-- Exact integer polynomial for the test value on the root progression
selected by a base local event. -/
theorem branchTestValue_root_progression
    {L : Branch} {x₀ x p a d₀ d : ℕ}
    (h₀ : LocalBranchObstruction L x₀ p a d₀)
    (h : LocalBranchObstruction L x p a d) :
    let q : ℕ := p ^ a
    let s : ℕ := x₀ % q
    let c₀ : ℕ := branchValue L s / q
    let k : ℕ := x / q
    (branchTestValue L x d : ℤ) =
      commonQuadraticCoefficient * q * k ^ 2 +
        ((q : ℤ) * (branchUCoefficient L * c₀) +
          branchResidualCoefficient L) * k +
        branchTestValue L s c₀ := by
  dsimp only
  let q : ℕ := p ^ a
  let s : ℕ := x₀ % q
  let c₀ : ℕ := branchValue L s / q
  let k : ℕ := x / q
  have hqPos : 0 < q := pow_pos h₀.1.pos a
  have hsDiv : q ∣ branchValue L s := by
    simpa [q, s] using branchValue_mod_pow_dvd h₀
  have hbase : q * c₀ = branchValue L s := by
    simpa [c₀] using Nat.mul_div_cancel' hsDiv
  have hmod : x ≡ x₀ [MOD q] := by
    simpa [q] using localBranchRoots_modEq h h₀
  have hrem : x % q = s := by
    simpa [s, Nat.ModEq] using hmod
  have hxProgression : x = s + q * k := by
    calc
      x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
      _ = s + q * k := by rw [hrem]; simp [k, Nat.add_comm]
  have hdProgression : d = c₀ + branchSlope L * k := by
    have hfactor := h.2.2.1.2.1
    apply Nat.mul_left_cancel hqPos
    calc
      q * d = branchValue L x := hfactor.symm
      _ = branchSlope L * (s + q * k) + branchOffset L := by
        rw [hxProgression, branchValue_eq_slope_mul_add]
      _ = q * (c₀ + branchSlope L * k) := by
        rw [branchValue_eq_slope_mul_add] at hbase
        calc
          branchSlope L * (s + q * k) + branchOffset L =
              (branchSlope L * s + branchOffset L) +
                branchSlope L * (q * k) := by ring
          _ = q * c₀ + branchSlope L * (q * k) := by rw [← hbase]
          _ = q * (c₀ + branchSlope L * k) := by ring
  have hc₀Pos : 0 < c₀ := by
    have hsPos : 0 < branchValue L s := by
      cases L with
      | P => simpa [branchValue] using (branches_positive s).1
      | Q => simpa [branchValue] using (branches_positive s).2.1
      | R => simpa [branchValue] using (branches_positive s).2.2.1
      | S => simpa [branchValue] using (branches_positive s).2.2.2
    nlinarith
  have htest := branchTestValue_int_eq_phi (L := L)
    (x := x) (d := d) (localCofactor_pos h)
  have htest₀ := branchTestValue_int_eq_phi (L := L)
    (x := s) (d := c₀) hc₀Pos
  change (branchTestValue L x d : ℤ) =
    commonQuadraticCoefficient * (q : ℤ) * (k : ℤ) ^ 2 +
      ((q : ℤ) * (branchUCoefficient L * (c₀ : ℤ)) +
        branchResidualCoefficient L) * (k : ℤ) +
      (branchTestValue L s c₀ : ℤ)
  cases L with
  | P =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Pz s := by
        rw [(branch_casts s).1]
        exact_mod_cast hbase
      have hphi := PhiP_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi
  | Q =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Qz s := by
        rw [(branch_casts s).2.1]
        exact_mod_cast hbase
      have hphi := PhiQ_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi
  | R =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Rz s := by
        rw [(branch_casts s).2.2.1]
        exact_mod_cast hbase
      have hphi := PhiR_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi
  | S =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Sz s := by
        rw [(branch_casts s).2.2.2]
        exact_mod_cast hbase
      have hphi := PhiS_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi

/-- Equation (16) in the exact `padicBranchMap` form used by the finite block
count.  It is valid at every output depth, including depth zero. -/
theorem branchTestValue_eq_padicBranchMap
    {L : Branch} {x₀ x p a d₀ d r : ℕ}
    (h₀ : LocalBranchObstruction L x₀ p a d₀)
    (h : LocalBranchObstruction L x p a d) :
    let q : ℕ := p ^ a
    let s : ℕ := x₀ % q
    let c₀ : ℕ := branchValue L s / q
    let k : ℕ := x / q
    (branchTestValue L x d : ZMod (p ^ r)) =
      padicBranchMap (p : ZMod (p ^ r))
        (branchPadicQuadratic p a : ZMod (p ^ r))
        (branchPadicLinear L p a c₀ : ZMod (p ^ r))
        (branchResidualCoefficient L : ZMod (p ^ r))
        (branchTestValue L s c₀ : ZMod (p ^ r))
        (k : ZMod (p ^ r)) := by
  dsimp only
  let q : ℕ := p ^ a
  let s : ℕ := x₀ % q
  let c₀ : ℕ := branchValue L s / q
  let k : ℕ := x / q
  have haPos : 0 < a := h₀.2.2.1.1
  have hpow : p ^ a = p * p ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    ring
  have hroot := branchTestValue_root_progression h₀ h
  have hcast := congrArg (fun z : ℤ ↦ (z : ZMod (p ^ r))) hroot
  push_cast at hcast
  have hxquot :
      (((x : ℤ) / (p : ℤ) ^ a : ℤ) : ZMod (p ^ r)) =
        ((x / p ^ a : ℕ) : ZMod (p ^ r)) := by
    calc
      _ = (((x / p ^ a : ℕ) : ℤ) : ZMod (p ^ r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (p ^ r)))
          (by simpa using (Int.natCast_ediv x (p ^ a)).symm)
      _ = _ := Int.cast_natCast (R := ZMod (p ^ r)) _
  have hcquot :
      ((((branchValue L (x₀ % p ^ a) : ℕ) : ℤ) /
          (p : ℤ) ^ a : ℤ) : ZMod (p ^ r)) =
        ((branchValue L (x₀ % p ^ a) / p ^ a : ℕ) :
          ZMod (p ^ r)) := by
    calc
      _ = (((branchValue L (x₀ % p ^ a) / p ^ a : ℕ) : ℤ) :
          ZMod (p ^ r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (p ^ r)))
          (by simpa using
            (Int.natCast_ediv (branchValue L (x₀ % p ^ a)) (p ^ a)).symm)
      _ = _ := Int.cast_natCast (R := ZMod (p ^ r)) _
  rw [hxquot, hcquot] at hcast
  have hquadratic :
      (p : ZMod (p ^ r)) *
          (branchPadicQuadratic p a : ZMod (p ^ r)) =
        (commonQuadraticCoefficient : ZMod (p ^ r)) * (p ^ a : ℕ) := by
    simp [branchPadicQuadratic, hpow]
    ring
  have hlinear :
      (p : ZMod (p ^ r)) *
          (branchPadicLinear L p a c₀ : ZMod (p ^ r)) =
        (p ^ a : ℕ) *
          ((branchUCoefficient L : ZMod (p ^ r)) * (c₀ : ℕ)) := by
    simp [branchPadicLinear, hpow]
    ring
  change (branchTestValue L x d : ZMod (p ^ r)) = _
  rw [padicBranchMap, hquadratic, hlinear]
  simpa [q, s, c₀, k] using hcast

theorem halfDigitCount_cast_div_eq_rho
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (halfDigitCount p : ℝ) / (p : ℝ) = higherPowerRho p := by
  have hpOdd : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).2 hp2
  have htwo : 2 ∣ p + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  unfold halfDigitCount higherPowerRho
  rw [Nat.cast_div_charZero htwo]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  push_cast
  ring

/-! ## Fixed branch/prime-power fibers -/

/-- Parameters in `[1,X]` carrying at least one local obstruction on the
fixed branch at the fixed exact prime power.  The cofactor is existentially
quantified here because it is forced by the exact factorization. -/
noncomputable def localHigherPowerFiber
    (X : ℕ) (L : Branch) (p a : ℕ) : Finset ℕ := by
  classical
  exact (parameterRange X).filter fun x ↦
    ∃ d, LocalBranchObstruction L x p a d

@[simp] theorem mem_localHigherPowerFiber
    {X x p a : ℕ} {L : Branch} :
    x ∈ localHigherPowerFiber X L p a ↔
      x ∈ parameterRange X ∧
        ∃ d, LocalBranchObstruction L x p a d := by
  classical
  simp [localHigherPowerFiber]

/-- Exact complete/padded-block bound for one nonempty local fiber.  The
depth is `log_p (X/p^a)`, and no positivity hypothesis is imposed on it;
when `X/p^a=0` the theorem retains the intended depth-zero estimate. -/
theorem localHigherPowerFiber_card_le_block
    {X p a : ℕ} {L : Branch} :
    (localHigherPowerFiber X L p a).card ≤
      (((X / p ^ a + 1) / p ^ higherPowerDepth p a X) + 1) *
        halfDigitCount p ^ higherPowerDepth p a X := by
  classical
  by_cases hempty : localHigherPowerFiber X L p a = ∅
  · simp [hempty]
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases mem_localHigherPowerFiber.mp hx₀ with ⟨_hx₀Range, d₀, h₀⟩
    let r : ℕ := higherPowerDepth p a X
    let q : ℕ := p ^ a
    let s : ℕ := x₀ % q
    let c₀ : ℕ := branchValue L s / q
    let A : Finset (ZMod (p ^ r)) := lowerHalfResidues p r
    let admissible : Finset ℕ :=
      (Finset.range (X / q + 1)).filter fun k ↦
        padicBranchMap (p : ZMod (p ^ r))
          (branchPadicQuadratic p a : ZMod (p ^ r))
          (branchPadicLinear L p a c₀ : ZMod (p ^ r))
          (branchResidualCoefficient L : ZMod (p ^ r))
          (branchTestValue L s c₀ : ZMod (p ^ r))
          (k : ZMod (p ^ r)) ∈ A
    have hmap : ∀ x ∈ localHigherPowerFiber X L p a,
        x / q ∈ admissible := by
      intro x hx
      rcases mem_localHigherPowerFiber.mp hx with ⟨hxRange, d, hlocal⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right
          (mem_parameterRange.mp hxRange).2)
      · have hdigit := natCast_mem_lowerHalfResidues (r := r)
          hlocal.1 hlocal.2.1 hlocal.2.2.2
        change padicBranchMap (p : ZMod (p ^ r))
            (branchPadicQuadratic p a : ZMod (p ^ r))
            (branchPadicLinear L p a c₀ : ZMod (p ^ r))
            (branchResidualCoefficient L : ZMod (p ^ r))
            (branchTestValue L s c₀ : ZMod (p ^ r))
            (x / q : ZMod (p ^ r)) ∈ A
        rw [← branchTestValue_eq_padicBranchMap h₀ hlocal]
        exact hdigit
    have hinj : Set.InjOn (fun x : ℕ ↦ x / q)
        (localHigherPowerFiber X L p a : Set ℕ) := by
      intro x hx y hy hdiv
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hxRange, d, hxlocal⟩
      rcases mem_localHigherPowerFiber.mp hy with ⟨_hyRange, e, hylocal⟩
      change x / q = y / q at hdiv
      have hmod : x % q = y % q := by
        have hxy : x ≡ y [MOD q] := by
          simpa [q] using localBranchRoots_modEq hxlocal hylocal
        exact hxy
      calc
        x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
        _ = q * (y / q) + y % q := by rw [hdiv, hmod]
        _ = y := Nat.div_add_mod y q
    have hfiber : (localHigherPowerFiber X L p a).card ≤ admissible.card :=
      Finset.card_le_card_of_injOn (fun x : ℕ ↦ x / q) hmap hinj
    have hp3 : 3 ≤ p := by
      have hp2le := h₀.1.two_le
      have hpne2 := h₀.2.1
      omega
    have hblock : admissible.card ≤
        (((X / q + 1) / p ^ r) + 1) * halfDigitCount p ^ r := by
      have hcount := padicBranchAllowedCount_le h₀.1
        (branchPadicQuadratic p a : ZMod (p ^ r))
        (branchPadicLinear L p a c₀ : ZMod (p ^ r))
        (branchTestValue L s c₀ : ZMod (p ^ r))
        (branchResidualCoefficient_isUnit (r := r) h₀)
        A (lowerHalfResidues_card hp3)
        (start := 0) (N := X / q + 1)
      simpa [admissible, padicBranchAllowedCount, intervalResidueCount]
        using hcount
    simpa [q, r] using hfiber.trans hblock

/-- Root-class count used for the terminal regime `X < p^a`. -/
theorem localHigherPowerFiber_card_le_rootCount
    {X p a : ℕ} {L : Branch} :
    (localHigherPowerFiber X L p a).card ≤ X / p ^ a + 1 := by
  classical
  by_cases hempty : localHigherPowerFiber X L p a = ∅
  · simp [hempty]
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases mem_localHigherPowerFiber.mp hx₀ with ⟨_hx₀Range, d₀, h₀⟩
    apply Erdos730.TransitionDensity.card_le_div_add_one_of_modEq
      (v := x₀)
    · intro x hx
      exact (mem_parameterRange.mp
        (mem_localHigherPowerFiber.mp hx).1).2
    · intro x hx
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hxRange, d, hlocal⟩
      exact localBranchRoots_modEq hlocal h₀

theorem localHigherPowerFiber_card_le_one_of_lt
    {X p a : ℕ} {L : Branch} (hXq : X < p ^ a) :
    (localHigherPowerFiber X L p a).card ≤ 1 := by
  have hzero : X / p ^ a = 0 := Nat.div_eq_of_lt hXq
  simpa [hzero] using
    (localHigherPowerFiber_card_le_rootCount (X := X) (p := p)
      (a := a) (L := L))

/-- All four affine branch values are at most the common terminal cutoff
`380827 X` on the parameter interval `[1,X]`. -/
theorem branchValue_le_higherPowerBranchHeight
    {X x : ℕ} (L : Branch) (hx : x ∈ parameterRange X) :
    branchValue L x ≤ higherPowerBranchHeight * X := by
  rcases mem_parameterRange.mp hx with ⟨hx1, hxX⟩
  rw [branchValue_eq_slope_mul_add]
  cases L <;>
    simp only [branchSlope, branchOffset, higherPowerBranchHeight] <;>
    omega

theorem localPrimePower_le_higherPowerBranchHeight
    {X x p a d : ℕ} {L : Branch}
    (hx : x ∈ parameterRange X)
    (hlocal : LocalBranchObstruction L x p a d) :
    p ^ a ≤ higherPowerBranchHeight * X := by
  have hq : p ^ a ≤ p ^ a * d :=
    Nat.le_mul_of_pos_right _ (localCofactor_pos hlocal)
  rw [← hlocal.2.2.1.2.1] at hq
  exact hq.trans (branchValue_le_higherPowerBranchHeight L hx)

/-- Adding one to the numerator can increase a natural quotient by at most
one.  This is the only floor estimate used in normalizing the block bound. -/
theorem succ_div_le_div_add_one (U P : ℕ) :
    (U + 1) / P ≤ U / P + 1 := by
  rw [Nat.succ_div]
  split <;> omega

/-- A total encoding of prime-power pairs into the shifted Tannery index.
On the actual prime-pair set the fallback branch is never used. -/
noncomputable def higherPowerPairIndex (pa : ℕ × ℕ) : HigherPowerIndex := by
  classical
  exact if hp : pa.1.Prime then (⟨pa.1, hp⟩, pa.2 - 2)
    else (⟨2, Nat.prime_two⟩, pa.2 - 2)

theorem higherPowerPairIndex_eq
    {p a : ℕ} (hp : p.Prime) :
    higherPowerPairIndex (p, a) = (⟨p, hp⟩, a - 2) := by
  simp [higherPowerPairIndex, hp]

theorem higherPowerPairIndex_injOn (Z : ℕ) :
    Set.InjOn higherPowerPairIndex (higherPrimePowerPairs Z : Set (ℕ × ℕ)) := by
  classical
  rintro ⟨p, a⟩ hpa ⟨q, b⟩ hqb heq
  rcases mem_higherPrimePowerPairs_iff.mp hpa with ⟨hp, ha2, _hpaZ⟩
  rcases mem_higherPrimePowerPairs_iff.mp hqb with ⟨hq, hb2, _hqbZ⟩
  simp only [higherPowerPairIndex, dif_pos hp, dif_pos hq] at heq
  obtain ⟨hpq, hab⟩ := Prod.mk.inj heq
  have hpq' : p = q := congrArg Subtype.val hpq
  subst q
  have : a = b := by omega
  subst b
  rfl

/-! ## Normalization against the Tannery envelope -/

/-- In the complete-block regime `p^a ≤ X`, one fixed fiber is bounded by
twice the normalized envelope.  The factor two is an explicit payment for
the two padded `+1` terms; no asymptotic notation is hidden here. -/
theorem localHigherPowerFiber_normalized_le_two_envelope
    {X p a : ℕ} {L : Branch}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha2 : 2 ≤ a)
    (hqX : p ^ a ≤ X) :
    ((localHigherPowerFiber X L p a).card : ℝ) / (X : ℝ) ≤
      2 * higherPowerEnvelope X (⟨p, hp⟩, a - 2) := by
  let q : ℕ := p ^ a
  let r : ℕ := higherPowerDepth p a X
  let P : ℕ := p ^ r
  let H : ℕ := halfDigitCount p
  let U : ℕ := X / q
  let D : ℕ := U / P
  let B : ℕ := (localHigherPowerFiber X L p a).card
  have hqPos : 0 < q := pow_pos hp.pos a
  have hXPos : 0 < X := hqPos.trans_le hqX
  have hUPos : 0 < U := by
    exact Nat.div_pos hqX hqPos
  have hPPos : 0 < P := pow_pos hp.pos r
  have hPleU : P ≤ U := by
    simpa [P, r] using! Nat.pow_log_le_self p hUPos.ne'
  have hDPos : 0 < D := Nat.div_pos hPleU hPPos
  have hcoeff : (U + 1) / P + 1 ≤ 4 * D := by
    have hsucc := succ_div_le_div_add_one U P
    omega
  have hblock : B ≤ ((U + 1) / P + 1) * H ^ r := by
    simpa [B, U, P, H, r, q] using
      (localHigherPowerFiber_card_le_block
        (X := X) (p := p) (a := a) (L := L))
  have hBgeom : B ≤ 4 * D * H ^ r :=
    hblock.trans (Nat.mul_le_mul_right (H ^ r) hcoeff)
  have hDP : D * P ≤ U := by
    simpa [D] using Nat.div_mul_le_self U P
  have hUq : U * q ≤ X := by
    simpa [U] using Nat.div_mul_le_self X q
  have hDPq : D * P * q ≤ X :=
    (Nat.mul_le_mul_right q hDP).trans hUq
  have hnat : B * q * P ≤ 4 * X * H ^ r := by
    calc
      B * q * P ≤ (4 * D * H ^ r) * q * P :=
        Nat.mul_le_mul_right P (Nat.mul_le_mul_right q hBgeom)
      _ = (4 * H ^ r) * (D * P * q) := by ring
      _ ≤ (4 * H ^ r) * X := Nat.mul_le_mul_left _ hDPq
      _ = 4 * X * H ^ r := by ring
  have hreal : (B : ℝ) * (q : ℝ) * (P : ℝ) ≤
      4 * (X : ℝ) * (H : ℝ) ^ r := by
    exact_mod_cast hnat
  have hratio : (B : ℝ) / (X : ℝ) ≤
      (4 * (H : ℝ) ^ r) / ((q : ℝ) * (P : ℝ)) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hXPos)
      (mul_pos (by exact_mod_cast hqPos) (by exact_mod_cast hPPos))).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hreal
  calc
    ((localHigherPowerFiber X L p a).card : ℝ) / (X : ℝ) =
        (B : ℝ) / (X : ℝ) := by rfl
    _ ≤ (4 * (H : ℝ) ^ r) / ((q : ℝ) * (P : ℝ)) := hratio
    _ = 2 * higherPowerEnvelope X (⟨p, hp⟩, a - 2) := by
      have ha : a - 2 + 2 = a := by omega
      rw [higherPowerEnvelope, ha,
        ← halfDigitCount_cast_div_eq_rho hp hp2, div_pow]
      simp only [q, P, H, r, Nat.cast_pow]
      ring

/-- Uniform one-pair estimate.  If `p^a ≤ X` it uses the geometric block
bound; otherwise the unique root class costs one terminal payment.  The
prime `2` fiber is empty by the local-event definition. -/
theorem localHigherPowerFiber_normalized_le_pair_payment
    {X p a Z : ℕ} {L : Branch} (hX : 0 < X)
    (hpa : (p, a) ∈ higherPrimePowerPairs Z) :
    ((localHigherPowerFiber X L p a).card : ℝ) / (X : ℝ) ≤
      2 * higherPowerEnvelope X (higherPowerPairIndex (p, a)) +
        1 / (X : ℝ) := by
  rcases mem_higherPrimePowerPairs_iff.mp hpa with ⟨hp, ha2, _hpowZ⟩
  by_cases hp2 : p = 2
  · subst p
    have hempty : localHigherPowerFiber X L 2 a = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hx, d, hlocal⟩
      exact hlocal.2.1 rfl
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    exact add_nonneg
      (mul_nonneg (by norm_num) (higherPowerEnvelope_nonneg X _))
      (by positivity)
  · rw [higherPowerPairIndex_eq hp]
    by_cases hqX : p ^ a ≤ X
    · exact (localHigherPowerFiber_normalized_le_two_envelope
        hp hp2 ha2 hqX).trans (le_add_of_nonneg_right (by positivity))
    · have hterminal := localHigherPowerFiber_card_le_one_of_lt
          (L := L) (Nat.lt_of_not_ge hqX)
      have hcast : ((localHigherPowerFiber X L p a).card : ℝ) ≤ 1 := by
        exact_mod_cast hterminal
      have hdiv : ((localHigherPowerFiber X L p a).card : ℝ) /
          (X : ℝ) ≤ 1 / (X : ℝ) :=
        div_le_div_of_nonneg_right hcast (by positivity)
      exact hdiv.trans (le_add_of_nonneg_left
        (mul_nonneg (by positivity) (higherPowerEnvelope_nonneg X _)))

/-! ## The global higher-power witness ledger -/

abbrev HigherPowerKey := Σ _L : Branch, Σ _pa : ℕ × ℕ, ℕ

def higherPowerWitnessKey (w : LocalBranchWitness) : HigherPowerKey :=
  ⟨localWitnessBranch w,
    ⟨(localWitnessPrime w, localWitnessExponent w),
      localWitnessParameter w⟩⟩

noncomputable def higherPowerKeys (X : ℕ) : Finset HigherPowerKey :=
  (Finset.univ : Finset Branch).sigma fun L ↦
    (higherPrimePowerPairs (higherPowerBranchHeight * X)).sigma fun pa ↦
      localHigherPowerFiber X L pa.1 pa.2

theorem higherPowerWitnessKey_mapsTo (X : ℕ) :
    Set.MapsTo higherPowerWitnessKey
      (localHigherPowerWitnessesUpTo X : Set LocalBranchWitness)
      (higherPowerKeys X : Set HigherPowerKey) := by
  intro w hw
  have hhigh := Finset.mem_filter.mp hw
  have hlocal := mem_localBranchWitnessesUpTo.mp hhigh.1
  have hx : localWitnessParameter w ∈ parameterRange X :=
    (mem_witnessBox.mp hlocal.1).1
  change higherPowerWitnessKey w ∈ higherPowerKeys X
  rw [higherPowerKeys]
  simp only [higherPowerWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · apply mem_higherPrimePowerPairs_iff.mpr
    exact ⟨hlocal.2.1, hhigh.2,
      localPrimePower_le_higherPowerBranchHeight hx hlocal.2⟩
  · exact mem_localHigherPowerFiber.mpr
      ⟨hx, ⟨localWitnessCofactor w, hlocal.2⟩⟩

theorem higherPowerWitnessKey_injOn (X : ℕ) :
    Set.InjOn higherPowerWitnessKey
      (localHigherPowerWitnessesUpTo X : Set LocalBranchWitness) := by
  rintro ⟨L, x, p, a, d⟩ hw ⟨K, y, q, b, e⟩ hv hkey
  have hL : L = K := congrArg (fun z : HigherPowerKey ↦ z.1) hkey
  have hpa : (p, a) = (q, b) :=
    congrArg (fun z : HigherPowerKey ↦ z.2.1) hkey
  have hxy : x = y := congrArg (fun z : HigherPowerKey ↦ z.2.2) hkey
  subst K
  injection hpa with hpq hab
  subst q
  subst b
  subst y
  have hwd := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.2.2.1.2.1
  have hve := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hv).1).2.2.2.1.2.1
  change branchValue L x = p ^ a * d at hwd
  change branchValue L x = p ^ a * e at hve
  have hp : 0 < p := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.1.pos
  have hde : d = e := by
    apply Nat.mul_left_cancel (pow_pos hp a)
    rw [← hwd, ← hve]
  subst e
  rfl

theorem localHigherPowerWitnesses_card_le_keys (X : ℕ) :
    (localHigherPowerWitnessesUpTo X).card ≤ (higherPowerKeys X).card :=
  Finset.card_le_card_of_injOn higherPowerWitnessKey
    (higherPowerWitnessKey_mapsTo X) (higherPowerWitnessKey_injOn X)

theorem higherPowerKeys_card (X : ℕ) :
    (higherPowerKeys X).card =
      ∑ L : Branch,
        ∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
          (localHigherPowerFiber X L pa.1 pa.2).card := by
  simp [higherPowerKeys, Finset.card_sigma]

theorem higherPowerPair_envelope_sum_le_tsum (X Z : ℕ) :
    (∑ pa ∈ higherPrimePowerPairs Z,
      higherPowerEnvelope X (higherPowerPairIndex pa)) ≤
        ∑' i : HigherPowerIndex, higherPowerEnvelope X i := by
  classical
  rw [← Finset.sum_image (f := higherPowerEnvelope X)
    (higherPowerPairIndex_injOn Z)]
  have hsum : Summable (higherPowerEnvelope X) :=
    higherPowerMajorant_summable.of_nonneg_of_le
      (higherPowerEnvelope_nonneg X)
      (higherPowerEnvelope_le_majorant X)
  exact hsum.sum_le_tsum _
    (fun i _hi ↦ higherPowerEnvelope_nonneg X i)

/-- The normalized sum of all prime-power fibers on one branch is bounded
by the doubled Tannery series plus one terminal payment per eligible pair. -/
theorem branchHigherPowerFiberSum_normalized_le
    (X : ℕ) (hX : 0 < X) (L : Branch) :
    ((∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
        (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
        (X : ℝ) ≤
      2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ) := by
  classical
  let S := higherPrimePowerPairs (higherPowerBranchHeight * X)
  have hterm :
      ∑ pa ∈ S,
          ((localHigherPowerFiber X L pa.1 pa.2).card : ℝ) / (X : ℝ) ≤
        ∑ pa ∈ S,
          (2 * higherPowerEnvelope X (higherPowerPairIndex pa) +
            1 / (X : ℝ)) := by
    apply Finset.sum_le_sum
    intro pa hpa
    exact localHigherPowerFiber_normalized_le_pair_payment hX hpa
  have hfinite :
      (∑ pa ∈ S, higherPowerEnvelope X (higherPowerPairIndex pa)) ≤
        ∑' i : HigherPowerIndex, higherPowerEnvelope X i := by
    simpa [S] using higherPowerPair_envelope_sum_le_tsum X
      (higherPowerBranchHeight * X)
  calc
    ((∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
        (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
        (X : ℝ) =
        ∑ pa ∈ S,
          ((localHigherPowerFiber X L pa.1 pa.2).card : ℝ) / (X : ℝ) := by
      simp only [S, Nat.cast_sum, Finset.sum_div]
    _ ≤ ∑ pa ∈ S,
          (2 * higherPowerEnvelope X (higherPowerPairIndex pa) +
            1 / (X : ℝ)) := hterm
    _ = 2 * (∑ pa ∈ S,
          higherPowerEnvelope X (higherPowerPairIndex pa)) +
          (S.card : ℝ) / (X : ℝ) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
          (S.card : ℝ) / (X : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hfinite
        (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl
    _ = _ := by simp [S]

/-- Exact finite global domination of the higher-power local-witness range.
The outer factor four is the branch count; every other constant is displayed
in the preceding one-fiber lemmas. -/
theorem normalizedHigherPowerWitnessCount_le_majorant
    (X : ℕ) (hX : 0 < X) :
    Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount X ≤
      4 * (2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ)) := by
  have hcardNat := localHigherPowerWitnesses_card_le_keys X
  rw [higherPowerKeys_card] at hcardNat
  have hcardReal : ((localHigherPowerWitnessesUpTo X).card : ℝ) ≤
      ((∑ L : Branch,
        ∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
          (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  unfold Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount
  calc
    ((localHigherPowerWitnessesUpTo X).card : ℝ) / (X : ℝ) ≤
        ((∑ L : Branch,
          ∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
            (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
          (X : ℝ) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = ∑ L : Branch,
        (((∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
          (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
            (X : ℝ)) := by
      simp only [Nat.cast_sum, Finset.sum_div]
    _ ≤ ∑ _L : Branch,
        (2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
          ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
            (X : ℝ)) := by
      apply Finset.sum_le_sum
      intro L _hL
      exact branchHigherPowerFiberSum_normalized_le X hX L
    _ = 4 * (2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ)) := by
      have hcard : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
      norm_num

/-- Unconditional closure of the concrete higher-prime-power range required
by `RangeAssembly`. -/
theorem tendsto_normalizedHigherPowerWitnessCount_zero :
    Tendsto Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall
      Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount_nonneg
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact normalizedHigherPowerWitnessCount_le_majorant X hX
  · have hgeo := tendsto_tsum_higherPowerEnvelope_zero.const_mul 2
    have hsum := hgeo.add tendsto_higherPrimePowerPairs_scaled_card_div
    simpa only [mul_zero, zero_add] using hsum.const_mul 4

end Erdos730.HigherPowerEvents

end Campaign180File33

/- Source module: ErdosProblems.Erdos730.FixedDepthFourier -/
section Campaign180File34
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: fixed-depth finite Fourier infrastructure

This module formalizes the exact finite Fourier identity, complete-sum support
restriction, prime-power quadratic Gauss magnitudes, low-effective-modulus
cancellation, the shifted harmonic layer estimate, and the sharp product
`L¹` bound for consecutive-interval digit boxes.  Every analytic estimate is
proved here rather than introduced as an assumption.
-/

namespace Erdos730
namespace FixedDepthFourier

open scoped ZMod
open Finset AddChar

noncomputable section

/-! ## Exact finite Fourier inversion for an interval count -/

/-- Complex-valued indicator of a finite subset. -/
def finsetIndicator {α : Type*} [DecidableEq α] (A : Finset α) (x : α) : ℂ :=
  if x ∈ A then 1 else 0

@[simp] theorem finsetIndicator_apply_mem
    {α : Type*} [DecidableEq α] {A : Finset α} {x : α} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by
  simp [finsetIndicator, hx]

@[simp] theorem finsetIndicator_apply_not_mem
    {α : Type*} [DecidableEq α] {A : Finset α} {x : α} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by
  simp [finsetIndicator, hx]

theorem sum_finsetIndicator_eq_card
    {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    ∑ x : α, finsetIndicator A x = (A.card : ℂ) := by
  simp [finsetIndicator]

/-- Pointwise unnormalized Fourier inversion on `ZMod Q`. -/
theorem finiteFourier_inversion_at
    {Q : ℕ} [NeZero Q] (Φ : ZMod Q → ℂ) (x : ZMod Q) :
    Φ x = (Q : ℂ)⁻¹ *
      ∑ h : ZMod Q, ZMod.stdAddChar (h * x) * ZMod.dft Φ h := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply Φ) x
  rw [ZMod.invDFT_apply] at hinv
  simpa [smul_eq_mul, mul_comm] using hinv.symm

/-- The incomplete phase sum occurring after Fourier inversion. -/
def intervalPhaseSum {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (h : ZMod Q) : ℂ :=
  ∑ t ∈ Finset.range N, ZMod.stdAddChar (h * F t)

/-- Number of interval parameters whose phase lands in `A`. -/
def intervalHitCount {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) : ℕ :=
  ((Finset.range N).filter fun t => F t ∈ A).card

/-- **Exact identity (30).**  This is Fourier inversion followed by a finite
interchange of the frequency and interval sums. -/
theorem intervalHitCount_fourier_identity
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) :
    (intervalHitCount N F A : ℂ) =
      (Q : ℂ)⁻¹ * ∑ h : ZMod Q,
        ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h := by
  have hcount :
      (intervalHitCount N F A : ℂ) =
        ∑ t ∈ Finset.range N, finsetIndicator A (F t) := by
    simp only [intervalHitCount, Finset.sum_boole, finsetIndicator]
  rw [hcount]
  simp_rw [finiteFourier_inversion_at (finsetIndicator A)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext h
  simp only [intervalPhaseSum]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- The zero-frequency term in (30) is exactly `|A| * N / Q`. -/
theorem zeroFrequency_term
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (A : Finset (ZMod Q)) :
    (Q : ℂ)⁻¹ * ZMod.dft (finsetIndicator A) 0 *
        intervalPhaseSum (Q := Q) N (fun _ => 0) 0 =
      (A.card : ℂ) * N / Q := by
  rw [ZMod.dft_apply_zero, sum_finsetIndicator_eq_card]
  simp [intervalPhaseSum]
  field_simp

/-! ## Exact finite completion identity -/

/-- Fourier phase mass of an arbitrary finite subset of `ZMod Q`. -/
def finsetPhaseSum {Q : ℕ} [NeZero Q]
    (B : Finset (ZMod Q)) (s : ZMod Q) : ℂ :=
  ∑ x ∈ B, ZMod.stdAddChar (s * x)

/-- Complete additive twist of a function on `ZMod Q`. -/
def completeTwist {Q : ℕ} [NeZero Q]
    (f : ZMod Q → ℂ) (s : ZMod Q) : ℂ :=
  ∑ z : ZMod Q, ZMod.stdAddChar (s * z) * f z

/-- Exact finite completion: a sum over `B` is a normalized sum of complete
twists against the Fourier mass of `B`. -/
theorem finiteCompletion_identity
    {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) (B : Finset (ZMod Q)) :
    (∑ x ∈ B, f x) =
      (Q : ℂ)⁻¹ * ∑ s : ZMod Q,
        completeTwist f s * finsetPhaseSum B (-s) := by
  calc
    (∑ x ∈ B, f x) =
        ∑ x ∈ B, (Q : ℂ)⁻¹ *
          ∑ h : ZMod Q,
            ZMod.stdAddChar (h * x) * ZMod.dft f h := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact finiteFourier_inversion_at f x
    _ = (Q : ℂ)⁻¹ * ∑ h : ZMod Q,
          ZMod.dft f h * finsetPhaseSum B h := by
      simp only [finsetPhaseSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext h
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = (Q : ℂ)⁻¹ * ∑ s : ZMod Q,
          completeTwist f s * finsetPhaseSum B (-s) := by
      congr 1
      exact Fintype.sum_equiv (Equiv.neg (ZMod Q))
        (fun h : ZMod Q ↦ ZMod.dft f h * finsetPhaseSum B h)
        (fun s : ZMod Q ↦ completeTwist f s * finsetPhaseSum B (-s))
        (fun h ↦ by
          simp only [Equiv.neg_apply, neg_neg]
          congr 1
          simp only [completeTwist, ZMod.dft_apply, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro z _hz
          congr 2
          ring)

/-- Zero frequency of an incomplete phase sum. -/
@[simp] theorem intervalPhaseSum_zero
    {Q : ℕ} [NeZero Q] (N : ℕ) (F : ℕ → ZMod Q) :
    intervalPhaseSum N F 0 = N := by
  simp [intervalPhaseSum]

/-- Exact removal of the zero frequency from (30). -/
theorem intervalHitCount_discrepancy_identity
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) :
    (intervalHitCount N F A : ℂ) - (A.card : ℂ) * N / Q =
      (Q : ℂ)⁻¹ * ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h := by
  rw [intervalHitCount_fourier_identity]
  rw [← Finset.add_sum_erase Finset.univ
    (fun h : ZMod Q ↦
      ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h)
    (Finset.mem_univ (0 : ZMod Q))]
  rw [ZMod.dft_apply_zero, sum_finsetIndicator_eq_card, intervalPhaseSum_zero]
  simp only [div_eq_mul_inv]
  ring

/-- Norm form of the nonzero-frequency discrepancy bound. -/
theorem intervalHitCount_discrepancy_le
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) :
    ‖(intervalHitCount N F A : ℂ) - (A.card : ℂ) * N / Q‖ ≤
      (Q : ℝ)⁻¹ * ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ‖ZMod.dft (finsetIndicator A) h‖ * ‖intervalPhaseSum N F h‖ := by
  rw [intervalHitCount_discrepancy_identity, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg Q))
  calc
    ‖∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h‖ ≤
      ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ‖ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h‖ := by
          exact norm_sum_le _ _
    _ = ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ‖ZMod.dft (finsetIndicator A) h‖ * ‖intervalPhaseSum N F h‖ := by
          apply Finset.sum_congr rfl
          intro h _hh
          rw [norm_mul]

/-! ## Complete residue blocks -/

/-- Summing a function of a residue class through one natural residue block
is the same as summing it over `ZMod Q`. -/
theorem sum_range_zmod_eq_sum
    {Q : ℕ} [NeZero Q] {M : Type*} [AddCommMonoid M] (g : ZMod Q → M) :
    (∑ n ∈ Finset.range Q, g n) = ∑ z : ZMod Q, g z := by
  cases Q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ Q =>
      rw [← Fin.sum_univ_eq_sum_range]
      exact Fintype.sum_equiv (ZMod.finEquiv (Q + 1))
        (fun i : Fin (Q + 1) ↦ g ((i : ℕ) : ZMod (Q + 1))) g
        (fun i ↦
          congrArg g <| ZMod.natCast_zmod_val ((ZMod.finEquiv (Q + 1)) i))

/-- A natural interval of `K` complete residue blocks contributes `K` times
the corresponding complete `ZMod Q` sum. -/
theorem sum_range_zmod_blocks
    {Q : ℕ} [NeZero Q] (g : ZMod Q → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range (Q * K), g n) = K • ∑ z : ZMod Q, g z := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hblock :
          (∑ x ∈ Finset.range Q,
              g ((Q * K + x : ℕ) : ZMod Q)) =
            ∑ x ∈ Finset.range Q, g x := by
        apply Finset.sum_congr rfl
        intro x _hx
        congr 1
        simp
      rw [hblock, sum_range_zmod_eq_sum]
      exact (succ_nsmul (∑ z : ZMod Q, g z) K).symm

/-! ## Translation and complete-sum vanishing -/

/-- A complete character sum vanishes whenever translation changes every
phase by the same nontrivial character value. -/
theorem completeSum_eq_zero_of_constantShift
    {R : Type*} [AddCommGroup R] [Fintype R]
    (ψ : AddChar R ℂ) (f : R → R) (d c : R)
    (hshift : ∀ z, f (d + z) = f z + c)
    (hc : ψ c ≠ 1) :
    ∑ z : R, ψ (f z) = 0 := by
  have hperm :
      (∑ z : R, ψ (f (d + z))) = ∑ z : R, ψ (f z) :=
    Fintype.sum_equiv (Equiv.addLeft d) _ _ fun _ => rfl
  simp_rw [hshift, map_add_eq_mul] at hperm
  have hmul : ψ c * (∑ z : R, ψ (f z)) = ∑ z : R, ψ (f z) := by
    rw [Finset.mul_sum]
    simpa [mul_comm] using hperm
  exact eq_zero_of_mul_eq_self_left hc hmul

/-- Quadratic phase over a commutative ring. -/
def quadraticPhase {R : Type*} [CommRing R]
    (A B C z : R) : R := A * z ^ 2 + B * z + C

/-- If `A*d=0`, translation by `d` changes the quadratic phase by the
constant `B*d`. -/
theorem quadraticPhase_shift_of_mul_eq_zero
    {R : Type*} [CommRing R] (A B C d z : R) (hAd : A * d = 0) :
    quadraticPhase A B C (d + z) =
      quadraticPhase A B C z + B * d := by
  simp only [quadraticPhase]
  linear_combination (d + 2 * z) * hAd

/-- The top `p`-power layer annihilates one further factor of `p` modulo
`p^m`. -/
theorem primePow_shift_mul_eq_zero
    {p m : ℕ} [NeZero (p ^ m)] (hm : 1 ≤ m) :
    (p : ZMod (p ^ m)) * (p ^ (m - 1) : ZMod (p ^ m)) = 0 := by
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  have heq : p * p ^ (m - 1) = p ^ m := by
    calc
      p * p ^ (m - 1) = p ^ (m - 1) * p := by ac_rfl
      _ = p ^ ((m - 1) + 1) := (pow_succ p (m - 1)).symm
      _ = p ^ m := by congr 1 <;> omega
  rw [heq, ZMod.natCast_self]

/-- If `p∤b`, then `b*p^(m-1)` is nonzero modulo `p^m`. -/
theorem primePow_topLayer_ne_zero
    {p m b : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (hb : ¬p ∣ b) :
    (b : ZMod (p ^ m)) * (p ^ (m - 1) : ZMod (p ^ m)) ≠ 0 := by
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  intro hz
  have hdiv : p ^ m ∣ b * p ^ (m - 1) :=
    (ZMod.natCast_eq_zero_iff (b * p ^ (m - 1)) (p ^ m)).mp hz
  apply hb
  have hpow : 0 < p ^ (m - 1) := pow_pos hp.pos _
  have hm' : m = (m - 1) + 1 := by omega
  have hbase : p ^ m = p ^ (m - 1) * p := by
    conv_lhs => rw [hm', pow_succ]
  have hrhs : b * p ^ (m - 1) = p ^ (m - 1) * b := by ac_rfl
  rw [hbase, hrhs] at hdiv
  exact (Nat.mul_dvd_mul_iff_left hpow).mp hdiv

/-- The `p` explicit elements of the kernel of multiplication by `p` on
`ZMod (p^m)`. -/
def primePowKernelMap
    {p m : ℕ} [NeZero (p ^ m)] (hm : 1 ≤ m) (j : Fin p) :
    {z : ZMod (p ^ m) // (p : ZMod (p ^ m)) * z = 0} := by
  refine ⟨((j.val * p ^ (m - 1) : ℕ) : ZMod (p ^ m)), ?_⟩
  rw [Nat.cast_mul]
  calc
    (p : ZMod (p ^ m)) *
        ((j.val : ZMod (p ^ m)) *
          ((p ^ (m - 1) : ℕ) : ZMod (p ^ m))) =
      (j.val : ZMod (p ^ m)) *
        ((p : ZMod (p ^ m)) *
          ((p ^ (m - 1) : ℕ) : ZMod (p ^ m))) := by ring
    _ = 0 := by
      rw [Nat.cast_pow, primePow_shift_mul_eq_zero hm, mul_zero]

/-- Multiplication by `p` on `ZMod (p^m)` has exactly `p` kernel elements
when `m ≥ 1`. -/
theorem card_primePow_mul_kernel
    {p m : ℕ} [NeZero (p ^ m)] (hp : p.Prime) (hm : 1 ≤ m) :
    Fintype.card {z : ZMod (p ^ m) // (p : ZMod (p ^ m)) * z = 0} = p := by
  let d := p ^ (m - 1)
  have hd : 0 < d := pow_pos hp.pos _
  have hq : p ^ m = p * d := by
    dsimp [d]
    calc
      p ^ m = p ^ ((m - 1) + 1) := by congr 1 <;> omega
      _ = p ^ (m - 1) * p := pow_succ p (m - 1)
      _ = p * p ^ (m - 1) := by ac_rfl
  have hinj : Function.Injective (primePowKernelMap (p := p) (m := m) hm) := by
    intro j k hjk
    apply Fin.ext
    have hval := congrArg (fun z ↦ z.1.val) hjk
    have hjlt : j.val * d < p ^ m := by
      rw [hq]
      exact Nat.mul_lt_mul_of_pos_right j.isLt hd
    have hklt : k.val * d < p ^ m := by
      rw [hq]
      exact Nat.mul_lt_mul_of_pos_right k.isLt hd
    have hmul : j.val * d = k.val * d := by
      simpa only [primePowKernelMap, d, ZMod.val_natCast_of_lt hjlt,
        ZMod.val_natCast_of_lt hklt] using hval
    exact Nat.mul_right_cancel hd hmul
  have hsurj : Function.Surjective (primePowKernelMap (p := p) (m := m) hm) := by
    intro z
    have hzcast :
        (((p * z.1.val : ℕ) : ZMod (p ^ m))) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact z.2
    have hqdiv : p ^ m ∣ p * z.1.val :=
      (ZMod.natCast_eq_zero_iff (p * z.1.val) (p ^ m)).mp hzcast
    have hqdiv' : p * d ∣ p * z.1.val := by
      rcases hqdiv with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc
        p * z.1.val = p ^ m * c := hc
        _ = (p * d) * c := by rw [hq]
    have hddiv : d ∣ z.1.val :=
      (Nat.mul_dvd_mul_iff_left hp.pos).mp hqdiv'
    have hjlt : z.1.val / d < p := by
      rw [Nat.div_lt_iff_lt_mul hd]
      calc
        z.1.val < p ^ m := ZMod.val_lt z.1
        _ = p * d := hq
    let j : Fin p := ⟨z.1.val / d, hjlt⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    change (((j.val * p ^ (m - 1) : ℕ) : ZMod (p ^ m))) = z.1
    have hjd : j.val * p ^ (m - 1) = z.1.val := by
      dsimp [j, d] at *
      exact Nat.div_mul_cancel hddiv
    rw [hjd]
    exact ZMod.natCast_zmod_val z.1
  let e := Equiv.ofBijective (primePowKernelMap (p := p) (m := m) hm) ⟨hinj, hsurj⟩
  simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm

/-- **Complete-sum support restriction from Lemma 2.**  For
`A=p*alpha`, the complete quadratic sum modulo `p^m` vanishes unless its
linear coefficient is divisible by `p`. -/
theorem completeQuadraticSum_eq_zero_of_not_dvd
    {p m alpha b gamma : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (hb : ¬p ∣ b) :
    (∑ z : ZMod (p ^ m),
      ZMod.stdAddChar
        (quadraticPhase ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m)))
          (b : ZMod (p ^ m)) (gamma : ZMod (p ^ m)) z)) = 0 := by
  let d : ZMod (p ^ m) := (p ^ (m - 1) : ℕ)
  let c : ZMod (p ^ m) := (b : ZMod (p ^ m)) * d
  have hpd : (p : ZMod (p ^ m)) * d = 0 := by
    simpa [d] using primePow_shift_mul_eq_zero (p := p) (m := m) hm
  have hAd :
      ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m))) * d = 0 := by
    calc
      ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m))) * d =
          (alpha : ZMod (p ^ m)) * ((p : ZMod (p ^ m)) * d) := by ring
      _ = 0 := by rw [hpd, mul_zero]
  have hc0 : c ≠ 0 := by
    simpa [c, d] using
      primePow_topLayer_ne_zero (p := p) (m := m) (b := b) hp hm hb
  have hchar : ZMod.stdAddChar c ≠ 1 := by
    intro hc
    exact hc0
      ((ZMod.isPrimitive_stdAddChar (p ^ m)).zmod_char_eq_one_iff
        (p ^ m) c |>.mp hc)
  apply completeSum_eq_zero_of_constantShift
    ZMod.stdAddChar
    (quadraticPhase ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m)))
      (b : ZMod (p ^ m)) (gamma : ZMod (p ^ m))) d c
  · intro z
    simpa [add_comm, c] using
      quadraticPhase_shift_of_mul_eq_zero
        ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m)))
          (b : ZMod (p ^ m)) (gamma : ZMod (p ^ m)) d z hAd
  · exact hchar

/-! ## Exact low-effective-modulus vanishing -/

/-- The fixed-depth polynomial `p * α * t² + β * t + γ`. -/
def fixedDepthQuadratic {p m : ℕ}
    (α β γ t : ZMod (p ^ m)) : ZMod (p ^ m) :=
  (p : ZMod (p ^ m)) * α * t ^ 2 + β * t + γ

/-- A unit linear coefficient makes the fixed-depth quadratic polynomial a
permutation modulo every positive prime power (indeed, the proof only needs
`p > 0`). -/
theorem fixedDepthQuadratic_bijective
    {p m : ℕ} (hp0 : 0 < p) {β : ZMod (p ^ m)} (hβ : IsUnit β)
    (α γ : ZMod (p ^ m)) :
    Function.Bijective (fixedDepthQuadratic α β γ) := by
  have hfun : fixedDepthQuadratic α β γ =
      padicBranchMap (p : ZMod (p ^ m)) α 0 β γ := by
    funext t
    simp [fixedDepthQuadratic, padicBranchMap]
  rw [hfun]
  exact padicBranchMap_bijective (p := p) (j := m) hp0 hβ α 0 γ

/-- A nontrivial character summed over the permuted fixed-depth polynomial
vanishes on a complete residue system. -/
theorem completeFixedDepthQuadraticSum_eq_zero
    {p m : ℕ} [NeZero (p ^ m)] (hp0 : 0 < p)
    {β : ZMod (p ^ m)} (hβ : IsUnit β)
    (α γ u : ZMod (p ^ m)) (hu : u ≠ 0) :
    (∑ z : ZMod (p ^ m),
      ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z)) = 0 := by
  have hperm :
      (∑ z : ZMod (p ^ m),
          ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z)) =
        ∑ y : ZMod (p ^ m), ZMod.stdAddChar (u * y) :=
    Fintype.sum_bijective (fixedDepthQuadratic α β γ)
      (fixedDepthQuadratic_bijective hp0 hβ α γ)
      (fun z ↦ ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z))
      (fun y ↦ ZMod.stdAddChar (u * y)) (fun _z ↦ rfl)
  rw [hperm]
  simpa [hu, mul_comm] using
    AddChar.sum_mulShift u (ZMod.isPrimitive_stdAddChar (p ^ m))

/-- If the effective modulus exponent `m` is at most the interval depth
`r`, the length-`p^r` interval is a union of complete residue systems and
the quadratic phase sum vanishes exactly. -/
theorem incompleteFixedDepthQuadraticSum_eq_zero_of_le
    {p m r : ℕ} [NeZero (p ^ m)] (hp0 : 0 < p) (hmr : m ≤ r)
    {β : ZMod (p ^ m)} (hβ : IsUnit β)
    (α γ u : ZMod (p ^ m)) (hu : u ≠ 0) :
    (∑ t ∈ Finset.range (p ^ r),
      ZMod.stdAddChar
        (u * fixedDepthQuadratic α β γ (t : ZMod (p ^ m)))) = 0 := by
  have hpow : p ^ r = p ^ m * p ^ (r - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmr]
  rw [hpow]
  calc
    (∑ t ∈ Finset.range (p ^ m * p ^ (r - m)),
      ZMod.stdAddChar
        (u * fixedDepthQuadratic α β γ (t : ZMod (p ^ m)))) =
        p ^ (r - m) • ∑ z : ZMod (p ^ m),
          ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z) := by
      exact sum_range_zmod_blocks
        (fun z : ZMod (p ^ m) ↦
          ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z)) _
    _ = 0 := by
      rw [completeFixedDepthQuadraticSum_eq_zero hp0 hβ α γ u hu, nsmul_zero]

/-- A quadratic Gauss sum with invertible doubled leading coefficient has
exact squared magnitude equal to the modulus.  This is the kernel-checked
form of the classical odd-modulus Gauss bound. -/
theorem quadraticGaussSum_normSq
    {n : ℕ} [NeZero n] (a b c : ZMod n)
    (ha : IsUnit ((2 : ZMod n) * a)) :
    Complex.normSq
      (∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)) = n := by
  let G : ℂ := ∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)
  have hzero (h : ZMod n) : ((2 : ZMod n) * a) * h = 0 ↔ h = 0 := by
    constructor
    · intro hh
      apply ha.mul_left_cancel
      simpa using hh
    · rintro rfl
      simp
  have hshift (x : ZMod n) :
      (∑ y : ZMod n,
          ZMod.stdAddChar
            (-quadraticPhase a b c x + quadraticPhase a b c y)) =
        ∑ h : ZMod n,
          ZMod.stdAddChar
            (quadraticPhase a b c (x + h) - quadraticPhase a b c x) := by
    exact (Fintype.sum_equiv (Equiv.addLeft x)
      (fun h : ZMod n ↦
        ZMod.stdAddChar
          (quadraticPhase a b c (x + h) - quadraticPhase a b c x))
      (fun y : ZMod n ↦
        ZMod.stdAddChar
          (-quadraticPhase a b c x + quadraticPhase a b c y))
      (fun h ↦ by
        change ZMod.stdAddChar
            (quadraticPhase a b c (x + h) - quadraticPhase a b c x) =
          ZMod.stdAddChar
            (-quadraticPhase a b c x + quadraticPhase a b c (x + h))
        congr 1
        ring)).symm
  have hcomplex : ((Complex.normSq G : ℝ) : ℂ) = (n : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [G]
    rw [map_sum]
    simp_rw [← AddChar.map_neg_eq_conj]
    rw [Finset.sum_mul_sum]
    simp_rw [← AddChar.map_add_eq_mul]
    simp_rw [hshift]
    rw [Finset.sum_comm]
    simp_rw [quadraticPhase]
    have hphase (h x : ZMod n) :
        a * (x + h) ^ 2 + b * (x + h) + c -
            (a * x ^ 2 + b * x + c) =
          (a * h ^ 2 + b * h) + x * (((2 : ZMod n) * a) * h) := by
      ring
    simp_rw [hphase, AddChar.map_add_eq_mul]
    simp_rw [← Finset.mul_sum]
    simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
    simp_rw [hzero]
    simp [ZMod.card]
  exact_mod_cast hcomplex

/-- Degenerate prime-power Gauss identity used in (31): if both quadratic
and linear coefficients have one factor of `p`, and `2α` is a unit, then the
squared magnitude is `p^(m+1)`. -/
theorem primePowDegenerateQuadraticGaussSum_normSq
    {p m : ℕ} [NeZero (p ^ m)] (hp : p.Prime) (hm : 1 ≤ m)
    (α b c : ZMod (p ^ m)) (h2α : IsUnit ((2 : ZMod (p ^ m)) * α)) :
    Complex.normSq
      (∑ x : ZMod (p ^ m),
        ZMod.stdAddChar
          (quadraticPhase ((p : ZMod (p ^ m)) * α)
            ((p : ZMod (p ^ m)) * b) c x)) =
      ((p ^ (m + 1) : ℕ) : ℝ) := by
  let A : ZMod (p ^ m) := (p : ZMod (p ^ m)) * α
  let B : ZMod (p ^ m) := (p : ZMod (p ^ m)) * b
  let G : ℂ := ∑ x : ZMod (p ^ m),
    ZMod.stdAddChar (quadraticPhase A B c x)
  have hkernel (h : ZMod (p ^ m)) :
      ((2 : ZMod (p ^ m)) * A) * h = 0 ↔
        (p : ZMod (p ^ m)) * h = 0 := by
    have hrewrite : ((2 : ZMod (p ^ m)) * A) * h =
        ((2 : ZMod (p ^ m)) * α) * ((p : ZMod (p ^ m)) * h) := by
      dsimp only [A]
      ring
    rw [hrewrite]
    constructor
    · intro hh
      apply h2α.mul_left_cancel
      simpa using hh
    · intro hh
      rw [hh, mul_zero]
  have hphasezero (h : ZMod (p ^ m))
      (hh : (p : ZMod (p ^ m)) * h = 0) :
      A * h ^ 2 + B * h = 0 := by
    dsimp only [A, B]
    calc
      ((p : ZMod (p ^ m)) * α) * h ^ 2 +
          ((p : ZMod (p ^ m)) * b) * h =
        α * h * ((p : ZMod (p ^ m)) * h) +
          b * ((p : ZMod (p ^ m)) * h) := by ring
      _ = 0 := by rw [hh]; simp
  have hshift (x : ZMod (p ^ m)) :
      (∑ y : ZMod (p ^ m),
          ZMod.stdAddChar
            (-quadraticPhase A B c x + quadraticPhase A B c y)) =
        ∑ h : ZMod (p ^ m),
          ZMod.stdAddChar
            (quadraticPhase A B c (x + h) - quadraticPhase A B c x) := by
    exact (Fintype.sum_equiv (Equiv.addLeft x)
      (fun h : ZMod (p ^ m) ↦
        ZMod.stdAddChar
          (quadraticPhase A B c (x + h) - quadraticPhase A B c x))
      (fun y : ZMod (p ^ m) ↦
        ZMod.stdAddChar
          (-quadraticPhase A B c x + quadraticPhase A B c y))
      (fun h ↦ by
        change ZMod.stdAddChar
            (quadraticPhase A B c (x + h) - quadraticPhase A B c x) =
          ZMod.stdAddChar
            (-quadraticPhase A B c x + quadraticPhase A B c (x + h))
        congr 1
        ring)).symm
  have hsum :
      (∑ h : ZMod (p ^ m),
          ZMod.stdAddChar (A * h ^ 2 + B * h) *
            ((if (p : ZMod (p ^ m)) * h = 0 then p ^ m else 0 : ℕ) : ℂ)) =
        ((p ^ (m + 1) : ℕ) : ℂ) := by
    calc
      (∑ h : ZMod (p ^ m),
          ZMod.stdAddChar (A * h ^ 2 + B * h) *
            ((if (p : ZMod (p ^ m)) * h = 0 then p ^ m else 0 : ℕ) : ℂ)) =
        ∑ h : ZMod (p ^ m),
          if (p : ZMod (p ^ m)) * h = 0 then
            (((p ^ m : ℕ) : ℂ)) else 0 := by
            apply Finset.sum_congr rfl
            intro h _hh
            by_cases hz : (p : ZMod (p ^ m)) * h = 0
            · simp [hz, hphasezero h hz]
            · simp [hz]
      _ = (Fintype.card
            {h : ZMod (p ^ m) // (p : ZMod (p ^ m)) * h = 0} : ℂ) *
              ((p ^ m : ℕ) : ℂ) := by
          rw [Fintype.card_subtype]
          simp [Finset.sum_ite]
      _ = ((p ^ (m + 1) : ℕ) : ℂ) := by
          rw [card_primePow_mul_kernel hp hm, pow_succ]
          push_cast
          ring
  have hcomplex : ((Complex.normSq G : ℝ) : ℂ) = (p ^ (m + 1) : ℕ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [G]
    rw [map_sum]
    simp_rw [← AddChar.map_neg_eq_conj]
    rw [Finset.sum_mul_sum]
    simp_rw [← AddChar.map_add_eq_mul]
    simp_rw [hshift]
    rw [Finset.sum_comm]
    simp_rw [quadraticPhase]
    have hphase (h x : ZMod (p ^ m)) :
        A * (x + h) ^ 2 + B * (x + h) + c -
            (A * x ^ 2 + B * x + c) =
          (A * h ^ 2 + B * h) +
            x * (((2 : ZMod (p ^ m)) * A) * h) := by
      ring
    simp_rw [hphase, AddChar.map_add_eq_mul]
    simp_rw [← Finset.mul_sum]
    simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p ^ m))]
    simp_rw [hkernel]
    simpa only [ZMod.card, AddChar.map_add_eq_mul] using hsum
  dsimp only [G, A, B] at hcomplex
  exact_mod_cast hcomplex

/-- Norm form of the degenerate prime-power identity, matching (31). -/
theorem primePowDegenerateQuadraticGaussSum_norm
    {p m : ℕ} [NeZero (p ^ m)] (hp : p.Prime) (hm : 1 ≤ m)
    (α b c : ZMod (p ^ m)) (h2α : IsUnit ((2 : ZMod (p ^ m)) * α)) :
    ‖∑ x : ZMod (p ^ m),
      ZMod.stdAddChar
        (quadraticPhase ((p : ZMod (p ^ m)) * α)
          ((p : ZMod (p ^ m)) * b) c x)‖ =
      Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) := by
  have hsq :
      ‖∑ x : ZMod (p ^ m),
        ZMod.stdAddChar
          (quadraticPhase ((p : ZMod (p ^ m)) * α)
            ((p : ZMod (p ^ m)) * b) c x)‖ ^ 2 =
        ((p ^ (m + 1) : ℕ) : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq,
      primePowDegenerateQuadraticGaussSum_normSq hp hm α b c h2α]
  have hsqrt :
      (Real.sqrt (((p ^ (m + 1) : ℕ) : ℝ))) ^ 2 =
        ((p ^ (m + 1) : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  nlinarith [norm_nonneg
    (∑ x : ZMod (p ^ m),
      ZMod.stdAddChar
        (quadraticPhase ((p : ZMod (p ^ m)) * α)
          ((p : ZMod (p ^ m)) * b) c x)),
    Real.sqrt_nonneg (((p ^ (m + 1) : ℕ) : ℝ))]

/-- Norm form of `quadraticGaussSum_normSq`. -/
theorem quadraticGaussSum_norm
    {n : ℕ} [NeZero n] (a b c : ZMod n)
    (ha : IsUnit ((2 : ZMod n) * a)) :
    ‖∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)‖ =
      Real.sqrt n := by
  have hsq :
      ‖∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)‖ ^ 2 =
        (n : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, quadraticGaussSum_normSq a b c ha]
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  nlinarith [norm_nonneg
    (∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)),
    Real.sqrt_nonneg (n : ℝ)]

/-- Prime-power specialization: an odd-prime unit leading coefficient has
the exact classical square-root Gauss magnitude. -/
theorem primePowQuadraticGaussSum_norm
    {p k A B C : ℕ} [NeZero (p ^ k)]
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : ¬p ∣ A) :
    ‖∑ x : ZMod (p ^ k),
      ZMod.stdAddChar
        (quadraticPhase (A : ZMod (p ^ k)) (B : ZMod (p ^ k))
          (C : ZMod (p ^ k)) x)‖ = Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  have h2 : ¬p ∣ 2 := by
    rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
    exact hp2
  have hunit2 : IsUnit (2 : ZMod (p ^ k)) :=
    natCast_isUnit_zmod_primePow hp h2
  have hunitA : IsUnit (A : ZMod (p ^ k)) :=
    natCast_isUnit_zmod_primePow hp hA
  exact quadraticGaussSum_norm (A : ZMod (p ^ k))
    (B : ZMod (p ^ k)) (C : ZMod (p ^ k)) (hunit2.mul hunitA)

/-! ## Geometric sums and the harmonic layer bound -/

/-- A finite geometric progression, in the notation used by both completion
and one-digit Fourier factors. -/
def geometricPhaseSum (z : ℂ) (N : ℕ) : ℂ :=
  ∑ v ∈ Finset.range N, z ^ v

/-- Trivial length bound for a geometric sum on the unit circle. -/
theorem norm_geometricPhaseSum_le_length
    {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖geometricPhaseSum z N‖ ≤ N := by
  calc
    ‖geometricPhaseSum z N‖ ≤ ∑ v ∈ Finset.range N, ‖z ^ v‖ := by
      exact norm_sum_le _ _
    _ = ∑ _v ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp [norm_pow, hz]
    _ = N := by simp

/-- Nontrivial geometric-series bound.  The numerator contributes at most
two and the exact chord length remains in the denominator. -/
theorem norm_geometricPhaseSum_le_two_div
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖geometricPhaseSum z N‖ ≤ 2 / ‖z - 1‖ := by
  rw [geometricPhaseSum, geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp [norm_pow, hz] <;> norm_num

/-- Moving the start of a consecutive power interval only multiplies its
sum by a unit-modulus scalar. -/
theorem norm_consecutivePowerSum_eq
    {z : ℂ} (hz : ‖z‖ = 1) (M N : ℕ) :
    ‖∑ e ∈ Finset.Ico M (M + N), z ^ e‖ = ‖geometricPhaseSum z N‖ := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show M + N - M = N by omega]
  simp only [pow_add, ← Finset.mul_sum, geometricPhaseSum,
    norm_mul, norm_pow, hz, one_pow, one_mul]

/-- Chord separation for the lower half of the `p`th roots of unity.  This
is the analytic input behind the geometric-series layer cake. -/
theorem stdAddChar_chord_lower_half
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hj : 0 < j) (hhalf : 2 * j ≤ p) :
    (4 : ℝ) * j / p ≤ ‖ZMod.stdAddChar (j : ZMod p) - 1‖ := by
  have hchar : ZMod.stdAddChar (j : ZMod p) =
      Complex.exp (Complex.I * (((2 : ℝ) * Real.pi * j) / p)) := by
    rw [show (j : ZMod p) = ((j : ℤ) : ZMod p) by norm_num,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hchar]
  have harg :
      Complex.I *
          (((2 : ℝ) : ℂ) * (Real.pi : ℂ) * (j : ℂ) / (p : ℂ)) =
        Complex.I * ((((2 : ℝ) * Real.pi * j) / p : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hx0 : 0 ≤ Real.pi * (j : ℝ) / p := by positivity
  have hxhalf : Real.pi * (j : ℝ) / p ≤ Real.pi / 2 := by
    apply (div_le_iff₀ (show (0 : ℝ) < p by positivity)).2
    have hpile : (2 : ℝ) * j ≤ p := by exact_mod_cast hhalf
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin
    (x := Real.pi * (j : ℝ) / p)
    (abs_le.2 ⟨by linarith, hxhalf⟩)
  rw [abs_of_nonneg hx0] at hsin
  have hpR : (0 : ℝ) < p := by positivity
  field_simp [Real.pi_ne_zero, ne_of_gt hpR] at hsin ⊢
  nlinarith [Real.pi_pos]

/-- Geometric-sum decay at a nonzero lower-half frequency. -/
theorem norm_geometricPhaseSum_stdAddChar_lower_half
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hj : 0 < j) (hhalf : 2 * j ≤ p)
    (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ ≤
      (p : ℝ) / (2 * j) := by
  have hjp : j < p := by omega
  have hjz : (j : ZMod p) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hj hjp)
      ((ZMod.natCast_eq_zero_iff j p).mp hz)
  have hchar1 : ZMod.stdAddChar (j : ZMod p) ≠ 1 := by
    intro h
    exact hjz ((ZMod.isPrimitive_stdAddChar p).zmod_char_eq_one_iff
      p (j : ZMod p) |>.mp h)
  have hphaseNorm : ‖ZMod.stdAddChar (j : ZMod p)‖ = 1 :=
    AddChar.norm_apply ZMod.stdAddChar (j : ZMod p)
  refine (norm_geometricPhaseSum_le_two_div hphaseNorm hchar1 N).trans ?_
  have hden : 0 < ‖ZMod.stdAddChar (j : ZMod p) - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hchar1)
  have hjR : (0 : ℝ) < 2 * j := by positivity
  rw [div_le_div_iff₀ hden hjR]
  have hchord := stdAddChar_chord_lower_half hp hj hhalf
  have hpR : (0 : ℝ) < p := by positivity
  have hmul := (div_le_iff₀ hpR).mp hchord
  nlinarith

/-- Negating a frequency conjugates its geometric sum, hence preserves its
norm. -/
theorem norm_geometricPhaseSum_stdAddChar_neg
    {p : ℕ} [NeZero p] (s : ZMod p) (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ =
      ‖geometricPhaseSum (ZMod.stdAddChar s) N‖ := by
  have hconj :
      geometricPhaseSum (ZMod.stdAddChar (-s)) N =
        (starRingEnd ℂ) (geometricPhaseSum (ZMod.stdAddChar s) N) := by
    simp only [geometricPhaseSum, AddChar.map_neg_eq_conj]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    exact (map_pow (starRingEnd ℂ) (ZMod.stdAddChar s) v).symm
  rw [hconj, Complex.norm_conj]

/-- Upper-half frequency decay, obtained from the lower half by conjugation. -/
theorem norm_geometricPhaseSum_stdAddChar_upper_half
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hjp : j < p) (hhalf : p ≤ 2 * j)
    (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ ≤
      (p : ℝ) / (2 * ((p - j : ℕ) : ℝ)) := by
  have hsub0 : 0 < p - j := Nat.sub_pos_of_lt hjp
  have hsubhalf : 2 * (p - j) ≤ p := by omega
  have hjneg : (j : ZMod p) = -((p - j : ℕ) : ZMod p) := by
    apply (eq_neg_iff_add_eq_zero).2
    rw [← Nat.cast_add]
    rw [Nat.add_sub_of_le hjp.le, ZMod.natCast_self]
  rw [hjneg, norm_geometricPhaseSum_stdAddChar_neg]
  exact norm_geometricPhaseSum_stdAddChar_lower_half hp hsub0 hsubhalf N

/-- Symmetric pointwise majorant valid at every nonzero natural frequency
`1 ≤ j < p`. -/
theorem norm_geometricPhaseSum_stdAddChar_le_symmetric
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hj : 0 < j) (hjp : j < p)
    (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ ≤
      (p : ℝ) / 2 *
        (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
  rcases le_total (2 * j) p with hhalf | hhalf
  · refine (norm_geometricPhaseSum_stdAddChar_lower_half hp hj hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * j) = (p : ℝ) / 2 * (j : ℝ)⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · refine (norm_geometricPhaseSum_stdAddChar_upper_half hp hjp hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * ((p - j : ℕ) : ℝ)) =
          (p : ℝ) / 2 * (((p - j : ℕ) : ℝ))⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)

/-- The real harmonic layer used after ordering nonzero frequencies by
distance from the zero frequency. -/
theorem real_harmonic_layer_le (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ)⁻¹)) ≤ 1 + Real.log N := by
  calc
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ)⁻¹)) =
        ((harmonic N : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- Reflection preserves the reciprocal mass on the nonzero natural
frequency interval. -/
theorem sum_Ico_inv_sub_eq (p : ℕ) :
    (∑ j ∈ Finset.Ico 1 p, ((((p - j : ℕ) : ℝ))⁻¹)) =
      ∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹) := by
  simpa using
    (Finset.sum_Ico_reflect (fun j : ℕ ↦ ((j : ℝ)⁻¹)) 1
      (m := p) (n := p) (by omega))

/-- Harmonic bound on the nonzero natural frequency interval. -/
theorem sum_Ico_inv_le_one_add_log (p : ℕ) :
    (∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹)) ≤ 1 + Real.log p := by
  calc
    (∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹)) ≤
        ∑ j ∈ Finset.Icc 1 p, ((j : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢
        omega
      · intro j _hjIcc _hjIco
        positivity
    _ ≤ 1 + Real.log p := real_harmonic_layer_le p

/-- Unshifted one-dimensional layer cake over all nonzero frequencies. -/
theorem nonzero_natural_frequency_mass_le
    {p : ℕ} [NeZero p] (hp : 0 < p) (N : ℕ) :
    (∑ j ∈ Finset.Ico 1 p,
      ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖) ≤
        (p : ℝ) * (1 + Real.log p) := by
  calc
    (∑ j ∈ Finset.Ico 1 p,
      ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖) ≤
        ∑ j ∈ Finset.Ico 1 p, (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_Ico] at hj
      exact norm_geometricPhaseSum_stdAddChar_le_symmetric hp hj.1 hj.2 N
    _ = (p : ℝ) * ∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, sum_Ico_inv_sub_eq]
      ring
    _ ≤ (p : ℝ) * (1 + Real.log p) :=
      mul_le_mul_of_nonneg_left (sum_Ico_inv_le_one_add_log p) (Nat.cast_nonneg p)

/-- Unshifted one-dimensional layer cake including the zero frequency. -/
theorem unshifted_frequency_mass_le
    {p : ℕ} [NeZero p] (hp : 0 < p) {N : ℕ} (hN : N ≤ p) :
    (∑ s : ZMod p,
      ‖geometricPhaseSum (ZMod.stdAddChar s) N‖) ≤
        (p : ℝ) * (2 + Real.log p) := by
  have hsplit :
      (∑ j ∈ Finset.range p,
          ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖) =
        ‖geometricPhaseSum (ZMod.stdAddChar (0 : ZMod p)) N‖ +
          ∑ j ∈ Finset.Ico 1 p,
            ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ := by
    let f : ℕ → ℝ := fun j ↦
      ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖
    have hone : ∑ j ∈ Finset.Ico 0 1, f j = f 0 := by
      norm_num
    rw [Finset.range_eq_Ico]
    calc
      ∑ j ∈ Finset.Ico 0 p, f j =
          (∑ j ∈ Finset.Ico 0 1, f j) + ∑ j ∈ Finset.Ico 1 p, f j :=
        (Finset.sum_Ico_consecutive f (show 0 ≤ 1 by omega)
          (show 1 ≤ p by omega)).symm
      _ = f 0 + ∑ j ∈ Finset.Ico 1 p, f j := by rw [hone]
      _ = ‖geometricPhaseSum (ZMod.stdAddChar (0 : ZMod p)) N‖ +
          ∑ j ∈ Finset.Ico 1 p,
            ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ := by
        simp [f]
  have hzero :
      ‖geometricPhaseSum (ZMod.stdAddChar (0 : ZMod p)) N‖ = (N : ℝ) := by
    simp [geometricPhaseSum]
  calc
    (∑ s : ZMod p,
      ‖geometricPhaseSum (ZMod.stdAddChar s) N‖) =
        ∑ j ∈ Finset.range p,
          ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ :=
      (sum_range_zmod_eq_sum
        (fun s : ZMod p ↦ ‖geometricPhaseSum (ZMod.stdAddChar s) N‖)).symm
    _ = (N : ℝ) + ∑ j ∈ Finset.Ico 1 p,
        ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ := by
      rw [hsplit, hzero]
    _ ≤ (p : ℝ) + (p : ℝ) * (1 + Real.log p) := by
      exact add_le_add (by exact_mod_cast hN)
        (nonzero_natural_frequency_mass_le hp N)
    _ = (p : ℝ) * (2 + Real.log p) := by ring

/-! ## Shifted one-dimensional layer cake -/

/-- The unit-circle phase at real angle `x`. -/
def realUnitPhase (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))

@[simp] theorem norm_realUnitPhase (x : ℝ) :
    ‖realUnitPhase x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal x

/-- A point in the lower half-circle has chord length at least four times
its normalized distance from the origin. -/
theorem realUnitPhase_chord_lower
    (u v : ℝ) (hvu : v ≤ u) (hu0 : 0 ≤ u) (huhalf : u ≤ 1 / 2) :
    4 * v ≤ ‖realUnitPhase (2 * Real.pi * u) - 1‖ := by
  rw [realUnitPhase, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * u / 2 = Real.pi * u by ring]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hx0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
  have hxhalf : Real.pi * u ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin
    (x := Real.pi * u) (abs_le.2 ⟨by linarith, hxhalf⟩)
  rw [abs_of_nonneg hx0] at hsin
  field_simp [Real.pi_ne_zero] at hsin
  nlinarith [Real.pi_pos]

/-- The reflected upper-half version of `realUnitPhase_chord_lower`. -/
theorem realUnitPhase_chord_upper
    (u v : ℝ) (hvu : v ≤ 1 - u)
    (huhalf : 1 / 2 ≤ u) (hu1 : u ≤ 1) :
    4 * v ≤ ‖realUnitPhase (2 * Real.pi * u) - 1‖ := by
  have hy0 : 0 ≤ 1 - u := by linarith
  have hyhalf : 1 - u ≤ 1 / 2 := by linarith
  have hbase := realUnitPhase_chord_lower (1 - u) v hvu hy0 hyhalf
  rw [realUnitPhase, Complex.norm_exp_I_mul_ofReal_sub_one] at hbase ⊢
  rw [show 2 * Real.pi * u / 2 = Real.pi * u by ring]
  rw [show 2 * Real.pi * (1 - u) / 2 =
      Real.pi - Real.pi * u by ring] at hbase
  rw [Real.sin_pi_sub] at hbase
  exact hbase

/-- Geometric decay for a shifted grid point in the lower half-circle. -/
theorem norm_geometricPhaseSum_shiftedGrid_lower
    {p j : ℕ} (hp : 0 < p) (hj : 0 < j)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hhalf : theta + (j : ℝ) / p ≤ 1 / 2) (N : ℕ) :
    ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖ ≤
      (p : ℝ) / (2 * j) := by
  let z := realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))
  have hchord : (4 : ℝ) * ((j : ℝ) / p) ≤ ‖z - 1‖ := by
    exact realUnitPhase_chord_lower
      (theta + (j : ℝ) / p) ((j : ℝ) / p)
      (by linarith) (by positivity) hhalf
  have hchordpos : 0 < ‖z - 1‖ := by
    have : 0 < (4 : ℝ) * ((j : ℝ) / p) := by positivity
    linarith
  have hz1 : z ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hchordpos)
  refine (norm_geometricPhaseSum_le_two_div
    (z := z) (by simp [z]) hz1 N).trans ?_
  have hpR : (0 : ℝ) < p := by positivity
  have hjR : (0 : ℝ) < 2 * j := by positivity
  rw [div_le_div_iff₀ hchordpos hjR]
  have hchord' : (4 : ℝ) * j / p ≤ ‖z - 1‖ := by
    convert hchord using 1 <;> ring
  have hmul := (div_le_iff₀ hpR).mp hchord'
  nlinarith

/-- Geometric decay for a shifted grid point in the upper half-circle. -/
theorem norm_geometricPhaseSum_shiftedGrid_upper
    {p j : ℕ} (hp : 0 < p) (hjp : j + 1 < p)
    (theta : ℝ) (htheta : theta ≤ (1 : ℝ) / p)
    (hhalf : 1 / 2 ≤ theta + (j : ℝ) / p) (N : ℕ) :
    ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖ ≤
      (p : ℝ) / (2 * ((p - 1 - j : ℕ) : ℝ)) := by
  let u : ℝ := theta + (j : ℝ) / p
  let v : ℝ := ((p - 1 - j : ℕ) : ℝ) / p
  let z := realUnitPhase (2 * Real.pi * u)
  have hsubpos : 0 < p - 1 - j := by omega
  have hvpos : 0 < v := by
    dsimp [v]
    positivity
  have hvu : v ≤ 1 - u := by
    dsimp [u, v]
    have hpR : (0 : ℝ) < p := by positivity
    have hjcast : ((p - 1 - j : ℕ) : ℝ) = p - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      norm_num
    rw [hjcast]
    have htheta' := (le_div_iff₀ hpR).mp htheta
    field_simp [ne_of_gt hpR]
    nlinarith
  have hu1 : u ≤ 1 := by
    dsimp [u]
    have hpR : (0 : ℝ) < p := by positivity
    have hjcast : (j : ℝ) + 1 ≤ p := by
      exact_mod_cast (show j + 1 ≤ p by omega)
    have htheta' := (le_div_iff₀ hpR).mp htheta
    field_simp [ne_of_gt hpR]
    nlinarith
  have hchord : (4 : ℝ) * v ≤ ‖z - 1‖ := by
    exact realUnitPhase_chord_upper u v hvu hhalf hu1
  have hchordpos : 0 < ‖z - 1‖ := by
    have : 0 < (4 : ℝ) * v := by positivity
    linarith
  have hz1 : z ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hchordpos)
  refine (norm_geometricPhaseSum_le_two_div
    (z := z) (by simp [z]) hz1 N).trans ?_
  have hpR : (0 : ℝ) < p := by positivity
  have hsubR : (0 : ℝ) < 2 * (p - 1 - j : ℕ) := by positivity
  rw [div_le_div_iff₀ hchordpos hsubR]
  have hchord' : (4 : ℝ) * (p - 1 - j : ℕ) / p ≤ ‖z - 1‖ := by
    dsimp [v] at hchord
    convert hchord using 1 <;> ring
  have hmul := (div_le_iff₀ hpR).mp hchord'
  nlinarith

/-- Symmetric majorant for every interior point of a shifted `p`-grid whose
shift lies in one canonical grid cell. -/
theorem norm_geometricPhaseSum_shiftedGrid_le_symmetric
    {p j : ℕ} (hp : 0 < p) (hj : 0 < j) (hjp : j + 1 < p)
    (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hthetap : theta ≤ (1 : ℝ) / p) (N : ℕ) :
    ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖ ≤
      (p : ℝ) / 2 *
        (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
  rcases le_total (theta + (j : ℝ) / p) (1 / 2) with hhalf | hhalf
  · refine (norm_geometricPhaseSum_shiftedGrid_lower
      hp hj theta htheta0 hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * j) = (p : ℝ) / 2 * (j : ℝ)⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · refine (norm_geometricPhaseSum_shiftedGrid_upper
      hp hjp theta hthetap hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * ((p - 1 - j : ℕ) : ℝ)) =
          (p : ℝ) / 2 * (((p - 1 - j : ℕ) : ℝ))⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)

/-- **Shifted one-dimensional layer cake (34).**  For a shift in one
canonical grid cell, the two endpoint frequencies cost at most `2p`; the
remaining frequencies form a reflected harmonic layer. -/
theorem shiftedGrid_frequency_mass_le
    {p N : ℕ} (hp2 : 2 ≤ p) (hN : N ≤ p)
    (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hthetap : theta ≤ (1 : ℝ) / p) :
    (∑ j ∈ Finset.range p,
      ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖) ≤
      (p : ℝ) * (3 + Real.log p) := by
  have hp : 0 < p := by omega
  let f : ℕ → ℝ := fun j ↦
    ‖geometricPhaseSum
      (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖
  have hend (j : ℕ) : f j ≤ (p : ℝ) := by
    refine (norm_geometricPhaseSum_le_length
      (z := realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p)))
      (by simp) N).trans ?_
    exact_mod_cast hN
  have hsplit :
      (∑ j ∈ Finset.range p, f j) =
        f 0 + (∑ j ∈ Finset.Ico 1 (p - 1), f j) + f (p - 1) := by
    rw [Finset.range_eq_Ico]
    calc
      ∑ j ∈ Finset.Ico 0 p, f j =
          (∑ j ∈ Finset.Ico 0 (p - 1), f j) +
            ∑ j ∈ Finset.Ico (p - 1) p, f j :=
        (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm
      _ = ((∑ j ∈ Finset.Ico 0 1, f j) +
            ∑ j ∈ Finset.Ico 1 (p - 1), f j) +
            ∑ j ∈ Finset.Ico (p - 1) p, f j := by
        congr 1
        exact (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm
      _ = f 0 + (∑ j ∈ Finset.Ico 1 (p - 1), f j) + f (p - 1) := by
        have hp_succ : p = (p - 1) + 1 := by omega
        rw [hp_succ]
        norm_num
  have hreflect :
      (∑ j ∈ Finset.Ico 1 (p - 1),
        ((((p - 1 - j : ℕ) : ℝ))⁻¹)) =
        ∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹) := by
    exact sum_Ico_inv_sub_eq (p - 1)
  have hharmonic :
      (∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹)) ≤
        1 + Real.log p := by
    calc
      (∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹)) ≤
          ∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_Ico] at hj ⊢
          omega
        · intro j _hj _hj'
          positivity
      _ ≤ 1 + Real.log p := sum_Ico_inv_le_one_add_log p
  have hinterior :
      (∑ j ∈ Finset.Ico 1 (p - 1), f j) ≤
        (p : ℝ) * (1 + Real.log p) := by
    calc
      (∑ j ∈ Finset.Ico 1 (p - 1), f j) ≤
          ∑ j ∈ Finset.Ico 1 (p - 1),
            (p : ℝ) / 2 *
              (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
        apply Finset.sum_le_sum
        intro j hj
        simp only [Finset.mem_Ico] at hj
        exact norm_geometricPhaseSum_shiftedGrid_le_symmetric
          hp hj.1 (by omega) theta htheta0 hthetap N
      _ = (p : ℝ) *
          ∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, hreflect]
        ring
      _ ≤ (p : ℝ) * (1 + Real.log p) :=
        mul_le_mul_of_nonneg_left hharmonic (Nat.cast_nonneg p)
  rw [hsplit]
  calc
    f 0 + (∑ j ∈ Finset.Ico 1 (p - 1), f j) + f (p - 1) ≤
        (p : ℝ) + (p : ℝ) * (1 + Real.log p) + (p : ℝ) :=
      add_le_add (add_le_add (hend 0) hinterior) (hend (p - 1))
    _ = (p : ℝ) * (3 + Real.log p) := by ring

/-! ## Exact digit-box factorization and an unconditional `L¹` bound -/

/-- A point of a digit box: at coordinate `i` its digit belongs to `E i`. -/
abbrev DigitTuple {d : ℕ} (E : Fin d → Finset ℕ) :=
  (i : Fin d) → ↑(E i)

/-- The contribution of one digit to the negative Fourier phase modulo
`p^d`. -/
def digitPhase {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d))
    (i : Fin d) (e : ↑(E i)) : ZMod (p ^ d) :=
  -(h * (((e : ℕ) * p ^ (i : ℕ) : ℕ) : ZMod (p ^ d)))

/-- Fourier coefficient of a digit box, written directly as a sum over its
digit tuples. -/
def digitBoxFourierCoeff {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) : ℂ :=
  ∑ x : DigitTuple E,
    ZMod.stdAddChar (∑ i : Fin d, digitPhase E h i (x i))

/-- The one-coordinate factor in the Fourier coefficient of a digit box. -/
def digitFourierFactor {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) (i : Fin d) : ℂ :=
  ∑ e : ↑(E i), ZMod.stdAddChar (digitPhase E h i e)

/-- The Fourier coefficient of a digit box factors exactly digit by digit. -/
theorem digitBoxFourierCoeff_factorization
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) :
    digitBoxFourierCoeff E h = ∏ i : Fin d, digitFourierFactor E h i := by
  simp only [digitBoxFourierCoeff, digitFourierFactor]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  have hmap (s : Finset (Fin d)) :
      ZMod.stdAddChar (∑ i ∈ s, digitPhase E h i (x i)) =
        ∏ i ∈ s, ZMod.stdAddChar (digitPhase E h i (x i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, Finset.prod_insert hi,
          AddChar.map_add_eq_mul, ih]
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte,
    Finset.prod_filter] using hmap Finset.univ

/-- Triangle inequality for a one-coordinate digit factor. -/
theorem norm_digitFourierFactor_le_card
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) (i : Fin d) :
    ‖digitFourierFactor E h i‖ ≤ (E i).card := by
  calc
    ‖digitFourierFactor E h i‖ ≤
        ∑ e : ↑(E i), ‖ZMod.stdAddChar (digitPhase E h i e)‖ := by
      exact norm_sum_le _ _
    _ = ∑ _e : ↑(E i), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact AddChar.norm_apply ZMod.stdAddChar (digitPhase E h i e)
    _ = (E i).card := by simp

/-- Pointwise trivial bound for a digit-box Fourier coefficient. -/
theorem norm_digitBoxFourierCoeff_le_cardProduct
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) :
    ‖digitBoxFourierCoeff E h‖ ≤ ∏ i : Fin d, ((E i).card : ℝ) := by
  rw [digitBoxFourierCoeff_factorization, norm_prod]
  exact Finset.prod_le_prod
    (fun i _hi ↦ norm_nonneg (digitFourierFactor E h i))
    (fun i _hi ↦ norm_digitFourierFactor_le_card E h i)

/-- Unconditional finite `L¹` bound obtained from exact factorization and
the triangle inequality.  The sharper logarithmic bound (35) replaces the
factor `∏ |E_i|` here by `(3 + log p)^d`. -/
theorem digitBoxFourierCoeff_l1_le
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) :
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) ≤
      (p ^ d : ℝ) * ∏ i : Fin d, ((E i).card : ℝ) := by
  calc
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) ≤
        ∑ _h : ZMod (p ^ d), ∏ i : Fin d, ((E i).card : ℝ) := by
      exact Finset.sum_le_sum fun h _hh ↦
        norm_digitBoxFourierCoeff_le_cardProduct E h
    _ = (p ^ d : ℝ) * ∏ i : Fin d, ((E i).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
      norm_num

/-! ## Sharp Fourier L1 bound for interval digit boxes -/

theorem stdAddChar_primeScale {p d x : ℕ} [NeZero p] :
    ZMod.stdAddChar (((p * x : ℕ) : ZMod (p ^ (d + 1)))) =
      ZMod.stdAddChar ((x : ℕ) : ZMod (p ^ d)) := by
  rw [show ((p * x : ℕ) : ZMod (p ^ (d + 1))) =
      ((p * x : ℤ) : ZMod (p ^ (d + 1))) by norm_num,
    show ((x : ℕ) : ZMod (p ^ d)) = ((x : ℤ) : ZMod (p ^ d)) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_succ]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp [hpC]

theorem stdAddChar_tailDigit {p d a b e i : ℕ} [NeZero p] :
    ZMod.stdAddChar
        (-((((a + p ^ d * b) * e * p ^ (i + 1) : ℕ)) :
          ZMod (p ^ (d + 1)))) =
      ZMod.stdAddChar
        (-(((a * e * p ^ i : ℕ)) : ZMod (p ^ d))) := by
  have hnat :
      (a + p ^ d * b) * e * p ^ (i + 1) =
        p * (a * e * p ^ i) + p ^ (d + 1) * (b * e * p ^ i) := by
    rw [pow_succ p d, pow_succ p i]
    ring
  have hphase :
      ((((a + p ^ d * b) * e * p ^ (i + 1) : ℕ)) :
          ZMod (p ^ (d + 1))) =
        ((p * (a * e * p ^ i) : ℕ) : ZMod (p ^ (d + 1))) := by
    rw [hnat]
    push_cast
    have hpzero : (p : ZMod (p ^ (d + 1))) ^ (d + 1) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hpzero, zero_mul, add_zero]
  rw [hphase, AddChar.map_neg_eq_conj, AddChar.map_neg_eq_conj,
    stdAddChar_primeScale]

def naturalDigitFourierFactor (p : ℕ) [NeZero p] {d : ℕ}
    (E : Fin d → Finset ℕ) (h : ℕ) (i : Fin d) : ℂ :=
  ∑ e : ↑(E i), ZMod.stdAddChar
    (-(((h * (e : ℕ) * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))

def naturalDigitBoxFourierCoeff (p : ℕ) [NeZero p] {d : ℕ}
    (E : Fin d → Finset ℕ) (h : ℕ) : ℂ :=
  ∏ i : Fin d, naturalDigitFourierFactor p E h i

theorem digitFourierFactor_natCast_eq {d p : ℕ} [NeZero p]
    (E : Fin d → Finset ℕ) (h : ℕ) (i : Fin d) :
    digitFourierFactor E (h : ZMod (p ^ d)) i = naturalDigitFourierFactor p E h i := by
  apply Finset.sum_congr rfl
  intro e _he
  congr 1
  simp only [digitPhase]
  push_cast
  ring

theorem digitBoxFourierCoeff_natCast_eq {d p : ℕ} [NeZero p]
    (E : Fin d → Finset ℕ) (h : ℕ) :
    digitBoxFourierCoeff E (h : ZMod (p ^ d)) = naturalDigitBoxFourierCoeff p E h := by
  rw [digitBoxFourierCoeff_factorization]
  apply Finset.prod_congr rfl
  intro i _hi
  exact digitFourierFactor_natCast_eq E h i

theorem norm_naturalDigitFourierFactor_interval
    {d p : ℕ} [NeZero p] (E : Fin d → Finset ℕ)
    (h : ℕ) (i : Fin d) (M N : ℕ)
    (hE : E i = Finset.Ico M (M + N)) :
    ‖naturalDigitFourierFactor p E h i‖ =
      ‖geometricPhaseSum
        (ZMod.stdAddChar
          (-(((h * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))) N‖ := by
  let z : ℂ := ZMod.stdAddChar
    (-(((h * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))
  have hterm (e : ℕ) :
      ZMod.stdAddChar
          (-(((h * e * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d))) =
        z ^ e := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    push_cast
    simp only [nsmul_eq_mul]
    ring
  rw [naturalDigitFourierFactor, hE]
  rw [Finset.sum_coe_sort (Finset.Ico M (M + N))
    (fun e : ℕ ↦ ZMod.stdAddChar
      (-(((h * e * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d))))]
  simp_rw [hterm]
  exact norm_consecutivePowerSum_eq
    (AddChar.norm_apply ZMod.stdAddChar
      (-(((h * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))) M N

theorem realUnitPhase_neg (x : ℝ) :
    realUnitPhase (-x) = (starRingEnd ℂ) (realUnitPhase x) := by
  rw [realUnitPhase, realUnitPhase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  push_cast
  ring

theorem stdAddChar_natCast_as_realUnitPhase
    {q h : ℕ} [NeZero q] :
    ZMod.stdAddChar (h : ZMod q) =
      realUnitPhase (2 * Real.pi * ((h : ℝ) / q)) := by
  rw [show (h : ZMod q) = ((h : ℤ) : ZMod q) by norm_num,
    ZMod.stdAddChar_coe]
  unfold realUnitPhase
  congr 1
  push_cast
  ring

theorem stdAddChar_neg_natCast_as_realUnitPhase
    {q h : ℕ} [NeZero q] :
    ZMod.stdAddChar (-(h : ZMod q)) =
      realUnitPhase (-2 * Real.pi * ((h : ℝ) / q)) := by
  rw [AddChar.map_neg_eq_conj, stdAddChar_natCast_as_realUnitPhase]
  convert (realUnitPhase_neg (2 * Real.pi * ((h : ℝ) / q))).symm using 1 <;>
    ring

theorem norm_geometricPhaseSum_realUnitPhase_neg (x : ℝ) (N : ℕ) :
    ‖geometricPhaseSum (realUnitPhase (-x)) N‖ =
      ‖geometricPhaseSum (realUnitPhase x) N‖ := by
  have hconj :
      geometricPhaseSum (realUnitPhase (-x)) N =
        (starRingEnd ℂ) (geometricPhaseSum (realUnitPhase x) N) := by
    rw [realUnitPhase_neg]
    simp only [geometricPhaseSum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    exact (map_pow (starRingEnd ℂ) (realUnitPhase x) v).symm
  rw [hconj, Complex.norm_conj]

theorem topDigitFactor_block_mass_le
    {p d : ℕ} [NeZero p] (hp2 : 2 ≤ p)
    (E : Fin (d + 1) → Finset ℕ) (a M N : ℕ) (ha : a < p ^ d)
    (hE : E ⟨0, Nat.succ_pos d⟩ = Finset.Ico M (M + N))
    (hN : N ≤ p) :
    (∑ b ∈ Finset.range p,
      ‖naturalDigitFourierFactor p E (a + p ^ d * b) ⟨0, Nat.succ_pos d⟩‖) ≤
        (p : ℝ) * (3 + Real.log p) := by
  have hp : 0 < p := by omega
  let theta : ℝ := (a : ℝ) / p ^ (d + 1)
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    positivity
  have hthetap : theta ≤ (1 : ℝ) / p := by
    dsimp [theta]
    have hpR : (0 : ℝ) < p := by positivity
    have hpowR : (0 : ℝ) < p ^ d := by positivity
    have haR : (a : ℝ) ≤ p ^ d := by exact_mod_cast ha.le
    rw [pow_succ]
    field_simp [ne_of_gt hpR, ne_of_gt hpowR]
    nlinarith
  have hfactor (b : ℕ) :
      ‖naturalDigitFourierFactor p E (a + p ^ d * b) ⟨0, Nat.succ_pos d⟩‖ =
        ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (b : ℝ) / p))) N‖ := by
    rw [norm_naturalDigitFourierFactor_interval E (a + p ^ d * b)
      ⟨0, Nat.succ_pos d⟩ M N hE]
    simp only [Fin.val_zero, pow_zero, mul_one,
      stdAddChar_neg_natCast_as_realUnitPhase]
    calc
      ‖geometricPhaseSum
          (realUnitPhase
            (-2 * Real.pi * (((a + p ^ d * b : ℕ) : ℝ) /
              ((p ^ (d + 1) : ℕ) : ℝ)))) N‖ =
        ‖geometricPhaseSum
          (realUnitPhase
            (2 * Real.pi * (((a + p ^ d * b : ℕ) : ℝ) /
              ((p ^ (d + 1) : ℕ) : ℝ)))) N‖ := by
          convert norm_geometricPhaseSum_realUnitPhase_neg
            (2 * Real.pi * (((a + p ^ d * b : ℕ) : ℝ) /
              ((p ^ (d + 1) : ℕ) : ℝ))) N using 1 <;>
            ring
      _ = ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (b : ℝ) / p))) N‖ := by
        congr 3
        dsimp [theta]
        push_cast
        rw [pow_succ]
        have hpR : (p : ℝ) ≠ 0 := by positivity
        have hpowR : (p : ℝ) ^ d ≠ 0 := pow_ne_zero _ hpR
        field_simp [hpR, hpowR]
  simp_rw [hfactor]
  exact shiftedGrid_frequency_mass_le hp2 hN theta htheta0 hthetap

theorem naturalDigitFourierFactor_succ
    {p d a b : ℕ} [NeZero p] (E : Fin (d + 1) → Finset ℕ)
    (i : Fin d) :
    naturalDigitFourierFactor p E (a + p ^ d * b) i.succ =
      naturalDigitFourierFactor p (fun k : Fin d ↦ E k.succ) a i := by
  apply Finset.sum_congr rfl
  intro e _he
  exact stdAddChar_tailDigit

theorem naturalDigitBoxFourierCoeff_split
    {p d a b : ℕ} [NeZero p] (E : Fin (d + 1) → Finset ℕ) :
    naturalDigitBoxFourierCoeff p E (a + p ^ d * b) =
      naturalDigitFourierFactor p E (a + p ^ d * b) ⟨0, Nat.succ_pos d⟩ *
        naturalDigitBoxFourierCoeff p (fun k : Fin d ↦ E k.succ) a := by
  rw [naturalDigitBoxFourierCoeff, Fin.prod_univ_succ, naturalDigitBoxFourierCoeff]
  congr 1
  apply Finset.prod_congr rfl
  intro i _hi
  exact naturalDigitFourierFactor_succ E i

theorem sum_range_mul_blocks
    {M : Type*} [AddCommMonoid M] (A p : ℕ) (f : ℕ → M) :
    (∑ h ∈ Finset.range (A * p), f h) =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range p, f (a + A * b) := by
  rw [mul_comm A p]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ h : Fin (p * A), f h) =
        ∑ ba : Fin p × Fin A, f ((finProdFinEquiv ba : Fin (p * A)) : ℕ) := by
      exact (Fintype.sum_equiv finProdFinEquiv
        (fun ba : Fin p × Fin A ↦
          f ((finProdFinEquiv ba : Fin (p * A)) : ℕ))
        (fun h : Fin (p * A) ↦ f h) (fun _ ↦ rfl)).symm
    _ = ∑ a : Fin A, ∑ b : Fin p, f ((a : ℕ) + A * (b : ℕ)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl

def IsIntervalDigitBox {d : ℕ} (p : ℕ) (E : Fin d → Finset ℕ) : Prop :=
  ∀ i, ∃ M N : ℕ, E i = Finset.Ico M (M + N) ∧ N ≤ p

theorem naturalDigitBoxFourierCoeff_l1_le
    {d p : ℕ} [NeZero p] (hp2 : 2 ≤ p)
    (E : Fin d → Finset ℕ) (hE : IsIntervalDigitBox p E) :
    (∑ h ∈ Finset.range (p ^ d), ‖naturalDigitBoxFourierCoeff p E h‖) ≤
      (p : ℝ) ^ d * (3 + Real.log p) ^ d := by
  induction d with
  | zero =>
      simp [naturalDigitBoxFourierCoeff]
  | succ d ih =>
      let E' : Fin d → Finset ℕ := fun i ↦ E i.succ
      have hE' : IsIntervalDigitBox p E' := by
        intro i
        exact hE i.succ
      rcases hE ⟨0, Nat.succ_pos d⟩ with ⟨M, N, hE0, hN⟩
      have hC : 0 ≤ (p : ℝ) * (3 + Real.log p) := by positivity
      have hblock (a : ℕ) (ha : a < p ^ d) :
          (∑ b ∈ Finset.range p,
            ‖naturalDigitBoxFourierCoeff p E (a + p ^ d * b)‖) ≤
            (p : ℝ) * (3 + Real.log p) * ‖naturalDigitBoxFourierCoeff p E' a‖ := by
        have htop := topDigitFactor_block_mass_le hp2 E a M N ha hE0 hN
        calc
          (∑ b ∈ Finset.range p,
            ‖naturalDigitBoxFourierCoeff p E (a + p ^ d * b)‖) =
              (∑ b ∈ Finset.range p,
                ‖naturalDigitFourierFactor p E (a + p ^ d * b)
                  ⟨0, Nat.succ_pos d⟩‖) * ‖naturalDigitBoxFourierCoeff p E' a‖ := by
            simp_rw [naturalDigitBoxFourierCoeff_split, norm_mul]
            rw [Finset.sum_mul]
          _ ≤ ((p : ℝ) * (3 + Real.log p)) * ‖naturalDigitBoxFourierCoeff p E' a‖ :=
            mul_le_mul_of_nonneg_right htop (norm_nonneg _)
      rw [pow_succ, sum_range_mul_blocks]
      calc
        (∑ a ∈ Finset.range (p ^ d),
          ∑ b ∈ Finset.range p,
            ‖naturalDigitBoxFourierCoeff p E (a + p ^ d * b)‖) ≤
            ∑ a ∈ Finset.range (p ^ d),
              ((p : ℝ) * (3 + Real.log p)) * ‖naturalDigitBoxFourierCoeff p E' a‖ := by
          apply Finset.sum_le_sum
          intro a ha
          exact hblock a (Finset.mem_range.mp ha)
        _ = ((p : ℝ) * (3 + Real.log p)) *
            ∑ a ∈ Finset.range (p ^ d), ‖naturalDigitBoxFourierCoeff p E' a‖ := by
          rw [Finset.mul_sum]
        _ ≤ ((p : ℝ) * (3 + Real.log p)) *
            ((p : ℝ) ^ d * (3 + Real.log p) ^ d) :=
          mul_le_mul_of_nonneg_left (ih E' hE') hC
        _ = (p : ℝ) ^ (d + 1) * (3 + Real.log p) ^ (d + 1) := by
          ring

theorem digitBoxFourierCoeff_interval_l1_le
    {d p : ℕ} [NeZero p] (hp2 : 2 ≤ p)
    (E : Fin d → Finset ℕ) (hE : IsIntervalDigitBox p E) :
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) ≤
      (p : ℝ) ^ d * (3 + Real.log p) ^ d := by
  calc
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) =
        ∑ h ∈ Finset.range (p ^ d),
          ‖digitBoxFourierCoeff E (h : ZMod (p ^ d))‖ :=
      (sum_range_zmod_eq_sum
        (fun h : ZMod (p ^ d) ↦ ‖digitBoxFourierCoeff E h‖)).symm
    _ = ∑ h ∈ Finset.range (p ^ d), ‖naturalDigitBoxFourierCoeff p E h‖ := by
      apply Finset.sum_congr rfl
      intro h _hh
      rw [digitBoxFourierCoeff_natCast_eq]
    _ ≤ (p : ℝ) ^ d * (3 + Real.log p) ^ d :=
      naturalDigitBoxFourierCoeff_l1_le hp2 E hE


def residueClassMap {p q s0 : ℕ} [NeZero p] [NeZero q]
    (hs0 : s0 < p) (j : Fin q) :
    {s : ZMod (p * q) // s.val % p = s0} := by
  have hnlt : s0 + p * j.val < p * q := by
    have hp : 0 < p := NeZero.pos p
    have hq : 0 < q := NeZero.pos q
    calc
      s0 + p * j.val < p + p * j.val := Nat.add_lt_add_right hs0 _
      _ = p * (j.val + 1) := by ring
      _ ≤ p * q := Nat.mul_le_mul_left p (Nat.succ_le_of_lt j.isLt)
  refine ⟨((s0 + p * j.val : ℕ) : ZMod (p * q)), ?_⟩
  rw [ZMod.val_natCast_of_lt hnlt, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hs0]

theorem residueClassMap_bijective
    {p q s0 : ℕ} [NeZero p] [NeZero q] (hs0 : s0 < p) :
    Function.Bijective (residueClassMap (p := p) (q := q) hs0) := by
  have hp : 0 < p := NeZero.pos p
  have hq : 0 < q := NeZero.pos q
  constructor
  · intro j k hjk
    apply Fin.ext
    have hval := congrArg (fun z ↦ z.1.val) hjk
    have hjlt : s0 + p * j.val < p * q := by
      calc
        s0 + p * j.val < p + p * j.val := Nat.add_lt_add_right hs0 _
        _ = p * (j.val + 1) := by ring
        _ ≤ p * q := Nat.mul_le_mul_left p (Nat.succ_le_of_lt j.isLt)
    have hklt : s0 + p * k.val < p * q := by
      calc
        s0 + p * k.val < p + p * k.val := Nat.add_lt_add_right hs0 _
        _ = p * (k.val + 1) := by ring
        _ ≤ p * q := Nat.mul_le_mul_left p (Nat.succ_le_of_lt k.isLt)
    simp only [residueClassMap, ZMod.val_natCast_of_lt hjlt,
      ZMod.val_natCast_of_lt hklt] at hval
    have hmul : p * j.val = p * k.val := Nat.add_left_cancel hval
    exact Nat.mul_left_cancel hp hmul
  · intro s
    have hdivlt : s.1.val / p < q := by
      rw [Nat.div_lt_iff_lt_mul hp]
      simpa [mul_comm] using s.1.val_lt
    let j : Fin q := ⟨s.1.val / p, hdivlt⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    change (((s0 + p * j.val : ℕ) : ZMod (p * q))) = s.1
    have hn : s0 + p * j.val = s.1.val := by
      dsimp [j]
      calc
        s0 + p * (s.1.val / p) =
            s.1.val % p + p * (s.1.val / p) := by rw [s.2]
        _ = s.1.val := Nat.mod_add_div s.1.val p
    rw [hn]
    exact ZMod.natCast_zmod_val s.1

def residueClassEquiv {p q s0 : ℕ} [NeZero p] [NeZero q]
    (hs0 : s0 < p) :
    Fin q ≃ {s : ZMod (p * q) // s.val % p = s0} :=
  Equiv.ofBijective (residueClassMap (p := p) (q := q) hs0)
    (residueClassMap_bijective hs0)

theorem sum_residueClass_eq
    {p q s0 : ℕ} [NeZero p] [NeZero q] (hs0 : s0 < p)
    (f : ZMod (p * q) → ℝ) :
    (∑ s : ZMod (p * q), if s.val % p = s0 then f s else 0) =
      ∑ j ∈ Finset.range q, f ((s0 + p * j : ℕ) : ZMod (p * q)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ s : ZMod (p * q), if s.val % p = s0 then f s else 0) =
        ∑ s : {s : ZMod (p * q) // s.val % p = s0}, f s.1 := by
      rw [← Finset.sum_filter]
      simpa using
        (Finset.sum_subtype
          (Finset.univ.filter fun s : ZMod (p * q) ↦ s.val % p = s0)
          (fun s ↦ by simp) f)
    _ = ∑ j : Fin q,
        f ((residueClassEquiv hs0 j).1) := by
      exact Fintype.sum_equiv (residueClassEquiv hs0).symm
        (fun s : {s : ZMod (p * q) // s.val % p = s0} ↦ f s.1)
        (fun j : Fin q ↦ f ((residueClassEquiv hs0 j).1)) (fun s ↦ by simp)
    _ = ∑ j : Fin q, f ((s0 + p * (j : ℕ) : ℕ) : ZMod (p * q)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

theorem residueClass_geometric_mass_le
    {p q s0 N : ℕ} [NeZero p] [NeZero q]
    (hq2 : 2 ≤ q) (hs0 : s0 < p) (hN : N ≤ q) :
    (∑ s : ZMod (p * q),
      if s.val % p = s0 then
        ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) ≤
      (q : ℝ) * (3 + Real.log q) := by
  have hp : 0 < p := NeZero.pos p
  have hq : 0 < q := NeZero.pos q
  let theta : ℝ := (s0 : ℝ) / (p * q)
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    positivity
  have hthetaq : theta ≤ (1 : ℝ) / q := by
    dsimp [theta]
    have hpR : (0 : ℝ) < p := by positivity
    have hqR : (0 : ℝ) < q := by positivity
    have hs0R : (s0 : ℝ) ≤ p := by exact_mod_cast hs0.le
    push_cast
    field_simp [ne_of_gt hpR, ne_of_gt hqR]
    nlinarith
  rw [sum_residueClass_eq hs0]
  have hfactor (j : ℕ) :
      ‖geometricPhaseSum
          (ZMod.stdAddChar
            (-((s0 + p * j : ℕ) : ZMod (p * q)))) N‖ =
        ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / q))) N‖ := by
    rw [stdAddChar_neg_natCast_as_realUnitPhase]
    calc
      ‖geometricPhaseSum
          (realUnitPhase
            (-2 * Real.pi * (((s0 + p * j : ℕ) : ℝ) / ((p * q : ℕ) : ℝ)))) N‖ =
          ‖geometricPhaseSum
            (realUnitPhase
              (2 * Real.pi * (((s0 + p * j : ℕ) : ℝ) /
                ((p * q : ℕ) : ℝ)))) N‖ := by
        convert norm_geometricPhaseSum_realUnitPhase_neg
          (2 * Real.pi * (((s0 + p * j : ℕ) : ℝ) /
            ((p * q : ℕ) : ℝ))) N using 1 <;> ring
      _ = ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / q))) N‖ := by
        congr 3
        dsimp [theta]
        push_cast
        have hpR : (p : ℝ) ≠ 0 := by positivity
        have hqR : (q : ℝ) ≠ 0 := by positivity
        field_simp [hpR, hqR]
  simp_rw [hfactor]
  exact shiftedGrid_frequency_mass_le hq2 hN theta htheta0 hthetaq

theorem residueClass_geometric_mass_le_of_modulus_eq
    {Q p q s0 N : ℕ} [NeZero Q] [NeZero p] [NeZero q]
    (hQ : Q = p * q) (hq2 : 2 ≤ q) (hs0 : s0 < p) (hN : N ≤ q) :
    (∑ s : ZMod Q,
      if s.val % p = s0 then
        ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) ≤
      (q : ℝ) * (3 + Real.log q) := by
  subst Q
  exact residueClass_geometric_mass_le hq2 hs0 hN

theorem dvd_add_iff_mod_eq_complement
    {p c n : ℕ} (hp : 0 < p) (hc : ¬p ∣ c) :
    p ∣ c + n ↔ n % p = p - c % p := by
  have hcp : c % p < p := Nat.mod_lt c hp
  have hnp : n % p < p := Nat.mod_lt n hp
  have hcmod : c % p ≠ 0 := by
    intro h
    exact hc (Nat.dvd_iff_mod_eq_zero.2 h)
  constructor
  · intro hdiv
    have hmod : (c % p + n % p) % p = 0 := by
      rw [← Nat.add_mod]
      exact Nat.dvd_iff_mod_eq_zero.1 hdiv
    have hsumdiv : p ∣ c % p + n % p :=
      Nat.dvd_iff_mod_eq_zero.2 hmod
    rcases hsumdiv with ⟨k, hk⟩
    have hsumpos : 0 < c % p + n % p := by omega
    have hsumlt : c % p + n % p < 2 * p := by omega
    have hk1 : k = 1 := by nlinarith
    have hsumeq : c % p + n % p = p := by simpa [hk1] using hk
    omega
  · intro hn
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hn]
    have hcp_le : c % p ≤ p := hcp.le
    rw [Nat.add_sub_of_le hcp_le, Nat.mod_self]

def residueInterval {Q : ℕ} [NeZero Q] (N : ℕ) : Finset (ZMod Q) :=
  (Finset.range N).image fun t : ℕ ↦ (t : ZMod Q)

theorem natCast_injective_on_range
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) :
    Set.InjOn (fun t : ℕ ↦ (t : ZMod Q)) (Finset.range N) := by
  intro a ha b hb hab
  have haQ : a < Q := (Finset.mem_range.mp ha).trans_le hN
  have hbQ : b < Q := (Finset.mem_range.mp hb).trans_le hN
  have hval := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt haQ,
    Nat.mod_eq_of_lt hbQ] using hval

theorem sum_residueInterval
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) (f : ZMod Q → ℂ) :
    (∑ x ∈ residueInterval N, f x) =
      ∑ t ∈ Finset.range N, f (t : ZMod Q) := by
  rw [residueInterval, Finset.sum_image (natCast_injective_on_range hN)]

theorem finsetPhaseSum_residueInterval
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) (s : ZMod Q) :
    finsetPhaseSum (residueInterval N) s =
      intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod Q)) s := by
  rw [finsetPhaseSum, sum_residueInterval hN]
  rfl

theorem intervalCompletion_identity
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) (f : ZMod Q → ℂ) :
    (∑ t ∈ Finset.range N, f (t : ZMod Q)) =
      (Q : ℂ)⁻¹ * ∑ s : ZMod Q,
        completeTwist f s *
          intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod Q)) (-s) := by
  rw [← sum_residueInterval hN]
  rw [finiteCompletion_identity]
  congr 1
  apply Finset.sum_congr rfl
  intro s _hs
  rw [finsetPhaseSum_residueInterval hN]

def fixedDepthPhaseFunction {p m : ℕ} [NeZero (p ^ m)]
    (alpha beta gamma u : ℕ) (z : ZMod (p ^ m)) : ℂ :=
  ZMod.stdAddChar
    ((u : ZMod (p ^ m)) *
      fixedDepthQuadratic (p := p) (m := m)
        (alpha : ZMod (p ^ m)) (beta : ZMod (p ^ m))
        (gamma : ZMod (p ^ m)) z)

theorem completeTwist_fixedDepthPhaseFunction
    {p m : ℕ} [NeZero (p ^ m)]
    (alpha beta gamma u : ℕ) (s : ZMod (p ^ m)) :
    completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s =
      ∑ z : ZMod (p ^ m),
        ZMod.stdAddChar
          (quadraticPhase
            ((p : ZMod (p ^ m)) *
              ((u * alpha : ℕ) : ZMod (p ^ m)))
            ((u * beta + s.val : ℕ) : ZMod (p ^ m))
            ((u * gamma : ℕ) : ZMod (p ^ m)) z) := by
  simp only [completeTwist, fixedDepthPhaseFunction, ← AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro z _hz
  congr 1
  have hs : ((s.val : ℕ) : ZMod (p ^ m)) = s :=
    ZMod.natCast_zmod_val s
  rw [Nat.cast_add, hs]
  simp only [fixedDepthQuadratic, quadraticPhase]
  push_cast
  ring

theorem completeTwist_fixedDepthPhaseFunction_eq_zero_of_not_dvd
    {p m alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (s : ZMod (p ^ m))
    (hs : ¬p ∣ u * beta + s.val) :
    completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s = 0 := by
  rw [completeTwist_fixedDepthPhaseFunction]
  exact completeQuadraticSum_eq_zero_of_not_dvd
    (p := p) (m := m) (alpha := u * alpha)
    (b := u * beta + s.val) (gamma := u * gamma) hp hm hs

theorem norm_completeTwist_fixedDepthPhaseFunction_of_dvd
    {p m alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hu : ¬p ∣ u)
    (s : ZMod (p ^ m)) (hs : p ∣ u * beta + s.val) :
    ‖completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s‖ =
      Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) := by
  have h2 : ¬p ∣ 2 := by
    rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
    exact hp2
  have hua : ¬p ∣ u * alpha := by
    simpa only [hp.dvd_mul] using not_or_intro hu halpha
  have hunit2 : IsUnit (2 : ZMod (p ^ m)) :=
    natCast_isUnit_zmod_primePow hp h2
  have hunitUA : IsUnit ((u * alpha : ℕ) : ZMod (p ^ m)) :=
    natCast_isUnit_zmod_primePow hp hua
  have h2ua :
      IsUnit ((2 : ZMod (p ^ m)) *
        ((u * alpha : ℕ) : ZMod (p ^ m))) := hunit2.mul hunitUA
  let b' : ℕ := (u * beta + s.val) / p
  have hb : p * b' = u * beta + s.val := by
    exact Nat.mul_div_cancel' hs
  rw [completeTwist_fixedDepthPhaseFunction]
  convert primePowDegenerateQuadraticGaussSum_norm hp hm
    (((u * alpha : ℕ) : ZMod (p ^ m)))
    ((b' : ℕ) : ZMod (p ^ m))
    (((u * gamma : ℕ) : ZMod (p ^ m))) h2ua using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro z _hz
  congr 2
  push_cast
  simpa only [Nat.cast_add, Nat.cast_mul] using
    congrArg (fun n : ℕ ↦ (n : ZMod (p ^ m))) hb.symm

theorem intervalPhaseSum_natural_eq_geometric
    {Q N : ℕ} [NeZero Q] (s : ZMod Q) :
    intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod Q)) s =
      geometricPhaseSum (ZMod.stdAddChar s) N := by
  simp only [intervalPhaseSum, geometricPhaseSum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem norm_fixedDepthIncompleteSum_le_completion
    {p m N alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm2 : 2 ≤ m) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta) (hu : ¬p ∣ u)
    (hN : N ≤ p ^ (m - 1)) :
    ‖∑ t ∈ Finset.range N,
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        (t : ZMod (p ^ m))‖ ≤
      ((p ^ m : ℕ) : ℝ)⁻¹ *
        Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
          (((p ^ (m - 1) : ℕ) : ℝ) *
            (3 + Real.log (p ^ (m - 1)))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let q : ℕ := p ^ (m - 1)
  have hmq : 1 ≤ m - 1 := by omega
  have hq2 : 2 ≤ q := by
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := by simp
      _ ≤ p ^ (m - 1) := Nat.pow_le_pow_right hp.pos hmq
      _ = q := rfl
  letI : NeZero q := ⟨by omega⟩
  have hQ : p ^ m = p * q := by
    dsimp [q]
    calc
      p ^ m = p ^ ((m - 1) + 1) := by congr 1 <;> omega
      _ = p ^ (m - 1) * p := pow_succ p (m - 1)
      _ = p * p ^ (m - 1) := by ac_rfl
  have hNQ : N ≤ p ^ m := by
    refine hN.trans ?_
    rw [hQ]
    calc
      q = 1 * q := by simp
      _ ≤ p * q := Nat.mul_le_mul_right q hp.one_le
  have hc : ¬p ∣ u * beta := by
    simpa only [hp.dvd_mul] using not_or_intro hu hbeta
  let s0 : ℕ := p - (u * beta) % p
  have hcmod : (u * beta) % p ≠ 0 := by
    intro h
    exact hc (Nat.dvd_iff_mod_eq_zero.2 h)
  have hcmodlt : (u * beta) % p < p := Nat.mod_lt _ hp.pos
  have hs0pos : 0 < s0 := by omega
  have hs0lt : s0 < p := by omega
  have hmass :
      (∑ s : ZMod (p ^ m),
        if s.val % p = s0 then
          ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) ≤
        (q : ℝ) * (3 + Real.log q) := by
    exact residueClass_geometric_mass_le_of_modulus_eq
      hQ hq2 hs0lt hN
  rw [intervalCompletion_identity hNQ]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    ‖∑ s : ZMod (p ^ m),
        completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s *
          intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod (p ^ m))) (-s)‖ ≤
        ∑ s : ZMod (p ^ m),
          ‖completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s *
            intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod (p ^ m))) (-s)‖ :=
      norm_sum_le _ _
    _ = ∑ s : ZMod (p ^ m),
        if s.val % p = s0 then
          Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
            ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0 := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [intervalPhaseSum_natural_eq_geometric]
      have hsupport : p ∣ u * beta + s.val ↔ s.val % p = s0 := by
        simpa [s0] using
          (dvd_add_iff_mod_eq_complement (p := p) (c := u * beta)
            (n := s.val) hp.pos hc)
      by_cases hs : s.val % p = s0
      · have hdvd : p ∣ u * beta + s.val := hsupport.2 hs
        rw [if_pos hs, norm_mul,
          norm_completeTwist_fixedDepthPhaseFunction_of_dvd
            hp (by omega) hp2 halpha hu s hdvd]
      · have hndvd : ¬p ∣ u * beta + s.val := by
          exact fun h ↦ hs (hsupport.1 h)
        rw [if_neg hs,
          completeTwist_fixedDepthPhaseFunction_eq_zero_of_not_dvd
            hp (by omega) s hndvd, zero_mul, norm_zero]
    _ = Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        (∑ s : ZMod (p ^ m),
          if s.val % p = s0 then
            ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases hs : s.val % p = s0 <;> simp [hs]
    _ ≤ Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        ((q : ℝ) * (3 + Real.log q)) :=
      mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)
    _ = Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        (((p ^ (m - 1) : ℕ) : ℝ) *
          (3 + Real.log (p ^ (m - 1)))) := by
      dsimp [q]
      simp only [Nat.cast_pow]

theorem primePower_completion_prefactor_eq_sqrt
    {p m : ℕ} (hp : 0 < p) (hm : 1 ≤ m) :
    ((p ^ m : ℕ) : ℝ)⁻¹ * Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        ((p ^ (m - 1) : ℕ) : ℝ) =
      Real.sqrt ((p ^ (m - 1) : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hpowR : (0 : ℝ) < (p : ℝ) ^ (m - 1) := by positivity
  push_cast
  have hexp : m + 1 = 2 + (m - 1) := by omega
  rw [hexp, pow_add]
  rw [Real.sqrt_mul (sq_nonneg (p : ℝ))]
  rw [show (p : ℝ) ^ 2 = (p : ℝ) ^ 2 by rfl,
    Real.sqrt_sq_eq_abs, abs_of_pos hpR]
  rw [show m = 1 + (m - 1) by omega, pow_add, pow_one]
  field_simp [ne_of_gt hpR, ne_of_gt hpowR]
  congr 1
  omega

theorem primePower_logFactor_le
    {p m r : ℕ} (hp : 0 < p) (hmr : m ≤ 2 * r) :
    3 + Real.log (p ^ (m - 1)) ≤
      ((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  rw [Real.log_pow]
  have hmcast : ((m - 1 : ℕ) : ℝ) ≤ 2 * r := by exact_mod_cast (by omega : m - 1 ≤ 2 * r)
  have hrcast : (0 : ℝ) ≤ r := by positivity
  push_cast
  nlinarith

theorem primePower_sqrtFactor_le
    {p m r : ℕ} (hp : 0 < p) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hmr : m ≤ 2 * r) :
    Real.sqrt ((p ^ (m - 1) : ℕ) : ℝ) ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.pow_le_pow_right hp (by omega : m - 1 ≤ 2 * r - 1)

theorem norm_fixedDepthIncompleteSum_le_uniform
    {p m r alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hr : 1 ≤ r) (hrm : r < m) (hmr : m ≤ 2 * r)
    (hp2 : p ≠ 2) (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (hu : ¬p ∣ u) :
    ‖∑ t ∈ Finset.range (p ^ r),
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        (t : ZMod (p ^ m))‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
  have hm2 : 2 ≤ m := by omega
  have hN : p ^ r ≤ p ^ (m - 1) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have hbase := norm_fixedDepthIncompleteSum_le_completion
    (p := p) (m := m) (N := p ^ r) (alpha := alpha) (beta := beta)
    (gamma := gamma) (u := u) hp hm2 hp2 halpha hbeta hu hN
  calc
    ‖∑ t ∈ Finset.range (p ^ r),
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        (t : ZMod (p ^ m))‖ ≤
        ((p ^ m : ℕ) : ℝ)⁻¹ *
          Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
            (((p ^ (m - 1) : ℕ) : ℝ) *
              (3 + Real.log (p ^ (m - 1)))) := hbase
    _ = Real.sqrt ((p ^ (m - 1) : ℕ) : ℝ) *
        (3 + Real.log (p ^ (m - 1))) := by
      rw [show
        ((p ^ m : ℕ) : ℝ)⁻¹ *
            Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
              (((p ^ (m - 1) : ℕ) : ℝ) *
                (3 + Real.log (p ^ (m - 1)))) =
          (((p ^ m : ℕ) : ℝ)⁻¹ *
            Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
              ((p ^ (m - 1) : ℕ) : ℝ)) *
                (3 + Real.log (p ^ (m - 1))) by ring]
      rw [primePower_completion_prefactor_eq_sqrt hp.pos (by omega)]
    _ ≤ Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
      apply mul_le_mul
      · exact primePower_sqrtFactor_le hp.pos (by omega) hr hmr
      · exact primePower_logFactor_le hp.pos hmr
      · apply add_nonneg (by norm_num)
        apply Real.log_nonneg
        exact_mod_cast (Nat.one_le_pow (m - 1) p hp.one_le)
      · exact Real.sqrt_nonneg _

theorem norm_fixedDepthIncompleteSum_shift_le_uniform
    {p m r alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hr : 1 ≤ r) (hrm : r < m) (hmr : m ≤ 2 * r)
    (hp2 : p ≠ 2) (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (hu : ¬p ∣ u) (M : ℕ) :
    ‖∑ t ∈ Finset.range (p ^ r),
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        ((M + t : ℕ) : ZMod (p ^ m))‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
  let beta' : ℕ := beta + 2 * p * alpha * M
  let gamma' : ℕ := p * alpha * M ^ 2 + beta * M + gamma
  have hmultiple : p ∣ 2 * p * alpha * M := by
    refine ⟨2 * alpha * M, ?_⟩
    ring
  have hbeta' : ¬p ∣ beta' := by
    intro h
    exact hbeta ((Nat.dvd_add_iff_left hmultiple).mpr h)
  have hphase (t : ℕ) :
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
          ((M + t : ℕ) : ZMod (p ^ m)) =
        fixedDepthPhaseFunction (p := p) (m := m) alpha beta' gamma' u
          (t : ZMod (p ^ m)) := by
    simp only [fixedDepthPhaseFunction]
    congr 1
    simp only [fixedDepthQuadratic]
    dsimp [beta', gamma']
    push_cast
    ring
  simp_rw [hphase]
  exact norm_fixedDepthIncompleteSum_le_uniform
    hp hr hrm hmr hp2 halpha hbeta' hu

theorem stdAddChar_powScale {p v m x : ℕ} [NeZero p] :
    ZMod.stdAddChar (((p ^ v * x : ℕ) : ZMod (p ^ (v + m)))) =
      ZMod.stdAddChar ((x : ℕ) : ZMod (p ^ m)) := by
  rw [show ((p ^ v * x : ℕ) : ZMod (p ^ (v + m))) =
      ((p ^ v * x : ℤ) : ZMod (p ^ (v + m))) by norm_num,
    show ((x : ℕ) : ZMod (p ^ m)) = ((x : ℤ) : ZMod (p ^ m)) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp [pow_ne_zero _ hpC]

def fixedDepthQuadraticNat
    (p alpha beta gamma t : ℕ) : ℕ :=
  p * alpha * t ^ 2 + beta * t + gamma

theorem fixedDepthPhase_reduce
    {p v m alpha beta gamma u t : ℕ} [NeZero p] :
    ZMod.stdAddChar
        (((p ^ v * u : ℕ) : ZMod (p ^ (v + m))) *
          fixedDepthQuadratic
            (alpha : ZMod (p ^ (v + m)))
            (beta : ZMod (p ^ (v + m)))
            (gamma : ZMod (p ^ (v + m)))
            (t : ZMod (p ^ (v + m)))) =
      fixedDepthPhaseFunction (p := p) (m := m)
        alpha beta gamma u (t : ZMod (p ^ m)) := by
  rw [show
      (((p ^ v * u : ℕ) : ZMod (p ^ (v + m))) *
        fixedDepthQuadratic
          (alpha : ZMod (p ^ (v + m)))
          (beta : ZMod (p ^ (v + m)))
          (gamma : ZMod (p ^ (v + m)))
          (t : ZMod (p ^ (v + m)))) =
        ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℕ) :
          ZMod (p ^ (v + m))) by
      simp only [fixedDepthQuadratic, fixedDepthQuadraticNat]
      push_cast
      ring]
  rw [stdAddChar_powScale]
  simp only [fixedDepthPhaseFunction, fixedDepthQuadratic, fixedDepthQuadraticNat]
  congr 1
  push_cast
  ring

theorem fixedDepthPhase_reduce_of_exponent_eq
    {p q v m alpha beta gamma u t : ℕ} [NeZero p]
    (hq : q = v + m) :
    ZMod.stdAddChar
        (((p ^ v * u : ℕ) : ZMod (p ^ q)) *
          fixedDepthQuadratic
            (alpha : ZMod (p ^ q))
            (beta : ZMod (p ^ q))
            (gamma : ZMod (p ^ q))
            (t : ZMod (p ^ q))) =
      fixedDepthPhaseFunction (p := p) (m := m)
        alpha beta gamma u (t : ZMod (p ^ m)) := by
  rw [show
      (((p ^ v * u : ℕ) : ZMod (p ^ q)) *
        fixedDepthQuadratic
          (alpha : ZMod (p ^ q))
          (beta : ZMod (p ^ q))
          (gamma : ZMod (p ^ q))
          (t : ZMod (p ^ q))) =
        ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℕ) :
          ZMod (p ^ q)) by
      simp only [fixedDepthQuadratic, fixedDepthQuadraticNat]
      push_cast
      ring]
  rw [show
      fixedDepthPhaseFunction (p := p) (m := m)
          alpha beta gamma u (t : ZMod (p ^ m)) =
        ZMod.stdAddChar
          ((u * fixedDepthQuadraticNat p alpha beta gamma t : ℕ) :
            ZMod (p ^ m)) by
      simp only [fixedDepthPhaseFunction, fixedDepthQuadratic,
        fixedDepthQuadraticNat]
      congr 1
      push_cast
      ring]
  rw [show
      ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℕ) :
          ZMod (p ^ q)) =
        ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℤ) :
          ZMod (p ^ q)) by norm_num,
    show
      ((u * fixedDepthQuadraticNat p alpha beta gamma t : ℕ) : ZMod (p ^ m)) =
        ((u * fixedDepthQuadraticNat p alpha beta gamma t : ℤ) : ZMod (p ^ m)) by
          norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [hq, pow_add]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp [pow_ne_zero _ hpC]

theorem norm_fixedDepthIntervalPhaseSum_le_uniform
    {p r alpha beta gamma : ℕ} [NeZero p]
    (hp : p.Prime) (hr : 1 ≤ r) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (M : ℕ) (h : ZMod (p ^ (2 * r))) (hh : h ≠ 0) :
    ‖intervalPhaseSum (p ^ r)
        (fun t : ℕ ↦
          fixedDepthQuadratic
            (alpha : ZMod (p ^ (2 * r)))
            (beta : ZMod (p ^ (2 * r)))
            (gamma : ZMod (p ^ (2 * r)))
            ((M + t : ℕ) : ZMod (p ^ (2 * r)))) h‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
  have hn : h.val ≠ 0 := (ZMod.val_ne_zero h).2 hh
  rcases Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one with
    ⟨v, u, hu, hval⟩
  have hv : v < 2 * r := by
    by_contra hnot
    have hvle : 2 * r ≤ v := Nat.le_of_not_gt hnot
    have hdvd : p ^ (2 * r) ∣ h.val := by
      rw [hval]
      exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hvle) u
    have hpos : 0 < h.val := Nat.pos_of_ne_zero hn
    have hle : p ^ (2 * r) ≤ h.val := Nat.le_of_dvd hpos hdvd
    exact (not_le_of_gt h.val_lt) hle
  let m : ℕ := 2 * r - v
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmle : m ≤ 2 * r := by dsimp [m]; omega
  have hexp : 2 * r = v + m := by dsimp [m]; omega
  have hsum :
      intervalPhaseSum (p ^ r)
          (fun t : ℕ ↦
            fixedDepthQuadratic
              (alpha : ZMod (p ^ (2 * r)))
              (beta : ZMod (p ^ (2 * r)))
              (gamma : ZMod (p ^ (2 * r)))
              ((M + t : ℕ) : ZMod (p ^ (2 * r)))) h =
        ∑ t ∈ Finset.range (p ^ r),
          fixedDepthPhaseFunction (p := p) (m := m)
            alpha beta gamma u ((M + t : ℕ) : ZMod (p ^ m)) := by
    simp only [intervalPhaseSum]
    apply Finset.sum_congr rfl
    intro t _ht
    rw [← ZMod.natCast_zmod_val h, hval]
    exact
      (fixedDepthPhase_reduce_of_exponent_eq (p := p) (q := 2 * r)
        (v := v) (m := m)
        (alpha := alpha) (beta := beta) (gamma := gamma) (u := u)
        (t := M + t) hexp)
  rw [hsum]
  by_cases hmr : m ≤ r
  · let beta' : ℕ := beta + 2 * p * alpha * M
    let gamma' : ℕ := p * alpha * M ^ 2 + beta * M + gamma
    have hmultiple : p ∣ 2 * p * alpha * M := by
      refine ⟨2 * alpha * M, ?_⟩
      ring
    have hbeta' : ¬p ∣ beta' := by
      intro hdiv
      exact hbeta ((Nat.dvd_add_iff_left hmultiple).mpr hdiv)
    have hphase (t : ℕ) :
        fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
            ((M + t : ℕ) : ZMod (p ^ m)) =
          fixedDepthPhaseFunction (p := p) (m := m) alpha beta' gamma' u
            (t : ZMod (p ^ m)) := by
      simp only [fixedDepthPhaseFunction]
      congr 1
      simp only [fixedDepthQuadratic]
      dsimp [beta', gamma']
      push_cast
      ring
    simp_rw [hphase]
    have hbetaUnit : IsUnit (beta' : ZMod (p ^ m)) :=
      natCast_isUnit_zmod_primePow hp hbeta'
    have huNe : (u : ZMod (p ^ m)) ≠ 0 := by
      intro hzero
      have hpowdvd : p ^ m ∣ u :=
        (ZMod.natCast_eq_zero_iff u (p ^ m)).1 hzero
      exact hu (by
        simpa only [pow_one] using
          ((Nat.pow_dvd_pow p hm).trans hpowdvd))
    have hzero := incompleteFixedDepthQuadraticSum_eq_zero_of_le
      (p := p) (m := m) (r := r) hp.pos hmr hbetaUnit
      (alpha : ZMod (p ^ m)) (gamma' : ZMod (p ^ m))
      (u : ZMod (p ^ m)) huNe
    have hzero' :
        (∑ t ∈ Finset.range (p ^ r),
          fixedDepthPhaseFunction (p := p) (m := m)
            alpha beta' gamma' u (t : ZMod (p ^ m))) = 0 := by
      simpa only [fixedDepthPhaseFunction] using hzero
    rw [hzero', norm_zero]
    positivity
  · exact norm_fixedDepthIncompleteSum_shift_le_uniform
      hp hr (Nat.lt_of_not_ge hmr) hmle hp2 halpha hbeta hu M

theorem fixedDepth_intervalHitCount_discrepancy_le
    {p r alpha beta gamma : ℕ} [NeZero p]
    (hp : p.Prime) (hr : 1 ≤ r) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (M : ℕ) (A : Finset (ZMod (p ^ (2 * r))))
    (hA :
      (∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖) ≤
        ((p ^ (2 * r) : ℕ) : ℝ) *
          (3 + Real.log p) ^ (2 * r)) :
    ‖(intervalHitCount (p ^ r)
          (fun t : ℕ ↦
            fixedDepthQuadratic
              (alpha : ZMod (p ^ (2 * r)))
              (beta : ZMod (p ^ (2 * r)))
              (gamma : ZMod (p ^ (2 * r)))
              ((M + t : ℕ) : ZMod (p ^ (2 * r)))) A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
          (3 + Real.log p) ^ (2 * r) := by
  let F : ℕ → ZMod (p ^ (2 * r)) := fun t ↦
    fixedDepthQuadratic
      (alpha : ZMod (p ^ (2 * r)))
      (beta : ZMod (p ^ (2 * r)))
      (gamma : ZMod (p ^ (2 * r)))
      ((M + t : ℕ) : ZMod (p ^ (2 * r)))
  let C : ℝ :=
    Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
      (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p))
  let L : ℝ := (3 + Real.log p) ^ (2 * r)
  have hlog : 0 ≤ Real.log (p : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hphase (h : ZMod (p ^ (2 * r))) (hh : h ≠ 0) :
      ‖intervalPhaseSum (p ^ r) F h‖ ≤ C := by
    exact norm_fixedDepthIntervalPhaseSum_le_uniform
      hp hr hp2 halpha hbeta M h hh
  have herase :
      (∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖) ≤
        ∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖ := by
    exact Finset.sum_le_univ_sum_of_nonneg
      (fun h ↦ norm_nonneg (ZMod.dft (finsetIndicator A) h))
  change
    ‖(intervalHitCount (p ^ r) F A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤ C * L
  calc
    ‖(intervalHitCount (p ^ r) F A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤
      (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖ * ‖intervalPhaseSum (p ^ r) F h‖ :=
      by
        simpa only [Nat.cast_pow] using
          (intervalHitCount_discrepancy_le (p ^ r) F A)
    _ ≤ (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖ * C := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro h hhmem
      exact mul_le_mul_of_nonneg_left
        (hphase h (Finset.ne_of_mem_erase hhmem))
        (norm_nonneg _)
    _ = (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ((∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖) * C) := by
      rw [Finset.sum_mul]
    _ ≤ (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ((∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖) * C) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right herase hC)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ((((p ^ (2 * r) : ℕ) : ℝ) * L) * C) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hA hC)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = C * L := by
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hQnat : p ^ (2 * r) ≠ 0 := pow_ne_zero _ hp.ne_zero
      have hQ : (((p ^ (2 * r) : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hQnat
      field_simp [hQ]

theorem fixedDepth_intervalHitCount_le
    {p r alpha beta gamma : ℕ} [NeZero p]
    (hp : p.Prime) (hr : 1 ≤ r) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (M : ℕ) (A : Finset (ZMod (p ^ (2 * r))))
    (hA :
      (∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖) ≤
        ((p ^ (2 * r) : ℕ) : ℝ) *
          (3 + Real.log p) ^ (2 * r)) :
    (intervalHitCount (p ^ r)
        (fun t : ℕ ↦
          fixedDepthQuadratic
            (alpha : ZMod (p ^ (2 * r)))
            (beta : ZMod (p ^ (2 * r)))
            (gamma : ZMod (p ^ (2 * r)))
            ((M + t : ℕ) : ZMod (p ^ (2 * r)))) A : ℝ) ≤
      (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) +
        Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
          (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
            (3 + Real.log p) ^ (2 * r) := by
  let F : ℕ → ZMod (p ^ (2 * r)) := fun t ↦
    fixedDepthQuadratic
      (alpha : ZMod (p ^ (2 * r)))
      (beta : ZMod (p ^ (2 * r)))
      (gamma : ZMod (p ^ (2 * r)))
      ((M + t : ℕ) : ZMod (p ^ (2 * r)))
  let D : ℝ :=
    Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
      (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
        (3 + Real.log p) ^ (2 * r)
  have hdisc := fixedDepth_intervalHitCount_discrepancy_le
    (p := p) (r := r) (alpha := alpha) (beta := beta) (gamma := gamma)
    hp hr hp2 halpha hbeta M A hA
  have hre :
      ((intervalHitCount (p ^ r) F A : ℝ) -
        (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) ≤
        ‖(intervalHitCount (p ^ r) F A : ℂ) -
          (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ := by
    have hre0 := Complex.re_le_norm
      ((intervalHitCount (p ^ r) F A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r)))
    have hexp :
        ((A.card : ℂ) * (p ^ r) / (p ^ (2 * r))).re =
          (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) := by
      have hz :
          (A.card : ℂ) * (p ^ r) / (p ^ (2 * r)) =
            Complex.ofReal ((A.card : ℝ) * (p ^ r : ℕ) /
              (p ^ (2 * r) : ℕ)) := by
        norm_num
      rw [hz, Complex.ofReal_re]
    simpa only [Complex.sub_re, Complex.natCast_re, hexp] using hre0
  change (intervalHitCount (p ^ r) F A : ℝ) ≤
    (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) + D
  have hdisc' :
      ‖(intervalHitCount (p ^ r) F A : ℂ) -
          (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤ D := by
    simpa only [F, D] using hdisc
  linarith


end

end FixedDepthFourier
end Erdos730

end Campaign180File34

/- Source module: ErdosProblems.Erdos730.FiniteBlockCount -/
section Campaign180File35
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Finite complete-block counting for Erdős 730

This file isolates the exact division of a natural prefix into complete
blocks of length `P` and one terminal block.  It is the finite combinatorial
step used when applying the fixed-depth Fourier estimate.
-/

namespace Erdos730.FiniteBlockCount

open Finset
open Erdos730.FixedDepthFourier

/-- If every translated complete block of length `P` contains at most `B`
accepted inputs, then a prefix of length `N` contains at most
`floor(N/P) * B + P` accepted inputs.  The final `P` is a literal terminal
block cap, so no analytic discrepancy is charged to an incomplete block. -/
theorem card_filter_range_le_completeBlocks_add_terminal
    (N P B : ℕ) (accept : ℕ → Prop) [DecidablePred accept]
    (hP : 0 < P)
    (hblock : ∀ k : ℕ,
      ((Finset.range P).filter fun t ↦ accept (t + P * k)).card ≤ B) :
    ((Finset.range N).filter accept).card ≤ (N / P) * B + P := by
  let K := N / P
  let R := N % P
  let indicator : ℕ → ℕ := fun n ↦ if accept n then 1 else 0
  have hN : N = P * K + R := by
    dsimp only [K, R]
    exact (Nat.div_add_mod N P).symm
  have hprefix :
      (∑ n ∈ Finset.range (P * K), indicator n) ≤ K * B := by
    rw [sum_range_mul_blocks P K indicator, Finset.sum_comm]
    calc
      (∑ k ∈ Finset.range K, ∑ t ∈ Finset.range P,
          indicator (t + P * k)) ≤
          ∑ _k ∈ Finset.range K, B := by
        apply Finset.sum_le_sum
        intro k _hk
        simpa only [indicator, Finset.sum_boole] using! hblock k
      _ = K * B := by simp
  have hterminal :
      (∑ t ∈ Finset.range R, indicator (P * K + t)) ≤ P := by
    calc
      (∑ t ∈ Finset.range R, indicator (P * K + t)) ≤
          ∑ _t ∈ Finset.range R, 1 := by
        apply Finset.sum_le_sum
        intro t _ht
        dsimp only [indicator]
        split <;> omega
      _ = R := by simp
      _ ≤ P := by
        simpa only [R] using (Nat.mod_lt N hP).le
  have hcard :
      ((Finset.range N).filter accept).card =
        ∑ n ∈ Finset.range N, indicator n := by
    symm
    simpa only [indicator] using!
      (Finset.sum_boole (R := ℕ) accept (Finset.range N))
  rw [hcard]
  calc
    (∑ n ∈ Finset.range N, indicator n) =
        (∑ n ∈ Finset.range (P * K), indicator n) +
          ∑ t ∈ Finset.range R, indicator (P * K + t) := by
      conv_lhs => rw [hN]
      exact Finset.sum_range_add (f := indicator) (P * K) R
    _ ≤ K * B + P := Nat.add_le_add hprefix hterminal
    _ = (N / P) * B + P := by rfl


end Erdos730.FiniteBlockCount

end Campaign180File35

/- Source module: ErdosProblems.Erdos730.FixedDepthDensity -/
section Campaign180File36
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: the fixed-depth analytic density passage

This file isolates equations (37)--(42) from the event-counting ledger.  We
use the relaxed full lower-half box.  At depth `r` its exact density is

`4⁻ʳ * (1 + 1 / p)^(2*r)`.

The difference from `4⁻ʳ` contributes a summable `p⁻²` error after the
per-prime `1/p` weight.  The Fourier discrepancy, terminal blocks, and the
per-prime `+1` terms are packaged as explicit analytic majorants and shown to
vanish.  Thus the majorant tends to the Mertens band mass

`4⁻ʳ * log ((r+2)/(r+1))`.

No event-density assertion is assumed in this module.  Its final comparison
theorem consumes only a separately supplied finite count inequality against
the concrete majorant.
-/

open Filter Finset
open scoped Topology Chebyshev

namespace Erdos730
namespace FixedDepthDensity

open DigitBoxes FullDensity

noncomputable section

/-! ## The exact finite band and relaxed digit density -/

/-- Primes in the real-cutoff depth-`r` band
`X^(1/(r+2)) < p ≤ X^(1/(r+1))`. -/
def fixedDepthPrimeSet (r X : ℕ) : Finset ℕ :=
  (Finset.Ioc
      ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
      ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊).filter Nat.Prime

/-- Exact density of the relaxed full `2r`-digit lower-half box. -/
def relaxedDigitDensity (r p : ℕ) : ℝ :=
  (((halfDigitCount p : ℕ) : ℝ) / (p : ℝ)) ^ (2 * r)

/-- The limiting density at fixed depth. -/
def fixedDepthBaseDensity (r : ℕ) : ℝ := (1 / 4 : ℝ) ^ r

/-- Explicit coefficient in the `O_r(1/p)` density estimate. -/
def fixedDepthDensityErrorConstant (r : ℕ) : ℝ :=
  (2 * r : ℕ) * (2 : ℝ) ^ (2 * r)

theorem relaxedDigitDensity_eq_card_ratio
    {r p : ℕ} (hp : 3 ≤ p) :
    relaxedDigitDensity r p =
      ((lowerHalfResidues p (2 * r)).card : ℝ) / (p : ℝ) ^ (2 * r) := by
  rw [lowerHalfResidues_card hp]
  simp only [relaxedDigitDensity, Nat.cast_pow]
  rw [div_pow]

lemma halfDigitCount_cast_eq {p : ℕ} (hpodd : p % 2 = 1) :
    ((halfDigitCount p : ℕ) : ℝ) = ((p : ℝ) + 1) / 2 := by
  have hpform : p = 2 * (p / 2) + 1 := by omega
  unfold halfDigitCount
  rw [hpform]
  norm_num

/-- Equation (37) for the relaxed full lower-half box. -/
theorem relaxedDigitDensity_formula
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    relaxedDigitDensity r p =
      fixedDepthBaseDensity r * (1 + (p : ℝ)⁻¹) ^ (2 * r) := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  rw [relaxedDigitDensity, halfDigitCount_cast_eq hpodd,
    fixedDepthBaseDensity]
  have hratio : (((p : ℝ) + 1) / 2) / (p : ℝ) =
      (1 / 2 : ℝ) * (1 + (p : ℝ)⁻¹) := by
    field_simp
  rw [hratio, mul_pow]
  congr 1
  rw [show 2 * r = r + r by omega, pow_add]
  rw [← mul_pow]
  norm_num

lemma one_add_pow_sub_one_le
    (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ n - 1 ≤ (n : ℝ) * 2 ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ha0 : 0 ≤ 1 + x := by linarith
      have ha1 : 1 ≤ 1 + x := by linarith
      have ha2 : 1 + x ≤ 2 := by linarith
      have hdiff0 : 0 ≤ (1 + x) ^ n - 1 := by
        exact sub_nonneg.mpr (one_le_pow₀ ha1)
      calc
        (1 + x) ^ (n + 1) - 1 =
            ((1 + x) ^ n - 1) * (1 + x) + x := by ring
        _ ≤ ((n : ℝ) * 2 ^ n * x) * 2 + x := by
          gcongr
        _ ≤ ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * x := by
          have hpow : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
          have hxpow : x ≤ 2 ^ (n + 1) * x :=
            by simpa using mul_le_mul_of_nonneg_right hpow hx0
          calc
            ((n : ℝ) * 2 ^ n * x) * 2 + x =
                (n : ℝ) * 2 ^ (n + 1) * x + x := by
              rw [pow_succ]
              ring
            _ ≤ (n : ℝ) * 2 ^ (n + 1) * x + 2 ^ (n + 1) * x :=
              add_le_add_right hxpow _
            _ = ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * x := by
              push_cast
              ring

theorem relaxedDigitDensity_sub_base_nonneg
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    0 ≤ relaxedDigitDensity r p - fixedDepthBaseDensity r := by
  rw [relaxedDigitDensity_formula hpodd hp]
  have hbase : 0 ≤ fixedDepthBaseDensity r := by
    exact pow_nonneg (by norm_num [fixedDepthBaseDensity]) _
  have hinv : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hpow : 1 ≤ (1 + (p : ℝ)⁻¹) ^ (2 * r) :=
    one_le_pow₀ (by linarith)
  nlinarith

/-- Explicit `O_r(1/p)` bound for the relaxed density. -/
theorem relaxedDigitDensity_sub_base_le
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    relaxedDigitDensity r p - fixedDepthBaseDensity r ≤
      fixedDepthDensityErrorConstant r / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hx0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hpR.le
  have hx1 : (p : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hpR).2 (by exact_mod_cast hp)
  have hpow := one_add_pow_sub_one_le (2 * r) hx0 hx1
  have hbase0 : 0 ≤ fixedDepthBaseDensity r := by
    exact pow_nonneg (by norm_num [fixedDepthBaseDensity]) _
  have hbase1 : fixedDepthBaseDensity r ≤ 1 := by
    exact pow_le_one₀ (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  rw [relaxedDigitDensity_formula hpodd hp]
  calc
    fixedDepthBaseDensity r * (1 + (p : ℝ)⁻¹) ^ (2 * r) -
          fixedDepthBaseDensity r =
        fixedDepthBaseDensity r *
          ((1 + (p : ℝ)⁻¹) ^ (2 * r) - 1) := by ring
    _ ≤ fixedDepthBaseDensity r *
          (((2 * r : ℕ) : ℝ) * 2 ^ (2 * r) * (p : ℝ)⁻¹) := by
      gcongr
    _ ≤ ((2 * r : ℕ) : ℝ) * 2 ^ (2 * r) * (p : ℝ)⁻¹ := by
      have hA : 0 ≤ ((2 * r : ℕ) : ℝ) * 2 ^ (2 * r) * (p : ℝ)⁻¹ := by
        positivity
      simpa using mul_le_mul_of_nonneg_right hbase1 hA
    _ = fixedDepthDensityErrorConstant r / (p : ℝ) := by
      rw [fixedDepthDensityErrorConstant, div_eq_mul_inv]

/-- After the reciprocal-prime weight, the density correction is `O_r(p⁻²)`. -/
theorem relaxedDigitDensity_weighted_error_le
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ) ≤
      fixedDepthDensityErrorConstant r / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by positivity
  calc
    (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ) ≤
        (fixedDepthDensityErrorConstant r / (p : ℝ)) / (p : ℝ) :=
      div_le_div_of_nonneg_right
        (relaxedDigitDensity_sub_base_le hpodd hp) hpR.le
    _ = fixedDepthDensityErrorConstant r / (p : ℝ) ^ 2 := by ring

theorem relaxedDigitDensity_nonneg (r p : ℕ) :
    0 ≤ relaxedDigitDensity r p := by
  unfold relaxedDigitDensity
  positivity

/-- The relaxed box density is at most one; this absorbs the `+1` interval
term in equation (38) into `fixedDepthUnitError`. -/
theorem relaxedDigitDensity_le_one
    {r p : ℕ} (hp : 1 ≤ p) :
    relaxedDigitDensity r p ≤ 1 := by
  unfold relaxedDigitDensity
  apply pow_le_one₀
  · positivity
  · apply (div_le_one₀ (by positivity : (0 : ℝ) < p)).2
    exact_mod_cast halfDigitCount_le hp

/-! ## Tail domination and the exact Mertens decomposition -/

lemma sum_Ioc_eq_range_shift (f : ℕ → ℝ) (L U : ℕ) :
    (∑ n ∈ Finset.Ioc L U, f n) =
      ∑ k ∈ Finset.range (U - L), f (k + L + 1) := by
  classical
  apply Finset.sum_bij (fun n hn ↦ n - (L + 1))
  · intro n hn
    simp only [Finset.mem_range]
    simp only [Finset.mem_Ioc] at hn
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Ioc] at ha hb
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨k + L + 1, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    congr 1
    omega

lemma sum_Ioc_le_tail {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : Summable f) (L U : ℕ) :
    (∑ n ∈ Finset.Ioc L U, f n) ≤
      ∑' k : ℕ, f (k + L + 1) := by
  rw [sum_Ioc_eq_range_shift]
  have hshift : Summable (fun k : ℕ ↦ f (k + L + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((summable_nat_add_iff (L + 1)).2 hs)
  exact hshift.sum_le_tsum (Finset.range (U - L)) (fun k _ ↦ hf _)

lemma tendsto_fixedDepthPrimeBandLowerFloor (r : ℕ) :
    Tendsto (fun X : ℕ ↦
      ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop)

lemma tendsto_fixedDepthPrimeBandUpper_nat (r : ℕ) :
    Tendsto (fun X : ℕ ↦ fixedDepthPrimeBandUpper r (X : ℝ))
      atTop atTop := by
  exact (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop

/-- The reciprocal-square tail starting just above `L`. -/
def reciprocalSquareTail (L : ℕ) : ℝ :=
  ∑' k : ℕ, (((k + L + 1 : ℕ) : ℝ) ^ 2)⁻¹

lemma reciprocalSquare_summable :
    Summable (fun n : ℕ ↦ (((n : ℕ) : ℝ) ^ 2)⁻¹) :=
  Real.summable_nat_pow_inv.mpr (by omega)

theorem tendsto_reciprocalSquareTail_zero :
    Tendsto reciprocalSquareTail atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add
    (f := fun n : ℕ ↦ (((n : ℕ) : ℝ) ^ 2)⁻¹)
  have h' := h.comp (tendsto_add_atTop_nat 1)
  simpa only [reciprocalSquareTail, Nat.add_assoc] using! h'

/-- The exact weighted relaxed-density correction over the depth band. -/
def fixedDepthDensityCorrection (r X : ℕ) : ℝ :=
  ∑ p ∈ fixedDepthPrimeSet r X,
    (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ)

theorem fixedDepthDensityCorrection_nonneg
    {r X : ℕ}
    (hL : 2 ≤ ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) :
    0 ≤ fixedDepthDensityCorrection r X := by
  apply Finset.sum_nonneg
  intro p hp
  rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
  have hp2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 :=
    (hp.2.mod_two_eq_one_iff_ne_two).2 hp2
  exact div_nonneg (relaxedDigitDensity_sub_base_nonneg hpodd (by omega))
    (Nat.cast_nonneg p)

/-- The finite `p⁻²` density correction is bounded by a genuine summable
tail beginning at the lower band endpoint. -/
theorem fixedDepthDensityCorrection_le_tail
    {r X : ℕ}
    (hL : 2 ≤ ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) :
    fixedDepthDensityCorrection r X ≤
      fixedDepthDensityErrorConstant r *
        reciprocalSquareTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by
  let L := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let U := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  have hC : 0 ≤ fixedDepthDensityErrorConstant r := by
    unfold fixedDepthDensityErrorConstant
    positivity
  have hsquare : Summable
      (fun p : ℕ ↦ fixedDepthDensityErrorConstant r *
        (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
    reciprocalSquare_summable.mul_left _
  calc
    fixedDepthDensityCorrection r X =
        ∑ p ∈ fixedDepthPrimeSet r X,
          (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ) := rfl
    _ ≤ ∑ p ∈ fixedDepthPrimeSet r X,
          fixedDepthDensityErrorConstant r * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp2 : p ≠ 2 := by omega
      have hpodd : p % 2 = 1 :=
        (hp.2.mod_two_eq_one_iff_ne_two).2 hp2
      simpa [div_eq_mul_inv] using
        relaxedDigitDensity_weighted_error_le (r := r) hpodd (by omega)
    _ ≤ ∑ p ∈ Finset.Ioc L U,
          fixedDepthDensityErrorConstant r * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := hp
        rw [fixedDepthPrimeSet, Finset.mem_filter] at hp'
        simpa [L, U] using hp'.1
      · intro p _hp _hnot
        positivity
    _ ≤ ∑' k : ℕ,
          fixedDepthDensityErrorConstant r *
            ((((k + L + 1 : ℕ) : ℕ) : ℝ) ^ 2)⁻¹ :=
      sum_Ioc_le_tail (fun _ ↦ by positivity) hsquare L U
    _ = fixedDepthDensityErrorConstant r * reciprocalSquareTail L := by
      rw [reciprocalSquareTail, tsum_mul_left]
    _ = fixedDepthDensityErrorConstant r *
        reciprocalSquareTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by rfl

theorem tendsto_fixedDepthDensityCorrection_zero (r : ℕ) :
    Tendsto (fixedDepthDensityCorrection r) atTop (𝓝 0) := by
  have htail := tendsto_reciprocalSquareTail_zero.comp
    (tendsto_fixedDepthPrimeBandLowerFloor r)
  have hmajorant : Tendsto (fun X : ℕ ↦
      fixedDepthDensityErrorConstant r *
        reciprocalSquareTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) atTop (𝓝 0) := by
    simpa using htail.const_mul (fixedDepthDensityErrorConstant r)
  apply squeeze_zero'
  · filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop 2]
      with X hL
    exact fixedDepthDensityCorrection_nonneg hL
  · filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop 2]
      with X hL
    exact fixedDepthDensityCorrection_le_tail hL
  · exact hmajorant

theorem fixedDepthPrimeSet_reciprocalSum_eq
    {r X : ℕ} (hX : 1 ≤ X) :
    (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ)⁻¹) =
      fixedDepthReciprocalPrimeBand r (X : ℝ) := by
  let L := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let U := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  have hLU : L ≤ U := by
    apply Nat.floor_mono
    exact fixedDepthPrimeBandLower_le_upper r (by exact_mod_cast hX)
  have hunion :
      (Finset.Ioc 0 L).filter Nat.Prime ∪
          (Finset.Ioc L U).filter Nat.Prime =
        (Finset.Ioc 0 U).filter Nat.Prime := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU]
  have hdis : Disjoint
      ((Finset.Ioc 0 L).filter Nat.Prime)
      ((Finset.Ioc L U).filter Nat.Prime) :=
    (Finset.Ioc_disjoint_Ioc_of_le (le_refl L)).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [fixedDepthReciprocalPrimeBand, reciprocalPrimeSumReal,
    reciprocalPrimeSumReal]
  change (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime, (p : ℝ)⁻¹) =
    (∑ p ∈ (Finset.Ioc 0 U).filter Nat.Prime, (p : ℝ)⁻¹) -
      ∑ p ∈ (Finset.Ioc 0 L).filter Nat.Prime, (p : ℝ)⁻¹
  rw [← hunion, Finset.sum_union hdis]
  ring

/-- Exact decomposition of the relaxed prime mass into the Mertens main term
and the summable density correction. -/
theorem fixedDepthRelaxedPrimeMass_eq
    {r X : ℕ} (hX : 1 ≤ X) :
    (∑ p ∈ fixedDepthPrimeSet r X,
        relaxedDigitDensity r p / (p : ℝ)) =
      fixedDepthBaseDensity r *
          fixedDepthReciprocalPrimeBand r (X : ℝ) +
        fixedDepthDensityCorrection r X := by
  rw [← fixedDepthPrimeSet_reciprocalSum_eq hX,
    fixedDepthDensityCorrection, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

theorem tendsto_fixedDepthRelaxedPrimeMass (r : ℕ) :
    Tendsto (fun X : ℕ ↦
      ∑ p ∈ fixedDepthPrimeSet r X,
        relaxedDigitDensity r p / (p : ℝ)) atTop
      (𝓝 (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r)) := by
  have hmain :=
    (tendsto_fixedDepthReciprocalPrimeBand_nat r).const_mul
      (fixedDepthBaseDensity r)
  have h := hmain.add (tendsto_fixedDepthDensityCorrection_zero r)
  have h' : Tendsto (fun X : ℕ ↦
      fixedDepthBaseDensity r *
          fixedDepthReciprocalPrimeBand r (X : ℝ) +
        fixedDepthDensityCorrection r X) atTop
      (𝓝 (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r)) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  exact (fixedDepthRelaxedPrimeMass_eq hX).symm

/-! ## The fixed-depth Fourier discrepancy tail -/

/-- The normalized per-prime Fourier envelope.  The harmless `3 + log p`
form directly matches the interval `L¹` surface in
`Erdos730FixedDepthFourier`; it also dominates the paper's `1 + log p` form. -/
def fixedDepthFourierWeight (r p : ℕ) : ℝ :=
  (3 + Real.log p) ^ (2 * r + 1) *
    (p : ℝ) ^ (-(3 / 2 : ℝ))

/-- The finite Fourier envelope over the depth band. -/
def fixedDepthFourierBandError (r X : ℕ) : ℝ :=
  ∑ p ∈ fixedDepthPrimeSet r X, fixedDepthFourierWeight r p

/-- The explicit paper coefficient `2 C_r`, with
`C_r = (2r+3) 3^(2r)`. -/
def fixedDepthFourierErrorConstant (r : ℕ) : ℝ :=
  2 * (2 * r + 3 : ℕ) * (3 : ℝ) ^ (2 * r)

/-- Complete normalized Fourier-error majorant. -/
def fixedDepthFourierError (r X : ℕ) : ℝ :=
  fixedDepthFourierErrorConstant r * fixedDepthFourierBandError r X

/-- The exact one-block discrepancy on the right side of
`FixedDepthFourier.fixedDepth_intervalHitCount_discrepancy_le`. -/
def fixedDepthBlockDiscrepancy (r p : ℕ) : ℝ :=
  Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) *
    (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
      (3 + Real.log p) ^ (2 * r)

theorem fixedDepthBlockDiscrepancy_nonneg (r p : ℕ) :
    0 ≤ fixedDepthBlockDiscrepancy r p := by
  unfold fixedDepthBlockDiscrepancy
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (by positivity)))
    (pow_nonneg (by positivity) _)

theorem one_le_fixedDepthBlockDiscrepancy
    {r p : ℕ} (hp : 0 < p) (hr : 1 ≤ r) :
    1 ≤ fixedDepthBlockDiscrepancy r p := by
  have hp1 : 1 ≤ p := hp
  have hpowNat : 1 ≤ p ^ (2 * r - 1) :=
    Nat.one_le_pow _ p hp
  have hpowReal : (1 : ℝ) ≤ ((p ^ (2 * r - 1) : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hsqrt : (1 : ℝ) ≤
      Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) := by
    exact Real.le_sqrt_of_sq_le (by simpa using hpowReal)
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hcoef : (1 : ℝ) ≤ ((2 * r + 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * r + 3)
  have hlog1 : (1 : ℝ) ≤ 1 + Real.log p := by linarith
  have hlog3 : (1 : ℝ) ≤ (3 + Real.log p) ^ (2 * r) :=
    one_le_pow₀ (by linarith)
  rw [fixedDepthBlockDiscrepancy]
  calc
    (1 : ℝ) = 1 * (1 * 1) * 1 := by norm_num
    _ ≤ Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
          (3 + Real.log p) ^ (2 * r) := by gcongr

/-- Exact natural-number complete-block count.  The band condition pays for
the endpoint `+1` without introducing another Fourier block. -/
theorem fixedDepthBlockCount_mul_pow_le
    {X p r : ℕ} (hp : 0 < p) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    ((X / p + 1) / p ^ r) * p ^ (r + 1) ≤ 2 * X := by
  let B := (X / p + 1) / p ^ r
  have hdiv : B * p ^ r ≤ X / p + 1 := by
    exact Nat.div_mul_le_self (X / p + 1) (p ^ r)
  have hpX : p ≤ X := by
    calc
      p = p ^ 1 := by simp
      _ ≤ p ^ (r + 1) := Nat.pow_le_pow_right hp (by omega)
      _ ≤ X := hband
  have hXp : (X / p) * p ≤ X := Nat.div_mul_le_self X p
  calc
    B * p ^ (r + 1) = (B * p ^ r) * p := by
      rw [pow_succ]
      ring
    _ ≤ (X / p + 1) * p := Nat.mul_le_mul_right p hdiv
    _ = (X / p) * p + p := by ring
    _ ≤ X + X := Nat.add_le_add hXp hpX
    _ = 2 * X := by ring

theorem fixedDepthBlockCount_normalized_le
    {X p r : ℕ} (hp : 0 < p) (hX : 0 < X) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    ((((X / p + 1) / p ^ r : ℕ) : ℝ) / (X : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hnat := fixedDepthBlockCount_mul_pow_le hp hr hband
  have hreal : (((X / p + 1) / p ^ r : ℕ) : ℝ) *
      (p : ℝ) ^ (r + 1) ≤ 2 * (X : ℝ) := by
    exact_mod_cast hnat
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  apply (div_le_div_iff₀ hXR (pow_pos hpR (r + 1))).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hreal

lemma sqrt_prime_pow_div (p r : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) /
        (p : ℝ) ^ (r + 1) =
      (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hexp : (((2 * r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) =
      (r : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hpR.le, hexp, ← Real.rpow_natCast]
  rw [← Real.rpow_sub hpR]
  congr 1
  push_cast
  ring

/-- The chosen fixed-r Fourier coefficient dominates the exact translated
Lemma-2 discrepancy, including the factor two from the number of complete
`p^r` blocks. -/
theorem fixedDepthBlockDiscrepancy_scaled_le
    {p r : ℕ} (hp : 0 < p) (hr : 1 ≤ r) :
    (2 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp)
  have hsqrt := sqrt_prime_pow_div p r hp hr
  have hz : 0 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hpR.le _
  have hC : 0 ≤ (((2 * r + 3 : ℕ) : ℝ)) := by positivity
  calc
    (2 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p =
        2 * (Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) /
          (p : ℝ) ^ (r + 1)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      rw [fixedDepthBlockDiscrepancy]
      ring
    _ = 2 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by rw [hsqrt]
    _ ≤ 2 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (3 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      gcongr
      norm_num
    _ = 2 * (((2 * r + 3 : ℕ) : ℝ)) *
          ((3 + Real.log p) ^ (2 * r + 1) *
            (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
      rw [fixedDepthFourierErrorConstant, fixedDepthFourierWeight]
      have hpow : (1 : ℝ) ≤ 3 ^ (2 * r) :=
        one_le_pow₀ (by norm_num)
      have hfac : 2 * (((2 * r + 3 : ℕ) : ℝ)) ≤
          2 * (((2 * r + 3 : ℕ) : ℝ)) * 3 ^ (2 * r) := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hpow)]
      exact mul_le_mul_of_nonneg_right hfac
        (mul_nonneg (pow_nonneg (by linarith) _) hz)

/-- The same coefficient also absorbs the extra factor two introduced when a
real complete-block bound is rounded up to a natural-number bound.  The
slack is `3^(2r) ≥ 2` for every positive depth. -/
theorem fixedDepthBlockDiscrepancy_double_scaled_le
    {p r : ℕ} (hp : 0 < p) (hr : 1 ≤ r) :
    (4 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp)
  have hsqrt := sqrt_prime_pow_div p r hp hr
  have hz : 0 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hpR.le _
  have hC : 0 ≤ (((2 * r + 3 : ℕ) : ℝ)) := by positivity
  calc
    (4 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p =
        4 * (Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) /
          (p : ℝ) ^ (r + 1)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      rw [fixedDepthBlockDiscrepancy]
      ring
    _ = 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by rw [hsqrt]
    _ ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (3 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      gcongr
      norm_num
    _ = 4 * (((2 * r + 3 : ℕ) : ℝ)) *
          ((3 + Real.log p) ^ (2 * r + 1) *
            (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
      rw [fixedDepthFourierErrorConstant, fixedDepthFourierWeight]
      have hpow : (2 : ℝ) ≤ 3 ^ (2 * r) := by
        calc
          (2 : ℝ) ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (2 * r) := by
            exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hfac : 4 * (((2 * r + 3 : ℕ) : ℝ)) ≤
          2 * (((2 * r + 3 : ℕ) : ℝ)) * 3 ^ (2 * r) := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hpow)]
      exact mul_le_mul_of_nonneg_right hfac
        (mul_nonneg (pow_nonneg (by linarith) _) hz)

/-- Auditable normalized bridge for all complete blocks of one prime. -/
theorem fixedDepthCompleteBlocks_normalized_discrepancy_le
    {X p r : ℕ} (hp : 0 < p) (hX : 0 < X) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
        fixedDepthBlockDiscrepancy r p) / (X : ℝ) ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hD := fixedDepthBlockDiscrepancy_nonneg r p
  calc
    ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          fixedDepthBlockDiscrepancy r p) / (X : ℝ) =
        ((((X / p + 1) / p ^ r : ℕ) : ℝ) / (X : ℝ)) *
          fixedDepthBlockDiscrepancy r p := by ring
    _ ≤ (2 / (p : ℝ) ^ (r + 1)) *
          fixedDepthBlockDiscrepancy r p :=
      mul_le_mul_of_nonneg_right
        (fixedDepthBlockCount_normalized_le hp hX hr hband) hD
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p :=
      fixedDepthBlockDiscrepancy_scaled_le hp hr

/-- Normalized complete-block discrepancy after the one-time ceiling loss in
`card_filter_range_cast_le_completeBlocks_add_terminal`. -/
theorem two_mul_fixedDepthCompleteBlocks_normalized_discrepancy_le
    {X p r : ℕ} (hp : 0 < p) (hX : 0 < X) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    2 * (((((X / p + 1) / p ^ r : ℕ) : ℝ) *
        fixedDepthBlockDiscrepancy r p) / (X : ℝ)) ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hD := fixedDepthBlockDiscrepancy_nonneg r p
  calc
    2 * (((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          fixedDepthBlockDiscrepancy r p) / (X : ℝ)) =
        (2 * ((((X / p + 1) / p ^ r : ℕ) : ℝ) / (X : ℝ))) *
          fixedDepthBlockDiscrepancy r p := by ring
    _ ≤ (4 / (p : ℝ) ^ (r + 1)) *
          fixedDepthBlockDiscrepancy r p := by
      apply mul_le_mul_of_nonneg_right _ hD
      have htwo := mul_le_mul_of_nonneg_left
        (fixedDepthBlockCount_normalized_le hp hX hr hband)
        (by norm_num : (0 : ℝ) ≤ 2)
      convert htwo using 1 <;> ring
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p :=
      fixedDepthBlockDiscrepancy_double_scaled_le hp hr

lemma eventually_three_add_log_pow_le_rpow (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (3 + Real.log x) ^ K ≤ x ^ (1 / 4 : ℝ) := by
  let A : ℝ := (2 : ℝ) ^ K
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (K : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).bound (inv_pos.mpr hA)
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 3,
      eventually_gt_atTop (0 : ℝ)] with x hx hlog hx0
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hnormlog : ‖Real.log x ^ (K : ℝ)‖ = Real.log x ^ K := by
    rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hlog0 K)]
  have hnormx : ‖x ^ (1 / 4 : ℝ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  rw [hnormlog, hnormx] at hx
  have hscaled : A * Real.log x ^ K ≤ x ^ (1 / 4 : ℝ) := by
    calc
      A * Real.log x ^ K ≤ A * (A⁻¹ * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx hA.le
      _ = x ^ (1 / 4 : ℝ) := by field_simp
  calc
    (3 + Real.log x) ^ K ≤ (2 * Real.log x) ^ K := by
      gcongr
      linarith
    _ = A * Real.log x ^ K := by rw [mul_pow]
    _ ≤ x ^ (1 / 4 : ℝ) := hscaled

/-- The logarithmic Fourier weight is eventually dominated by the summable
`p^(-5/4)` sequence. -/
theorem eventually_fixedDepthFourierWeight_le (r : ℕ) :
    ∀ᶠ p : ℕ in atTop,
      fixedDepthFourierWeight r p ≤ (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have h := tendsto_natCast_atTop_atTop.eventually
    (eventually_three_add_log_pow_le_rpow (2 * r + 1))
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with p hp hp0
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [fixedDepthFourierWeight]
  calc
    (3 + Real.log ↑p) ^ (2 * r + 1) * ↑p ^ (-(3 / 2 : ℝ)) ≤
        ↑p ^ (1 / 4 : ℝ) * ↑p ^ (-(3 / 2 : ℝ)) := by
      gcongr
    _ = ↑p ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hpR]
      norm_num

lemma reciprocalFiveQuarter_summable :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
  Real.summable_nat_rpow.mpr (by norm_num)

/-- Tail of the summable `n^(-5/4)` comparison sequence. -/
def reciprocalFiveQuarterTail (L : ℕ) : ℝ :=
  ∑' k : ℕ, ((k + L + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))

theorem tendsto_reciprocalFiveQuarterTail_zero :
    Tendsto reciprocalFiveQuarterTail atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add
    (f := fun n : ℕ ↦ (n : ℝ) ^ (-(5 / 4 : ℝ)))
  have h' := h.comp (tendsto_add_atTop_nat 1)
  simpa only [reciprocalFiveQuarterTail, Nat.add_assoc] using! h'

theorem fixedDepthFourierBandError_nonneg (r X : ℕ) :
    0 ≤ fixedDepthFourierBandError r X := by
  apply Finset.sum_nonneg
  intro p _hp
  unfold fixedDepthFourierWeight
  exact mul_nonneg (pow_nonneg (by positivity) _)
    (Real.rpow_nonneg (Nat.cast_nonneg p) _)

theorem eventually_fixedDepthFourierBandError_le_tail (r : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      fixedDepthFourierBandError r X ≤
        reciprocalFiveQuarterTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by
  have hweight := eventually_fixedDepthFourierWeight_le r
  rw [eventually_atTop] at hweight
  obtain ⟨N, hN⟩ := hweight
  filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop N]
      with X hL
  let L := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let U := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  calc
    fixedDepthFourierBandError r X =
        ∑ p ∈ fixedDepthPrimeSet r X, fixedDepthFourierWeight r p := rfl
    _ ≤ ∑ p ∈ fixedDepthPrimeSet r X,
          (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := hp
      rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp'
      exact hN p (by omega)
    _ ≤ ∑ p ∈ Finset.Ioc L U,
          (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := hp
        rw [fixedDepthPrimeSet, Finset.mem_filter] at hp'
        simpa [L, U] using hp'.1
      · intro p _hp _hnot
        exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    _ ≤ ∑' k : ℕ,
          ((k + L + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) :=
      sum_Ioc_le_tail
        (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
        reciprocalFiveQuarter_summable L U
    _ = reciprocalFiveQuarterTail
        ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by rfl

/-- Equation (39): the normalized Fourier discrepancy summed over a fixed
depth band tends to zero. -/
theorem tendsto_fixedDepthFourierBandError_zero (r : ℕ) :
    Tendsto (fixedDepthFourierBandError r) atTop (𝓝 0) := by
  have htail := tendsto_reciprocalFiveQuarterTail_zero.comp
    (tendsto_fixedDepthPrimeBandLowerFloor r)
  apply squeeze_zero'
  · exact Eventually.of_forall (fixedDepthFourierBandError_nonneg r)
  · exact eventually_fixedDepthFourierBandError_le_tail r
  · exact htail

theorem tendsto_fixedDepthFourierError_zero (r : ℕ) :
    Tendsto (fixedDepthFourierError r) atTop (𝓝 0) := by
  simpa [fixedDepthFourierError] using!
    (tendsto_fixedDepthFourierBandError_zero r).const_mul
      (fixedDepthFourierErrorConstant r)

/-! ## Terminal blocks and the per-prime `+1` term -/

/-- Natural upper cutoff of the fixed-depth band. -/
def fixedDepthUpperCut (r X : ℕ) : ℕ :=
  ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊

theorem fixedDepthPrimeSet_card_le_upperCut (r X : ℕ) :
    (fixedDepthPrimeSet r X).card ≤ fixedDepthUpperCut r X := by
  calc
    (fixedDepthPrimeSet r X).card ≤
        (Finset.Ioc 0 (fixedDepthUpperCut r X)).card := by
      apply Finset.card_le_card
      intro p hp
      rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_Ioc]
      dsimp [fixedDepthUpperCut]
      omega
    _ = fixedDepthUpperCut r X := by simp

lemma card_filter_prime_Iic (n : ℕ) :
    ((Finset.Iic n).filter Nat.Prime).card = n.primeCounting := by
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp

theorem fixedDepthPrimeSet_card_le_primeCounting (r X : ℕ) :
    (fixedDepthPrimeSet r X).card ≤
      (fixedDepthUpperCut r X).primeCounting := by
  rw [← card_filter_prime_Iic]
  apply Finset.card_le_card
  intro p hp
  rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Finset.mem_filter, Finset.mem_Iic]
  exact ⟨hp.1.2, hp.2⟩

/-- The normalized sum of the terminal `p^r` blocks. -/
def fixedDepthTerminalBlockError (r X : ℕ) : ℝ :=
  (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) / (X : ℝ)

/-- The normalized count of one extra incomplete interval per prime. -/
def fixedDepthUnitError (r X : ℕ) : ℝ :=
  ((fixedDepthPrimeSet r X).card : ℝ) / (X : ℝ)

/-- Chebyshev majorant for the terminal-block error. -/
def fixedDepthTerminalChebyshevMajorant (r X : ℕ) : ℝ :=
  ((fixedDepthUpperCut r X).primeCounting : ℝ) /
    fixedDepthPrimeBandUpper r (X : ℝ)

theorem tendsto_fixedDepthUpper_div_self_zero
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun X : ℕ ↦
      fixedDepthPrimeBandUpper r (X : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  let b : ℝ := 1 - (((r + 1 : ℕ) : ℝ)⁻¹)
  have hb : 0 < b := by
    dsimp [b]
    apply sub_pos.mpr
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast (show 1 < r + 1 by omega)
  have h := (tendsto_rpow_neg_atTop hb).comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  change (X : ℝ) ^ (-b) =
    (X : ℝ) ^ (((r + 1 : ℕ) : ℝ)⁻¹) / X
  calc
    (X : ℝ) ^ (-b) =
        (X : ℝ) ^ ((((r + 1 : ℕ) : ℝ)⁻¹) - 1) := by
      congr 1
      dsimp [b]
      ring
    _ = (X : ℝ) ^ (((r + 1 : ℕ) : ℝ)⁻¹) / X := by
      simpa using
        Real.rpow_sub hXR (((r + 1 : ℕ) : ℝ)⁻¹) 1

theorem fixedDepthUnitError_nonneg (r X : ℕ) :
    0 ≤ fixedDepthUnitError r X := by
  unfold fixedDepthUnitError
  positivity

theorem fixedDepthUnitError_le_upper_div_self
    {r X : ℕ} (hX : 1 ≤ X) :
    fixedDepthUnitError r X ≤
      fixedDepthPrimeBandUpper r (X : ℝ) / (X : ℝ) := by
  have hXR : (0 : ℝ) < X := by positivity
  apply div_le_div_of_nonneg_right _ hXR.le
  calc
    ((fixedDepthPrimeSet r X).card : ℝ) ≤ fixedDepthUpperCut r X := by
      exact_mod_cast fixedDepthPrimeSet_card_le_upperCut r X
    _ ≤ fixedDepthPrimeBandUpper r (X : ℝ) := by
      exact Nat.floor_le (fixedDepthPrimeBandUpper_pos r (by positivity)).le

/-- The per-prime `+1` terms are `o(X)`. -/
theorem tendsto_fixedDepthUnitError_zero
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fixedDepthUnitError r) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (fixedDepthUnitError_nonneg r)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    exact fixedDepthUnitError_le_upper_div_self hX
  · exact tendsto_fixedDepthUpper_div_self_zero r hr

theorem fixedDepthTerminalBlockError_nonneg (r X : ℕ) :
    0 ≤ fixedDepthTerminalBlockError r X := by
  unfold fixedDepthTerminalBlockError
  positivity

/-- Exact finite form of the terminal-block estimate in equation (40). -/
theorem fixedDepthTerminalBlockError_le_Chebyshev
    {r X : ℕ} (hX : 1 ≤ X) :
    fixedDepthTerminalBlockError r X ≤
      fixedDepthTerminalChebyshevMajorant r X := by
  let u := fixedDepthPrimeBandUpper r (X : ℝ)
  let U := fixedDepthUpperCut r X
  have hXR : (0 : ℝ) < X := by positivity
  have hu0 : 0 < u := fixedDepthPrimeBandUpper_pos r hXR
  have hUu : (U : ℝ) ≤ u := by
    exact Nat.floor_le hu0.le
  have hsum :
      (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) ≤
        ((fixedDepthPrimeSet r X).card : ℝ) * u ^ r := by
    calc
      (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) ≤
          ∑ _p ∈ fixedDepthPrimeSet r X, u ^ r := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := hp
        rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp'
        apply pow_le_pow_left₀ (Nat.cast_nonneg p)
        exact (by exact_mod_cast hp'.1.2 : (p : ℝ) ≤ U) |>.trans hUu
      _ = ((fixedDepthPrimeSet r X).card : ℝ) * u ^ r := by simp
  have hcard : ((fixedDepthPrimeSet r X).card : ℝ) ≤
      ((fixedDepthUpperCut r X).primeCounting : ℝ) := by
    exact_mod_cast fixedDepthPrimeSet_card_le_primeCounting r X
  have hsum' :
      (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) ≤
        ((fixedDepthUpperCut r X).primeCounting : ℝ) * u ^ r :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard (pow_nonneg hu0.le r))
  have huPow : u ^ (r + 1) = (X : ℝ) := by
    simpa [u, fixedDepthPrimeBandUpper] using
      (Real.rpow_inv_natCast_pow (x := (X : ℝ)) hXR.le
        (show r + 1 ≠ 0 by omega))
  unfold fixedDepthTerminalBlockError fixedDepthTerminalChebyshevMajorant
  change (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) / (X : ℝ) ≤
    ((fixedDepthUpperCut r X).primeCounting : ℝ) / u
  calc
    (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) / (X : ℝ) ≤
        (((fixedDepthUpperCut r X).primeCounting : ℝ) * u ^ r) /
          (X : ℝ) := div_le_div_of_nonneg_right hsum' hXR.le
    _ = ((fixedDepthUpperCut r X).primeCounting : ℝ) / u := by
      rw [← huPow, pow_succ]
      field_simp

/-- Chebyshev's upper bound implies `π(u)/u → 0` along the fixed-depth
upper cutoff. -/
theorem tendsto_fixedDepthTerminalChebyshevMajorant_zero (r : ℕ) :
    Tendsto (fixedDepthTerminalChebyshevMajorant r) atTop (𝓝 0) := by
  let C : ℝ := Real.log 4 + 1
  have hcheb :=
    Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) one_pos
  have hcheb' :=
    (tendsto_fixedDepthPrimeBandUpper_nat r).eventually hcheb
  have hbound : ∀ᶠ X : ℕ in atTop,
      fixedDepthTerminalChebyshevMajorant r X ≤
        C / Real.log (fixedDepthPrimeBandUpper r (X : ℝ)) := by
    filter_upwards [hcheb',
      (tendsto_fixedDepthPrimeBandUpper_nat r).eventually_gt_atTop 1]
      with X hC hu
    have hu0 : 0 < fixedDepthPrimeBandUpper r (X : ℝ) :=
      zero_lt_one.trans hu
    change ((fixedDepthUpperCut r X).primeCounting : ℝ) /
      fixedDepthPrimeBandUpper r (X : ℝ) ≤ _
    have hC' : ((fixedDepthUpperCut r X).primeCounting : ℝ) ≤
        C * fixedDepthPrimeBandUpper r (X : ℝ) /
          Real.log (fixedDepthPrimeBandUpper r (X : ℝ)) := by
      simpa [fixedDepthUpperCut, C] using hC
    calc
      ((fixedDepthUpperCut r X).primeCounting : ℝ) /
          fixedDepthPrimeBandUpper r (X : ℝ) ≤
        (C * fixedDepthPrimeBandUpper r (X : ℝ) /
          Real.log (fixedDepthPrimeBandUpper r (X : ℝ))) /
          fixedDepthPrimeBandUpper r (X : ℝ) :=
        div_le_div_of_nonneg_right hC' hu0.le
      _ = C / Real.log (fixedDepthPrimeBandUpper r (X : ℝ)) := by
        field_simp
  have hright : Tendsto (fun X : ℕ ↦
      C / Real.log (fixedDepthPrimeBandUpper r (X : ℝ)))
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((Real.tendsto_log_atTop.comp
        (tendsto_fixedDepthPrimeBandUpper_nat r)).inv_tendsto_atTop.const_mul C)
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ by
      unfold fixedDepthTerminalChebyshevMajorant
      exact div_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  · exact hbound
  · exact hright

/-- Equation (40): terminal `p^r` blocks contribute `o(X)`. -/
theorem tendsto_fixedDepthTerminalBlockError_zero (r : ℕ) :
    Tendsto (fixedDepthTerminalBlockError r) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (fixedDepthTerminalBlockError_nonneg r)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    exact fixedDepthTerminalBlockError_le_Chebyshev hX
  · exact tendsto_fixedDepthTerminalChebyshevMajorant_zero r

/-! ## Combined analytic majorant and comparison interface -/

/-- Concrete normalized fixed-depth majorant corresponding to equation (38):
the relaxed box mass, the Fourier discrepancy, the terminal `p^r` blocks,
and one incomplete interval per prime. -/
def fixedDepthAnalyticMajorant (r X : ℕ) : ℝ :=
  (∑ p ∈ fixedDepthPrimeSet r X,
      relaxedDigitDensity r p / (p : ℝ)) +
    fixedDepthFourierError r X +
    fixedDepthTerminalBlockError r X +
    fixedDepthUnitError r X

/-- Equations (37)--(42): the complete fixed-depth analytic majorant tends
to `4⁻ʳ log ((r+2)/(r+1))`. -/
theorem tendsto_fixedDepthAnalyticMajorant
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fixedDepthAnalyticMajorant r) atTop
      (𝓝 (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r)) := by
  have h := (((tendsto_fixedDepthRelaxedPrimeMass r).add
    (tendsto_fixedDepthFourierError_zero r)).add
      (tendsto_fixedDepthTerminalBlockError_zero r)).add
        (tendsto_fixedDepthUnitError_zero r hr)
  simpa only [fixedDepthAnalyticMajorant, add_zero] using! h

/-- Quantified limsup form: any normalized count eventually dominated by the
concrete analytic majorant is eventually below the limiting constant plus an
arbitrary positive epsilon. -/
theorem eventually_le_limit_add_of_le_fixedDepthAnalyticMajorant
    {r : ℕ} (hr : 1 ≤ r) {f : ℕ → ℝ}
    (hdom : ∀ᶠ X : ℕ in atTop, f X ≤ fixedDepthAnalyticMajorant r X)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      f X ≤ fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r + ε := by
  have hupper := (tendsto_order.1
    (tendsto_fixedDepthAnalyticMajorant r hr)).2
      (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r + ε)
      (lt_add_of_pos_right _ hε)
  filter_upwards [hdom, hupper] with X hf hmajor
  exact hf.trans hmajor.le

/-- Literal limsup consumer.  The only non-analytic inputs are eventual
domination by the concrete majorant and the standard lower coboundedness of
the counted sequence (automatic for nonnegative normalized counts). -/
theorem limsup_le_of_le_fixedDepthAnalyticMajorant
    {r : ℕ} (hr : 1 ≤ r) {f : ℕ → ℝ}
    (hdom : ∀ᶠ X : ℕ in atTop, f X ≤ fixedDepthAnalyticMajorant r X)
    (hfCob : IsCoboundedUnder (· ≤ ·) atTop f) :
    limsup f atTop ≤
      fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r := by
  have hlim := tendsto_fixedDepthAnalyticMajorant r hr
  calc
    limsup f atTop ≤ limsup (fixedDepthAnalyticMajorant r) atTop :=
      limsup_le_limsup hdom hfCob hlim.isBoundedUnder_le
    _ = fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r :=
      hlim.limsup_eq

end

end FixedDepthDensity
end Erdos730

end Campaign180File36

/- Source module: ErdosProblems.Erdos730.LimsupSeries -/
section Campaign180File37
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Finite-depth limsup assembly for Erdős 730

The small-prime proof first fixes finitely many digit depths and then sends
the depth cutoff to infinity.  This file isolates that purely topological
passage.  It contains no number-theoretic input.
-/

open Filter
open scoped Topology

namespace Erdos730.LimsupSeries

variable {ι κ : Type*} {f : Filter κ} [f.NeBot]

omit [f.NeBot] in
theorem isBoundedUnder_le_finset_sum
    (s : Finset ι) (u : ι → κ → ℝ)
    (hbdd : ∀ i ∈ s, IsBoundedUnder (· ≤ ·) f (u i)) :
    IsBoundedUnder (· ≤ ·) f (fun x ↦ ∑ i ∈ s, u i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds (x := (0 : ℝ))).isBoundedUnder_le
  | @insert i s hi ih =>
      have hiBdd := hbdd i (Finset.mem_insert_self i s)
      have hsBdd := ih fun j hj ↦ hbdd j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert, hi] using! isBoundedUnder_le_add hiBdd hsBdd

theorem limsup_finset_sum_le_sum_limsup
    (s : Finset ι) (u : ι → κ → ℝ)
    (hnonneg : ∀ i ∈ s, ∀ x, 0 ≤ u i x)
    (hbdd : ∀ i ∈ s, IsBoundedUnder (· ≤ ·) f (u i)) :
    limsup (fun x ↦ ∑ i ∈ s, u i x) f ≤
      ∑ i ∈ s, limsup (u i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiNonneg : ∀ x, 0 ≤ u i x :=
        hnonneg i (Finset.mem_insert_self i s)
      have hiLower : IsBoundedUnder (· ≥ ·) f (u i) := by
        exact isBoundedUnder_of ⟨0, hiNonneg⟩
      have hiBdd := hbdd i (Finset.mem_insert_self i s)
      let rest : κ → ℝ := fun x ↦ ∑ j ∈ s, u j x
      have hrestNonneg : ∀ x, 0 ≤ rest x := by
        intro x
        dsimp only [rest]
        exact Finset.sum_nonneg fun j hj ↦
          hnonneg j (Finset.mem_insert_of_mem hj) x
      have hrestCob : IsCoboundedUnder (· ≤ ·) f rest :=
        isCoboundedUnder_le_of_le f hrestNonneg
      have hrestBdd : IsBoundedUnder (· ≤ ·) f rest := by
        dsimp only [rest]
        exact isBoundedUnder_le_finset_sum s u fun j hj ↦
          hbdd j (Finset.mem_insert_of_mem hj)
      have hadd := limsup_add_le (f := f) (u := u i) (v := rest)
        (h₁ := hiLower) (h₂ := hiBdd)
        (h₃ := hrestCob) (h₄ := hrestBdd)
      have hrest := ih
        (fun j hj ↦ hnonneg j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hbdd j (Finset.mem_insert_of_mem hj))
      have hrest' : limsup rest f ≤
          ∑ j ∈ s, limsup (u j) f := by
        simpa only [rest] using hrest
      rw [Finset.sum_insert hi]
      calc
        limsup (fun x ↦ ∑ j ∈ insert i s, u j x) f =
            limsup (u i + rest) f := by
          apply limsup_congr
          exact Eventually.of_forall fun x ↦ by
            simp [rest, hi]
        _ ≤ limsup (u i) f + limsup rest f := hadd
        _ ≤ limsup (u i) f + ∑ j ∈ s, limsup (u j) f := by
          exact add_le_add le_rfl hrest'

variable {term : ℕ → ℝ} {total : κ → ℝ} {band : ℕ → κ → ℝ}
  {tail : ℕ → κ → ℝ}

/-- A finite-depth decomposition with a uniformly vanishing tail turns the
fixed-depth limsup bounds into the corresponding infinite-series bound. -/
theorem limsup_le_tsum_of_finite_depth_and_tail
    (htermNonneg : ∀ r, 0 ≤ term r)
    (htermSum : Summable term)
    (htotalNonneg : ∀ x, 0 ≤ total x)
    (hbandNonneg : ∀ r x, 0 ≤ band r x)
    (hbandBdd : ∀ r, IsBoundedUnder (· ≤ ·) f (band r))
    (hbandLimsup : ∀ r, limsup (band r) f ≤ term r)
    (htailNonneg : ∀ R x, 0 ≤ tail R x)
    (htailBdd : ∀ R, IsBoundedUnder (· ≤ ·) f (tail R))
    (epsilon : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (htailLimsup : ∀ R, limsup (tail R) f ≤ epsilon R)
    (hdecomp : ∀ R, total ≤ᶠ[f]
      fun x ↦ (∑ r ∈ Finset.range R, band r x) + tail R x) :
    limsup total f ≤ ∑' r, term r := by
  have htotalCob : IsCoboundedUnder (· ≤ ·) f total :=
    isCoboundedUnder_le_of_le f htotalNonneg
  have hboundForall : ∀ R,
      limsup total f ≤ (∑ r ∈ Finset.range R, term r) + epsilon R := by
    intro R
    let partialSum : κ → ℝ := fun x ↦ ∑ r ∈ Finset.range R, band r x
    have hpartialBdd : IsBoundedUnder (· ≤ ·) f partialSum := by
      dsimp only [partialSum]
      exact isBoundedUnder_le_finset_sum (Finset.range R) band
        (fun r _ ↦ hbandBdd r)
    have hpartialLower : IsBoundedUnder (· ≥ ·) f partialSum := by
      exact isBoundedUnder_of ⟨0, fun x ↦ by
        dsimp only [partialSum]
        exact Finset.sum_nonneg fun r _ ↦ hbandNonneg r x⟩
    have htailCob : IsCoboundedUnder (· ≤ ·) f (tail R) :=
      isCoboundedUnder_le_of_le f (htailNonneg R)
    have hrhsBdd : IsBoundedUnder (· ≤ ·) f (partialSum + tail R) :=
      isBoundedUnder_le_add hpartialBdd (htailBdd R)
    have hmono : limsup total f ≤ limsup (partialSum + tail R) f := by
      apply limsup_le_limsup (hdecomp R) htotalCob hrhsBdd
    have hadd : limsup (partialSum + tail R) f ≤
        limsup partialSum f + limsup (tail R) f :=
      limsup_add_le (f := f) (u := partialSum) (v := tail R)
        (h₁ := hpartialLower) (h₂ := hpartialBdd)
        (h₃ := htailCob) (h₄ := htailBdd R)
    have hpartial : limsup partialSum f ≤
        ∑ r ∈ Finset.range R, limsup (band r) f := by
      dsimp only [partialSum]
      exact limsup_finset_sum_le_sum_limsup (Finset.range R) band
        (fun r _ ↦ hbandNonneg r) (fun r _ ↦ hbandBdd r)
    calc
      limsup total f ≤ limsup (partialSum + tail R) f := hmono
      _ ≤ limsup partialSum f + limsup (tail R) f := hadd
      _ ≤ (∑ r ∈ Finset.range R, limsup (band r) f) +
          limsup (tail R) f := add_le_add hpartial le_rfl
      _ ≤ (∑ r ∈ Finset.range R, term r) + epsilon R := by
        exact add_le_add
          (Finset.sum_le_sum fun r _ ↦ hbandLimsup r)
          (htailLimsup R)
  have hpartialLe (R : ℕ) :
      (∑ r ∈ Finset.range R, term r) ≤ ∑' r, term r := by
    exact htermSum.sum_le_tsum (Finset.range R) fun r _ ↦ htermNonneg r
  have heventual : ∀ᶠ R : ℕ in atTop,
      limsup total f ≤ (∑' r, term r) + epsilon R :=
    Eventually.of_forall fun R ↦
      (hboundForall R).trans
        (add_le_add (hpartialLe R) le_rfl)
  have hlimit : Tendsto (fun R : ℕ ↦ (∑' r, term r) + epsilon R)
      atTop (𝓝 (∑' r, term r)) := by
    have hconst : Tendsto (fun _ : ℕ ↦ ∑' r, term r) atTop
        (𝓝 (∑' r, term r)) := tendsto_const_nhds
    simpa only [zero_add, add_zero] using hconst.add hepsilon
  exact ge_of_tendsto hlimit heventual


end Erdos730.LimsupSeries

end Campaign180File37

/- Source module: ErdosProblems.Erdos730.LowerHalfFourier -/
section Campaign180File38
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: the concrete lower-half box on the Fourier surface

`Erdos730DigitBoxes` constructs the permitted residues from fixed-length
base-`p` digit lists, while `Erdos730FixedDepthFourier` factors Fourier
coefficients over dependent digit tuples.  This file proves that these are
literally the same finite set and transfers the sharp interval-box `L¹`
estimate to the concrete lower-half residue box used by the event ledger.
-/

namespace Erdos730.LowerHalfFourier

open DigitBoxes FixedDepthFourier
open scoped ZMod

noncomputable section

/-- Every coordinate uses the consecutive permitted interval
`{0, ..., (p+1)/2-1}`. -/
def lowerHalfDigitIntervals (p d : ℕ) : Fin d → Finset ℕ :=
  fun _ ↦ Finset.range (halfDigitCount p)

/-- Natural base-`p` value of a dependent tuple of permitted digits. -/
def lowerHalfTupleValue {p d : ℕ}
    (x : DigitTuple (lowerHalfDigitIntervals p d)) : ℕ :=
  Nat.ofDigits p (List.ofFn fun i : Fin d ↦ (x i : ℕ))

/-- The tuple presentation of the permitted residue box. -/
def lowerHalfTupleResidues (p d : ℕ) : Finset (ZMod (p ^ d)) :=
  (Finset.univ : Finset (DigitTuple (lowerHalfDigitIntervals p d))).image
    fun x ↦ (lowerHalfTupleValue x : ZMod (p ^ d))

theorem lowerHalfTuple_list_mem_fixedLengthDigits
    {p d : ℕ} (hp : 3 ≤ p)
    (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    List.ofFn (fun i : Fin d ↦ (x i : ℕ)) ∈
      List.fixedLengthDigits (one_lt_halfDigitCount hp) d := by
  rw [List.mem_fixedLengthDigits_iff (one_lt_halfDigitCount hp)]
  refine ⟨List.length_ofFn, ?_⟩
  intro a ha
  rw [List.mem_ofFn'] at ha
  rcases ha with ⟨i, rfl⟩
  exact Finset.mem_range.mp (x i).property

theorem lowerHalfTupleValue_eq_ofDigits
    {p d : ℕ} (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    lowerHalfTupleValue x =
      Nat.ofDigits p (List.ofFn fun i : Fin d ↦ (x i : ℕ)) := by
  rfl

theorem lowerHalfTupleValue_lt_pow
    {p d : ℕ} (hp : 3 ≤ p)
    (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    lowerHalfTupleValue x < p ^ d := by
  rw [lowerHalfTupleValue_eq_ofDigits]
  have hmem := lowerHalfTuple_list_mem_fixedLengthDigits hp x
  have hdigits := (List.mem_fixedLengthDigits_iff
    (one_lt_halfDigitCount hp)).mp hmem
  have hlt := Nat.ofDigits_lt_base_pow_length (by omega) fun a ha ↦
    (hdigits.2 a ha).trans_le (halfDigitCount_le (by omega))
  simpa [lowerHalfTupleValue, hdigits.1] using hlt

theorem lowerHalfTupleResidues_subset (p d : ℕ) (hp : 3 ≤ p) :
    lowerHalfTupleResidues p d ⊆ lowerHalfResidues p d := by
  intro z hz
  rw [lowerHalfTupleResidues, Finset.mem_image] at hz
  rcases hz with ⟨x, _hx, rfl⟩
  rw [lowerHalfResidues, Finset.mem_image]
  refine ⟨lowerHalfTupleValue x, ?_, rfl⟩
  rw [lowerHalfResiduesNat, dif_pos (one_lt_halfDigitCount hp),
    Finset.mem_image]
  refine ⟨List.ofFn (fun i : Fin d ↦ (x i : ℕ)),
    lowerHalfTuple_list_mem_fixedLengthDigits hp x, ?_⟩
  exact (lowerHalfTupleValue_eq_ofDigits x).symm

theorem lowerHalfTupleResidueMap_injective
    {p d : ℕ} (hp : 3 ≤ p) :
    Function.Injective
      (fun x : DigitTuple (lowerHalfDigitIntervals p d) ↦
        (lowerHalfTupleValue x : ZMod (p ^ d))) := by
  intro x y hxy
  have hxlt := lowerHalfTupleValue_lt_pow hp x
  have hylt := lowerHalfTupleValue_lt_pow hp y
  have hval := congrArg ZMod.val hxy
  have hnat : lowerHalfTupleValue x = lowerHalfTupleValue y := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt] using hval
  have hlist : List.ofFn (fun i : Fin d ↦ (x i : ℕ)) =
      List.ofFn (fun i : Fin d ↦ (y i : ℕ)) := by
    apply Nat.ofDigits_inj_of_len_eq (by omega : 1 < p)
      (by simp)
    · intro a ha
      have hmem := lowerHalfTuple_list_mem_fixedLengthDigits hp x
      exact ((List.mem_fixedLengthDigits_iff
        (one_lt_halfDigitCount hp)).mp hmem).2 a ha |>.trans_le
          (halfDigitCount_le (by omega))
    · intro a ha
      have hmem := lowerHalfTuple_list_mem_fixedLengthDigits hp y
      exact ((List.mem_fixedLengthDigits_iff
        (one_lt_halfDigitCount hp)).mp hmem).2 a ha |>.trans_le
          (halfDigitCount_le (by omega))
    · simpa only [← lowerHalfTupleValue_eq_ofDigits] using hnat
  have hfun : (fun i : Fin d ↦ (x i : ℕ)) =
      fun i : Fin d ↦ (y i : ℕ) := List.ofFn_injective hlist
  funext i
  exact Subtype.ext (congrFun hfun i)

theorem lowerHalfTupleResidues_card
    {p d : ℕ} (hp : 3 ≤ p) :
    (lowerHalfTupleResidues p d).card = halfDigitCount p ^ d := by
  rw [lowerHalfTupleResidues,
    Finset.card_image_iff.mpr (lowerHalfTupleResidueMap_injective hp).injOn,
    Finset.card_univ]
  change Fintype.card
      ((i : Fin d) → (lowerHalfDigitIntervals p d i)) =
    halfDigitCount p ^ d
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe]
  simp [lowerHalfDigitIntervals]

/-- The list-based and tuple-based presentations are exactly equal. -/
theorem lowerHalfTupleResidues_eq_lowerHalfResidues
    {p d : ℕ} (hp : 3 ≤ p) :
    lowerHalfTupleResidues p d = lowerHalfResidues p d := by
  apply Finset.eq_of_subset_of_card_le (lowerHalfTupleResidues_subset p d hp)
  rw [lowerHalfResidues_card hp, lowerHalfTupleResidues_card hp]

/-! ## Transfer to the tuple Fourier transform -/

theorem lowerHalfDigitIntervals_isInterval
    {p d : ℕ} (hp : 3 ≤ p) :
    IsIntervalDigitBox p (lowerHalfDigitIntervals p d) := by
  intro i
  refine ⟨0, halfDigitCount p, ?_, halfDigitCount_le (by omega)⟩
  change Finset.range (halfDigitCount p) =
    Finset.Ico 0 (0 + halfDigitCount p)
  rw [Nat.zero_add, Finset.range_eq_Ico]

theorem lowerHalfTupleValue_cast_eq_sum
    {p d : ℕ} (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    (lowerHalfTupleValue x : ZMod (p ^ d)) =
      ∑ i : Fin d,
        (((x i : ℕ) * p ^ (i : ℕ) : ℕ) : ZMod (p ^ d)) := by
  simp only [lowerHalfTupleValue, Nat.ofDigits_eq_sum_mapIdx,
    List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 3

theorem dft_finsetIndicator_eq_phaseSum
    {Q : ℕ} [NeZero Q] (A : Finset (ZMod Q)) (h : ZMod Q) :
    ZMod.dft (finsetIndicator A) h =
      ∑ z ∈ A, ZMod.stdAddChar (-(z * h)) := by
  rw [ZMod.dft_apply]
  simp [finsetIndicator]

theorem lowerHalfTuple_phase_eq
    {p d : ℕ} [NeZero (p ^ d)] (h : ZMod (p ^ d))
    (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    ZMod.stdAddChar
        (-((lowerHalfTupleValue x : ZMod (p ^ d)) * h)) =
      ZMod.stdAddChar
        (∑ i : Fin d,
          digitPhase (lowerHalfDigitIntervals p d) h i (x i)) := by
  congr 1
  rw [lowerHalfTupleValue_cast_eq_sum]
  simp only [digitPhase, Nat.cast_mul, Nat.cast_pow]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The DFT of the concrete lower-half indicator is exactly the product
coefficient used by the digitwise Fourier induction. -/
theorem dft_lowerHalfResidues_eq_digitBoxFourierCoeff
    {p d : ℕ} [NeZero (p ^ d)] (hp : 3 ≤ p) (h : ZMod (p ^ d)) :
    ZMod.dft (finsetIndicator (lowerHalfResidues p d)) h =
      digitBoxFourierCoeff (lowerHalfDigitIntervals p d) h := by
  rw [← lowerHalfTupleResidues_eq_lowerHalfResidues hp,
    dft_finsetIndicator_eq_phaseSum, lowerHalfTupleResidues]
  rw [Finset.sum_image (lowerHalfTupleResidueMap_injective hp).injOn]
  simp only [digitBoxFourierCoeff]
  apply Finset.sum_congr rfl
  intro x _hx
  exact lowerHalfTuple_phase_eq h x

/-- Sharp concrete `L¹` estimate for the Fourier transform of the permitted
lower-half digit box. -/
theorem dft_lowerHalfResidues_l1_le
    {p d : ℕ} [NeZero (p ^ d)] (hp : 3 ≤ p) :
    (∑ h : ZMod (p ^ d),
      ‖ZMod.dft (finsetIndicator (lowerHalfResidues p d)) h‖) ≤
      (p : ℝ) ^ d * (3 + Real.log p) ^ d := by
  letI : NeZero p := ⟨by omega⟩
  simp_rw [dft_lowerHalfResidues_eq_digitBoxFourierCoeff hp]
  exact digitBoxFourierCoeff_interval_l1_le (by omega)
    (lowerHalfDigitIntervals p d) (lowerHalfDigitIntervals_isInterval hp)


end

end Erdos730.LowerHalfFourier

end Campaign180File38

/- Source module: ErdosProblems.Erdos730.SmallPrimeDepth -/
section Campaign180File39
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: exact depth partition of the small-prime ledger

For a prime `p ≤ sqrt X`, the paper's unique depth is
`r = floor(log_p X) - 1`; it satisfies
`p^(r+1) ≤ X < p^(r+2)` and `r ≥ 1`.  This file partitions the exact local
small-prime witness finset by that depth and records the corresponding finite
union bound, including the residual depth tail.
-/

namespace Erdos730.SmallPrimeDepth

open BranchEvents RangeAssembly

noncomputable section

/-- The unique digit depth associated with a small prime at height `X`. -/
def smallPrimeDepth (p X : ℕ) : ℕ := Nat.log p X - 1

theorem smallPrimeDepth_spec
    {p X : ℕ} (hp : p.Prime) (hX : 0 < X) (hpSmall : p ≤ Nat.sqrt X) :
    1 ≤ smallPrimeDepth p X ∧
      p ^ (smallPrimeDepth p X + 1) ≤ X ∧
      X < p ^ (smallPrimeDepth p X + 2) := by
  have hp2 : p ^ 2 ≤ X := by
    rw [pow_two]
    exact Nat.le_sqrt.mp hpSmall
  have hlog2 : 2 ≤ Nat.log p X :=
    Nat.le_log_of_pow_le hp.one_lt hp2
  have hpowLow : p ^ Nat.log p X ≤ X :=
    Nat.pow_log_le_self p hX.ne'
  have hpowHigh : X < p ^ (Nat.log p X).succ :=
    Nat.lt_pow_succ_log_self hp.one_lt X
  unfold smallPrimeDepth
  constructor
  · omega
  constructor
  · have hexp : Nat.log p X - 1 + 1 = Nat.log p X := by omega
    rw [hexp]
    exact hpowLow
  · have hexp : Nat.log p X - 1 + 2 = (Nat.log p X).succ := by omega
    rw [hexp]
    exact hpowHigh

theorem smallPrimeDepth_eq_of_power_band
    {p X r : ℕ} (hlow : p ^ (r + 1) ≤ X)
    (hhigh : X < p ^ (r + 2)) :
    smallPrimeDepth p X = r := by
  have hlog : Nat.log p X = r + 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow hlow (by simpa [Nat.add_assoc] using hhigh)
  unfold smallPrimeDepth
  omega

/-- Small-prime witnesses of exact depth `r`. -/
noncomputable def localSmallPrimeDepthWitnessesUpTo (X r : ℕ) :
    Finset LocalBranchWitness :=
  (localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).filter fun w ↦
    smallPrimeDepth (localWitnessPrime w) X = r

/-- Small-prime witnesses whose depth has not yet been included below `R`. -/
noncomputable def localSmallPrimeDepthTailWitnessesUpTo (X R : ℕ) :
    Finset LocalBranchWitness :=
  (localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).filter fun w ↦
    R ≤ smallPrimeDepth (localWitnessPrime w) X

@[simp] theorem mem_localSmallPrimeDepthWitnessesUpTo
    {X r : ℕ} {w : LocalBranchWitness} :
    w ∈ localSmallPrimeDepthWitnessesUpTo X r ↔
      w ∈ localSmallPrimeWitnessesUpTo X (Nat.sqrt X) ∧
        smallPrimeDepth (localWitnessPrime w) X = r := by
  simp [localSmallPrimeDepthWitnessesUpTo]

@[simp] theorem mem_localSmallPrimeDepthTailWitnessesUpTo
    {X R : ℕ} {w : LocalBranchWitness} :
    w ∈ localSmallPrimeDepthTailWitnessesUpTo X R ↔
      w ∈ localSmallPrimeWitnessesUpTo X (Nat.sqrt X) ∧
        R ≤ smallPrimeDepth (localWitnessPrime w) X := by
  simp [localSmallPrimeDepthTailWitnessesUpTo]

/-- Exact finite decomposition into depths below `R` and the remaining tail. -/
theorem localSmallPrimeWitnesses_depth_union_tail (X R : ℕ) :
    localSmallPrimeWitnessesUpTo X (Nat.sqrt X) =
      (Finset.range R).biUnion
          (localSmallPrimeDepthWitnessesUpTo X) ∪
        localSmallPrimeDepthTailWitnessesUpTo X R := by
  classical
  ext w
  constructor
  · intro hw
    by_cases hdepth : smallPrimeDepth (localWitnessPrime w) X < R
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      exact ⟨smallPrimeDepth (localWitnessPrime w) X,
        Finset.mem_range.mpr hdepth,
        mem_localSmallPrimeDepthWitnessesUpTo.mpr ⟨hw, rfl⟩⟩
    · apply Finset.mem_union_right
      exact mem_localSmallPrimeDepthTailWitnessesUpTo.mpr
        ⟨hw, Nat.le_of_not_gt hdepth⟩
  · intro hw
    rcases Finset.mem_union.mp hw with hfinite | htail
    · rcases Finset.mem_biUnion.mp hfinite with ⟨r, _hr, hw⟩
      exact (mem_localSmallPrimeDepthWitnessesUpTo.mp hw).1
    · exact (mem_localSmallPrimeDepthTailWitnessesUpTo.mp htail).1

/-- Cardinal form of the depth decomposition.  Equality is unnecessary for
the density argument; this union bound deliberately avoids relying on
pairwise-disjoint simplification. -/
theorem localSmallPrimeWitnesses_card_le_depth_sum_add_tail (X R : ℕ) :
    (localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card ≤
      (∑ r ∈ Finset.range R,
        (localSmallPrimeDepthWitnessesUpTo X r).card) +
        (localSmallPrimeDepthTailWitnessesUpTo X R).card := by
  rw [localSmallPrimeWitnesses_depth_union_tail X R]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_biUnion_le le_rfl)

/-- Normalized exact-depth witness count. -/
def normalizedSmallPrimeDepthWitnessCount (r X : ℕ) : ℝ :=
  ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ) / (X : ℝ)

/-- Normalized residual depth-tail witness count. -/
def normalizedSmallPrimeDepthTailWitnessCount (R X : ℕ) : ℝ :=
  ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) / (X : ℝ)

theorem normalizedSmallPrimeDepthWitnessCount_nonneg (r X : ℕ) :
    0 ≤ normalizedSmallPrimeDepthWitnessCount r X := by
  unfold normalizedSmallPrimeDepthWitnessCount
  positivity

theorem normalizedSmallPrimeDepthTailWitnessCount_nonneg (R X : ℕ) :
    0 ≤ normalizedSmallPrimeDepthTailWitnessCount R X := by
  unfold normalizedSmallPrimeDepthTailWitnessCount
  positivity

/-- Pointwise normalized decomposition in exactly the form consumed by the
generic finite-depth limsup theorem. -/
theorem normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail (X R : ℕ) :
    normalizedSmallPrimeWitnessCount X ≤
      (∑ r ∈ Finset.range R, normalizedSmallPrimeDepthWitnessCount r X) +
        normalizedSmallPrimeDepthTailWitnessCount R X := by
  have hcard := localSmallPrimeWitnesses_card_le_depth_sum_add_tail X R
  have hcast :
      ((localSmallPrimeWitnessesUpTo X (Nat.sqrt X)).card : ℝ) ≤
        (∑ r ∈ Finset.range R,
          ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ)) +
          ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) := by
    exact_mod_cast hcard
  unfold normalizedSmallPrimeWitnessCount
    normalizedSmallPrimeDepthWitnessCount
    normalizedSmallPrimeDepthTailWitnessCount
  rw [← Finset.sum_div]
  simpa only [add_div] using
    (div_le_div_of_nonneg_right hcast (Nat.cast_nonneg X))


end

end Erdos730.SmallPrimeDepth

end Campaign180File39

/- Source module: ErdosProblems.Erdos730.SmallPrimeTail -/
section Campaign180File40
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: uniform fixed-depth tail budget

The sharp fixed-depth main term uses `4⁻ʳ`.  Uniformly in the remaining
depths, the complete-block argument uses the coarser ratio `(2/3)ʳ` because
every relevant prime is at least five.  This file proves that the resulting
tail of Mertens main terms vanishes as the retained depth tends to infinity.
-/

open Filter
open scoped Topology

namespace Erdos730.SmallPrimeTail

open Erdos730.FullDensity

noncomputable section

def uniformDepthMainTerm (r : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ r * fixedDepthPrimeBandMainTerm r

def uniformDepthMainTail (R : ℕ) : ℝ :=
  ∑' n : ℕ, uniformDepthMainTerm (n + R)

theorem fixedDepthPrimeBandMainTerm_nonneg (r : ℕ) :
    0 ≤ fixedDepthPrimeBandMainTerm r := by
  unfold fixedDepthPrimeBandMainTerm
  have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  apply Real.log_nonneg
  rw [le_div_iff₀ hden]
  push_cast
  norm_num

theorem fixedDepthPrimeBandMainTerm_le_one (r : ℕ) :
    fixedDepthPrimeBandMainTerm r ≤ 1 := by
  exact (Erdos730.log_density_ratio_le_inv_succ r).trans <| by
    have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
    exact (div_le_one hden).2 (by norm_num)

theorem uniformDepthMainTerm_nonneg (r : ℕ) :
    0 ≤ uniformDepthMainTerm r := by
  exact mul_nonneg (pow_nonneg (by norm_num) r)
    (fixedDepthPrimeBandMainTerm_nonneg r)

theorem uniformDepthMainTerm_le_geometric (r : ℕ) :
    uniformDepthMainTerm r ≤ (2 / 3 : ℝ) ^ r := by
  unfold uniformDepthMainTerm
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (fixedDepthPrimeBandMainTerm_le_one r) (pow_nonneg (by norm_num) r)

theorem uniformDepthMainTerm_summable : Summable uniformDepthMainTerm := by
  exact Summable.of_nonneg_of_le uniformDepthMainTerm_nonneg
    uniformDepthMainTerm_le_geometric
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem uniformDepthMainTail_nonneg (R : ℕ) : 0 ≤ uniformDepthMainTail R := by
  unfold uniformDepthMainTail
  exact tsum_nonneg fun n ↦ uniformDepthMainTerm_nonneg (n + R)

theorem uniformDepthMainTail_le (R : ℕ) :
    uniformDepthMainTail R ≤ 3 * (2 / 3 : ℝ) ^ R := by
  have hgeom : Summable (fun n : ℕ ↦ (2 / 3 : ℝ) ^ (n + R)) := by
    simpa only [pow_add, mul_comm] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)).mul_left ((2 / 3 : ℝ) ^ R)
  have hmain : Summable (fun n : ℕ ↦ uniformDepthMainTerm (n + R)) :=
    hgeom.of_nonneg_of_le
      (fun n ↦ uniformDepthMainTerm_nonneg (n + R))
      (fun n ↦ uniformDepthMainTerm_le_geometric (n + R))
  calc
    uniformDepthMainTail R ≤ ∑' n : ℕ, (2 / 3 : ℝ) ^ (n + R) := by
      unfold uniformDepthMainTail
      exact hmain.tsum_le_tsum
        (fun n ↦ uniformDepthMainTerm_le_geometric (n + R)) hgeom
    _ = 3 * (2 / 3 : ℝ) ^ R := by
      calc
        (∑' n : ℕ, (2 / 3 : ℝ) ^ (n + R)) =
            ∑' n : ℕ, (2 / 3 : ℝ) ^ n * (2 / 3 : ℝ) ^ R := by
          congr 1
          funext n
          rw [pow_add]
        _ = (∑' n : ℕ, (2 / 3 : ℝ) ^ n) * (2 / 3 : ℝ) ^ R :=
          tsum_mul_right
        _ = 3 * (2 / 3 : ℝ) ^ R := by
          rw [tsum_geometric_of_norm_lt_one
            (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)]
          norm_num

theorem uniformDepthMain_sum_Ico_le_tail (R J : ℕ) :
    (∑ r ∈ Finset.Ico R J, uniformDepthMainTerm r) ≤
      uniformDepthMainTail R := by
  have hshift : Summable (fun n : ℕ ↦ uniformDepthMainTerm (n + R)) :=
    uniformDepthMainTerm_summable.comp_injective
      (fun _ _ h ↦ Nat.add_right_cancel h)
  rw [Finset.sum_Ico_eq_sum_range]
  unfold uniformDepthMainTail
  simpa only [add_comm] using
    hshift.sum_le_tsum (Finset.range (J - R))
      (fun n _ ↦ uniformDepthMainTerm_nonneg (n + R))

/-- Equation (46), at the level of the Mertens main terms: the entire
coarsely weighted fixed-depth tail tends to zero. -/
theorem tendsto_uniformDepthMainTail_zero :
    Tendsto uniformDepthMainTail atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall uniformDepthMainTail_nonneg
  · exact Eventually.of_forall uniformDepthMainTail_le
  · simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)).const_mul 3

/-! ## The deepest moving bands -/

/-- Natural version of the moving depth cutoff used in equation (45). -/
def movingDepthLog (X : ℕ) : ℕ := Nat.log 3 (Nat.sqrt X)

/-- Majorant for all depths beyond `movingDepthLog X - 2`. -/
def deepestBandMajorant (X : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ (movingDepthLog X - 1) *
    reciprocalPrimeSum (Nat.sqrt X)

theorem tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨N * N, fun X hX ↦ ?_⟩
  exact Nat.le_sqrt.mpr hX

theorem tendsto_natLog_three_atTop :
    Tendsto (Nat.log 3) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨3 ^ N, fun X hX ↦ ?_⟩
  exact Nat.le_log_of_pow_le (by norm_num) hX

theorem tendsto_movingDepthLog_atTop :
    Tendsto movingDepthLog atTop atTop := by
  exact tendsto_natLog_three_atTop.comp tendsto_natSqrt_atTop

def deepestDepthControl (m : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ (m - 1) *
    (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3)

theorem tendsto_deepestDepthControl_zero :
    Tendsto deepestDepthControl atTop (𝓝 0) := by
  let q : ℝ := 2 / 3
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hpow : Tendsto (fun m : ℕ ↦ q ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hmulpow : Tendsto (fun m : ℕ ↦ (m : ℝ) * q ^ m)
      atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have hinside : Tendsto (fun m : ℕ ↦
      q ^ m * (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3))
      atTop (𝓝 0) := by
    have hsum := hpow.add ((hmulpow.add hpow).const_mul (Real.log 3))
    convert hsum using 1
    · funext m
      push_cast
      ring
    · simp
  have hscaled := hinside.const_mul ((q ^ 1)⁻¹)
  have hscaled' : Tendsto (fun m : ℕ ↦
      (q ^ 1)⁻¹ *
        (q ^ m * (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hscaled
  apply hscaled'.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  unfold deepestDepthControl
  rw [pow_sub₀ q (by norm_num [q]) hm]
  norm_num [q]
  ring

theorem deepestBandMajorant_nonneg (X : ℕ) :
    0 ≤ deepestBandMajorant X := by
  unfold deepestBandMajorant
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (reciprocalPrimeSum_nonneg _)

theorem deepestBandMajorant_le_control
    {X : ℕ} (hX : 9 ≤ X) :
    deepestBandMajorant X ≤ deepestDepthControl (movingDepthLog X) := by
  let N := Nat.sqrt X
  let m := Nat.log 3 N
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    apply Nat.le_sqrt.mpr
    norm_num1
    exact hX
  have hNpos : 0 < N := by omega
  have hm1 : 1 ≤ m := by
    dsimp only [m]
    exact Nat.le_log_of_pow_le (by norm_num) hN3
  have hNpow : N < 3 ^ (m + 1) := by
    dsimp only [m]
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) N
  have hlogN : Real.log N < ((m + 1 : ℕ) : ℝ) * Real.log 3 := by
    have hcast : (N : ℝ) < ((3 ^ (m + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNpow
    have hlog := Real.strictMonoOn_log
      (show (N : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hNpos)
      (show ((3 ^ (m + 1) : ℕ) : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        positivity)
      hcast
    rw [Nat.cast_pow, Real.log_pow] at hlog
    simpa [mul_comm] using hlog
  have hrec : reciprocalPrimeSum N ≤
      1 + ((m + 1 : ℕ) : ℝ) * Real.log 3 :=
    (reciprocalPrimeSum_le_one_add_log N).trans
      (add_le_add le_rfl hlogN.le)
  unfold deepestBandMajorant deepestDepthControl movingDepthLog
  change (2 / 3 : ℝ) ^ (m - 1) * reciprocalPrimeSum N ≤
    (2 / 3 : ℝ) ^ (m - 1) *
      (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3)
  exact mul_le_mul_of_nonneg_left hrec (pow_nonneg (by norm_num) _)

/-- The deepest-band payment in equation (45) is `o(1)`. -/
theorem tendsto_deepestBandMajorant_zero :
    Tendsto deepestBandMajorant atTop (𝓝 0) := by
  have hcontrol : Tendsto
      (fun X ↦ deepestDepthControl (movingDepthLog X)) atTop (𝓝 0) :=
    tendsto_deepestDepthControl_zero.comp tendsto_movingDepthLog_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall deepestBandMajorant_nonneg
  · filter_upwards [eventually_ge_atTop 9] with X hX
    exact deepestBandMajorant_le_control hX
  · exact hcontrol

/-! ## Summed quantitative Mertens error -/

def uniformMertensWeight (r : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ r * ((r + 2 : ℕ) : ℝ)

def uniformMertensWeightSeries : ℝ :=
  ∑' r : ℕ, uniformMertensWeight r

theorem uniformMertensWeight_nonneg (r : ℕ) :
    0 ≤ uniformMertensWeight r := by
  unfold uniformMertensWeight
  positivity

theorem uniformMertensWeight_summable :
    Summable uniformMertensWeight := by
  have hq : ‖(2 / 3 : ℝ)‖ < 1 := by norm_num
  have hlinear : Summable (fun r : ℕ ↦
      (r : ℝ) * (2 / 3 : ℝ) ^ r) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq)
  have hconst : Summable (fun r : ℕ ↦
      2 * (2 / 3 : ℝ) ^ r) :=
    (summable_geometric_of_norm_lt_one hq).mul_left 2
  convert hlinear.add hconst using 1
  funext r
  unfold uniformMertensWeight
  push_cast
  ring

theorem uniformMertensWeightSeries_nonneg :
    0 ≤ uniformMertensWeightSeries := by
  unfold uniformMertensWeightSeries
  exact tsum_nonneg uniformMertensWeight_nonneg

/-- A uniform upper bound for the sum of all quantitative Mertens endpoint
errors in equation (44). -/
def uniformMertensErrorMajorant (X : ℕ) : ℝ :=
  2 * reciprocalPrimeMertensErrorConstant * uniformMertensWeightSeries /
    Real.log (X : ℝ)

theorem tendsto_uniformMertensErrorMajorant_zero :
    Tendsto uniformMertensErrorMajorant atTop (𝓝 0) := by
  have hlogInv : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))⁻¹)
      atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop.comp
      tendsto_natCast_atTop_atTop
  have hscaled := hlogInv.const_mul
    (2 * reciprocalPrimeMertensErrorConstant * uniformMertensWeightSeries)
  simpa only [uniformMertensErrorMajorant, div_eq_mul_inv, mul_zero] using! hscaled

/-- Quantitative equation (44), after multiplying by the uniform geometric
depth weight. -/
theorem weightedFixedDepthReciprocalPrimeBand_le
    (r : ℕ) {X : ℝ} (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X) :
    (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r X ≤
      uniformDepthMainTerm r +
        (2 * reciprocalPrimeMertensErrorConstant / Real.log X) *
          uniformMertensWeight r := by
  have hband := fixedDepthReciprocalPrimeBand_le r hX hlower
  have hq : 0 ≤ (2 / 3 : ℝ) ^ r := pow_nonneg (by norm_num) r
  calc
    (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r X ≤
        (2 / 3 : ℝ) ^ r *
          (fixedDepthPrimeBandMainTerm r +
            2 * reciprocalPrimeMertensErrorConstant *
              (((r + 2 : ℕ) : ℝ)) / Real.log X) :=
      mul_le_mul_of_nonneg_left hband hq
    _ = uniformDepthMainTerm r +
        (2 * reciprocalPrimeMertensErrorConstant / Real.log X) *
          uniformMertensWeight r := by
      unfold uniformDepthMainTerm uniformMertensWeight
      ring

/-- Uniform summed form of equation (44) over any finite collection of
depths whose lower endpoints are at least two. -/
theorem weightedFixedDepthBand_sum_le_main_add_error
    (s : Finset ℕ) {X : ℕ} (hX : 1 < X)
    (hlower : ∀ r ∈ s,
      2 ≤ fixedDepthPrimeBandLower r (X : ℝ)) :
    (∑ r ∈ s,
      (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r (X : ℝ)) ≤
      (∑ r ∈ s, uniformDepthMainTerm r) +
        uniformMertensErrorMajorant X := by
  let coeff : ℝ :=
    2 * reciprocalPrimeMertensErrorConstant / Real.log (X : ℝ)
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcoeff : 0 ≤ coeff := by
    dsimp only [coeff]
    positivity [reciprocalPrimeMertensErrorConstant_pos]
  have hsumWeight :
      (∑ r ∈ s, uniformMertensWeight r) ≤
        uniformMertensWeightSeries := by
    unfold uniformMertensWeightSeries
    exact uniformMertensWeight_summable.sum_le_tsum s
      (fun r _ ↦ uniformMertensWeight_nonneg r)
  calc
    (∑ r ∈ s,
        (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r (X : ℝ)) ≤
        ∑ r ∈ s, (uniformDepthMainTerm r +
          coeff * uniformMertensWeight r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact weightedFixedDepthReciprocalPrimeBand_le r
        (by exact_mod_cast hX) (hlower r hr)
    _ = (∑ r ∈ s, uniformDepthMainTerm r) +
        coeff * ∑ r ∈ s, uniformMertensWeight r := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ r ∈ s, uniformDepthMainTerm r) +
        coeff * uniformMertensWeightSeries := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hsumWeight hcoeff)
    _ = (∑ r ∈ s, uniformDepthMainTerm r) +
        uniformMertensErrorMajorant X := by
      unfold uniformMertensErrorMajorant
      dsimp only [coeff]
      ring


end

end Erdos730.SmallPrimeTail

end Campaign180File40

/- Source module: ErdosProblems.Erdos730.SmallPrimeEvents -/
section Campaign180File41
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: concrete small-prime events

This file connects the exact local-obstruction ledger to the fixed-depth and
uniform-tail estimates in the first-power range `p ≤ sqrt X`.

The finite part is unconditional.  A witnessed tuple is injected into the
key `(branch, prime, parameter)`, and each fixed key is counted by the
root-progression fiber already constructed in `Erdos730HigherPowerEvents`.
At exponent one the generic padded-block estimate gives the uniform bound

`#fiber / X ≤ (3 / p) * ((p+1)/(2p))^r`.

The sharp fixed-depth estimate is kept behind one explicitly local Fourier
interface near the end of the file.  No density statement, target theorem,
or uniformity in the depth is assumed there.
-/

open Filter Finset
open scoped Topology

namespace Erdos730.SmallPrimeEvents

open BranchEvents DensityEvents DigitBoxes FullDensity FullDensityCore
open FiniteBlockCount FixedDepthDensity FixedDepthFourier
open HigherPowerEvents KummerTransition LimsupSeries RangeAssembly
open LowerHalfFourier
open SmallPrimeDepth SmallPrimeTail

noncomputable section

/-! ## A real-valued wrapper around finite complete-block counting -/

/-- A real upper bound for each complete block may be rounded up once.  If
the discrepancy is at least one, that rounding is absorbed by doubling the
discrepancy.  The actual prefix decomposition is the exact natural theorem
in `Erdos730FiniteBlockCount`. -/
theorem card_filter_range_cast_le_completeBlocks_add_terminal
    (N P : ℕ) (accept : ℕ → Prop) [DecidablePred accept]
    (hP : 0 < P) (main D : ℝ) (hmain : 0 ≤ main) (hD : 1 ≤ D)
    (hblock : ∀ k : ℕ,
      (((Finset.range P).filter fun t ↦ accept (t + P * k)).card : ℝ) ≤
        main + D) :
    (((Finset.range N).filter accept).card : ℝ) ≤
      ((N / P : ℕ) : ℝ) * (main + 2 * D) + P := by
  let B : ℕ := ⌈main + D⌉₊
  have hsum0 : 0 ≤ main + D := by linarith
  have hblockNat (k : ℕ) :
      ((Finset.range P).filter fun t ↦ accept (t + P * k)).card ≤ B := by
    have hreal := (hblock k).trans (Nat.le_ceil (main + D))
    exact_mod_cast hreal
  have hnat := card_filter_range_le_completeBlocks_add_terminal
    N P B accept hP hblockNat
  have hB : (B : ℝ) ≤ main + 2 * D := by
    have hceil := (Nat.ceil_lt_add_one hsum0).le
    dsimp only [B]
    linarith
  calc
    (((Finset.range N).filter accept).card : ℝ) ≤
        (((N / P) * B + P : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((N / P : ℕ) : ℝ) * (B : ℝ) + (P : ℝ) := by
      push_cast
      ring
    _ ≤ ((N / P : ℕ) : ℝ) * (main + 2 * D) + P := by
      gcongr

/-- Natural representative of the common quadratic coefficient. -/
def fixedDepthNaturalAlpha : ℕ := 84591927504

theorem fixedDepthNaturalAlpha_intCast :
    (fixedDepthNaturalAlpha : ℤ) = commonQuadraticCoefficient := by
  norm_num [fixedDepthNaturalAlpha, commonQuadraticCoefficient,
    ObstructionMaps.Tz_eq]

/-- All prime divisors of the quadratic coefficient are at most `43`. -/
theorem largePrime_not_dvd_fixedDepthNaturalAlpha
    {p : ℕ} (hp : p.Prime) (hp43 : 43 < p) :
    ¬p ∣ fixedDepthNaturalAlpha := by
  intro h
  have hfac : fixedDepthNaturalAlpha =
      2 ^ 4 * 3 ^ 5 * 7 * 41 ^ 2 * 43 ^ 2 := by
    norm_num [fixedDepthNaturalAlpha]
  rw [hfac] at h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · have hp2 := hp.dvd_of_dvd_pow h
          have := Nat.le_of_dvd (by norm_num : 0 < 2) hp2
          omega
        · have hp3 := hp.dvd_of_dvd_pow h
          have := Nat.le_of_dvd (by norm_num : 0 < 3) hp3
          omega
      · have := Nat.le_of_dvd (by norm_num : 0 < 7) h
        omega
    · have hp41 := hp.dvd_of_dvd_pow h
      have := Nat.le_of_dvd (by norm_num : 0 < 41) hp41
      omega
  · have hp43' := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num : 0 < 43) hp43'
    omega

/-- The standard representative of a unit modulo `p^j` is not divisible by
`p` when `j > 0`. -/
theorem zmod_val_not_dvd_prime_of_isUnit
    {p j : ℕ} [NeZero (p ^ j)] (hp : p.Prime) (hj : 1 ≤ j)
    (z : ZMod (p ^ j)) (hz : IsUnit z) : ¬p ∣ z.val := by
  have hzcast : IsUnit (z.val : ZMod (p ^ j)) := by
    rw [ZMod.natCast_zmod_val]
    exact hz
  have hcop := (ZMod.isUnit_iff_coprime z.val (p ^ j)).mp hzcast
  intro hpval
  have hppow : p ∣ p ^ j := dvd_pow_self p (by omega)
  have hcop' : p.Coprime p :=
    Nat.Coprime.of_dvd_right hppow
      (Nat.Coprime.of_dvd_left hpval hcop)
  exact hp.ne_one ((Nat.coprime_self p).mp hcop')

/-- Natural representative of the linear coefficient in the branch phase. -/
def fixedDepthNaturalBeta (p r : ℕ) (L : Branch) (c₀ : ℕ) : ℕ :=
  ((p : ZMod (p ^ (2 * r))) *
      (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r))) +
    (branchResidualCoefficient L : ZMod (p ^ (2 * r)))).val

/-- Natural representative of the constant coefficient in the branch phase. -/
def fixedDepthNaturalGamma
    (p r : ℕ) (L : Branch) (s c₀ : ℕ) : ℕ :=
  ((branchTestValue L s c₀ : ℕ) : ZMod (p ^ (2 * r))).val

theorem fixedDepthNaturalAlpha_cast
    {p r : ℕ} [NeZero p] :
    (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r))) =
      (branchPadicQuadratic p 1 : ZMod (p ^ (2 * r))) := by
  rw [show (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r))) =
      ((fixedDepthNaturalAlpha : ℤ) : ZMod (p ^ (2 * r))) by
    norm_num]
  rw [fixedDepthNaturalAlpha_intCast]
  simp [branchPadicQuadratic]

theorem fixedDepthNaturalBeta_cast
    {p r : ℕ} [NeZero p] (L : Branch) (c₀ : ℕ) :
    (fixedDepthNaturalBeta p r L c₀ : ZMod (p ^ (2 * r))) =
      (p : ZMod (p ^ (2 * r))) *
          (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r))) +
        (branchResidualCoefficient L : ZMod (p ^ (2 * r))) := by
  exact ZMod.natCast_zmod_val _

theorem fixedDepthNaturalGamma_cast
    {p r : ℕ} [NeZero p] (L : Branch) (s c₀ : ℕ) :
    (fixedDepthNaturalGamma p r L s c₀ : ZMod (p ^ (2 * r))) =
      (branchTestValue L s c₀ : ZMod (p ^ (2 * r))) := by
  exact ZMod.natCast_zmod_val _

/-- The linear coefficient is a unit modulo `p^(2r)`, because its residual
part is a unit and the remaining summand is nilpotent. -/
theorem prime_not_dvd_fixedDepthNaturalBeta
    {L : Branch} {x p a d r c₀ : ℕ}
    (hr : 1 ≤ r) (hlocal : LocalBranchObstruction L x p a d) :
    ¬p ∣ fixedDepthNaturalBeta p r L c₀ := by
  letI : NeZero p := ⟨hlocal.1.ne_zero⟩
  let Q : ℕ := p ^ (2 * r)
  have hunitResidual :
      IsUnit (branchResidualCoefficient L : ZMod Q) := by
    simpa only [Q] using
      (branchResidualCoefficient_isUnit (r := 2 * r) hlocal)
  have hnil : IsNilpotent
      ((p : ZMod Q) * (branchPadicLinear L p 1 c₀ : ZMod Q)) :=
    zmod_primeMultiple_isNilpotent _
  have hunitSum : IsUnit
      ((p : ZMod Q) * (branchPadicLinear L p 1 c₀ : ZMod Q) +
        (branchResidualCoefficient L : ZMod Q)) :=
    hnil.isUnit_add_right_of_commute hunitResidual (Commute.all _ _)
  have hunitBeta :
      IsUnit (fixedDepthNaturalBeta p r L c₀ : ZMod Q) := by
    rw [show
      (fixedDepthNaturalBeta p r L c₀ : ZMod Q) =
        (p : ZMod Q) * (branchPadicLinear L p 1 c₀ : ZMod Q) +
          (branchResidualCoefficient L : ZMod Q) by
      simpa only [Q] using fixedDepthNaturalBeta_cast L c₀]
    exact hunitSum
  have hcop : Nat.Coprime (fixedDepthNaturalBeta p r L c₀) Q :=
    (ZMod.isUnit_iff_coprime _ _).1 hunitBeta
  intro hdiv
  have hpQ : p ∣ Q := by
    dsimp only [Q]
    exact dvd_pow_self p (by omega)
  have hpgcd : p ∣ Nat.gcd (fixedDepthNaturalBeta p r L c₀) Q :=
    Nat.dvd_gcd hdiv hpQ
  rw [hcop.gcd_eq_one] at hpgcd
  exact hlocal.1.ne_one (Nat.dvd_one.mp hpgcd)

/-- Exact conversion of the root-progression phase to the natural
coefficient presentation consumed by the fixed-depth Fourier theorem. -/
theorem padicBranchMap_eq_fixedDepthQuadratic
    {p r : ℕ} [NeZero p] (L : Branch) (s c₀ : ℕ)
    (k : ZMod (p ^ (2 * r))) :
    padicBranchMap (p : ZMod (p ^ (2 * r)))
        (branchPadicQuadratic p 1 : ZMod (p ^ (2 * r)))
        (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r)))
        (branchResidualCoefficient L : ZMod (p ^ (2 * r)))
        (branchTestValue L s c₀ : ZMod (p ^ (2 * r))) k =
      fixedDepthQuadratic
        (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalBeta p r L c₀ : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalGamma p r L s c₀ : ZMod (p ^ (2 * r))) k := by
  rw [fixedDepthNaturalAlpha_cast, fixedDepthNaturalBeta_cast,
    fixedDepthNaturalGamma_cast]
  simp only [padicBranchMap, fixedDepthQuadratic]

/-! ## Exact prime bands and keyed fibers -/

/-- Primes in the exact natural-number depth band at height `X`. -/
def smallPrimeBandPrimes (X r : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt X)).filter fun p ↦
    p.Prime ∧ smallPrimeDepth p X = r

/-- Primes in the residual depth tail at height `X`. -/
def smallPrimeTailPrimes (X R : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt X)).filter fun p ↦
    p.Prime ∧ R ≤ smallPrimeDepth p X

@[simp] theorem mem_smallPrimeBandPrimes {X r p : ℕ} :
    p ∈ smallPrimeBandPrimes X r ↔
      2 ≤ p ∧ p ≤ Nat.sqrt X ∧ p.Prime ∧
        smallPrimeDepth p X = r := by
  simp [smallPrimeBandPrimes, and_assoc]

@[simp] theorem mem_smallPrimeTailPrimes {X R p : ℕ} :
    p ∈ smallPrimeTailPrimes X R ↔
      2 ≤ p ∧ p ≤ Nat.sqrt X ∧ p.Prime ∧
        R ≤ smallPrimeDepth p X := by
  simp [smallPrimeTailPrimes, and_assoc]

/-- A small-prime witness is determined by its branch, prime, and parameter;
the exact cofactor is recovered from the factorization. -/
abbrev SmallPrimeKey := Σ _L : Branch, Σ _p : ℕ, ℕ

def smallPrimeWitnessKey (w : LocalBranchWitness) : SmallPrimeKey :=
  ⟨localWitnessBranch w,
    ⟨localWitnessPrime w, localWitnessParameter w⟩⟩

/-- Keys over an arbitrary finite set of first-power primes. -/
def smallPrimeKeys (X : ℕ) (s : Finset ℕ) : Finset SmallPrimeKey :=
  (Finset.univ : Finset Branch).sigma fun L ↦
    s.sigma fun p ↦ localHigherPowerFiber X L p 1

theorem smallPrimeKeys_card (X : ℕ) (s : Finset ℕ) :
    (smallPrimeKeys X s).card =
      ∑ L : Branch, ∑ p ∈ s, (localHigherPowerFiber X L p 1).card := by
  simp [smallPrimeKeys, Finset.card_sigma]

theorem smallPrimeDepthWitnessKey_mapsTo (X r : ℕ) :
    Set.MapsTo smallPrimeWitnessKey
      (localSmallPrimeDepthWitnessesUpTo X r : Set LocalBranchWitness)
      (smallPrimeKeys X (smallPrimeBandPrimes X r) : Set SmallPrimeKey) := by
  intro w hw
  rcases mem_localSmallPrimeDepthWitnessesUpTo.mp hw with ⟨hsmall, hdepth⟩
  rcases Finset.mem_filter.mp hsmall with ⟨hledger, ha, hpSmall⟩
  have hlocal := mem_localBranchWitnessesUpTo.mp hledger
  have hx : localWitnessParameter w ∈ parameterRange X :=
    (mem_witnessBox.mp hlocal.1).1
  change smallPrimeWitnessKey w ∈
    smallPrimeKeys X (smallPrimeBandPrimes X r)
  rw [smallPrimeKeys]
  simp only [smallPrimeWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · exact mem_smallPrimeBandPrimes.mpr
      ⟨hlocal.2.1.two_le, hpSmall, hlocal.2.1, hdepth⟩
  · exact mem_localHigherPowerFiber.mpr
      ⟨hx, ⟨localWitnessCofactor w, by simpa [ha] using hlocal.2⟩⟩

theorem smallPrimeTailWitnessKey_mapsTo (X R : ℕ) :
    Set.MapsTo smallPrimeWitnessKey
      (localSmallPrimeDepthTailWitnessesUpTo X R : Set LocalBranchWitness)
      (smallPrimeKeys X (smallPrimeTailPrimes X R) : Set SmallPrimeKey) := by
  intro w hw
  rcases mem_localSmallPrimeDepthTailWitnessesUpTo.mp hw with
    ⟨hsmall, hdepth⟩
  rcases Finset.mem_filter.mp hsmall with ⟨hledger, ha, hpSmall⟩
  have hlocal := mem_localBranchWitnessesUpTo.mp hledger
  have hx : localWitnessParameter w ∈ parameterRange X :=
    (mem_witnessBox.mp hlocal.1).1
  change smallPrimeWitnessKey w ∈
    smallPrimeKeys X (smallPrimeTailPrimes X R)
  rw [smallPrimeKeys]
  simp only [smallPrimeWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · exact mem_smallPrimeTailPrimes.mpr
      ⟨hlocal.2.1.two_le, hpSmall, hlocal.2.1, hdepth⟩
  · exact mem_localHigherPowerFiber.mpr
      ⟨hx, ⟨localWitnessCofactor w, by simpa [ha] using hlocal.2⟩⟩

/-- The `(branch, prime, parameter)` key is injective on the exponent-one
ledger.  This is where uniqueness of the exact cofactor is used. -/
theorem smallPrimeWitnessKey_injOn (X : ℕ) :
    Set.InjOn smallPrimeWitnessKey
      (localSmallPrimeWitnessesUpTo X (Nat.sqrt X) :
        Set LocalBranchWitness) := by
  rintro ⟨L, x, p, a, d⟩ hw ⟨K, y, q, b, e⟩ hv hkey
  have hL : L = K := congrArg (fun z : SmallPrimeKey ↦ z.1) hkey
  have hpq : p = q := congrArg (fun z : SmallPrimeKey ↦ z.2.1) hkey
  have hxy : x = y := congrArg (fun z : SmallPrimeKey ↦ z.2.2) hkey
  subst K
  subst q
  subst y
  have hwa := (Finset.mem_filter.mp hw).2.1
  have hvb := (Finset.mem_filter.mp hv).2.1
  change a = 1 at hwa
  change b = 1 at hvb
  subst a
  subst b
  have hwd := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.2.2.1.2.1
  have hve := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hv).1).2.2.2.1.2.1
  change branchValue L x = p ^ 1 * d at hwd
  change branchValue L x = p ^ 1 * e at hve
  have hp : 0 < p := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.1.pos
  have hde : d = e := by
    apply Nat.mul_left_cancel hp
    simpa using hwd.symm.trans hve
  subst e
  rfl

theorem localSmallPrimeDepthWitnesses_card_le_keys (X r : ℕ) :
    (localSmallPrimeDepthWitnessesUpTo X r).card ≤
      (smallPrimeKeys X (smallPrimeBandPrimes X r)).card := by
  apply Finset.card_le_card_of_injOn smallPrimeWitnessKey
      (smallPrimeDepthWitnessKey_mapsTo X r)
  exact smallPrimeWitnessKey_injOn X |>.mono fun _ hw ↦
    (mem_localSmallPrimeDepthWitnessesUpTo.mp hw).1

theorem localSmallPrimeDepthTailWitnesses_card_le_keys (X R : ℕ) :
    (localSmallPrimeDepthTailWitnessesUpTo X R).card ≤
      (smallPrimeKeys X (smallPrimeTailPrimes X R)).card := by
  apply Finset.card_le_card_of_injOn smallPrimeWitnessKey
      (smallPrimeTailWitnessKey_mapsTo X R)
  exact smallPrimeWitnessKey_injOn X |>.mono fun _ hw ↦
    (mem_localSmallPrimeDepthTailWitnessesUpTo.mp hw).1

/-- Depth zero is absent from the exact small-prime ledger. -/
theorem localSmallPrimeDepthWitnesses_zero_eq_empty (X : ℕ) :
    localSmallPrimeDepthWitnessesUpTo X 0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rcases mem_localSmallPrimeDepthWitnessesUpTo.mp hw with
    ⟨hsmall, hdepth⟩
  rcases Finset.mem_filter.mp hsmall with ⟨hlocal, _ha, hpSmall⟩
  have hlocal' := mem_localBranchWitnessesUpTo.mp hlocal
  have hX : 0 < X := by
    have hx := mem_parameterRange.mp (mem_witnessBox.mp hlocal'.1).1
    omega
  have hdepthPos :=
    (smallPrimeDepth_spec hlocal'.2.1 hX hpSmall).1
  omega

@[simp] theorem normalizedSmallPrimeDepthWitnessCount_zero (X : ℕ) :
    normalizedSmallPrimeDepthWitnessCount 0 X = 0 := by
  simp [normalizedSmallPrimeDepthWitnessCount,
    localSmallPrimeDepthWitnesses_zero_eq_empty]

/-! ## Uniform complete-block estimate for one fiber -/

theorem higherPowerDepth_one_eq_smallPrimeDepth (p X : ℕ) :
    higherPowerDepth p 1 X = smallPrimeDepth p X := by
  simp [higherPowerDepth, smallPrimeDepth, Nat.log_div_base]

theorem higherPowerRho_le_two_thirds
    {p : ℕ} (hp3 : 3 ≤ p) : higherPowerRho p ≤ (2 / 3 : ℝ) := by
  unfold higherPowerRho
  have hp0 : (0 : ℝ) < p := by positivity
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p)]
  push_cast
  norm_num
  linarith

/-- Equation (43), with every floor and padded block retained. -/
theorem localSmallPrimeFiber_normalized_le_uniform
    {X p r : ℕ} {L : Branch}
    (hX : 0 < X) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpSmall : p ≤ Nat.sqrt X)
    (hr : smallPrimeDepth p X = r) :
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
      (3 / (p : ℝ)) * (2 / 3 : ℝ) ^ r := by
  have hp3 : 3 ≤ p :=
    Nat.succ_le_iff.mpr (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  let U : ℕ := X / p
  let P : ℕ := p ^ r
  let H : ℕ := halfDigitCount p
  let B : ℕ := (localHigherPowerFiber X L p 1).card
  have hspec := smallPrimeDepth_spec hp hX hpSmall
  have hr1 : 1 ≤ r := by simpa [hr] using hspec.1
  have hPX : p * P ≤ X := by
    simpa [P, hr, pow_succ', Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hspec.2.1
  have hPPos : 0 < P := pow_pos hp.pos r
  have hPleU : P ≤ U := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    simpa [P, mul_comm] using hPX
  have hDPos : 0 < U / P := Nat.div_pos hPleU hPPos
  have hcoeff : (U + 1) / P + 1 ≤ 3 * (U / P) := by
    have hs := HigherPowerEvents.succ_div_le_div_add_one U P
    omega
  have hblock : B ≤ ((U + 1) / P + 1) * H ^ r := by
    have h := localHigherPowerFiber_card_le_block
      (X := X) (p := p) (a := 1) (L := L)
    simpa [B, U, P, H, higherPowerDepth_one_eq_smallPrimeDepth, hr]
      using h
  have hUP : (U / P) * P ≤ U := Nat.div_mul_le_self U P
  have hpU : p * U ≤ X := by
    simpa [U, mul_comm] using Nat.div_mul_le_self X p
  have hnat : B * p * P ≤ 3 * X * H ^ r := by
    calc
      B * p * P ≤
          (((U + 1) / P + 1) * H ^ r) * p * P :=
        Nat.mul_le_mul_right P (Nat.mul_le_mul_right p hblock)
      _ ≤ (3 * (U / P) * H ^ r) * p * P := by
        exact Nat.mul_le_mul_right P (Nat.mul_le_mul_right p
          (Nat.mul_le_mul_right (H ^ r) hcoeff))
      _ = 3 * H ^ r * p * ((U / P) * P) := by ring
      _ ≤ 3 * H ^ r * p * U :=
        Nat.mul_le_mul_left _ hUP
      _ ≤ 3 * H ^ r * X :=
        by simpa [mul_assoc] using Nat.mul_le_mul_left (3 * H ^ r) hpU
      _ = 3 * X * H ^ r := by ring
  have hreal : (B : ℝ) * (p : ℝ) * (P : ℝ) ≤
      3 * (X : ℝ) * (H : ℝ) ^ r := by
    exact_mod_cast hnat
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hPR : (0 : ℝ) < P := by exact_mod_cast hPPos
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hratio : (B : ℝ) / (X : ℝ) ≤
      (3 / (p : ℝ)) * ((H : ℝ) / (p : ℝ)) ^ r := by
    have hquot : (B : ℝ) / (X : ℝ) ≤
        (3 * (H : ℝ) ^ r) / ((p : ℝ) * (P : ℝ)) := by
      apply (div_le_div_iff₀ hXR (mul_pos hpR hPR)).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hreal
    calc
      (B : ℝ) / (X : ℝ) ≤
          (3 * (H : ℝ) ^ r) / ((p : ℝ) * (P : ℝ)) := hquot
      _ = (3 / (p : ℝ)) * ((H : ℝ) / (p : ℝ)) ^ r := by
        simp only [P, Nat.cast_pow, div_pow]
        field_simp
  have hrho : ((H : ℝ) / (p : ℝ)) ≤ (2 / 3 : ℝ) := by
    rw [show (H : ℝ) / (p : ℝ) = higherPowerRho p by
      simpa [H] using halfDigitCount_cast_div_eq_rho hp hp2]
    exact higherPowerRho_le_two_thirds hp3
  calc
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) =
        (B : ℝ) / (X : ℝ) := by rfl
    _ ≤ (3 / (p : ℝ)) * ((H : ℝ) / (p : ℝ)) ^ r := hratio
    _ ≤ (3 / (p : ℝ)) * (2 / 3 : ℝ) ^ r := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hrho r) (by positivity)

/-! ## Sharp fixed-depth count for one branch and prime -/

/-- The concrete finite Fourier estimate for one branch/prime fiber.  The
complete-block multiplier is the natural floor
`(X / p + 1) / p^r`; retaining it is essential for the normalized Fourier
error bound. -/
theorem localSmallPrimeFiber_card_cast_le_fixedDepthRaw
    {X p r : ℕ} {L : Branch}
    (hX : 0 < X) (hp : p.Prime) (hp43 : 43 < p)
    (hpSmall : p ≤ Nat.sqrt X)
    (hdepth : smallPrimeDepth p X = r) :
    ((localHigherPowerFiber X L p 1).card : ℝ) ≤
      ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          (((lowerHalfResidues p (2 * r)).card : ℝ) *
              (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) +
            2 * fixedDepthBlockDiscrepancy r p)) +
        (p ^ r : ℕ) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by omega
  have hr : 1 ≤ r := by
    simpa only [hdepth] using (smallPrimeDepth_spec hp hX hpSmall).1
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hempty : localHigherPowerFiber X L p 1 = ∅
  · rw [hempty]
    simp only [card_empty, Nat.cast_zero]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (by positivity)
          (mul_nonneg (by norm_num)
            (fixedDepthBlockDiscrepancy_nonneg r p))))
      (Nat.cast_nonneg _)
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases mem_localHigherPowerFiber.mp hx₀ with ⟨_hx₀Range, d₀, h₀⟩
    let s : ℕ := x₀ % p
    let c₀ : ℕ := branchValue L s / p
    let A : Finset (ZMod (p ^ (2 * r))) := lowerHalfResidues p (2 * r)
    let F : ℕ → ZMod (p ^ (2 * r)) := fun k ↦
      fixedDepthQuadratic
        (fixedDepthNaturalAlpha : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalBeta p r L c₀ : ZMod (p ^ (2 * r)))
        (fixedDepthNaturalGamma p r L s c₀ : ZMod (p ^ (2 * r)))
        (k : ZMod (p ^ (2 * r)))
    let admissible : Finset ℕ :=
      (Finset.range (X / p + 1)).filter fun k ↦ F k ∈ A
    have hmap : ∀ x ∈ localHigherPowerFiber X L p 1,
        x / p ∈ admissible := by
      intro x hx
      rcases mem_localHigherPowerFiber.mp hx with ⟨hxRange, d, hlocal⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right
          (mem_parameterRange.mp hxRange).2)
      · have hdigit := natCast_mem_lowerHalfResidues (r := 2 * r)
          hlocal.1 hlocal.2.1 hlocal.2.2.2
        change F (x / p) ∈ A
        have hphase : F (x / p) =
            (branchTestValue L x d : ZMod (p ^ (2 * r))) := by
          rw [show F (x / p) =
              padicBranchMap (p : ZMod (p ^ (2 * r)))
                (branchPadicQuadratic p 1 : ZMod (p ^ (2 * r)))
                (branchPadicLinear L p 1 c₀ : ZMod (p ^ (2 * r)))
                (branchResidualCoefficient L : ZMod (p ^ (2 * r)))
                (branchTestValue L s c₀ : ZMod (p ^ (2 * r)))
                (x / p : ZMod (p ^ (2 * r))) by
            dsimp only [F]
            exact (padicBranchMap_eq_fixedDepthQuadratic L s c₀ _).symm]
          simpa only [s, c₀, pow_one] using
            (branchTestValue_eq_padicBranchMap
              (r := 2 * r) h₀ hlocal).symm
        rw [hphase]
        simpa only [A] using hdigit
    have hinj : Set.InjOn (fun x : ℕ ↦ x / p)
        (localHigherPowerFiber X L p 1 : Set ℕ) := by
      intro x hx y hy hdiv
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hxRange, d, hxlocal⟩
      rcases mem_localHigherPowerFiber.mp hy with ⟨_hyRange, e, hylocal⟩
      change x / p = y / p at hdiv
      have hmod : x % p = y % p := by
        have hxy : x ≡ y [MOD p] := by
          simpa only [pow_one] using localBranchRoots_modEq hxlocal hylocal
        exact hxy
      calc
        x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
        _ = p * (y / p) + y % p := by rw [hdiv, hmod]
        _ = y := Nat.div_add_mod y p
    have hfiber : (localHigherPowerFiber X L p 1).card ≤ admissible.card :=
      Finset.card_le_card_of_injOn (fun x : ℕ ↦ x / p) hmap hinj
    have hA :
        (∑ h : ZMod (p ^ (2 * r)),
            ‖ZMod.dft (finsetIndicator A) h‖) ≤
          ((p ^ (2 * r) : ℕ) : ℝ) *
            (3 + Real.log p) ^ (2 * r) := by
      simpa only [A, Nat.cast_pow] using
        (dft_lowerHalfResidues_l1_le (p := p) (d := 2 * r) hp3)
    have hblock (k : ℕ) :
        (((Finset.range (p ^ r)).filter fun t ↦
            F (t + p ^ r * k) ∈ A).card : ℝ) ≤
          ((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) +
            fixedDepthBlockDiscrepancy r p := by
      have hfourier := fixedDepth_intervalHitCount_le
        (p := p) (r := r)
        (alpha := fixedDepthNaturalAlpha)
        (beta := fixedDepthNaturalBeta p r L c₀)
        (gamma := fixedDepthNaturalGamma p r L s c₀)
        hp hr hp2
        (largePrime_not_dvd_fixedDepthNaturalAlpha hp hp43)
        (prime_not_dvd_fixedDepthNaturalBeta (c₀ := c₀) hr h₀)
        (p ^ r * k) A hA
      simpa only [intervalHitCount, F, fixedDepthBlockDiscrepancy,
        add_comm] using hfourier
    have hadmissible : (admissible.card : ℝ) ≤
        ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          (((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) +
            2 * fixedDepthBlockDiscrepancy r p)) +
          (p ^ r : ℕ) := by
      exact card_filter_range_cast_le_completeBlocks_add_terminal
        (X / p + 1) (p ^ r) (fun k ↦ F k ∈ A)
        (pow_pos hp.pos r)
        ((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ))
        (fixedDepthBlockDiscrepancy r p)
        (by positivity)
        (one_le_fixedDepthBlockDiscrepancy hp.pos hr)
        hblock
    calc
      ((localHigherPowerFiber X L p 1).card : ℝ) ≤
          (admissible.card : ℝ) := by exact_mod_cast hfiber
      _ ≤ _ := by simpa only [A] using hadmissible

/-- Normalized one-fiber estimate in exactly the four summands used by the
fixed-depth analytic majorant. -/
theorem localSmallPrimeFiber_normalized_le_fixedDepth
    {X p r : ℕ} {L : Branch}
    (hX : 0 < X) (hp : p.Prime) (hp43 : 43 < p)
    (hpSmall : p ≤ Nat.sqrt X)
    (hdepth : smallPrimeDepth p X = r) :
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
      relaxedDigitDensity r p / (p : ℝ) + 1 / (X : ℝ) +
        fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
          (p : ℝ) ^ r / (X : ℝ) := by
  have hp0 : 0 < p := hp.pos
  have hp3 : 3 ≤ p := by omega
  have hr : 1 ≤ r := by
    simpa only [hdepth] using (smallPrimeDepth_spec hp hX hpSmall).1
  let B : ℕ := (X / p + 1) / p ^ r
  let A : Finset (ZMod (p ^ (2 * r))) := lowerHalfResidues p (2 * r)
  have hraw := localSmallPrimeFiber_card_cast_le_fixedDepthRaw
    (L := L) hX hp hp43 hpSmall hdepth
  have hmain :
      ((A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) =
        relaxedDigitDensity r p * (p : ℝ) ^ r := by
    rw [relaxedDigitDensity_eq_card_ratio hp3]
    simp only [A, Nat.cast_pow]
    ring
  have hBPnat : B * p ^ r ≤ X / p + 1 := by
    exact Nat.div_mul_le_self (X / p + 1) (p ^ r)
  have hBP : (B : ℝ) * (p : ℝ) ^ r ≤ ((X / p + 1 : ℕ) : ℝ) := by
    exact_mod_cast hBPnat
  have hN : ((X / p + 1 : ℕ) : ℝ) ≤
      (X : ℝ) / (p : ℝ) + 1 := by
    push_cast
    linarith [(Nat.cast_div_le : ((X / p : ℕ) : ℝ) ≤
      (X : ℝ) / (p : ℝ))]
  have hdelta0 : 0 ≤ relaxedDigitDensity r p :=
    relaxedDigitDensity_nonneg r p
  have hmainBound :
      ((B : ℝ) *
          ((A.card : ℝ) * (p ^ r : ℕ) /
            (p ^ (2 * r) : ℕ))) / (X : ℝ) ≤
        relaxedDigitDensity r p / (p : ℝ) +
          relaxedDigitDensity r p / (X : ℝ) := by
    rw [hmain]
    have hprod :
        (B : ℝ) * (p : ℝ) ^ r * relaxedDigitDensity r p ≤
          ((X : ℝ) / (p : ℝ) + 1) * relaxedDigitDensity r p := by
      exact mul_le_mul_of_nonneg_right (hBP.trans hN) hdelta0
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    calc
      (B : ℝ) * (relaxedDigitDensity r p * (p : ℝ) ^ r) /
          (X : ℝ) =
          ((B : ℝ) * (p : ℝ) ^ r * relaxedDigitDensity r p) /
            (X : ℝ) := by ring
      _ ≤ (((X : ℝ) / (p : ℝ) + 1) *
          relaxedDigitDensity r p) / (X : ℝ) :=
        div_le_div_of_nonneg_right hprod hXR.le
      _ = relaxedDigitDensity r p / (p : ℝ) +
          relaxedDigitDensity r p / (X : ℝ) := by
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hXR0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
        field_simp [hpR, hXR0]
  have hband := (smallPrimeDepth_spec hp hX hpSmall).2.1
  rw [hdepth] at hband
  have hdisc :=
    two_mul_fixedDepthCompleteBlocks_normalized_discrepancy_le
      hp0 hX hr hband
  have hdeltaOne :
      relaxedDigitDensity r p / (X : ℝ) ≤ 1 / (X : ℝ) := by
    exact div_le_div_of_nonneg_right
      (relaxedDigitDensity_le_one hp.one_le) (by positivity)
  have hrawDiv :
      ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
        (((B : ℝ) *
          (((A.card : ℝ) * (p ^ r : ℕ) /
              (p ^ (2 * r) : ℕ)) +
            2 * fixedDepthBlockDiscrepancy r p)) +
          (p : ℝ) ^ r) / (X : ℝ) := by
    have := div_le_div_of_nonneg_right hraw (by positivity : (0 : ℝ) ≤ X)
    simpa only [B, A, Nat.cast_pow] using this
  calc
    ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
        (((B : ℝ) *
          (((A.card : ℝ) * (p ^ r : ℕ) /
              (p ^ (2 * r) : ℕ)) +
            2 * fixedDepthBlockDiscrepancy r p)) +
          (p : ℝ) ^ r) / (X : ℝ) := hrawDiv
    _ = ((B : ℝ) *
          ((A.card : ℝ) * (p ^ r : ℕ) /
            (p ^ (2 * r) : ℕ))) / (X : ℝ) +
        2 * (((B : ℝ) * fixedDepthBlockDiscrepancy r p) /
          (X : ℝ)) +
        (p : ℝ) ^ r / (X : ℝ) := by ring
    _ ≤ (relaxedDigitDensity r p / (p : ℝ) +
          relaxedDigitDensity r p / (X : ℝ)) +
        fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
        (p : ℝ) ^ r / (X : ℝ) := by
      exact add_le_add (add_le_add hmainBound hdisc) le_rfl
    _ ≤ relaxedDigitDensity r p / (p : ℝ) + 1 / (X : ℝ) +
        fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
        (p : ℝ) ^ r / (X : ℝ) := by
      gcongr

/-! ## Natural depth bands versus the real Mertens bands -/

/-- The floor-valued prime set occurring literally in
`fixedDepthReciprocalPrimeBand`. -/
def realDepthPrimeBand (X r : ℕ) : Finset ℕ :=
  (Finset.Ioc
      ⌊FullDensity.fixedDepthPrimeBandLower r (X : ℝ)⌋₊
      ⌊FullDensity.fixedDepthPrimeBandUpper r (X : ℝ)⌋₊).filter
    Nat.Prime

theorem smallPrimeBandPrimes_subset_realDepthPrimeBand
    {X r : ℕ} (hX : 0 < X) :
    smallPrimeBandPrimes X r ⊆ realDepthPrimeBand X r := by
  intro p hpBand
  rcases mem_smallPrimeBandPrimes.mp hpBand with
    ⟨_hp2, hpSmall, hp, hdepth⟩
  have hspec := smallPrimeDepth_spec hp hX hpSmall
  rw [hdepth] at hspec
  have hlowCast : (p : ℝ) ^ ((r + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hspec.2.1
  have hhighCast : (X : ℝ) <
      (p : ℝ) ^ ((r + 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hspec.2.2
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hlower : fixedDepthPrimeBandLower r (X : ℝ) < (p : ℝ) := by
    exact (Real.rpow_inv_lt_iff_of_pos hX0 hp0 (by positivity)).2 hhighCast
  have hupper : (p : ℝ) ≤ fixedDepthPrimeBandUpper r (X : ℝ) := by
    exact (Real.le_rpow_inv_iff_of_pos hp0 hX0 (by positivity)).2 hlowCast
  rw [realDepthPrimeBand, Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, Nat.le_floor hupper⟩, hp⟩
  exact (Nat.floor_lt (fixedDepthPrimeBandLower_pos r
    (by exact_mod_cast hX)).le).2 hlower

/-- At every positive fixed depth, the exact ledger count is eventually
dominated by four copies of the complete analytic majorant, one for each
branch. -/
theorem eventually_normalizedSmallPrimeDepthWitnessCount_le_majorant
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ X : ℕ in atTop,
      normalizedSmallPrimeDepthWitnessCount r X ≤
        4 * fixedDepthAnalyticMajorant r X := by
  filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop 43,
        eventually_gt_atTop (0 : ℕ)] with X hfloor hX
  have hsubset : smallPrimeBandPrimes X r ⊆ fixedDepthPrimeSet r X := by
    simpa only [realDepthPrimeBand, fixedDepthPrimeSet] using
      (smallPrimeBandPrimes_subset_realDepthPrimeBand (X := X) (r := r) hX)
  let g : ℕ → ℝ := fun p ↦
    relaxedDigitDensity r p / (p : ℝ) + 1 / (X : ℝ) +
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p +
        (p : ℝ) ^ r / (X : ℝ)
  have hg_nonneg (p : ℕ) : 0 ≤ g p := by
    dsimp only [g]
    have hdelta := relaxedDigitDensity_nonneg r p
    have hweight : 0 ≤ fixedDepthFourierWeight r p := by
      unfold fixedDepthFourierWeight
      positivity
    have hconstant : 0 ≤ fixedDepthFourierErrorConstant r := by
      unfold fixedDepthFourierErrorConstant
      positivity
    positivity
  have hsumIdentity :
      (∑ p ∈ fixedDepthPrimeSet r X, g p) =
        fixedDepthAnalyticMajorant r X := by
    unfold g fixedDepthAnalyticMajorant fixedDepthFourierError
      fixedDepthFourierBandError fixedDepthTerminalBlockError
      fixedDepthUnitError
    simp_rw [Finset.sum_add_distrib, Finset.sum_div]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
    ring
  have hprime (L : Branch) :
      (∑ p ∈ smallPrimeBandPrimes X r,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ)) ≤
        fixedDepthAnalyticMajorant r X := by
    calc
      (∑ p ∈ smallPrimeBandPrimes X r,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ)) ≤
          ∑ p ∈ smallPrimeBandPrimes X r, g p := by
        apply Finset.sum_le_sum
        intro p hpBand
        have hpBand' := mem_smallPrimeBandPrimes.mp hpBand
        have hpFull := hsubset hpBand
        have hp43 : 43 < p := by
          rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hpFull
          omega
        exact localSmallPrimeFiber_normalized_le_fixedDepth
          (L := L) hX hpBand'.2.2.1 hp43 hpBand'.2.1 hpBand'.2.2.2
      _ ≤ ∑ p ∈ fixedDepthPrimeSet r X, g p := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun p _hpFull _hpBand ↦ hg_nonneg p)
      _ = fixedDepthAnalyticMajorant r X := hsumIdentity
  have hcard := localSmallPrimeDepthWitnesses_card_le_keys X r
  have hcast :
      ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeBandPrimes X r)).card : ℝ) := by
    exact_mod_cast hcard
  unfold normalizedSmallPrimeDepthWitnessCount
  calc
    ((localSmallPrimeDepthWitnessesUpTo X r).card : ℝ) / (X : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeBandPrimes X r)).card : ℝ) /
          (X : ℝ) := by
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = ∑ L : Branch, ∑ p ∈ smallPrimeBandPrimes X r,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) := by
      rw [smallPrimeKeys_card]
      push_cast
      simp only [Finset.sum_div]
    _ ≤ ∑ _L : Branch, fixedDepthAnalyticMajorant r X := by
      exact Finset.sum_le_sum fun L _hL ↦ hprime L
    _ = 4 * fixedDepthAnalyticMajorant r X := by
      have hbranch : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hbranch]
      norm_num

theorem fixedDepthReciprocalPrimeBand_eq_sum_realDepthPrimeBand
    {X r : ℕ} (hX : 1 < X) :
    fixedDepthReciprocalPrimeBand r (X : ℝ) =
      ∑ p ∈ realDepthPrimeBand X r, (p : ℝ)⁻¹ := by
  let lo : ℕ := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let hi : ℕ := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  have hlohi : lo ≤ hi := by
    apply Nat.floor_mono
    exact fixedDepthPrimeBandLower_le_upper r (by exact_mod_cast hX.le)
  have hdisj : Disjoint
      ((Finset.Ioc 0 lo).filter Nat.Prime)
      ((Finset.Ioc lo hi).filter Nat.Prime) := by
    exact Finset.disjoint_filter_filter
      (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (d := hi) le_rfl)
  have hunion :
      (Finset.Ioc 0 lo).filter Nat.Prime ∪
          (Finset.Ioc lo hi).filter Nat.Prime =
        (Finset.Ioc 0 hi).filter Nat.Prime := by
    rw [← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le lo) hlohi]
  have hsum := Finset.sum_union hdisj
      (f := fun p : ℕ ↦ (p : ℝ)⁻¹)
  rw [hunion] at hsum
  unfold fixedDepthReciprocalPrimeBand reciprocalPrimeSumReal
  change (∑ p ∈ (Finset.Ioc 0 hi).filter Nat.Prime, (p : ℝ)⁻¹) -
      (∑ p ∈ (Finset.Ioc 0 lo).filter Nat.Prime, (p : ℝ)⁻¹) = _
  rw [realDepthPrimeBand]
  change _ = ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, (p : ℝ)⁻¹
  linarith

/-- Reciprocal-prime mass of the exact natural depth band. -/
def smallPrimeBandMass (X r : ℕ) : ℝ :=
  ∑ p ∈ smallPrimeBandPrimes X r, (p : ℝ)⁻¹

/-- Geometrically weighted reciprocal-prime mass in the residual tail. -/
def weightedSmallPrimeTailMass (X R : ℕ) : ℝ :=
  ∑ p ∈ smallPrimeTailPrimes X R,
    (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹

theorem smallPrimeBandMass_nonneg (X r : ℕ) :
    0 ≤ smallPrimeBandMass X r := by
  unfold smallPrimeBandMass
  positivity

theorem weightedSmallPrimeTailMass_nonneg (X R : ℕ) :
    0 ≤ weightedSmallPrimeTailMass X R := by
  unfold weightedSmallPrimeTailMass
  positivity

theorem smallPrimeBandMass_le_fixedDepthReciprocalPrimeBand
    {X r : ℕ} (hX : 1 < X) :
    smallPrimeBandMass X r ≤
      fixedDepthReciprocalPrimeBand r (X : ℝ) := by
  rw [fixedDepthReciprocalPrimeBand_eq_sum_realDepthPrimeBand hX]
  unfold smallPrimeBandMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (smallPrimeBandPrimes_subset_realDepthPrimeBand (by omega))
    (fun p _ _ ↦ by positivity)

/-! ## Uniform tail: shallow and deepest bands -/

def shallowSmallPrimeTailPrimes (X R J : ℕ) : Finset ℕ :=
  (smallPrimeTailPrimes X R).filter fun p ↦ smallPrimeDepth p X < J

def deepSmallPrimeTailPrimes (X R J : ℕ) : Finset ℕ :=
  (smallPrimeTailPrimes X R).filter fun p ↦ J ≤ smallPrimeDepth p X

@[simp] theorem mem_shallowSmallPrimeTailPrimes {X R J p : ℕ} :
    p ∈ shallowSmallPrimeTailPrimes X R J ↔
      p ∈ smallPrimeTailPrimes X R ∧ smallPrimeDepth p X < J := by
  simp [shallowSmallPrimeTailPrimes]

@[simp] theorem mem_deepSmallPrimeTailPrimes {X R J p : ℕ} :
    p ∈ deepSmallPrimeTailPrimes X R J ↔
      p ∈ smallPrimeTailPrimes X R ∧ J ≤ smallPrimeDepth p X := by
  simp [deepSmallPrimeTailPrimes]

theorem shallowSmallPrimeTailPrimes_eq_biUnion (X R J : ℕ) :
    shallowSmallPrimeTailPrimes X R J =
      (Finset.Ico R J).biUnion (smallPrimeBandPrimes X) := by
  ext p
  constructor
  · intro hp
    rcases mem_shallowSmallPrimeTailPrimes.mp hp with ⟨htail, hJ⟩
    have htail' := mem_smallPrimeTailPrimes.mp htail
    rw [Finset.mem_biUnion]
    exact ⟨smallPrimeDepth p X,
      Finset.mem_Ico.mpr ⟨htail'.2.2.2, hJ⟩,
      mem_smallPrimeBandPrimes.mpr
        ⟨htail'.1, htail'.2.1, htail'.2.2.1, rfl⟩⟩
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨r, hr, hpBand⟩
    have hr' := Finset.mem_Ico.mp hr
    have hpBand' := mem_smallPrimeBandPrimes.mp hpBand
    apply mem_shallowSmallPrimeTailPrimes.mpr
    refine ⟨mem_smallPrimeTailPrimes.mpr
      ⟨hpBand'.1, hpBand'.2.1, hpBand'.2.2.1, ?_⟩, ?_⟩
    · simpa [hpBand'.2.2.2] using hr'.1
    · simpa [hpBand'.2.2.2] using hr'.2

theorem smallPrimeBandPrimes_pairwiseDisjoint (X : ℕ) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint (smallPrimeBandPrimes X) := by
  intro r _hr t _ht hrt
  change Disjoint (smallPrimeBandPrimes X r) (smallPrimeBandPrimes X t)
  rw [Finset.disjoint_left]
  intro p hpr hpt
  have er := (mem_smallPrimeBandPrimes.mp hpr).2.2.2
  have et := (mem_smallPrimeBandPrimes.mp hpt).2.2.2
  exact hrt (er.symm.trans et)

theorem weighted_shallowSmallPrimeTail_sum_eq (X R J : ℕ) :
    (∑ p ∈ shallowSmallPrimeTailPrimes X R J,
      (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) =
      ∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r := by
  rw [shallowSmallPrimeTailPrimes_eq_biUnion,
    Finset.sum_biUnion (smallPrimeBandPrimes_pairwiseDisjoint X
      (Finset.Ico R J))]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑ p ∈ smallPrimeBandPrimes X r,
        (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) =
        ∑ p ∈ smallPrimeBandPrimes X r,
          (2 / 3 : ℝ) ^ r * (p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(mem_smallPrimeBandPrimes.mp hp).2.2.2]
    _ = (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r := by
      unfold smallPrimeBandMass
      rw [Finset.mul_sum]

theorem smallPrimeTailPrimes_shallow_union_deep (X R J : ℕ) :
    smallPrimeTailPrimes X R =
      shallowSmallPrimeTailPrimes X R J ∪
        deepSmallPrimeTailPrimes X R J := by
  ext p
  simp only [mem_smallPrimeTailPrimes, mem_shallowSmallPrimeTailPrimes,
    mem_deepSmallPrimeTailPrimes, Finset.mem_union]
  constructor
  · intro hp
    by_cases hd : smallPrimeDepth p X < J
    · exact Or.inl ⟨hp, hd⟩
    · exact Or.inr ⟨hp, Nat.le_of_not_gt hd⟩
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

theorem shallow_deep_disjoint (X R J : ℕ) :
    Disjoint (shallowSmallPrimeTailPrimes X R J)
      (deepSmallPrimeTailPrimes X R J) := by
  rw [Finset.disjoint_left]
  intro p hs hd
  have hs' := (mem_shallowSmallPrimeTailPrimes.mp hs).2
  have hd' := (mem_deepSmallPrimeTailPrimes.mp hd).2
  omega

theorem deepSmallPrimeTailMass_le (X R J : ℕ) :
    (∑ p ∈ deepSmallPrimeTailPrimes X R J,
      (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) ≤
      (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) := by
  calc
    (∑ p ∈ deepSmallPrimeTailPrimes X R J,
        (2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) ≤
        ∑ p ∈ deepSmallPrimeTailPrimes X R J,
          (2 / 3 : ℝ) ^ J * (p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (mem_deepSmallPrimeTailPrimes.mp hp).2)
        (by positivity)
    _ = (2 / 3 : ℝ) ^ J *
        ∑ p ∈ deepSmallPrimeTailPrimes X R J, (p : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) J)
      unfold reciprocalPrimeSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpTail := (mem_deepSmallPrimeTailPrimes.mp hp).1
        have hpTail' := mem_smallPrimeTailPrimes.mp hpTail
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpTail'.2.2.1⟩
      · intro p _ _
        positivity

theorem weightedSmallPrimeTailMass_le_shallow_add_deep
    (X R J : ℕ) :
    weightedSmallPrimeTailMass X R ≤
      (∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r) +
        (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) := by
  unfold weightedSmallPrimeTailMass
  rw [smallPrimeTailPrimes_shallow_union_deep X R J,
    Finset.sum_union (shallow_deep_disjoint X R J),
    weighted_shallowSmallPrimeTail_sum_eq]
  exact add_le_add le_rfl (deepSmallPrimeTailMass_le X R J)

/-! ## The ledger tail is controlled by the weighted prime mass -/

/-- The local obstruction itself excludes `p = 2`, so the corresponding
fiber is literally empty. -/
theorem localHigherPowerFiber_two_eq_empty (X : ℕ) (L : Branch) :
    localHigherPowerFiber X L 2 1 = ∅ := by
  ext x
  simp [mem_localHigherPowerFiber, LocalBranchObstruction]

/-- The factor `12` is exactly `4` branches times the factor `3` in the
padded complete-block estimate. -/
theorem normalizedSmallPrimeDepthTailWitnessCount_le_weightedMass
    {X R : ℕ} (hX : 0 < X) :
    normalizedSmallPrimeDepthTailWitnessCount R X ≤
      12 * weightedSmallPrimeTailMass X R := by
  have hcard := localSmallPrimeDepthTailWitnesses_card_le_keys X R
  have hcast :
      ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeTailPrimes X R)).card : ℝ) := by
    exact_mod_cast hcard
  unfold normalizedSmallPrimeDepthTailWitnessCount
  calc
    ((localSmallPrimeDepthTailWitnessesUpTo X R).card : ℝ) / (X : ℝ) ≤
        ((smallPrimeKeys X (smallPrimeTailPrimes X R)).card : ℝ) /
          (X : ℝ) := by
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = ∑ L : Branch, ∑ p ∈ smallPrimeTailPrimes X R,
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) := by
      rw [smallPrimeKeys_card]
      push_cast
      simp only [Finset.sum_div]
    _ ≤ ∑ L : Branch, ∑ p ∈ smallPrimeTailPrimes X R,
          3 * ((2 / 3 : ℝ) ^ smallPrimeDepth p X * (p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro L _hL
      apply Finset.sum_le_sum
      intro p hpTail
      have hpTail' := mem_smallPrimeTailPrimes.mp hpTail
      by_cases hp2 : p = 2
      · subst p
        rw [localHigherPowerFiber_two_eq_empty]
        simp
        positivity
      · have hfiber := localSmallPrimeFiber_normalized_le_uniform
            hX hpTail'.2.2.1 hp2 hpTail'.2.1
            (r := smallPrimeDepth p X) rfl (L := L)
        calc
          ((localHigherPowerFiber X L p 1).card : ℝ) / (X : ℝ) ≤
              (3 / (p : ℝ)) *
                (2 / 3 : ℝ) ^ smallPrimeDepth p X := hfiber
          _ = 3 * ((2 / 3 : ℝ) ^ smallPrimeDepth p X *
                (p : ℝ)⁻¹) := by ring
    _ = 12 * weightedSmallPrimeTailMass X R := by
      unfold weightedSmallPrimeTailMass
      rw [← Finset.mul_sum]
      have hbranch : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hbranch]
      ring

/-! ## A single uniform finite-depth tail bound -/

/-- If `r` lies below the moving deepest-band cutoff, then the lower
endpoint of its real prime band is at least two.  The proof keeps the
natural floor/logarithm bookkeeping explicit: `r + 2 ≤ log₃(√X)` gives
`2^(r+2) ≤ X`. -/
theorem fixedDepthPrimeBandLower_ge_two_of_lt_movingDepth
    {X r : ℕ} (hX : 9 ≤ X)
    (hr : r < movingDepthLog X - 1) :
    2 ≤ fixedDepthPrimeBandLower r (X : ℝ) := by
  let N : ℕ := Nat.sqrt X
  let m : ℕ := Nat.log 3 N
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Nat.sqrt_pos.2 (by omega)
  have hr' : r < m - 1 := by
    simpa only [movingDepthLog, N, m] using hr
  have hrm : r + 2 ≤ m := by
    omega
  have hpowLog : 3 ^ m ≤ N := by
    exact Nat.pow_log_le_self 3 hNpos.ne'
  have hpowTwo : 2 ^ (r + 2) ≤ X := by
    calc
      2 ^ (r + 2) ≤ 3 ^ (r + 2) :=
        Nat.pow_le_pow_left (by norm_num) _
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hrm
      _ ≤ N := hpowLog
      _ ≤ X := by
        dsimp only [N]
        exact Nat.sqrt_le_self X
  unfold fixedDepthPrimeBandLower
  rw [Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) ≤ X)
    (by positivity : (0 : ℝ) < (r + 2 : ℕ))]
  rw [Real.rpow_natCast]
  exact_mod_cast hpowTwo

/-- Finite, uniform equation (45): every residual depth is paid for by
the summable Mertens main tail, the quantitative Mertens error, or the
single deepest moving band. -/
theorem weightedSmallPrimeTailMass_le_majorant
    {X R : ℕ} (hX : 9 ≤ X) :
    weightedSmallPrimeTailMass X R ≤
      uniformDepthMainTail R + uniformMertensErrorMajorant X +
        deepestBandMajorant X := by
  let J : ℕ := movingDepthLog X - 1
  have hX1 : 1 < X := by omega
  have hband :
      (∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r) ≤
      ∑ r ∈ Finset.Ico R J,
        (2 / 3 : ℝ) ^ r *
          fixedDepthReciprocalPrimeBand r (X : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    exact mul_le_mul_of_nonneg_left
      (smallPrimeBandMass_le_fixedDepthReciprocalPrimeBand hX1)
      (pow_nonneg (by norm_num) r)
  have hMertens := weightedFixedDepthBand_sum_le_main_add_error
    (Finset.Ico R J) hX1 (fun r hr ↦
      fixedDepthPrimeBandLower_ge_two_of_lt_movingDepth hX
        (by simpa only [J] using (Finset.mem_Ico.mp hr).2))
  have hmain := uniformDepthMain_sum_Ico_le_tail R J
  calc
    weightedSmallPrimeTailMass X R ≤
        (∑ r ∈ Finset.Ico R J,
          (2 / 3 : ℝ) ^ r * smallPrimeBandMass X r) +
          (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) :=
      weightedSmallPrimeTailMass_le_shallow_add_deep X R J
    _ ≤ (∑ r ∈ Finset.Ico R J,
          (2 / 3 : ℝ) ^ r *
            fixedDepthReciprocalPrimeBand r (X : ℝ)) +
          (2 / 3 : ℝ) ^ J * reciprocalPrimeSum (Nat.sqrt X) :=
      add_le_add hband le_rfl
    _ ≤ ((∑ r ∈ Finset.Ico R J, uniformDepthMainTerm r) +
          uniformMertensErrorMajorant X) + deepestBandMajorant X := by
      exact add_le_add hMertens (by rfl)
    _ ≤ uniformDepthMainTail R + uniformMertensErrorMajorant X +
          deepestBandMajorant X := by
      exact add_le_add (add_le_add hmain le_rfl) le_rfl

/-- Quantified ledger-level tail bound consumed by the limsup-series
assembly. -/
theorem normalizedSmallPrimeDepthTailWitnessCount_le_majorant
    {X R : ℕ} (hX : 9 ≤ X) :
    normalizedSmallPrimeDepthTailWitnessCount R X ≤
      12 * (uniformDepthMainTail R + uniformMertensErrorMajorant X +
        deepestBandMajorant X) := by
  exact (normalizedSmallPrimeDepthTailWitnessCount_le_weightedMass
    (by omega : 0 < X)).trans (mul_le_mul_of_nonneg_left
      (weightedSmallPrimeTailMass_le_majorant hX) (by norm_num))

/-- The explicit analytic majorant for the normalized residual ledger. -/
def smallPrimeDepthTailMajorant (R X : ℕ) : ℝ :=
  12 * (uniformDepthMainTail R + uniformMertensErrorMajorant X +
    deepestBandMajorant X)

theorem tendsto_smallPrimeDepthTailMajorant (R : ℕ) :
    Tendsto (smallPrimeDepthTailMajorant R) atTop
      (nhds (12 * uniformDepthMainTail R)) := by
  have hconst : Tendsto (fun _ : ℕ ↦ uniformDepthMainTail R) atTop
      (nhds (uniformDepthMainTail R)) := tendsto_const_nhds
  have hsum := (hconst.add
    tendsto_uniformMertensErrorMajorant_zero).add
      tendsto_deepestBandMajorant_zero
  have hmul := hsum.const_mul 12
  simpa only [smallPrimeDepthTailMajorant, add_zero, mul_zero] using! hmul

theorem eventually_normalizedSmallPrimeDepthTailWitnessCount_le_majorant
    (R : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      normalizedSmallPrimeDepthTailWitnessCount R X ≤
        smallPrimeDepthTailMajorant R X := by
  filter_upwards [eventually_ge_atTop 9] with X hX
  exact normalizedSmallPrimeDepthTailWitnessCount_le_majorant hX

theorem normalizedSmallPrimeDepthTailWitnessCount_isBoundedUnder
    (R : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (normalizedSmallPrimeDepthTailWitnessCount R) := by
  rcases (tendsto_smallPrimeDepthTailMajorant R).isBoundedUnder_le.eventually_le
    with ⟨C, hC⟩
  apply isBoundedUnder_of_eventually_le (a := C)
  filter_upwards
    [eventually_normalizedSmallPrimeDepthTailWitnessCount_le_majorant R,
      hC] with X htail hmajor
  exact htail.trans hmajor

/-- Uniform limsup tail estimate, with no fixed-depth Fourier input. -/
theorem limsup_normalizedSmallPrimeDepthTailWitnessCount_le (R : ℕ) :
    limsup (normalizedSmallPrimeDepthTailWitnessCount R) atTop ≤
      12 * uniformDepthMainTail R := by
  have htailCob : IsCoboundedUnder (· ≤ ·) atTop
      (normalizedSmallPrimeDepthTailWitnessCount R) :=
    isCoboundedUnder_le_of_le atTop
      (normalizedSmallPrimeDepthTailWitnessCount_nonneg R)
  have hmajorBdd :=
    (tendsto_smallPrimeDepthTailMajorant R).isBoundedUnder_le
  calc
    limsup (normalizedSmallPrimeDepthTailWitnessCount R) atTop ≤
        limsup (smallPrimeDepthTailMajorant R) atTop :=
      limsup_le_limsup
        (eventually_normalizedSmallPrimeDepthTailWitnessCount_le_majorant R)
        htailCob hmajorBdd
    _ = 12 * uniformDepthMainTail R :=
      (tendsto_smallPrimeDepthTailMajorant R).limsup_eq

/-! ## Global assembly constants -/

/-- Four branches times the fixed-depth budget term. -/
def smallPrimeDepthBudgetTerm (r : ℕ) : ℝ :=
  4 * densityBudgetTerm r

theorem smallPrimeDepthBudgetTerm_nonneg (r : ℕ) :
    0 ≤ smallPrimeDepthBudgetTerm r := by
  exact mul_nonneg (by norm_num) (densityBudgetTerm_nonneg r)

theorem smallPrimeDepthBudgetTerm_summable :
    Summable smallPrimeDepthBudgetTerm := by
  exact densityBudgetTerm_summable.mul_left 4

theorem tsum_smallPrimeDepthBudgetTerm :
    (∑' r : ℕ, smallPrimeDepthBudgetTerm r) =
      4 * densityBudgetSeries := by
  unfold smallPrimeDepthBudgetTerm densityBudgetSeries
  rw [tsum_mul_left]

theorem tendsto_smallPrimeDepthTailBudget_zero :
    Tendsto (fun R : ℕ ↦ 12 * uniformDepthMainTail R) atTop
      (nhds 0) := by
  simpa only [mul_zero] using
    tendsto_uniformDepthMainTail_zero.const_mul 12

/-- Every exact-depth normalized ledger is bounded above. -/
theorem normalizedSmallPrimeDepthWitnessCount_isBoundedUnder (r : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop
      (normalizedSmallPrimeDepthWitnessCount r) := by
  by_cases hr0 : r = 0
  · subst r
    apply isBoundedUnder_of_eventually_le (a := 0)
    exact Eventually.of_forall fun X ↦ by
      simp
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hlim := (tendsto_fixedDepthAnalyticMajorant r hr).const_mul 4
    rcases hlim.isBoundedUnder_le.eventually_le with ⟨C, hC⟩
    apply isBoundedUnder_of_eventually_le (a := C)
    filter_upwards
      [eventually_normalizedSmallPrimeDepthWitnessCount_le_majorant r hr,
        hC] with X hcount hmajor
    exact hcount.trans hmajor

/-- Fixed-depth limsup estimate, including the absent depth-zero boundary. -/
theorem limsup_normalizedSmallPrimeDepthWitnessCount_le (r : ℕ) :
    limsup (normalizedSmallPrimeDepthWitnessCount r) atTop ≤
      smallPrimeDepthBudgetTerm r := by
  by_cases hr0 : r = 0
  · subst r
    have hfun : normalizedSmallPrimeDepthWitnessCount 0 =
        (fun _ : ℕ ↦ (0 : ℝ)) := by
      funext X
      exact normalizedSmallPrimeDepthWitnessCount_zero X
    rw [hfun]
    have hconst : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    rw [hconst.limsup_eq]
    simp [smallPrimeDepthBudgetTerm, densityBudgetTerm]
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hlim := (tendsto_fixedDepthAnalyticMajorant r hr).const_mul 4
    have hcountCob : IsCoboundedUnder (· ≤ ·) atTop
        (normalizedSmallPrimeDepthWitnessCount r) :=
      isCoboundedUnder_le_of_le atTop
        (normalizedSmallPrimeDepthWitnessCount_nonneg r)
    calc
      limsup (normalizedSmallPrimeDepthWitnessCount r) atTop ≤
          limsup (fun X : ℕ ↦ 4 * fixedDepthAnalyticMajorant r X) atTop :=
        limsup_le_limsup
          (eventually_normalizedSmallPrimeDepthWitnessCount_le_majorant r hr)
          hcountCob hlim.isBoundedUnder_le
      _ = 4 * (fixedDepthBaseDensity r *
          fixedDepthPrimeBandMainTerm r) := hlim.limsup_eq
      _ = smallPrimeDepthBudgetTerm r := by
        simp only [smallPrimeDepthBudgetTerm, densityBudgetTerm, hr0,
          if_false, fixedDepthBaseDensity, fixedDepthPrimeBandMainTerm]

/-- Boundedness of the entire normalized small-prime ledger already follows
from the depth-zero tail majorant; it does not depend on the sharp
fixed-depth Fourier estimate. -/
theorem normalizedSmallPrimeWitnessCount_isBoundedUnder :
    IsBoundedUnder (· ≤ ·) atTop normalizedSmallPrimeWitnessCount := by
  rcases
      (normalizedSmallPrimeDepthTailWitnessCount_isBoundedUnder 0).eventually_le
    with ⟨C, hC⟩
  apply isBoundedUnder_of_eventually_le (a := C)
  filter_upwards [hC] with X htail
  have hdecomp := normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail X 0
  have htotalTail : normalizedSmallPrimeWitnessCount X ≤
      normalizedSmallPrimeDepthTailWitnessCount 0 X := by
    simpa using hdecomp
  exact htotalTail.trans htail

/-- Full small-prime estimate: the fixed-depth Fourier bounds and the
uniform moving-depth tail assemble to the exact four-branch budget series. -/
theorem limsup_normalizedSmallPrimeWitnessCount_le :
    limsup normalizedSmallPrimeWitnessCount atTop ≤
      4 * densityBudgetSeries := by
  have hseries := limsup_le_tsum_of_finite_depth_and_tail
    (f := atTop)
    (term := smallPrimeDepthBudgetTerm)
    (total := normalizedSmallPrimeWitnessCount)
    (band := normalizedSmallPrimeDepthWitnessCount)
    (tail := normalizedSmallPrimeDepthTailWitnessCount)
    smallPrimeDepthBudgetTerm_nonneg
    smallPrimeDepthBudgetTerm_summable
    normalizedSmallPrimeWitnessCount_nonneg
    normalizedSmallPrimeDepthWitnessCount_nonneg
    normalizedSmallPrimeDepthWitnessCount_isBoundedUnder
    limsup_normalizedSmallPrimeDepthWitnessCount_le
    normalizedSmallPrimeDepthTailWitnessCount_nonneg
    normalizedSmallPrimeDepthTailWitnessCount_isBoundedUnder
    (fun R : ℕ ↦ 12 * uniformDepthMainTail R)
    tendsto_smallPrimeDepthTailBudget_zero
    limsup_normalizedSmallPrimeDepthTailWitnessCount_le
    (fun R ↦ Eventually.of_forall fun X ↦
      normalizedSmallPrimeWitnessCount_le_depth_sum_add_tail X R)
  simpa only [tsum_smallPrimeDepthBudgetTerm] using hseries

end

end Erdos730.SmallPrimeEvents

end Campaign180File41

/- Source module: ErdosProblems.Erdos730.FullDensityTheorem -/
section Campaign180File42
/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/

/-!
# Erdős 730: unconditional positive density and infinitude

This file is the terminal assembly of the four disjoint obstruction ranges.
The higher-power and transition ranges tend to zero, the fixed-depth plus
uniform-tail argument bounds the small-prime range, and fixed-modulus divisor
switching bounds the top-prime range.  The exact density budget then gives
positive lower density in the explicit four-linear-form family and hence the
upstream infinitude statement.
-/

open Filter
open scoped Topology

namespace Erdos730.FullDensityTheorem

open Erdos730

/-- The explicit family has lower density strictly greater than `107 / 2500`.
This discharges the former final hypothesis in
`Erdos730FullDensityReduction`. -/
theorem candidatePositiveDensity :
    FullDensityReduction.CandidatePositiveDensityClaim := by
  exact RangeAssembly.hasCandidatePositiveDensity_of_range_estimates
    HigherPowerEvents.tendsto_normalizedHigherPowerWitnessCount_zero
    SmallPrimeEvents.normalizedSmallPrimeWitnessCount_isBoundedUnder
    SmallPrimeEvents.limsup_normalizedSmallPrimeWitnessCount_le
    DivisorSwitching.normalizedTopPrimeWitnessCount_isBoundedUnder
    DivisorSwitching.limsup_normalizedTopPrimeWitnessCount_le

/-- **Erdős #730.**  There are infinitely many consecutive pairs whose
central binomial coefficients have identical prime support. -/
theorem pairSet_infinite : FullDensityCore.PairSet.Infinite := by
  exact FullDensityReduction.pairSet_infinite_of_candidatePositiveDensity
    candidatePositiveDensity


end Erdos730.FullDensityTheorem

end Campaign180File42

namespace Jig180Canonical
open Filter Topology
abbrev S : Set (ℕ × ℕ) :=
  {(n, m) : ℕ × ℕ | n < m ∧ n.centralBinom.primeFactors = m.centralBinom.primeFactors}
abbrev statement : Prop := S.Infinite
theorem set_eq : S = Erdos730.FullDensityCore.PairSet := rfl
theorem solution : statement := Erdos730.FullDensityTheorem.pairSet_infinite
end Jig180Canonical


namespace Submissions.Erdos730CentralBinomPrimeSupport.BlairPort
theorem proof : Jig180Canonical.statement := Jig180Canonical.solution
end Submissions.Erdos730CentralBinomPrimeSupport.BlairPort

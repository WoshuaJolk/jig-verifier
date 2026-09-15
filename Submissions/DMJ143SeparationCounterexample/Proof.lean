/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Use

/-! Port draft from 02da1ad1288b4881ea1f8e575fbe84af7db04364. Copyright 2025 The Formal Conjectures Authors; the source module explicitly credits AlphaProof for this counterexample. Erdős 1976 equation (10) supplies the motivating stronger separation question.
Only theorem relocation and the explicitly listed ordinary Mathlib imports differ from the upstream theorem; no new mathematics. -/

open scoped BigOperators

namespace Submissions.DMJ143SeparationCounterexample.Proof

theorem proof : ∃ (k₁ k₂ : ℕ), ∃ (_h₁ : k₂ ≤ k₁), ∃ (_h₂ : 3 ≤ k₂),
  {(n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ 2 * (n₁ + k₁) ∧
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors}.Nonempty := by
  use 10, 3, (by norm_num), (by norm_num)
  use (0, 13)
  norm_num [Finset.prod_Icc_succ_top]
  norm_num +decide [Nat.primeFactors, Nat.primeFactorsList]

end Submissions.DMJ143SeparationCounterexample.Proof

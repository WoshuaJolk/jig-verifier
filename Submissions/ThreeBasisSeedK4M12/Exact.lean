import Mathlib

namespace Submissions.ThreeBasisSeedK4M12.Exact

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def pair (x y : Fin 4 → ℂ) : ℂ := ∑ r, star (x r) * y r

def crossMatch (i j : Fin 12) : Prop :=
  (i.val = 0 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0) ∨
  (i.val = 1 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 1) ∨
  (i.val = 2 ∧ j.val = 10) ∨ (i.val = 10 ∧ j.val = 2) ∨
  (i.val = 3 ∧ j.val = 11) ∨ (i.val = 11 ∧ j.val = 3) ∨
  (i.val = 6 ∧ j.val = 8) ∨ (i.val = 8 ∧ j.val = 6) ∨
  (i.val = 7 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 7)

def edge (i j : Fin 12) : Prop :=
  i ≠ j ∧ (i.val / 4 = j.val / 4 ∨ crossMatch i j)

instance crossMatchDecidable (i j : Fin 12) : Decidable (crossMatch i j) := by
  unfold crossMatch
  infer_instance

instance edgeDecidable (i j : Fin 12) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel edge

def Rank4of5 (v : Fin 12 → Fin 4 → ℂ) (i j k l t : Fin 12) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

def vZ : Fin 12 → Fin 4 → ℤ := ![
  ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
  ![0, 1, 1, 1], ![1, 0, 1, -1], ![1, -3, 1, 2], ![3, 1, -2, 1],
  ![12, 4, -14, 7], ![-4, 12, -7, -14], ![7, -7, 0, -8], ![7, 7, 8, 0]
]

def v (i : Fin 12) : Fin 4 → ℂ := fun r => (vZ i r : ℂ)

def dot4Z (x y : Fin 4 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def minor3 (x y z : Fin 4 → ℤ) (c0 c1 c2 : Fin 4) : ℤ :=
  x c0 * y c1 * z c2 - x c0 * y c2 * z c1
    - x c1 * y c0 * z c2 + x c1 * y c2 * z c0
    + x c2 * y c0 * z c1 - x c2 * y c1 * z c0

def det4Z (x y z t : Fin 4 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 * t 3 - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3 + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2 - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3 + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3 - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2 + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3 - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3 + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1 - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2 + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2 - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1 + x 3 * y 2 * z 1 * t 0

lemma nz : ∀ i : Fin 12, ∃ r, vZ i r ≠ 0 := by decide +kernel
lemma orthZ : ∀ i j : Fin 12, dot4Z (vZ i) (vZ j) = 0 ↔ edge i j := by
  decide +kernel
lemma degrees : ∀ i, ((Finset.univ : Finset (Fin 12)).filter (edge i)).card = 4 := by
  decide +kernel
lemma triples : ∀ i j k : Fin 12, i < j → j < k →
    minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
    minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0 := by
  decide +kernel
lemma quintuples : ∀ i j k l t : Fin 12, i < j → j < k → k < l → l < t →
    det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0 ∨
    det4Z (vZ i) (vZ j) (vZ k) (vZ t) ≠ 0 ∨
    det4Z (vZ i) (vZ j) (vZ l) (vZ t) ≠ 0 ∨
    det4Z (vZ i) (vZ k) (vZ l) (vZ t) ≠ 0 ∨
    det4Z (vZ j) (vZ k) (vZ l) (vZ t) ≠ 0 := by
  decide +kernel

lemma adjOf {i j : Fin 12} (hne : i ≠ j) (he : edge i j) : graph.Adj i j :=
  (SimpleGraph.fromRel_adj edge i j).mpr ⟨hne, Or.inl he⟩

lemma connected : graph.Connected := by
  have step : ∀ i j : Fin 12, i ≠ j → edge i j → graph.Reachable i j :=
    fun i j hne he => (adjOf hne he).reachable
  have r0 : graph.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have r1 : graph.Reachable 0 1 := step 0 1 (by decide) (by decide)
  have r2 := r1.trans (step 1 2 (by decide) (by decide))
  have r3 := r2.trans (step 2 3 (by decide) (by decide))
  have r4 : graph.Reachable 0 4 := step 0 4 (by decide) (by decide)
  have r5 := r4.trans (step 4 5 (by decide) (by decide))
  have r6 := r5.trans (step 5 6 (by decide) (by decide))
  have r7 := r6.trans (step 6 7 (by decide) (by decide))
  have r8 := r6.trans (step 6 8 (by decide) (by decide))
  have r9 := r8.trans (step 8 9 (by decide) (by decide))
  have r10 := r9.trans (step 9 10 (by decide) (by decide))
  have r11 := r10.trans (step 10 11 (by decide) (by decide))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro w
  fin_cases w <;> assumption

lemma dot4_cast (x y : Fin 4 → ℤ) : pair (fun r => (x r : ℂ)) (fun r => (y r : ℂ)) =
    (dot4Z x y : ℂ) := by
  simp [pair, dot4Z, Fin.sum_univ_four, star_intCast]

lemma linInd_of_det4 {x y z t : Fin 4 → ℤ} (hd : det4Z x y z t ≠ 0) :
    LinearIndependent ℂ ![fun r => (x r : ℂ), fun r => (y r : ℂ),
      fun r => (z r : ℂ), fun r => (t r : ℂ)] := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ), (x 3 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ), (y 3 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ), (z 3 : ℂ);
       (t 0 : ℂ), (t 1 : ℂ), (t 2 : ℂ), (t 3 : ℂ)]
  have hdet : M.det = (det4Z x y z t : ℂ) := by
    simp [M, Matrix.det_succ_row_zero, det4Z, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by rw [hdet]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 4 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam : (fun i : Fin 4 => M i) =
      ![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ),
        fun r => (t r : ℂ)] := by
    ext i r
    fin_cases i <;> fin_cases r <;> simp [M]
  rwa [hfam] at hrows

lemma linInd3_of_cols {x y z : Fin 4 → ℤ} (a b c : Fin 4)
    (hd : minor3 x y z a b c ≠ 0) :
    LinearIndependent ℂ ![fun r => (x r : ℂ), fun r => (y r : ℂ),
      fun r => (z r : ℂ)] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x a : ℂ), (x b : ℂ), (x c : ℂ);
       (y a : ℂ), (y b : ℂ), (y c : ℂ);
       (z a : ℂ), (z b : ℂ), (z c : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have heq : M.det = (minor3 x y z a b c : ℂ) := by
      simp [M, minor3, Matrix.det_fin_three]
    rw [heq]
    exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) a, LinearMap.proj (R := ℂ) b,
      LinearMap.proj (R := ℂ) c]
  have hcomp :
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ),
        fun r => (z r : ℂ)] i)) = fun i => M i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [φ, M]
  have hli : LinearIndependent ℂ
      (fun i : Fin 3 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ),
        fun r => (z r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ hli

lemma linInd_v3 (i j k : Fin 12)
    (hd : minor3 (vZ i) (vZ j) (vZ k) 0 1 2 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 1 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 0 2 3 ≠ 0 ∨
      minor3 (vZ i) (vZ j) (vZ k) 1 2 3 ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  rcases hd with h | h | h | h
  · have q := linInd3_of_cols 0 1 2 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd3_of_cols 0 1 3 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd3_of_cols 0 2 3 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd3_of_cols 1 2 3 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]

lemma linInd_v4 (i j k l : Fin 12)
    (hd : det4Z (vZ i) (vZ j) (vZ k) (vZ l) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k, v l] := by
  have q := linInd_of_det4 hd
  convert q using 1
  ext s r
  fin_cases s <;> simp [v]

theorem proof :
  ∃ w : Fin 12 → Fin 4 → ℂ,
    (∀ i, w i ≠ 0) ∧
    (∀ i j, pair (w i) (w j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 12)).filter (edge i)).card = 4) ∧
    graph.Connected ∧
    (∀ i j k : Fin 12, i < j → j < k → LinearIndependent ℂ ![w i, w j, w k]) ∧
    (∀ i j k l t : Fin 12, i < j → j < k → k < l → l < t →
      Rank4of5 w i j k l t) := by
  refine ⟨v, ?_, ?_, degrees, connected, ?_, ?_⟩
  · intro i h
    obtain ⟨r, hr⟩ := nz i
    apply hr
    have := congrFun h r
    simpa [v] using this
  · intro i j
    change pair (fun r => (vZ i r : ℂ)) (fun r => (vZ j r : ℂ)) = 0 ↔ edge i j
    rw [dot4_cast, Int.cast_eq_zero]
    exact orthZ i j
  · intro i j k hij hjk
    exact linInd_v3 i j k (triples i j k hij hjk)
  · intro i j k l t hij hjk hkl hlt
    rcases quintuples i j k l t hij hjk hkl hlt with h | h | h | h | h
    · exact Or.inl (linInd_v4 i j k l h)
    · exact Or.inr (Or.inl (linInd_v4 i j k t h))
    · exact Or.inr (Or.inr (Or.inl (linInd_v4 i j l t h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (linInd_v4 i k l t h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (linInd_v4 j k l t h))))

end Submissions.ThreeBasisSeedK4M12.Exact

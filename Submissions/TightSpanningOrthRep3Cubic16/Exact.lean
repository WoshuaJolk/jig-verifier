import Mathlib

namespace Submissions.TightSpanningOrthRep3Cubic16.Exact

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- Symmetric edge relation of an explicit connected C4-free cubic graph on 16 vertices. -/
def edge (i j : Fin 16) : Prop :=
  (min i.val j.val, max i.val j.val) ∈
    [(0,1),(0,11),(0,12),(1,3),(1,9),(2,7),(2,8),(2,12),(3,6),(3,15),(4,6),(4,9),(4,10),(5,8),(5,11),(5,13),(6,7),(7,11),(8,10),(9,13),(10,14),(12,15),(13,14),(14,15)]

instance edgeDecidable (i j : Fin 16) : Decidable (edge i j) := by
  unfold edge
  infer_instance

def graph : SimpleGraph (Fin 16) := SimpleGraph.fromRel edge

def pair (x y : Fin 3 → ℂ) : ℂ := ∑ r, star (x r) * y r

def Rank3of4 (v : Fin 16 → Fin 3 → ℂ) (i j k l : Fin 16) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k] ∨
  LinearIndependent ℂ ![v i, v j, v l] ∨
  LinearIndependent ℂ ![v i, v k, v l] ∨
  LinearIndependent ℂ ![v j, v k, v l]

/-- An explicit connected c4-free cubic graph on 16 vertices, realized as the exact Hermitian orthogonality
graph of 16 nonzero vectors in C^3: connected, cubic, tight (every two vectors
independent) and 4-spanning (no four in a common plane) - the m = 16 instance of
the k = 3 row of the seed hypothesis (`SeedSufficesForMixedMinUPB`), with the
graph prescribed. -/
abbrev statement : Prop :=
  ∃ v : Fin 16 → Fin 3 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, pair (v i) (v j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 16)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 16, i < j → LinearIndependent ℂ ![v i, v j]) ∧
    (∀ i j k l : Fin 16, i < j → j < k → k < l → Rank3of4 v i j k l)

def vZ : Fin 16 → Fin 3 → ℤ := ![
  ![2, 3, 2], ![-1, 2, -2], ![-17, 43, 26], ![2, 0, -1], ![5, -7, 1], ![-4, -5, 0], ![1, 1, 2], ![-1, -1, 1], ![130, -104, 257], ![4, 3, 1], ![113, 77, -26], ![-5, 4, -1], ![-8, -86, 137], ![5, -4, -8], ![80, -86, 93], ![-43, -133, -86]]

def v (i : Fin 16) : Fin 3 → ℂ := fun r => (vZ i r : ℂ)

def dot3Z (x y : Fin 3 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def minor2 (x y : Fin 3 → ℤ) (c0 c1 : Fin 3) : ℤ :=
  x c0 * y c1 - x c1 * y c0

def det3Z (x y z : Fin 3 → ℤ) : ℤ :=
  x 0 * y 1 * z 2 - x 0 * y 2 * z 1
    - x 1 * y 0 * z 2 + x 1 * y 2 * z 0
    + x 2 * y 0 * z 1 - x 2 * y 1 * z 0

lemma nz : ∀ i : Fin 16, ∃ r, vZ i r ≠ 0 := by decide +kernel
lemma orthZ : ∀ i j : Fin 16, dot3Z (vZ i) (vZ j) = 0 ↔ edge i j := by
  decide +kernel
lemma degrees : ∀ i, ((Finset.univ : Finset (Fin 16)).filter (edge i)).card = 3 := by
  decide +kernel
lemma pairs : ∀ i j : Fin 16, i < j →
    minor2 (vZ i) (vZ j) 0 1 ≠ 0 ∨
    minor2 (vZ i) (vZ j) 0 2 ≠ 0 ∨
    minor2 (vZ i) (vZ j) 1 2 ≠ 0 := by
  decide +kernel
lemma quadruples : ∀ i j k l : Fin 16, i < j → j < k → k < l →
    det3Z (vZ i) (vZ j) (vZ k) ≠ 0 ∨
    det3Z (vZ i) (vZ j) (vZ l) ≠ 0 ∨
    det3Z (vZ i) (vZ k) (vZ l) ≠ 0 ∨
    det3Z (vZ j) (vZ k) (vZ l) ≠ 0 := by
  decide +kernel

lemma adjOf {i j : Fin 16} (hne : i ≠ j) (he : edge i j) : graph.Adj i j :=
  (SimpleGraph.fromRel_adj edge i j).mpr ⟨hne, Or.inl he⟩

lemma connected : graph.Connected := by
  have step : ∀ i j : Fin 16, i ≠ j → edge i j → graph.Reachable i j :=
    fun i j hne he => (adjOf hne he).reachable
  have r0 : graph.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have r1 : graph.Reachable 0 1 := step 0 1 (by decide) (by decide)
  have r11 : graph.Reachable 0 11 := step 0 11 (by decide) (by decide)
  have r12 : graph.Reachable 0 12 := step 0 12 (by decide) (by decide)
  have r3 : graph.Reachable 0 3 := r1.trans (step 1 3 (by decide) (by decide))
  have r9 : graph.Reachable 0 9 := r1.trans (step 1 9 (by decide) (by decide))
  have r5 : graph.Reachable 0 5 := r11.trans (step 11 5 (by decide) (by decide))
  have r7 : graph.Reachable 0 7 := r11.trans (step 11 7 (by decide) (by decide))
  have r2 : graph.Reachable 0 2 := r12.trans (step 12 2 (by decide) (by decide))
  have r15 : graph.Reachable 0 15 := r12.trans (step 12 15 (by decide) (by decide))
  have r6 : graph.Reachable 0 6 := r3.trans (step 3 6 (by decide) (by decide))
  have r4 : graph.Reachable 0 4 := r9.trans (step 9 4 (by decide) (by decide))
  have r13 : graph.Reachable 0 13 := r9.trans (step 9 13 (by decide) (by decide))
  have r8 : graph.Reachable 0 8 := r5.trans (step 5 8 (by decide) (by decide))
  have r14 : graph.Reachable 0 14 := r15.trans (step 15 14 (by decide) (by decide))
  have r10 : graph.Reachable 0 10 := r4.trans (step 4 10 (by decide) (by decide))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro w
  fin_cases w <;> assumption

lemma dot3_cast (x y : Fin 3 → ℤ) : pair (fun r => (x r : ℂ)) (fun r => (y r : ℂ)) =
    (dot3Z x y : ℂ) := by
  simp [pair, dot3Z, Fin.sum_univ_three, star_intCast]

lemma linInd_of_det3 {x y z : Fin 3 → ℤ} (hd : det3Z x y z ≠ 0) :
    LinearIndependent ℂ ![fun r => (x r : ℂ), fun r => (y r : ℂ),
      fun r => (z r : ℂ)] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ);
       (y 0 : ℂ), (y 1 : ℂ), (y 2 : ℂ);
       (z 0 : ℂ), (z 1 : ℂ), (z 2 : ℂ)]
  have hdet : M.det = (det3Z x y z : ℂ) := by
    simp [M, Matrix.det_fin_three, det3Z]
  have hdet0 : M.det ≠ 0 := by rw [hdet]; exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam : (fun i : Fin 3 => M i) =
      ![fun r => (x r : ℂ), fun r => (y r : ℂ), fun r => (z r : ℂ)] := by
    ext i r
    fin_cases i <;> fin_cases r <;> simp [M]
  rwa [hfam] at hrows

lemma linInd2_of_cols {x y : Fin 3 → ℤ} (a b : Fin 3)
    (hd : minor2 x y a b ≠ 0) :
    LinearIndependent ℂ ![fun r => (x r : ℂ), fun r => (y r : ℂ)] := by
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    !![(x a : ℂ), (x b : ℂ);
       (y a : ℂ), (y b : ℂ)]
  have hdet0 : M.det ≠ 0 := by
    have heq : M.det = (minor2 x y a b : ℂ) := by
      simp [M, minor2, Matrix.det_fin_two]
    rw [heq]
    exact_mod_cast hd
  have hrows : LinearIndependent ℂ (fun i : Fin 2 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  let φ : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    LinearMap.pi ![LinearMap.proj (R := ℂ) a, LinearMap.proj (R := ℂ) b]
  have hcomp :
      (fun i : Fin 2 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ)] i)) =
        fun i => M i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [φ, M]
  have hli : LinearIndependent ℂ
      (fun i : Fin 2 => φ (![fun r => (x r : ℂ), fun r => (y r : ℂ)] i)) := by
    simpa [hcomp] using hrows
  exact LinearIndependent.of_comp φ hli

lemma linInd_v2 (i j : Fin 16)
    (hd : minor2 (vZ i) (vZ j) 0 1 ≠ 0 ∨
      minor2 (vZ i) (vZ j) 0 2 ≠ 0 ∨
      minor2 (vZ i) (vZ j) 1 2 ≠ 0) :
    LinearIndependent ℂ ![v i, v j] := by
  rcases hd with h | h | h
  · have q := linInd2_of_cols 0 1 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd2_of_cols 0 2 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]
  · have q := linInd2_of_cols 1 2 h
    convert q using 1
    ext s r
    fin_cases s <;> simp [v]

lemma linInd_v3 (i j k : Fin 16)
    (hd : det3Z (vZ i) (vZ j) (vZ k) ≠ 0) :
    LinearIndependent ℂ ![v i, v j, v k] := by
  have q := linInd_of_det3 hd
  convert q using 1
  ext s r
  fin_cases s <;> simp [v]

theorem proof :
  ∃ w : Fin 16 → Fin 3 → ℂ,
    (∀ i, w i ≠ 0) ∧
    (∀ i j, pair (w i) (w j) = 0 ↔ edge i j) ∧
    (∀ i, ((Finset.univ : Finset (Fin 16)).filter (edge i)).card = 3) ∧
    graph.Connected ∧
    (∀ i j : Fin 16, i < j → LinearIndependent ℂ ![w i, w j]) ∧
    (∀ i j k l : Fin 16, i < j → j < k → k < l → Rank3of4 w i j k l) := by
  refine ⟨v, ?_, ?_, degrees, connected, ?_, ?_⟩
  · intro i h
    obtain ⟨r, hr⟩ := nz i
    apply hr
    have := congrFun h r
    simpa [v] using this
  · intro i j
    change pair (fun r => (vZ i r : ℂ)) (fun r => (vZ j r : ℂ)) = 0 ↔ edge i j
    rw [dot3_cast, Int.cast_eq_zero]
    exact orthZ i j
  · intro i j hij
    exact linInd_v2 i j (pairs i j hij)
  · intro i j k l hij hjk hkl
    rcases quadruples i j k l hij hjk hkl with h | h | h | h
    · exact Or.inl (linInd_v3 i j k h)
    · exact Or.inr (Or.inl (linInd_v3 i j l h))
    · exact Or.inr (Or.inr (Or.inl (linInd_v3 i k l h)))
    · exact Or.inr (Or.inr (Or.inr (linInd_v3 j k l h)))

end Submissions.TightSpanningOrthRep3Cubic16.Exact

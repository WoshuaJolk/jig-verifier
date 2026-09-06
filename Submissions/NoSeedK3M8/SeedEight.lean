import Mathlib

/-!
No eight-vector seed in C³ exists. The graph proof is structural, not an
enumeration: square-free cubic graphs on eight vertices would partition into
triangles, contradicting three not dividing eight. The general Hermitian
dimension obstruction below is adapted from woshuajolk's green Jig artifact
eee84aeb-43c2-440d-8956-653874536e6f, SeedLocalObstruction.Obstruction.
Connectedness and four-spanning are not needed for this obstruction.
-/

namespace Submissions.NoSeedK3M8.SeedEight
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def SquareFree : Prop :=
  ∀ a b, a ≠ b → ∀ x y,
    G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y

lemma triangle_at (hcard : Fintype.card V = 8)
    (hdeg : ∀ v, G.degree v = 3) (hs : SquareFree G) (v : V) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  classical
  let N := G.neighborFinset
  let U := (N v).biUnion fun x => (N x).erase v
  have hd (x : V) : (N x).card = 3 := hdeg x
  have he (x : V) (hx : x ∈ N v) : ((N x).erase v).card = 2 := by
    have hv : v ∈ N x := (G.mem_neighborFinset x v).mpr
      (G.adj_symm ((G.mem_neighborFinset v x).mp hx))
    have := Finset.card_erase_of_mem hv
    have := hd x
    omega
  have hdis : Set.PairwiseDisjoint ↑(N v) (fun x => (N x).erase v) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    have hx := hs a b hab v x
      (G.adj_symm ((G.mem_neighborFinset v a).mp ha))
      (G.adj_symm ((G.mem_neighborFinset v b).mp hb))
      ((G.mem_neighborFinset a x).mp (Finset.mem_erase.mp hxa).2)
      ((G.mem_neighborFinset b x).mp (Finset.mem_erase.mp hxb).2)
    exact (Finset.mem_erase.mp hxa).1 hx.symm
  have hU : U.card = 6 := by
    rw [Finset.card_biUnion hdis]
    calc
      ∑ x ∈ N v, ((N x).erase v).card = ∑ x ∈ N v, 2 :=
        Finset.sum_congr rfl he
      _ = 6 := by simp [hd]
  have hvU : v ∉ U := by simp [U]
  by_contra ht
  push Not at ht
  have hNU : Disjoint (N v) U := by
    apply Finset.disjoint_left.mpr
    intro a ha haU
    obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp haU
    exact ht b a ((G.mem_neighborFinset v b).mp hb) ((G.mem_neighborFinset v a).mp ha)
      ((G.mem_neighborFinset b a).mp (Finset.mem_erase.mp hab).2)
  have hsum := Finset.card_union_of_disjoint hNU
  have hbound := Finset.card_le_univ (N v ∪ U)
  rw [hsum, hd, hU, hcard] at hbound
  omega

lemma triangles_unique (hdeg : ∀ v, G.degree v = 3) (hs : SquareFree G)
    {A B : Finset V} (hA : G.IsNClique 3 A) (hB : G.IsNClique 3 B)
    {v : V} (hvA : v ∈ A) (hvB : v ∈ B) : A = B := by
  classical
  have hAc : (A.erase v).card = 2 := by
    have := Finset.card_erase_of_mem hvA
    have := hA.card_eq
    omega
  have hBc : (B.erase v).card = 2 := by
    have := Finset.card_erase_of_mem hvB
    have := hB.card_eq
    omega
  have hsub : A.erase v ∪ B.erase v ⊆ G.neighborFinset v := by
    intro x hx
    apply (G.mem_neighborFinset v x).mpr
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA.isClique hvA (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1.symm
    · exact hB.isClique hvB (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1.symm
  have hbound := Finset.card_le_card hsub
  have hrel := Finset.card_union_add_card_inter (A.erase v) (B.erase v)
  have hNc : (G.neighborFinset v).card = 3 := hdeg v
  have hpos : 0 < (A.erase v ∩ B.erase v).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  obtain ⟨hav, haA⟩ := Finset.mem_erase.mp (Finset.mem_inter.mp ha).1
  have haB := (Finset.mem_erase.mp (Finset.mem_inter.mp ha).2).2
  have hpair : ({v, a} : Finset V).card < B.card := by
    rw [hB.card_eq]
    simp [Ne.symm hav]
  obtain ⟨b, hbB, hbpair⟩ := Finset.exists_mem_notMem_of_card_lt_card hpair
  have hbne : b ≠ v ∧ b ≠ a := by simpa using hbpair
  have hbv : b ≠ v := hbne.1
  have hba : b ≠ a := hbne.2
  apply Finset.eq_of_subset_of_card_le ?_ (by rw [hA.card_eq, hB.card_eq])
  intro x hx
  by_cases hxv : x = v
  · simpa [hxv] using hvB
  by_cases hxa : x = a
  · simpa [hxa] using haB
  have hxb := hs v a hav.symm x b
    (hA.isClique hvA hx (Ne.symm hxv)) (hA.isClique haA hx (Ne.symm hxa))
    (hB.isClique hvB hbB hbv.symm) (hB.isClique haB hbB hba.symm)
  simpa [hxb] using hbB

theorem cubic_eight_has_square (hcard : Fintype.card V = 8)
    (hdeg : ∀ v, G.degree v = 3) : ¬ SquareFree G := by
  classical
  intro hs
  let T := G.cliqueFinset 3
  have hcover : T.biUnion id = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨a, b, hva, hvb, hab⟩ := triangle_at G hcard hdeg hs v
    apply Finset.mem_biUnion.mpr
    refine ⟨{v, a, b}, ?_, by simp⟩
    apply G.mem_cliqueFinset_iff.mpr
    constructor
    · simp only [Finset.coe_insert, Finset.coe_singleton]
      rw [SimpleGraph.isClique_insert]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.isClique_insert, hab]
      · intro x hx hxv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hva
        · exact hvb
    · simp [hva.ne, hvb.ne, hab.ne]
  have hdis : Set.PairwiseDisjoint (T : Set (Finset V)) (fun A : Finset V => A) := by
    intro A hA B hB hne
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    exact hne (triangles_unique G hdeg hs
      (G.mem_cliqueFinset_iff.mp hA) (G.mem_cliqueFinset_iff.mp hB) hvA hvB)
  have hsum : (T.biUnion id).card = T.card * 3 := by
    change (T.biUnion fun A => A).card = T.card * 3
    rw [Finset.card_biUnion hdis]
    calc
      ∑ A ∈ T, (id A).card = ∑ A ∈ T, 3 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact (G.mem_cliqueFinset_iff.mp hA).card_eq
      _ = T.card * 3 := by simp
  rw [hcover, Finset.card_univ, hcard] at hsum
  omega





/- Linear algebra adapted from woshuajolk's green SeedLocalObstruction.Obstruction proof. -/



open scoped BigOperators
open Finset

noncomputable section

def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

def Tight {k m : ℕ} (v : Fin m → Fin k → ℂ) : Prop :=
  ∀ S : Finset (Fin m), S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i

lemma pair_add_left {k : ℕ} (x z y : Fin k → ℂ) :
    pair (x + z) y = pair x y + pair z y := by
  simp [pair, add_mul, Finset.sum_add_distrib]

lemma pair_smul_left {k : ℕ} (c : ℂ) (x y : Fin k → ℂ) :
    pair (c • x) y = star c * pair x y := by
  unfold pair
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

lemma pair_add_right {k : ℕ} (x y z : Fin k → ℂ) :
    pair x (y + z) = pair x y + pair x z := by
  simp [pair, mul_add, Finset.sum_add_distrib]

lemma pair_smul_right {k : ℕ} (c : ℂ) (x y : Fin k → ℂ) :
    pair x (c • y) = c * pair x y := by
  unfold pair
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

lemma pair_star {k : ℕ} (x y : Fin k → ℂ) : star (pair x y) = pair y x := by
  unfold pair
  rw [star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [star_mul, star_star, mul_comm]

lemma pair_sum_left {n k : ℕ} (c : Fin n → ℂ) (x : Fin n → Fin k → ℂ)
    (y : Fin k → ℂ) :
    pair (∑ i, c i • x i) y = ∑ i, star (c i) * pair (x i) y := by
  have h : ∀ s : Finset (Fin n),
      pair (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, star (c i) * pair (x i) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [pair]
    | insert i s hi ih =>
        rw [sum_insert hi, sum_insert hi, pair_add_left, pair_smul_left, ih]
  simpa using h univ

lemma pair_self_ne_zero {k : ℕ} {x : Fin k → ℂ} (hx : x ≠ 0) : pair x x ≠ 0 := by
  obtain ⟨r₀, hr₀⟩ : ∃ r, x r ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext hc)
  have key : ∀ r : Fin k, star (x r) * x r = ((‖x r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    have h := Complex.conj_mul' (x r)
    simpa [Complex.star_def] using h
  have hsum : pair x x = ((∑ r, ‖x r‖ ^ 2 : ℝ) : ℂ) := by
    rw [pair, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun r _ => key r)
  rw [hsum]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r (_ : r ∈ Finset.univ) => sq_nonneg ‖x r‖)).1 hzero
  have hn : ‖x r₀‖ = 0 := by
    have h2 := hall r₀ (Finset.mem_univ r₀)
    nlinarith [norm_nonneg (x r₀)]
  exact hr₀ (norm_eq_zero.1 hn)

lemma pair_self_eq_zero {k : ℕ} {x : Fin k → ℂ} (h : pair x x = 0) : x = 0 := by
  by_contra hx
  exact pair_self_ne_zero hx h

def orthMap {n k : ℕ} (x : Fin n → Fin k → ℂ) :
    (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i =>
    { toFun := fun y => pair (x i) y
      map_add' := fun y z => pair_add_right (x i) y z
      map_smul' := fun c y => by
        simp [pair_smul_right, RingHom.id_apply] }

lemma orthMap_apply {n k : ℕ} (x : Fin n → Fin k → ℂ) (y : Fin k → ℂ) (i : Fin n) :
    orthMap x y i = pair (x i) y := rfl

theorem local_obstruction :
    ∀ (k m : ℕ) (v : Fin m → Fin k → ℂ),
      2 ≤ k →
      Tight v →
      ∀ j : ℕ, 2 ≤ j → j + 1 ≤ k →
        ∀ T : Finset (Fin m), T.card = j →
          ¬ ∃ U : Finset (Fin m),
              U.card = k + 1 - j ∧
              ∀ u ∈ U, ∀ t ∈ T, pair (v u) (v t) = 0 := by
  intro k m v hk htight j hj2 hjk T hTcard
  rintro ⟨U, hUcard, hUorth⟩
  have hTcard' : T.card + 1 ≤ k := by omega
  have hUcard' : U.card + 1 ≤ k := by omega
  have hTli : LinearIndependent ℂ (fun i : (T : Set (Fin m)) => v i) :=
    htight T hTcard'
  have hUli : LinearIndependent ℂ (fun i : (U : Set (Fin m)) => v i) :=
    htight U hUcard'
  let eT := T.orderIsoOfFin hTcard
  let nU := k + 1 - j
  let eU := U.orderIsoOfFin hUcard
  have hTli' : LinearIndependent ℂ (fun i : Fin j => v (eT i)) :=
    hTli.comp (fun i => (eT i : (T : Set (Fin m)))) eT.injective
  have hUli' : LinearIndependent ℂ (fun i : Fin nU => v (eU i)) :=
    hUli.comp (fun i => (eU i : (U : Set (Fin m)))) eU.injective
  let xT : Fin j → Fin k → ℂ := fun i => v (eT i)
  let φ := orthMap xT
  have hTspan :
      Module.finrank ℂ (Submodule.span ℂ (Set.range xT)) = j := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ) (b := xT)).mp hTli'
    simpa [Fintype.card_fin, Set.finrank] using h.symm
  have hUspan :
      Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun i : Fin nU => v (eU i))) = nU := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := ℂ)
      (b := fun i : Fin nU => v (eU i))).mp hUli'
    simpa [Fintype.card_fin, Set.finrank] using h.symm
  have hUker : ∀ i : Fin nU, φ (v (eU i)) = 0 := by
    intro i
    ext t
    have ht : (eT t : Fin m) ∈ T := (eT t).property
    have hu : (eU i : Fin m) ∈ U := (eU i).property
    have hvu : pair (v (eU i)) (v (eT t)) = 0 := hUorth _ hu _ ht
    have : pair (v (eT t)) (v (eU i)) = 0 := by
      have h := pair_star (v (eU i)) (v (eT t))
      simpa [hvu] using h.symm
    simpa [φ, orthMap_apply, xT] using this
  have hspanU_le_ker :
      Submodule.span ℂ (Set.range fun i : Fin nU => v (eU i)) ≤ LinearMap.ker φ := by
    intro w hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
    rw [LinearMap.mem_ker]
    have hmap : φ (∑ i, c i • v (eU i)) = ∑ i, c i • φ (v (eU i)) := by
      simp [map_sum, map_smul]
    rw [hmap]
    simp [hUker]
  have hUle : nU ≤ Module.finrank ℂ (LinearMap.ker φ) := by
    have hmono := Submodule.finrank_mono hspanU_le_ker
    exact hUspan.symm.trans_le hmono
  have hinf :
      Submodule.span ℂ (Set.range xT) ⊓ LinearMap.ker φ = ⊥ := by
    ext w
    constructor
    · intro hw
      have hwspan : w ∈ Submodule.span ℂ (Set.range xT) := hw.1
      have hwker : w ∈ LinearMap.ker φ := hw.2
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwspan
      have hφ0 : φ (∑ i, c i • xT i) = 0 := LinearMap.mem_ker.mp hwker
      have horth : ∀ i : Fin j, pair (xT i) (∑ t, c t • xT t) = 0 := by
        intro i
        have hi := congrArg (fun f : Fin j → ℂ => f i) hφ0
        simpa [φ, orthMap_apply] using hi
      have hself : pair (∑ i, c i • xT i) (∑ t, c t • xT t) = 0 := by
        rw [pair_sum_left]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [horth]
      exact pair_self_eq_zero hself
    · intro hw
      rw [Submodule.mem_bot] at hw
      subst hw
      exact ⟨Submodule.zero_mem _, LinearMap.mem_ker.mpr (map_zero φ)⟩
  have hsumle :
      Module.finrank ℂ (Submodule.span ℂ (Set.range xT)) +
        Module.finrank ℂ (LinearMap.ker φ)
        ≤ Module.finrank ℂ (Fin k → ℂ) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℂ (Set.range xT)) (LinearMap.ker φ)
    have hinf0 : Module.finrank ℂ
        (Submodule.span ℂ (Set.range xT) ⊓ LinearMap.ker φ :
          Submodule ℂ (Fin k → ℂ)) = 0 := by
      rw [hinf, finrank_bot]
    have hsuple : Module.finrank ℂ
        (Submodule.span ℂ (Set.range xT) ⊔ LinearMap.ker φ :
          Submodule ℂ (Fin k → ℂ))
          ≤ Module.finrank ℂ (Fin k → ℂ) := Submodule.finrank_le _
    omega
  have hV : Module.finrank ℂ (Fin k → ℂ) = k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hjnUle : j + nU ≤ k := by
    have hsum' := hsumle
    rw [hTspan, hV] at hsum'
    have hkerle : Module.finrank ℂ (LinearMap.ker φ) ≤ k - j := by omega
    have : nU ≤ k - j := le_trans hUle hkerle
    omega
  have hjnUeq : j + nU = k + 1 := by
    dsimp [nU]
    omega
  omega

end



def orthGraph {k m : ℕ} (v : Fin m → Fin k → ℂ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i i' => pair (v i) (v i') = 0

def seedExists (k m : ℕ) : Prop :=
  ∃ v : Fin m → Fin k → ℂ, ∃ N : Fin m → Finset (Fin m),
    (∀ i, v i ≠ 0) ∧
    (∀ i i', pair (v i) (v i') = 0 ↔ i' ∈ N i) ∧
    (∀ i, (N i).card = k) ∧
    (orthGraph v).Connected ∧
    (∀ S : Finset (Fin m), S.card + 1 ≤ k →
      LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i) ∧
    (∀ S : Finset (Fin m), S.card = k + 1 →
      ∀ a : Fin k → ℂ, a ≠ 0 → ∃ i ∈ S, pair a (v i) ≠ 0)

lemma orthGraph_pair {k m : ℕ} {v : Fin m → Fin k → ℂ} {a b : Fin m}
    (h : (orthGraph v).Adj a b) : pair (v a) (v b) = 0 := by
  rcases h.2 with h | h
  · exact h
  · have he := pair_star (v b) (v a)
    simpa [h] using he.symm

theorem proof : ¬ seedExists 3 8 := by
  classical
  rintro ⟨v, N, hnz, hN, hcard, hconn, htight, hspan⟩
  have hdeg : ∀ i, (orthGraph v).degree i = 3 := by
    intro i
    have heq : (orthGraph v).neighborFinset i = N i := by
      ext j
      rw [SimpleGraph.mem_neighborFinset]
      constructor
      · intro h
        exact (hN i j).mp (orthGraph_pair h)
      · intro h
        have hij : pair (v i) (v j) = 0 := (hN i j).mpr h
        refine ⟨?_, Or.inl hij⟩
        intro he
        subst j
        exact pair_self_ne_zero (hnz i) hij
    rw [← SimpleGraph.card_neighborFinset_eq_degree, heq, hcard]
  apply cubic_eight_has_square (orthGraph v) (by simp) hdeg
  intro a b hab x y hax hbx hay hby
  by_contra hxy
  have hT : ({a,b} : Finset (Fin 8)).card = 2 := by simp [hab]
  have hU : ({x,y} : Finset (Fin 8)).card = 3 + 1 - 2 := by simp [hxy]
  apply local_obstruction 3 8 v (by omega) htight 2 (by omega) (by omega) {a,b} hT
  refine ⟨{x,y}, hU, ?_⟩
  intro u hu t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu ht
  rcases hu with rfl | rfl <;> rcases ht with rfl | rfl
  · exact orthGraph_pair hax.symm
  · exact orthGraph_pair hbx.symm
  · exact orthGraph_pair hay.symm
  · exact orthGraph_pair hby.symm

#print axioms proof

end Submissions.NoSeedK3M8.SeedEight

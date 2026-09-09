import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic

open scoped Pointwise BigOperators Function

namespace Submissions.Erdos52NestedOverlap.CRT


theorem select_primes (m : ℕ) :
    ∃ p : Fin m → ℕ, Function.Injective p ∧ ∀ i, (p i).Prime ∧ 2 < p i := by
  classical
  let Q : Set ℕ := {p | p.Prime} \ {2}
  have hQ : Q.Infinite := Nat.infinite_setOfPred_prime.sdiff (Set.finite_singleton 2)
  let e : ℕ ↪ Q := hQ.natEmbedding Q
  refine ⟨fun i => (e i.val).val, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    exact e.injective (Subtype.ext h)
  · intro i
    have hi := (e i.val).prop
    have hp : ((e i.val).val).Prime := hi.1
    have hn : (e i.val).val ≠ 2 := hi.2
    exact ⟨hp, lt_of_le_of_ne hp.two_le (Ne.symm hn)⟩



theorem exists_arithmetic_witness {m : ℕ} (p : Fin m → ℕ)
    (hinj : Function.Injective p)
    (hp : ∀ i, (p i).Prime) (hodd : ∀ i, 2 < p i) :
    ∃ (S : ℕ) (a b : Fin m → ℕ),
      0 < S ∧
      (∀ i, 0 < a i ∧ 0 < b i ∧ a i + b i = S ∧
        p i ∣ b i ∧ ¬p i ∣ b i / p i) ∧
      (∀ i j, ¬p i ∣ a j) ∧
      (∀ i j, p i ∣ b j ↔ i = j) := by
  classical
  let modulus : Fin m → ℕ := fun i => (p i) ^ 2
  let residue (i j : Fin m) : ℕ := if i = j then p j else 2
  have hnonzero : ∀ i ∈ (Finset.univ : Finset (Fin m)), modulus i ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (hp i).ne_zero
  have hcop : Set.Pairwise (Finset.univ : Finset (Fin m))
      (Nat.Coprime on modulus) := by
    intro i _ j _ hij
    exact Nat.coprime_pow_primes 2 2 (hp i) (hp j) (fun h => hij (hinj h))
  let sol (i : Fin m) :=
    Nat.chineseRemainderOfFinset (residue i) modulus Finset.univ hnonzero hcop
  let b : Fin m → ℕ := fun i => (sol i).val
  let M : ℕ := ∏ j : Fin m, modulus j
  let S : ℕ := M + 1
  let a : Fin m → ℕ := fun i => S - b i
  have hspec (i j : Fin m) :
      b i ≡ (if i = j then p j else 2) [MOD (p j) ^ 2] := by
    change (sol i).val ≡ residue i j [MOD modulus j]
    exact (sol i).property j (Finset.mem_univ j)
  have hown (i : Fin m) : b i ≡ p i [MOD (p i) ^ 2] := by
    simpa using hspec i i
  have hother (i j : Fin m) (hij : i ≠ j) :
      b i ≡ 2 [MOD (p j) ^ 2] := by
    simpa only [if_neg hij] using hspec i j
  have hblt (i : Fin m) : b i < M :=
    Nat.chineseRemainderOfFinset_lt_prod (residue i) modulus hnonzero hcop
  have hbltS (i : Fin m) : b i < S :=
    lt_trans (hblt i) (Nat.lt_succ_self M)
  have hapos (i : Fin m) : 0 < a i := Nat.sub_pos_of_lt (hbltS i)
  have hasum (i : Fin m) : a i + b i = S := Nat.sub_add_cancel (hbltS i).le
  have hpdvdsq (i : Fin m) : p i ∣ (p i) ^ 2 := ⟨p i, pow_two (p i)⟩
  have hsqgt (i : Fin m) : p i < (p i) ^ 2 := by
    calc
      p i = p i * 1 := (Nat.mul_one (p i)).symm
      _ < p i * p i := Nat.mul_lt_mul_of_pos_left (hp i).one_lt (hp i).pos
      _ = (p i) ^ 2 := (pow_two (p i)).symm
  have hbdiv (i : Fin m) : p i ∣ b i :=
    ((hown i).dvd_iff (hpdvdsq i)).mpr (dvd_refl (p i))
  have hbnot2 (i : Fin m) : ¬(p i) ^ 2 ∣ b i := by
    intro hdiv
    have hsmall : (p i) ^ 2 ∣ p i :=
      ((hown i).dvd_iff (dvd_refl ((p i) ^ 2))).mp hdiv
    exact (not_le_of_gt (hsqgt i)) (Nat.le_of_dvd (hp i).pos hsmall)
  have hbpos (i : Fin m) : 0 < b i := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hbnot2 i
    rw [hz]
    exact dvd_zero _
  have hbquot (i : Fin m) : ¬p i ∣ b i / p i := by
    rintro ⟨c, hc⟩
    apply hbnot2 i
    refine ⟨c, ?_⟩
    calc
      b i = p i * (b i / p i) := (Nat.mul_div_cancel' (hbdiv i)).symm
      _ = p i * (p i * c) := by rw [hc]
      _ = (p i) ^ 2 * c := by rw [pow_two, mul_assoc]
  have hpdvdM (i : Fin m) : p i ∣ M := by
    have hsq : (p i) ^ 2 ∣ M :=
      Finset.dvd_prod_of_mem modulus (Finset.mem_univ i)
    exact (hpdvdsq i).trans hsq
  have hS (i : Fin m) : S ≡ 1 [MOD p i] := by
    have hz : M ≡ 0 [MOD p i] := Nat.modEq_zero_iff_dvd.mpr (hpdvdM i)
    simpa only [S, zero_add] using hz.add (Nat.ModEq.refl (n := p i) 1)
  have hafree (i j : Fin m) : ¬p i ∣ a j := by
    intro hdiv
    have hz : a j ≡ 0 [MOD p i] := Nat.modEq_zero_iff_dvd.mpr hdiv
    have hsum := hz.add (Nat.ModEq.refl (n := p i) (b j))
    simp only [hasum j, zero_add] at hsum
    have hbj1 : b j ≡ 1 [MOD p i] := hsum.symm.trans (hS i)
    by_cases hij : i = j
    · subst j
      exact (hp i).not_dvd_one
        ((hbj1.dvd_iff (dvd_refl (p i))).mp (hbdiv i))
    · have hbj2 : b j ≡ 2 [MOD p i] :=
        (hother j i (Ne.symm hij)).of_dvd (hpdvdsq i)
      have h21 : (2 : ℕ) ≡ 1 [MOD p i] := hbj2.symm.trans hbj1
      have hbad : (2 : ℕ) = 1 := h21.eq_of_lt_of_lt (hodd i) (hp i).one_lt
      exact (by decide : (2 : ℕ) ≠ 1) hbad
  have hbpattern (i j : Fin m) : p i ∣ b j ↔ i = j := by
    constructor
    · intro hdiv
      by_contra hij
      have hdiv2 : p i ∣ 2 :=
        ((hother j i (Ne.symm hij)).dvd_iff (hpdvdsq i)).mp hdiv
      exact (not_le_of_gt (hodd i)) (Nat.le_of_dvd (by decide : 0 < 2) hdiv2)
    · intro hij
      subst j
      exact hbdiv i
  exact ⟨S, a, b, Nat.zero_lt_succ M,
    fun i => ⟨hapos i, hbpos i, hasum i, hbdiv i, hbquot i⟩,
    hafree, hbpattern⟩



theorem nested_overlap_from_witnesses
    (m S : ℕ) (p a b : Fin m → ℕ) (_hS : 0 < S)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hsum : ∀ i, a i + b i = S)
    (hdiv : ∀ i, p i ∣ b i)
    (_hquot : ∀ i, ¬p i ∣ b i / p i)
    (hafree : ∀ i j, ¬p i ∣ a j)
    (hseparate : ∀ i j, p i ∣ b j ↔ i = j) :
    ∃ V : ℕ → Finset ℕ,
      V = (fun k => Finset.univ.image a ∪
        ((Finset.univ : Finset (Fin m)).filter fun i => k ≤ i.val).image b) ∧
      (∀ x ∈ V 0, 0 < x) ∧
      (∀ i : Fin m,
        V i.val = insert (b i) (V (i.val + 1)) ∧
        b i ∉ V (i.val + 1) ∧
        a i ∈ V (i.val + 1) ∧
        ∀ x ∈ V (i.val + 1), ¬p i ∣ x) ∧
      (∀ i : Fin m,
        ({a i} : Finset ℕ) + ({b i / p i} : Finset ℕ).image (fun x => p i * x) = {S}) ∧
      ((Finset.univ : Finset (Fin m)).filter fun i =>
        S ∈ ({a i} : Finset ℕ) +
          ({b i / p i} : Finset ℕ).image (fun x => p i * x)).card = m := by
  classical
  let V : ℕ → Finset ℕ := fun k => Finset.univ.image a ∪
    ((Finset.univ : Finset (Fin m)).filter fun i => k ≤ i.val).image b
  let F : Fin m → Finset ℕ := fun i =>
    ({a i} : Finset ℕ) + ({b i / p i} : Finset ℕ).image (fun x => p i * x)
  have hmem (k x : ℕ) :
      x ∈ V k ↔ (∃ j, a j = x) ∨ ∃ j, k ≤ j.val ∧ b j = x := by
    simp only [V, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hfree (i : Fin m) (x : ℕ) (hx : x ∈ V (i.val + 1)) : ¬p i ∣ x := by
    intro hd
    rcases (hmem _ _).mp hx with ⟨j, rfl⟩ | ⟨j, hj, rfl⟩
    · exact hafree i j hd
    · have hij : i = j := (hseparate i j).mp hd
      subst j
      exact Nat.not_add_one_le_self i.val hj
  have hF (i : Fin m) : F i = {S} := by
    dsimp only [F]
    rw [Finset.image_singleton, Finset.singleton_add_singleton,
      Nat.mul_div_cancel' (hdiv i), hsum i]
  refine ⟨V, rfl, ?_, ?_, hF, ?_⟩
  · intro x hx
    rcases (hmem _ _).mp hx with ⟨j, rfl⟩ | ⟨j, _, rfl⟩
    · exact ha j
    · exact hb j
  · intro i
    refine ⟨?_, ?_, ?_, hfree i⟩
    · apply Finset.ext
      intro x
      simp only [Finset.mem_insert, hmem]
      constructor
      · rintro (hax | ⟨j, hij, rfl⟩)
        · exact Or.inr (Or.inl hax)
        · rcases eq_or_lt_of_le hij with hij | hij
          · have hji : j = i := Fin.ext hij.symm
            subst j
            exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨j, Nat.succ_le_of_lt hij, rfl⟩)
      · rintro (rfl | hax | ⟨j, hij, rfl⟩)
        · exact Or.inr ⟨i, le_rfl, rfl⟩
        · exact Or.inl hax
        · exact Or.inr ⟨j, (Nat.le_succ i.val).trans hij, rfl⟩
    · intro hx
      exact hfree i (b i) hx (hdiv i)
    · exact (hmem _ _).mpr (Or.inl ⟨i, rfl⟩)
  · change ((Finset.univ : Finset (Fin m)).filter fun i => S ∈ F i).card = m
    simp [hF]


theorem proof :
    ∀ m : ℕ, ∃ (S : ℕ) (V : ℕ → Finset ℕ) (p a b : Fin m → ℕ),
      0 < S ∧
      (∀ x ∈ V 0, 0 < x) ∧
      Function.Injective p ∧
      (∀ i : Fin m,
        (p i).Prime ∧ 2 < p i ∧
        V i.val = insert (b i) (V (i.val + 1)) ∧
        b i ∉ V (i.val + 1) ∧
        a i ∈ V (i.val + 1) ∧
        (∀ x ∈ V (i.val + 1), ¬p i ∣ x) ∧
        p i ∣ b i ∧ ¬p i ∣ b i / p i) ∧
      (∀ i : Fin m,
        ({a i} : Finset ℕ) + ({b i / p i} : Finset ℕ).image (fun y => p i * y) = {S}) ∧
      ((Finset.univ : Finset (Fin m)).filter fun i =>
        S ∈ ({a i} : Finset ℕ) +
          ({b i / p i} : Finset ℕ).image (fun y => p i * y)).card = m := by
  intro m
  obtain ⟨p, hinj, hp⟩ := select_primes m
  obtain ⟨S, a, b, hS, hab, hafree, hseparate⟩ :=
    exists_arithmetic_witness p hinj (fun i => (hp i).1) (fun i => (hp i).2)
  obtain ⟨V, _, hV, hnode, hF, hcount⟩ :=
    nested_overlap_from_witnesses m S p a b hS
      (fun i => (hab i).1) (fun i => (hab i).2.1)
      (fun i => (hab i).2.2.1) (fun i => (hab i).2.2.2.1)
      (fun i => (hab i).2.2.2.2) hafree hseparate
  refine ⟨S, V, p, a, b, hS, hV, hinj, ?_, hF, hcount⟩
  intro i
  exact ⟨(hp i).1, (hp i).2, (hnode i).1, (hnode i).2.1,
    (hnode i).2.2.1, (hnode i).2.2.2, (hab i).2.2.2.1, (hab i).2.2.2.2⟩

end Submissions.Erdos52NestedOverlap.CRT

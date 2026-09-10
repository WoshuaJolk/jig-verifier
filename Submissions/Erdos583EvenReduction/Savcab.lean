import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ReduceOption
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Group.Nat.Even

namespace Submissions.Erdos583EvenReduction.Savcab

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V, p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b → ∃! p : List V, p ∈ paths ∧ PathUses p a b

def leafGraph {V : Type} (G : SimpleGraph V) (c : V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some b => b = c
    | some a, none => a = c
    | some a, some b => G.Adj a b
  symm := ⟨by
    intro a b h
    cases a with
    | none => cases b <;> exact h
    | some a =>
        cases b with
        | none => exact h
        | some b => exact h.symm⟩
  loopless := ⟨by
    intro a h
    cases a with
    | none => exact h
    | some a => exact G.irrefl h⟩

@[simp] theorem not_pathUses_nil {V : Type} (a b : V) :
    ¬PathUses [] a b := by
  rintro ⟨l, r, h | h⟩ <;>
    have hh := congrArg List.length h <;>
    simp only [List.length_append, List.length_cons, List.length_nil] at hh <;> omega

@[simp] theorem not_pathUses_singleton {V : Type} (x a b : V) :
    ¬PathUses [x] a b := by
  rintro ⟨l, r, h | h⟩ <;>
    have hh := congrArg List.length h <;>
    simp only [List.length_append, List.length_cons, List.length_nil] at hh <;> omega

theorem pathUses_cons_cons {V : Type} (x y a b : V) (r : List V) :
    PathUses (x :: y :: r) a b ↔
      ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ∨ PathUses (y :: r) a b := by
  constructor
  · rintro ⟨l, s, h | h⟩
    · cases l with
      | nil =>
          have hh := List.cons.inj h
          exact Or.inl (Or.inl ⟨hh.1, (List.cons.inj hh.2).1⟩)
      | cons z l => exact Or.inr ⟨l, s, Or.inl (List.cons.inj h).2⟩
    · cases l with
      | nil =>
          have hh := List.cons.inj h
          exact Or.inl (Or.inr ⟨hh.1, (List.cons.inj hh.2).1⟩)
      | cons z l => exact Or.inr ⟨l, s, Or.inr (List.cons.inj h).2⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨[], r, Or.inl rfl⟩
      · exact ⟨[], r, Or.inr rfl⟩
    · rcases h with ⟨l, s, h | h⟩
      · exact ⟨x :: l, s, Or.inl (congrArg (List.cons x) h)⟩
      · exact ⟨x :: l, s, Or.inr (congrArg (List.cons x) h)⟩

@[simp] theorem pathUses_none_cons {V : Type} (p : List (Option V)) (a b : V) :
    PathUses (none :: p) (some a) (some b) ↔ PathUses p (some a) (some b) := by
  cases p with
  | nil => simp
  | cons x p => simp [pathUses_cons_cons]

theorem isPath_tail {V : Type} {G : SimpleGraph V} {x : V} {p : List V}
    (h : IsPath G (x :: p)) : IsPath G p := by
  have hc : List.IsChain G.Adj (x :: p) := h.2
  exact ⟨(List.nodup_cons.mp h.1).2, hc.tail⟩

theorem nodup_reduceOption {V : Type} (p : List (Option V)) :
    p.Nodup → p.reduceOption.Nodup := by
  induction p with
  | nil => intro h; simpa using h
  | cons x p ih =>
      intro h
      have hn := List.nodup_cons.mp h
      cases x with
      | none => simpa using ih hn.2
      | some a =>
          simp only [List.reduceOption_cons_of_some, List.nodup_cons]
          exact ⟨fun ha => hn.1 (List.reduceOption_mem_iff.mp ha), ih hn.2⟩

theorem no_internal_none {V : Type} {G : SimpleGraph V} {c : V}
    {a b : Option V} {r : List (Option V)}
    (h : IsPath (leafGraph G c) (a :: none :: b :: r)) : False := by
  have hc : List.IsChain (leafGraph G c).Adj (a :: none :: b :: r) := h.2
  have ha := (List.isChain_cons_cons.mp hc).1
  have hb := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hc).2).1
  cases a with
  | none => exact ha
  | some a =>
      cases b with
      | none => exact hb
      | some b =>
          have hac : a = c := ha
          have hbc : b = c := hb
          have hn := (List.nodup_cons.mp h.1).1
          apply hn
          simp [hac, hbc]

theorem chain_reduceOption {V : Type} (G : SimpleGraph V) (c : V)
    (p : List (Option V)) :
    IsPath (leafGraph G c) p → List.IsChain G.Adj p.reduceOption := by
  induction p with
  | nil => intro h; exact .nil
  | cons x p ih =>
      intro h
      have ht := isPath_tail h
      cases x with
      | none => simpa using ih ht
      | some a =>
          cases p with
          | nil => exact .singleton a
          | cons y p =>
              cases y with
              | none =>
                  cases p with
                  | nil => exact .singleton a
                  | cons z p => exact (no_internal_none h).elim
              | some b =>
                  have hc : List.IsChain (leafGraph G c).Adj (some a :: some b :: p) := h.2
                  have hab : G.Adj a b := (List.isChain_cons_cons.mp hc).1
                  exact .cons_cons hab (ih ht)

theorem isPath_reduceOption {V : Type} {G : SimpleGraph V} {c : V}
    {p : List (Option V)} (h : IsPath (leafGraph G c) p) : IsPath G p.reduceOption :=
  ⟨nodup_reduceOption p h.1, chain_reduceOption G c p h⟩

theorem pathUses_reduceOption_iff {V : Type} (G : SimpleGraph V) (c : V)
    (p : List (Option V)) :
    IsPath (leafGraph G c) p → ∀ a b : V,
      PathUses p (some a) (some b) ↔ PathUses p.reduceOption a b := by
  induction p with
  | nil => intro h a b; simp
  | cons x p ih =>
      intro h a b
      have ht := isPath_tail h
      cases x with
      | none => simpa only [pathUses_none_cons, List.reduceOption_cons_of_none] using ih ht a b
      | some x =>
          cases p with
          | nil => simp
          | cons y p =>
              cases y with
              | none =>
                  cases p with
                  | nil => simp [pathUses_cons_cons]
                  | cons z p => exact (no_internal_none h).elim
              | some y =>
                  change PathUses (some x :: some y :: p) (some a) (some b) ↔
                    PathUses (x :: y :: p.reduceOption) a b
                  rw [pathUses_cons_cons, pathUses_cons_cons]
                  simp only [Option.some.injEq]
                  exact or_congr Iff.rfl (ih ht a b)

theorem leaf_removal {V : Type} {G : SimpleGraph V} {c : V}
    {p : List (Option V)} (h : IsPath (leafGraph G c) p) :
    IsPath G p.reduceOption ∧
      ∀ a b : V, PathUses p (some a) (some b) ↔ PathUses p.reduceOption a b :=
  ⟨isPath_reduceOption h, pathUses_reduceOption_iff G c p h⟩

theorem decomposition_reduceOption {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {c : V} {paths : Finset (List (Option V))}
    (h : IsPathDecomposition (leafGraph G c) paths) :
    IsPathDecomposition G (paths.image List.reduceOption) := by
  constructor
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact isPath_reduceOption (h.1 q hq)
  · intro a b hab
    have hab' : (leafGraph G c).Adj (some a) (some b) := hab
    obtain ⟨p, hp, hu⟩ := h.2 hab'
    refine ⟨p.reduceOption, ⟨Finset.mem_image_of_mem _ hp.1,
      (pathUses_reduceOption_iff G c p (h.1 p hp.1) a b).mp hp.2⟩, ?_⟩
    intro q hq
    obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hq.1
    have hru : PathUses r (some a) (some b) :=
      (pathUses_reduceOption_iff G c r (h.1 r hr) a b).mpr (by simpa only [hrq] using hq.2)
    exact hrq.symm.trans (congrArg List.reduceOption (hu r ⟨hr, hru⟩))

theorem leaf_decomposition_removal {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {c : V} {paths : Finset (List (Option V))}
    (h : IsPathDecomposition (leafGraph G c) paths) :
    ∃ paths' : Finset (List V),
      paths'.card ≤ paths.card ∧ IsPathDecomposition G paths' :=
  ⟨paths.image List.reduceOption, Finset.card_image_le, decomposition_reduceOption h⟩


theorem pathUses_map {V W : Type} (f : V → W) {p : List V} {a b : V}
    (h : PathUses p a b) : PathUses (p.map f) (f a) (f b) := by
  obtain ⟨l, r, h | h⟩ := h
  · exact ⟨l.map f, r.map f, Or.inl (by simp [h])⟩
  · exact ⟨l.map f, r.map f, Or.inr (by simp [h])⟩

theorem pathUses_map_iff {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {p : List V} {a b : V} :
    PathUses (p.map e) (e a) (e b) ↔ PathUses p a b := by
  refine ⟨fun h => ?_, pathUses_map e⟩
  simpa [List.map_map, Function.comp_def] using pathUses_map e.symm h

theorem isPath_map_iff {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (p : List V) : IsPath H (p.map e) ↔ IsPath G p := by
  simp only [IsPath, List.Chain', List.nodup_map_iff e.injective,
    List.isChain_map, e.map_adj_iff]

theorem decomposition_map {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {paths : Finset (List V)} (h : IsPathDecomposition G paths) :
    IsPathDecomposition H (paths.image (List.map e)) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (isPath_map_iff e p).2 (h.1 p hp)
  · intro a b hab
    obtain ⟨p, hp, huniq⟩ := h.2 (e.symm.map_adj_iff.mpr hab)
    refine ⟨p.map e, ⟨Finset.mem_image.mpr ⟨p, hp.1, rfl⟩, ?_⟩, ?_⟩
    · simpa using pathUses_map e hp.2
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq.1
      have huses : PathUses r (e.symm a) (e.symm b) := by
        simpa [List.map_map, Function.comp_def] using pathUses_map e.symm hq.2
      exact congrArg (List.map e) (huniq r ⟨hr, huses⟩)

theorem decomposition_map_card {V W : Type} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (paths : Finset (List V)) : (paths.image (List.map e)).card = paths.card :=
  Finset.card_image_of_injective paths e.injective.list_map

theorem decomposition_map_iff {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (paths : Finset (List V)) :
    IsPathDecomposition H (paths.image (List.map e)) ↔ IsPathDecomposition G paths := by
  refine ⟨fun h => ?_, decomposition_map e⟩
  simpa [Finset.image_image, List.map_map, Function.comp_def] using
    decomposition_map e.symm h

theorem exists_decomposition_card_le_iff {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ) :
    (∃ paths : Finset (List V), IsPathDecomposition G paths ∧ paths.card ≤ k) ↔
    (∃ paths : Finset (List W), IsPathDecomposition H paths ∧ paths.card ≤ k) := by
  constructor
  · rintro ⟨paths, hpaths, hcard⟩
    exact ⟨paths.image (List.map e), decomposition_map e hpaths,
      by simpa only [decomposition_map_card] using hcard⟩
  · rintro ⟨paths, hpaths, hcard⟩
    exact ⟨paths.image (List.map e.symm), decomposition_map e.symm hpaths,
      by simpa only [decomposition_map_card] using hcard⟩


theorem leaf_connected {V : Type} (G : SimpleGraph V) (c : V)
    (hg : G.Connected) : (leafGraph G c).Connected := by
  have reach : ∀ x, (leafGraph G c).Reachable (some c) x := by
    intro x
    cases x with
    | none =>
      exact SimpleGraph.Adj.reachable (show (leafGraph G c).Adj (some c) none from rfl)
    | some x =>
      let f : G →g leafGraph G c := ⟨Option.some, fun h => h⟩
      exact (hg c x).map f
  exact ⟨fun x y => (reach x).symm.trans (reach y)⟩

abbrev FullGallai : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.Connected →
    ∃ paths : Finset (List (Fin n)),
      paths.card ≤ (n + 1) / 2 ∧ IsPathDecomposition G paths

abbrev EvenGallai : Prop :=
  ∀ n : ℕ, Even n → ∀ G : SimpleGraph (Fin n), G.Connected →
    ∃ paths : Finset (List (Fin n)),
      paths.card ≤ n / 2 ∧ IsPathDecomposition G paths

theorem full_iff_even : FullGallai ↔ EvenGallai := by
  classical
  constructor
  · intro hf n hn G hg
    obtain ⟨p, hp, hd⟩ := hf n G hg
    refine ⟨p, ?_, hd⟩
    have he := Nat.even_iff.mp hn
    omega
  · intro he n G hg
    by_cases hn : Even n
    · obtain ⟨p, hp, hd⟩ := he n hn G hg
      exact ⟨p, by omega, hd⟩
    · let c : Fin n := Classical.choice hg.nonempty
      let H := leafGraph G c
      let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquivLast
      let K : SimpleGraph (Fin (n + 1)) := H.comap e
      let iso : K ≃g H := SimpleGraph.Iso.comap e H
      have hc : H.Connected := leaf_connected G c hg
      have hK : K.Connected := hc.map iso.symm.toHom iso.symm.surjective
      have hn' : Even (n + 1) := by
        rw [Nat.even_iff] at hn ⊢
        omega
      obtain ⟨p, hp, hd⟩ := he (n + 1) hn' K hK
      have hdH : IsPathDecomposition H (p.image (List.map iso)) := decomposition_map iso hd
      obtain ⟨q, hq, hdG⟩ := leaf_decomposition_removal hdH
      refine ⟨q, ?_, hdG⟩
      rw [decomposition_map_card] at hq
      exact hq.trans hp

end Submissions.Erdos583EvenReduction.Savcab

import Init

namespace Submissions.J4P26ExchangeDepth.Proof

def card (m : Nat) : Nat :=
  ((List.range 15).filter (fun x => m.testBit x)).length

def removed (m : Nat) : Nat :=
  ([0, 1, 2, 4, 5, 9, 10, 12, 14].filter (fun x => !(m.testBit x))).length

abbrev APFree (m : Nat) : Prop :=
  ∀ a : Fin 15, ∀ d : Fin 5, 0 < d.val → a.val + 3*d.val < 15 →
    (m.testBit a.val && m.testBit (a.val+d.val) &&
      m.testBit (a.val+2*d.val) && m.testBit (a.val+3*d.val)) = false

theorem block_0 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (0+32*mid.val+lo.val) →
    APFree (0+32*mid.val+lo.val) →
    0+32*mid.val+lo.val = 27099 ∨ 0+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_1 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (1024+32*mid.val+lo.val) →
    APFree (1024+32*mid.val+lo.val) →
    1024+32*mid.val+lo.val = 27099 ∨ 1024+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_2 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (2048+32*mid.val+lo.val) →
    APFree (2048+32*mid.val+lo.val) →
    2048+32*mid.val+lo.val = 27099 ∨ 2048+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_3 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (3072+32*mid.val+lo.val) →
    APFree (3072+32*mid.val+lo.val) →
    3072+32*mid.val+lo.val = 27099 ∨ 3072+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_4 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (4096+32*mid.val+lo.val) →
    APFree (4096+32*mid.val+lo.val) →
    4096+32*mid.val+lo.val = 27099 ∨ 4096+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_5 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (5120+32*mid.val+lo.val) →
    APFree (5120+32*mid.val+lo.val) →
    5120+32*mid.val+lo.val = 27099 ∨ 5120+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_6 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (6144+32*mid.val+lo.val) →
    APFree (6144+32*mid.val+lo.val) →
    6144+32*mid.val+lo.val = 27099 ∨ 6144+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_7 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (7168+32*mid.val+lo.val) →
    APFree (7168+32*mid.val+lo.val) →
    7168+32*mid.val+lo.val = 27099 ∨ 7168+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_8 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (8192+32*mid.val+lo.val) →
    APFree (8192+32*mid.val+lo.val) →
    8192+32*mid.val+lo.val = 27099 ∨ 8192+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_9 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (9216+32*mid.val+lo.val) →
    APFree (9216+32*mid.val+lo.val) →
    9216+32*mid.val+lo.val = 27099 ∨ 9216+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_10 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (10240+32*mid.val+lo.val) →
    APFree (10240+32*mid.val+lo.val) →
    10240+32*mid.val+lo.val = 27099 ∨ 10240+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_11 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (11264+32*mid.val+lo.val) →
    APFree (11264+32*mid.val+lo.val) →
    11264+32*mid.val+lo.val = 27099 ∨ 11264+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_12 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (12288+32*mid.val+lo.val) →
    APFree (12288+32*mid.val+lo.val) →
    12288+32*mid.val+lo.val = 27099 ∨ 12288+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_13 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (13312+32*mid.val+lo.val) →
    APFree (13312+32*mid.val+lo.val) →
    13312+32*mid.val+lo.val = 27099 ∨ 13312+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_14 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (14336+32*mid.val+lo.val) →
    APFree (14336+32*mid.val+lo.val) →
    14336+32*mid.val+lo.val = 27099 ∨ 14336+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_15 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (15360+32*mid.val+lo.val) →
    APFree (15360+32*mid.val+lo.val) →
    15360+32*mid.val+lo.val = 27099 ∨ 15360+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_16 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (16384+32*mid.val+lo.val) →
    APFree (16384+32*mid.val+lo.val) →
    16384+32*mid.val+lo.val = 27099 ∨ 16384+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_17 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (17408+32*mid.val+lo.val) →
    APFree (17408+32*mid.val+lo.val) →
    17408+32*mid.val+lo.val = 27099 ∨ 17408+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_18 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (18432+32*mid.val+lo.val) →
    APFree (18432+32*mid.val+lo.val) →
    18432+32*mid.val+lo.val = 27099 ∨ 18432+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_19 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (19456+32*mid.val+lo.val) →
    APFree (19456+32*mid.val+lo.val) →
    19456+32*mid.val+lo.val = 27099 ∨ 19456+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_20 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (20480+32*mid.val+lo.val) →
    APFree (20480+32*mid.val+lo.val) →
    20480+32*mid.val+lo.val = 27099 ∨ 20480+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_21 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (21504+32*mid.val+lo.val) →
    APFree (21504+32*mid.val+lo.val) →
    21504+32*mid.val+lo.val = 27099 ∨ 21504+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_22 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (22528+32*mid.val+lo.val) →
    APFree (22528+32*mid.val+lo.val) →
    22528+32*mid.val+lo.val = 27099 ∨ 22528+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_23 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (23552+32*mid.val+lo.val) →
    APFree (23552+32*mid.val+lo.val) →
    23552+32*mid.val+lo.val = 27099 ∨ 23552+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_24 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (24576+32*mid.val+lo.val) →
    APFree (24576+32*mid.val+lo.val) →
    24576+32*mid.val+lo.val = 27099 ∨ 24576+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_25 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (25600+32*mid.val+lo.val) →
    APFree (25600+32*mid.val+lo.val) →
    25600+32*mid.val+lo.val = 27099 ∨ 25600+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_26 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (26624+32*mid.val+lo.val) →
    APFree (26624+32*mid.val+lo.val) →
    26624+32*mid.val+lo.val = 27099 ∨ 26624+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_27 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (27648+32*mid.val+lo.val) →
    APFree (27648+32*mid.val+lo.val) →
    27648+32*mid.val+lo.val = 27099 ∨ 27648+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_28 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (28672+32*mid.val+lo.val) →
    APFree (28672+32*mid.val+lo.val) →
    28672+32*mid.val+lo.val = 27099 ∨ 28672+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_29 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (29696+32*mid.val+lo.val) →
    APFree (29696+32*mid.val+lo.val) →
    29696+32*mid.val+lo.val = 27099 ∨ 29696+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_30 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (30720+32*mid.val+lo.val) →
    APFree (30720+32*mid.val+lo.val) →
    30720+32*mid.val+lo.val = 27099 ∨ 30720+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem block_31 : ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (31744+32*mid.val+lo.val) →
    APFree (31744+32*mid.val+lo.val) →
    31744+32*mid.val+lo.val = 27099 ∨ 31744+32*mid.val+lo.val = 28107 := by
  unfold card APFree
  decide

theorem classify_digits : ∀ hi : Fin 32, ∀ mid : Fin 32, ∀ lo : Fin 32,
    10 ≤ card (1024*hi.val+32*mid.val+lo.val) →
    APFree (1024*hi.val+32*mid.val+lo.val) →
    1024*hi.val+32*mid.val+lo.val = 27099 ∨
    1024*hi.val+32*mid.val+lo.val = 28107 := by
  intro hi
  have hs : hi.val = 0 ∨ hi.val = 1 ∨ hi.val = 2 ∨ hi.val = 3 ∨ hi.val = 4 ∨ hi.val = 5 ∨ hi.val = 6 ∨ hi.val = 7 ∨ hi.val = 8 ∨ hi.val = 9 ∨ hi.val = 10 ∨ hi.val = 11 ∨ hi.val = 12 ∨ hi.val = 13 ∨ hi.val = 14 ∨ hi.val = 15 ∨ hi.val = 16 ∨ hi.val = 17 ∨ hi.val = 18 ∨ hi.val = 19 ∨ hi.val = 20 ∨ hi.val = 21 ∨ hi.val = 22 ∨ hi.val = 23 ∨ hi.val = 24 ∨ hi.val = 25 ∨ hi.val = 26 ∨ hi.val = 27 ∨ hi.val = 28 ∨ hi.val = 29 ∨ hi.val = 30 ∨ hi.val = 31 := by omega
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · simp only [h]
    exact block_0
  · simp only [h]
    exact block_1
  · simp only [h]
    exact block_2
  · simp only [h]
    exact block_3
  · simp only [h]
    exact block_4
  · simp only [h]
    exact block_5
  · simp only [h]
    exact block_6
  · simp only [h]
    exact block_7
  · simp only [h]
    exact block_8
  · simp only [h]
    exact block_9
  · simp only [h]
    exact block_10
  · simp only [h]
    exact block_11
  · simp only [h]
    exact block_12
  · simp only [h]
    exact block_13
  · simp only [h]
    exact block_14
  · simp only [h]
    exact block_15
  · simp only [h]
    exact block_16
  · simp only [h]
    exact block_17
  · simp only [h]
    exact block_18
  · simp only [h]
    exact block_19
  · simp only [h]
    exact block_20
  · simp only [h]
    exact block_21
  · simp only [h]
    exact block_22
  · simp only [h]
    exact block_23
  · simp only [h]
    exact block_24
  · simp only [h]
    exact block_25
  · simp only [h]
    exact block_26
  · simp only [h]
    exact block_27
  · simp only [h]
    exact block_28
  · simp only [h]
    exact block_29
  · simp only [h]
    exact block_30
  · simp only [h]
    exact block_31

theorem classification (m : Fin 32768) :
    10 ≤ card m.val → APFree m.val → m.val = 27099 ∨ m.val = 28107 := by
  have H := classify_digits ⟨m.val/1024, by omega⟩
    ⟨(m.val%1024)/32, by omega⟩ ⟨m.val%32, by omega⟩
  change (10 ≤ card (1024*(m.val/1024)+32*((m.val%1024)/32)+m.val%32) →
    APFree (1024*(m.val/1024)+32*((m.val%1024)/32)+m.val%32) →
    1024*(m.val/1024)+32*((m.val%1024)/32)+m.val%32 = 27099 ∨
    1024*(m.val/1024)+32*((m.val%1024)/32)+m.val%32 = 28107) at H
  have hn : 1024*(m.val/1024)+32*((m.val%1024)/32)+m.val%32 = m.val := by omega
  simpa only [hn] using H

theorem cardinality_bound (m : Fin 32768) (hf : APFree m.val) :
    card m.val ≤ 10 := by
  by_cases hc : 10 ≤ card m.val
  · rcases classification m hc hf with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  · omega

theorem escape_depth (m : Fin 32768) (hf : APFree m.val)
    (hc : 9 < card m.val) : removed m.val = 5 := by
  rcases classification m (by omega) hf with h | h
  · rw [h]
    decide
  · rw [h]
    decide

theorem witness_data : APFree 22071 ∧ card 22071 = 9 ∧
    APFree 28107 ∧ card 28107 = 10 ∧ removed 28107 = 5 ∧
    (∀ x : Fin 15, (22071).testBit x.val = [0, 1, 2, 4, 5, 9, 10, 12, 14].contains x.val) := by
  unfold APFree card removed
  decide

theorem solves :
(∀ (m : Fin 32768),
10 ≤ card m.val → APFree m.val → m.val = 27099 ∨ m.val = 28107) ∧
(∀ (m : Fin 32768) (hf : APFree m.val),
card m.val ≤ 10) ∧
(∀ (m : Fin 32768) (hf : APFree m.val)
    (hc : 9 < card m.val),
removed m.val = 5) ∧
(APFree 22071 ∧ card 22071 = 9 ∧
    APFree 28107 ∧ card 28107 = 10 ∧ removed 28107 = 5 ∧
    (∀ x : Fin 15, (22071).testBit x.val = [0, 1, 2, 4, 5, 9, 10, 12, 14].contains x.val)) := by
  exact ⟨@classification, @cardinality_bound, @escape_depth, @witness_data⟩

end Submissions.J4P26ExchangeDepth.Proof


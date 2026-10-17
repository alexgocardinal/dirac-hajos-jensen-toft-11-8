import D5Structure

/-!
Four-color obstruction for the actual 23-vertex graph D5 after deleting 01.
The earlier finite rigidity is imported through compiled modules.
Run: lake env lean D5NoFour.lean
-/

namespace DiracHajos

def firstCopy (c : List (Fin 4)) : List (Fin 4) :=
  (List.range 12).map fun i => c.getD i 0

def secondCopy (c : List (Fin 4)) : List (Fin 4) :=
  (List.range 12).map fun i => c.getD (secondIndex i) 0

private theorem firstCopy_length (c : List (Fin 4)) :
    (firstCopy c).length = 12 := by simp [firstCopy]

private theorem secondCopy_length (c : List (Fin 4)) :
    (secondCopy c).length = 12 := by simp [secondCopy]

private theorem firstCopy_getD (c : List (Fin 4)) (i : Nat) (hi : i < 12) :
    (firstCopy c).getD i 0 = c.getD i 0 := by
  simp [firstCopy, List.getD, hi]

private theorem secondCopy_getD (c : List (Fin 4)) (i : Nat) (hi : i < 12) :
    (secondCopy c).getD i 0 = c.getD (secondIndex i) 0 := by
  simp [secondCopy, List.getD, hi]

private theorem secondIndex_injective : Function.Injective secondIndex := by
  intro a b h
  unfold secondIndex at h
  split_ifs at h <;> omega

private theorem secondIndex_pair_not_01 (e : Nat × Nat)
    (h : e ≠ (0, 1)) :
    (secondIndex e.1, secondIndex e.2) ≠ (0, 1) := by
  intro hp
  have h0 : secondIndex e.1 = secondIndex 0 := by
    simpa [secondIndex] using congrArg Prod.fst hp
  have h1 : secondIndex e.2 = secondIndex 1 := by
    simpa [secondIndex] using congrArg Prod.snd hp
  apply h
  exact Prod.ext (secondIndex_injective h0) (secondIndex_injective h1)

private theorem firstCopy_valid (c : List (Fin 4))
    (hp : properD5Minus01 c = true) :
    validPrefixFour (firstCopy c) = true := by
  unfold properD5Minus01 at hp
  unfold validPrefixFour
  apply List.all_eq_true.mpr
  intro e he
  by_cases hskip : e = (0, 3) ∨ e = (0, 1) ∨
      e.2 ≥ (firstCopy c).length
  · simp only [if_pos hskip]
  have h01 : e ≠ (0, 1) := by tauto
  have h03 : e ≠ (0, 3) := by tauto
  have hm : e ∈ d5OutputEdges := by
    have hh := (List.all_eq_true.mp d5_base_edges_present.1) e he
    have hh' : e = (0, 1) ∨ e = (0, 3) ∨ e ∈ d5OutputEdges := by
      simpa using hh
    tauto
  have hh := (List.all_eq_true.mp hp) e hm
  have hne : c.getD e.1 0 != c.getD e.2 0 := by
    simpa only [if_neg h01] using hh
  have hlt2 : e.2 < 12 := by
    have hlen := firstCopy_length c
    omega
  have horder : e.1 < e.2 := by
    have hh := (List.all_eq_true.mp edgesOrdered) e he
    simpa using hh
  have hlt1 : e.1 < 12 := by omega
  simpa only [if_neg hskip, firstCopy_getD c e.1 hlt1,
    firstCopy_getD c e.2 hlt2] using hne

private theorem secondCopy_valid (c : List (Fin 4))
    (hp : properD5Minus01 c = true) :
    validPrefixFour (secondCopy c) = true := by
  unfold properD5Minus01 at hp
  unfold validPrefixFour
  apply List.all_eq_true.mpr
  intro e he
  by_cases hskip : e = (0, 3) ∨ e = (0, 1) ∨
      e.2 ≥ (secondCopy c).length
  · simp only [if_pos hskip]
  have h01 : e ≠ (0, 1) := by tauto
  have h03 : e ≠ (0, 3) := by tauto
  have hm : (secondIndex e.1, secondIndex e.2) ∈ d5OutputEdges := by
    have hh := (List.all_eq_true.mp d5_base_edges_present.2) e he
    have hh' : e = (0, 1) ∨ e = (0, 3) ∨
        (secondIndex e.1, secondIndex e.2) ∈ d5OutputEdges := by
      simpa using hh
    tauto
  have hh := (List.all_eq_true.mp hp)
    (secondIndex e.1, secondIndex e.2) hm
  have hne : c.getD (secondIndex e.1) 0 !=
      c.getD (secondIndex e.2) 0 := by
    simpa only [if_neg (secondIndex_pair_not_01 e h01)] using hh
  have hlt2 : e.2 < 12 := by
    have hlen := secondCopy_length c
    omega
  have horder : e.1 < e.2 := by
    have hh := (List.all_eq_true.mp edgesOrdered) e he
    simpa using hh
  have hlt1 : e.1 < 12 := by omega
  simpa only [if_neg hskip, secondCopy_getD c e.1 hlt1,
    secondCopy_getD c e.2 hlt2] using hne

private theorem firstCopy_avoids (c : List (Fin 4))
    (hp : properD5Minus01 c = true) :
    ∀ i : Nat, i < (firstCopy c).length →
      (firstCopy c).getD i 0 ≠ c.getD 21 0 := by
  unfold properD5Minus01 at hp
  intro i hi
  have hi12 : i < 12 := by simpa [firstCopy] using hi
  have hm : (i, 21) ∈ d5OutputEdges := by
    have hh := (List.all_eq_true.mp d5_clique_adjacencies.1) i
      (List.mem_range.mpr hi12)
    simpa using hh
  have hh := (List.all_eq_true.mp hp) (i, 21) hm
  have hne : c.getD i 0 ≠ c.getD 21 0 := by
    have hb : c.getD i 0 != c.getD 21 0 := by
      simpa only [if_neg (by simp : (i, 21) ≠ (0, 1))] using hh
    simpa using hb
  simpa only [firstCopy_getD c i hi12] using hne

private theorem secondCopy_avoids (c : List (Fin 4))
    (hp : properD5Minus01 c = true) :
    ∀ i : Nat, i < (secondCopy c).length →
      (secondCopy c).getD i 0 ≠ c.getD 22 0 := by
  unfold properD5Minus01 at hp
  intro i hi
  have hi12 : i < 12 := by simpa [secondCopy] using hi
  have hm : (secondIndex i, 22) ∈ d5OutputEdges := by
    have hh := (List.all_eq_true.mp d5_clique_adjacencies.2) i
      (List.mem_range.mpr hi12)
    simpa using hh
  have hh := (List.all_eq_true.mp hp) (secondIndex i, 22) hm
  have hne : c.getD (secondIndex i) 0 ≠ c.getD 22 0 := by
    have hb : c.getD (secondIndex i) 0 != c.getD 22 0 := by
      simpa only [if_neg (by simp : (secondIndex i, 22) ≠ (0, 1))] using hh
    simpa using hb
  simpa only [secondCopy_getD c i hi12] using hne

/-- Deleting edge 01 from the concrete D5 does not admit four colors. -/
theorem d5_minus_01_not_four_colorable :
    ¬ ∃ c : List (Fin 4), c.length = 23 ∧
      properD5Minus01 c = true := by
  rintro ⟨c, _hlen, hp⟩
  have hpall : (d5OutputEdges.all fun e =>
      if e = (0, 1) then true else c.getD e.1 0 != c.getD e.2 0) = true := hp
  have hr1 := four_palette_rigidity (c.getD 21 0) (firstCopy c)
    (firstCopy_length c) (firstCopy_avoids c hp) (firstCopy_valid c hp)
  have hr2 := four_palette_rigidity (c.getD 22 0) (secondCopy c)
    (secondCopy_length c) (secondCopy_avoids c hp) (secondCopy_valid c hp)
  have h0 : (firstCopy c).getD 0 0 = (secondCopy c).getD 0 0 := by
    rw [firstCopy_getD c 0 (by omega), secondCopy_getD c 0 (by omega)]
    rfl
  have h1 : (firstCopy c).getD 1 0 = (secondCopy c).getD 1 0 := by
    rw [firstCopy_getD c 1 (by omega), secondCopy_getD c 1 (by omega)]
    rfl
  have h2 : (firstCopy c).getD 2 0 = (secondCopy c).getD 2 0 := by
    rw [firstCopy_getD c 2 (by omega), secondCopy_getD c 2 (by omega)]
    rfl
  have hbridge : (firstCopy c).getD 3 0 ≠
      (secondCopy c).getD 3 0 := by
    have hm : (3, 12) ∈ d5OutputEdges := d5_bridge_and_counts.1
    have hh := (List.all_eq_true.mp hpall) (3, 12) hm
    have hne : c.getD 3 0 ≠ c.getD 12 0 := by
      have hb : c.getD 3 0 != c.getD 12 0 := by
        simpa only [if_neg (by decide : (3, 12) ≠ (0, 1))] using hh
      simpa using hb
    rw [firstCopy_getD c 3 (by omega), secondCopy_getD c 3 (by omega)]
    exact hne
  have h3 : (firstCopy c).getD 3 0 = (secondCopy c).getD 3 0 := by
    by_cases heq : (firstCopy c).getD 0 0 = (firstCopy c).getD 1 0
    · have heq2 : (secondCopy c).getD 0 0 = (secondCopy c).getD 1 0 :=
        h0.symm.trans (heq.trans h1)
      calc
        (firstCopy c).getD 3 0 = (firstCopy c).getD 2 0 := hr1.1 heq
        _ = (secondCopy c).getD 2 0 := h2
        _ = (secondCopy c).getD 3 0 := (hr2.1 heq2).symm
    · have hne2 : (secondCopy c).getD 0 0 ≠
          (secondCopy c).getD 1 0 := by
        intro h
        exact heq (h0.trans (h.trans h1.symm))
      calc
        (firstCopy c).getD 3 0 = (firstCopy c).getD 0 0 := hr1.2 heq
        _ = (secondCopy c).getD 0 0 := h0
        _ = (secondCopy c).getD 3 0 := (hr2.2 hne2).symm
  exact hbridge h3

end DiracHajos

import GeneralCliqueEdgesFixed

/-!
Pull a proper coloring of the symbolic output graph back to its two
twelve-vertex base copies, ignoring the two deleted 03 edges and edge 01.
-/

namespace DiracHajos

def ProperOutput (r : Nat) (c : Nat → Fin (r + 3)) : Prop :=
  ∀ e ∈ dEdges r, c e.1 ≠ c e.2

def firstColors (r : Nat) (c : Nat → Fin (r + 3)) : List (Fin (r + 3)) :=
  (List.range 12).map c

def secondColors (r : Nat) (c : Nat → Fin (r + 3)) : List (Fin (r + 3)) :=
  (List.range 12).map fun i => c (secondIndex i)

theorem firstColors_length (r : Nat) (c : Nat → Fin (r + 3)) :
    (firstColors r c).length = 12 := by simp [firstColors]

theorem secondColors_length (r : Nat) (c : Nat → Fin (r + 3)) :
    (secondColors r c).length = 12 := by simp [secondColors]

theorem firstColors_getD (r : Nat) (c : Nat → Fin (r + 3))
    (i : Nat) (hi : i < 12) :
    (firstColors r c).getD i 0 = c i := by
  simp [firstColors, List.getD, hi]

theorem secondColors_getD (r : Nat) (c : Nat → Fin (r + 3))
    (i : Nat) (hi : i < 12) :
    (secondColors r c).getD i 0 = c (secondIndex i) := by
  simp [secondColors, List.getD, hi]

private theorem secondIndex_inj : Function.Injective secondIndex := by
  intro a b h
  unfold secondIndex at h
  split_ifs at h <;> omega

private theorem secondIndex_ne_three (i : Nat) : secondIndex i ≠ 3 := by
  unfold secondIndex
  split_ifs <;> omega

private theorem second_pair_ne_03 (e : Nat × Nat) :
    (secondIndex e.1, secondIndex e.2) ≠ (0, 3) := by
  intro h
  exact secondIndex_ne_three e.2 (congrArg Prod.snd h)

private theorem second_pair_ne_012 (e : Nat × Nat) (h03 : e ≠ (0, 3)) :
    (secondIndex e.1, secondIndex e.2) ≠ (0, 12) := by
  intro h
  have h0 : secondIndex e.1 = secondIndex 0 := by
    simpa [secondIndex] using congrArg Prod.fst h
  have h3 : secondIndex e.2 = secondIndex 3 := by
    simpa [secondIndex] using congrArg Prod.snd h
  exact h03 (Prod.ext (secondIndex_inj h0) (secondIndex_inj h3))

theorem firstColors_valid (r : Nat) (c : Nat → Fin (r + 3))
    (hp : ProperOutput r c) :
    (edges.all fun e =>
      if e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ (firstColors r c).length
      then true
      else (firstColors r c).getD e.1 0 !=
        (firstColors r c).getD e.2 0) = true := by
  apply List.all_eq_true.mpr
  intro e he
  by_cases hskip : e = (0, 3) ∨ e = (0, 1) ∨
      e.2 ≥ (firstColors r c).length
  · simp only [if_pos hskip]
  have h03 : e ≠ (0, 3) := by tauto
  have hlt2 : e.2 < 12 := by
    have hh := firstColors_length r c
    omega
  have h012 : e ≠ (0, 12) := by
    intro h
    have hh := congrArg Prod.snd h
    omega
  have hmem := dEdges_first_base r e he h03 h012
  have hne : c e.1 != c e.2 := by simpa using hp e hmem
  have horder : e.1 < e.2 := by
    have hh := (List.all_eq_true.mp edgesOrdered) e he
    simpa using hh
  have hlt1 : e.1 < 12 := by omega
  simpa only [if_neg hskip, firstColors_getD r c e.1 hlt1,
    firstColors_getD r c e.2 hlt2] using hne

theorem secondColors_valid (r : Nat) (c : Nat → Fin (r + 3))
    (hp : ProperOutput r c) :
    (edges.all fun e =>
      if e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ (secondColors r c).length
      then true
      else (secondColors r c).getD e.1 0 !=
        (secondColors r c).getD e.2 0) = true := by
  apply List.all_eq_true.mpr
  intro e he
  by_cases hskip : e = (0, 3) ∨ e = (0, 1) ∨
      e.2 ≥ (secondColors r c).length
  · simp only [if_pos hskip]
  have h03 : e ≠ (0, 3) := by tauto
  have hlt2 : e.2 < 12 := by
    have hh := secondColors_length r c
    omega
  have hmem := dEdges_second_base r e he
    (second_pair_ne_03 e) (second_pair_ne_012 e h03)
  have hne : c (secondIndex e.1) != c (secondIndex e.2) := by
    simpa using hp (secondIndex e.1, secondIndex e.2) hmem
  have horder : e.1 < e.2 := by
    have hh := (List.all_eq_true.mp edgesOrdered) e he
    simpa using hh
  have hlt1 : e.1 < 12 := by omega
  simpa only [if_neg hskip, secondColors_getD r c e.1 hlt1,
    secondColors_getD r c e.2 hlt2] using hne

end DiracHajos

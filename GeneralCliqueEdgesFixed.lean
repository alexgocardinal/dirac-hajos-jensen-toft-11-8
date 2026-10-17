import GeneralEdgeFacts

/-!
The clique and join edges in every symbolic output graph `dEdges r`.
-/

namespace DiracHajos

private theorem mem_firstClique (r : Nat) (j : Fin r) :
    21 + j.val ∈ firstClique r := by
  unfold firstClique
  apply List.mem_map.mpr
  exact ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩

private theorem mem_secondClique (r : Nat) (j : Fin r) :
    21 + r + j.val ∈ secondClique r := by
  unfold secondClique
  apply List.mem_map.mpr
  exact ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩

private theorem mem_secondBase (i : Nat) (hi : i < 12) :
    secondIndex i ∈ secondBase := by
  unfold secondBase
  apply List.mem_map.mpr
  exact ⟨i, List.mem_range.mpr hi, rfl⟩

/-- Distinct ordered vertices of the first added clique are adjacent. -/
theorem dEdges_first_clique (r : Nat) (i j : Fin r) (hij : i < j) :
    (21 + i.val, 21 + j.val) ∈ dEdges r := by
  have hraw : (21 + i.val, 21 + j.val) ∈ cliqueEdges (firstClique r) := by
    unfold cliqueEdges
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨21 + i.val, mem_firstClique r i, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨21 + j.val, mem_firstClique r j, ?_⟩
    simp [show 21 + i.val < 21 + j.val by omega]
  have h03 : (21 + i.val, 21 + j.val) ≠ (0, 3) := by
    intro h
    have hp := congrArg Prod.fst h
    omega
  have h012 : (21 + i.val, 21 + j.val) ≠ (0, 12) := by
    intro h
    have hp := congrArg Prod.fst h
    omega
  simp only [dEdges, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_union]
  tauto

/-- Distinct ordered vertices of the second added clique are adjacent. -/
theorem dEdges_second_clique (r : Nat) (i j : Fin r) (hij : i < j) :
    (21 + r + i.val, 21 + r + j.val) ∈ dEdges r := by
  have hraw : (21 + r + i.val, 21 + r + j.val) ∈
      cliqueEdges (secondClique r) := by
    unfold cliqueEdges
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨21 + r + i.val, mem_secondClique r i, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨21 + r + j.val, mem_secondClique r j, ?_⟩
    simp [show 21 + r + i.val < 21 + r + j.val by omega]
  have h03 : (21 + r + i.val, 21 + r + j.val) ≠ (0, 3) := by
    intro h
    have hp := congrArg Prod.fst h
    omega
  have h012 : (21 + r + i.val, 21 + r + j.val) ≠ (0, 12) := by
    intro h
    have hp := congrArg Prod.fst h
    omega
  simp only [dEdges, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_union]
  tauto

/-- Every first-copy base vertex is adjacent to every first-clique vertex. -/
theorem dEdges_first_join (r i : Nat) (hi : i < 12) (j : Fin r) :
    (i, 21 + j.val) ∈ dEdges r := by
  have hraw : (i, 21 + j.val) ∈
      crossEdges (List.range 12) (firstClique r) := by
    unfold crossEdges
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    apply List.mem_map.mpr
    exact ⟨21 + j.val, mem_firstClique r j, rfl⟩
  have h03 : (i, 21 + j.val) ≠ (0, 3) := by
    intro h
    have hp := congrArg Prod.snd h
    omega
  have h012 : (i, 21 + j.val) ≠ (0, 12) := by
    intro h
    have hp := congrArg Prod.snd h
    omega
  simp only [dEdges, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_union]
  tauto

/-- Every second-copy base vertex is adjacent to every second-clique vertex. -/
theorem dEdges_second_join (r i : Nat) (hi : i < 12) (j : Fin r) :
    (secondIndex i, 21 + r + j.val) ∈ dEdges r := by
  have hraw : (secondIndex i, 21 + r + j.val) ∈
      crossEdges secondBase (secondClique r) := by
    unfold crossEdges
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨secondIndex i, mem_secondBase i hi, ?_⟩
    apply List.mem_map.mpr
    exact ⟨21 + r + j.val, mem_secondClique r j, rfl⟩
  have h03 : (secondIndex i, 21 + r + j.val) ≠ (0, 3) := by
    intro h
    have hp := congrArg Prod.snd h
    omega
  have h012 : (secondIndex i, 21 + r + j.val) ≠ (0, 12) := by
    intro h
    have hp := congrArg Prod.snd h
    omega
  simp only [dEdges, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_union]
  tauto

end DiracHajos

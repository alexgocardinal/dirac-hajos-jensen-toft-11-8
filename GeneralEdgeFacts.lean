import GeneralConstructionNative

/-!
First structural facts about the symbolic output edge sets. These relate
membership in the explicit base lists and clique lists to membership in
`dEdges r`, after the two 03 edges are removed and the bridge is added.
-/

namespace DiracHajos

/-- The bridge edge occurs in every member of the family. -/
theorem dEdges_bridge (r : Nat) : (3, 12) ∈ dEdges r := by
  simp [dEdges]

/-- Any undeleted first-copy base edge survives in the output. -/
theorem dEdges_first_base (r : Nat) (e : Nat × Nat)
    (he : e ∈ edges) (h03 : e ≠ (0, 3)) (h012 : e ≠ (0, 12)) :
    e ∈ dEdges r := by
  have hbase : e ∈ baseCopyEdges := by
    simp [baseCopyEdges, he]
  simp only [dEdges, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_union]
  tauto

/-- Any undeleted second-copy base edge survives in the output. -/
theorem dEdges_second_base (r : Nat) (e : Nat × Nat)
    (he : e ∈ edges)
    (h03 : (secondIndex e.1, secondIndex e.2) ≠ (0, 3))
    (h012 : (secondIndex e.1, secondIndex e.2) ≠ (0, 12)) :
    (secondIndex e.1, secondIndex e.2) ∈ dEdges r := by
  have hbase : (secondIndex e.1, secondIndex e.2) ∈ baseCopyEdges := by
    unfold baseCopyEdges
    apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨e, he, rfl⟩
  simp only [dEdges, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_union]
  tauto

end DiracHajos

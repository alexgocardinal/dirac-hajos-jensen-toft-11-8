import GeneralCliqueColors
import GeneralCliqueObstruction

/-!
The symbolic output graph `dEdges r` has no proper coloring by `r + 3`
colors. For k = r + 4 this is the chromatic lower bound k. This file
does not establish the matching upper bound or criticality of the inputs.
-/

namespace DiracHajos

theorem no_output_coloring (r : Nat) :
    ¬ ∃ c : Nat → Fin (r + 3), ProperOutput r c := by
  rintro ⟨c, hp⟩
  apply general_clique_obstruction r
    (firstCliqueColors r c) (secondCliqueColors r c)
    (firstColors r c) (secondColors r c)
  · exact firstCliqueColors_injective r c hp
  · exact secondCliqueColors_injective r c hp
  · exact firstColors_length r c
  · exact secondColors_length r c
  · exact firstColors_avoid_clique r c hp
  · exact secondColors_avoid_clique r c hp
  · exact firstColors_valid r c hp
  · exact secondColors_valid r c hp
  · simp [firstColors, secondColors, secondIndex, List.getD]
  · simp [firstColors, secondColors, secondIndex, List.getD]
  · simp [firstColors, secondColors, secondIndex, List.getD]
  · have h := hp (3, 12) (dEdges_bridge r)
    simpa [firstColors, secondColors, secondIndex, List.getD] using h

end DiracHajos

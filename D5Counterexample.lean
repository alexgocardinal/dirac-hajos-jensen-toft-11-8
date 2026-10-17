import D5NoFour

/-!
The concrete k=5 counterexample: both D5 and D5 minus 01 require five
colors, while 01 is an edge of D5. The arbitrary-k theorem is separate.
Run: lake env lean D5Counterexample.lean
-/

namespace DiracHajos

def d5FiveColors : List (Fin 5) := [2, 0, 1, 3, 0, 0, 1, 2, 1, 2, 2, 0, 4, 0, 0, 1, 2, 1, 2, 2, 0, 4, 3]

theorem d5_five_coloring_valid :
    d5FiveColors.length = 23 ∧
    (d5OutputEdges.all fun e =>
      d5FiveColors.getD e.1 0 != d5FiveColors.getD e.2 0) = true := by
  decide

/-- Removing the edge 01 does not lower the required number of colors. -/
theorem d5_counterexample_certificates :
    (0, 1) ∈ d5OutputEdges ∧
    (¬ ∃ c : List (Fin 4), c.length = 23 ∧
      (d5OutputEdges.all fun e => c.getD e.1 0 != c.getD e.2 0) = true) ∧
    (¬ ∃ c : List (Fin 4), c.length = 23 ∧
      properD5Minus01 c = true) ∧
    (∃ c : List (Fin 5), c.length = 23 ∧
      (d5OutputEdges.all fun e =>
        c.getD e.1 0 != c.getD e.2 0) = true) := by
  refine ⟨d5_bridge_and_counts.2.1, ?_, d5_minus_01_not_four_colorable,
    ⟨d5FiveColors, d5_five_coloring_valid.1, d5_five_coloring_valid.2⟩⟩
  rintro ⟨c, hlen, hfull⟩
  apply d5_minus_01_not_four_colorable
  refine ⟨c, hlen, ?_⟩
  unfold properD5Minus01
  apply List.all_eq_true.mpr
  intro e he
  have hh := (List.all_eq_true.mp hfull) e he
  by_cases h01 : e = (0, 1)
  · simp only [if_pos h01]
  · simpa only [if_neg h01] using hh

end DiracHajos

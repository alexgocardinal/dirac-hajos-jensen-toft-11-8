import PaletteBridgeImported

/-!
Connect the concrete D5 output edge list to its two base-graph copies.
Run: lake env lean D5Structure.lean
-/

namespace DiracHajos

def d5OutputEdges : List (Nat × Nat) := [(0, 1), (0, 2), (0, 4), (0, 11), (0, 13), (0, 20), (0, 21), (0, 22), (1, 2), (1, 6), (1, 7), (1, 10), (1, 15), (1, 16), (1, 19), (1, 21), (1, 22), (2, 9), (2, 11), (2, 18), (2, 20), (2, 21), (2, 22), (3, 5), (3, 8), (3, 11), (3, 12), (3, 21), (4, 6), (4, 7), (4, 8), (4, 9), (4, 21), (5, 6), (5, 8), (5, 21), (6, 9), (6, 10), (6, 21), (7, 8), (7, 21), (8, 10), (8, 21), (9, 21), (10, 21), (11, 21), (12, 14), (12, 17), (12, 20), (12, 22), (13, 15), (13, 16), (13, 17), (13, 18), (13, 22), (14, 15), (14, 17), (14, 22), (15, 18), (15, 19), (15, 22), (16, 17), (16, 22), (17, 19), (17, 22), (18, 22), (19, 22), (20, 22)]

def secondIndex (i : Nat) : Nat := if i < 3 then i else i + 9

/-- Proper four-coloring test after the edge 01 is deleted. -/
def properD5Minus01 (c : List (Fin 4)) : Bool :=
  d5OutputEdges.all fun e =>
    if e = (0, 1) then true else c.getD e.1 0 != c.getD e.2 0

/-- Every nondeleted base edge occurs in each output copy. -/
theorem d5_base_edges_present :
    (edges.all fun e => decide
      (e = (0, 1) ∨ e = (0, 3) ∨ e ∈ d5OutputEdges)) = true ∧
    (edges.all fun e => decide
      (e = (0, 1) ∨ e = (0, 3) ∨
       (secondIndex e.1, secondIndex e.2) ∈ d5OutputEdges)) = true := by
  decide

/-- Each copy has a vertex adjacent to all twelve of its base vertices. -/
theorem d5_clique_adjacencies :
    ((List.range 12).all fun i => decide ((i, 21) ∈ d5OutputEdges)) = true ∧
    ((List.range 12).all fun i =>
      decide ((secondIndex i, 22) ∈ d5OutputEdges)) = true := by
  decide

theorem d5_bridge_and_counts :
    (3, 12) ∈ d5OutputEdges ∧ (0, 1) ∈ d5OutputEdges ∧
    d5OutputEdges.length = 68 := by decide

end DiracHajos

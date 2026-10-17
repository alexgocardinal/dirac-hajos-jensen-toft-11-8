import Mathlib

/-!
Finite color search in small, separately checked stages. Each `step` tries three
colors for the next vertex and discards assignments conflicting with an edge.
This checks the stated stage tables, not yet their completeness for every coloring.
Run: lake env lean AllColorRigidityFixed.lean
-/

namespace DiracHajos

def edges : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 11), (1, 2), (1, 6), (1, 7), (1, 10), (2, 9), (2, 11), (3, 5), (3, 8), (3, 11), (4, 6), (4, 7), (4, 8), (4, 9), (5, 6), (5, 8), (6, 9), (6, 10), (7, 8), (8, 10)]

def validPrefix (c : List (Fin 3)) : Bool :=
  edges.all fun e =>
    if e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ c.length then true
    else c.getD e.1 0 != c.getD e.2 0

def step (cs : List (List (Fin 3))) : List (List (Fin 3)) :=
  cs.flatMap fun c =>
    (([0, 1, 2] : List (Fin 3)).map fun x => c ++ [x]).filter validPrefix

def distinctStage0 : List (List (Fin 3)) := [[0, 1, 2]]
def distinctStage1 : List (List (Fin 3)) := [[0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2]]
def distinctStage2 : List (List (Fin 3)) := [[0, 1, 2, 0, 1], [0, 1, 2, 0, 2], [0, 1, 2, 1, 1], [0, 1, 2, 1, 2], [0, 1, 2, 2, 1], [0, 1, 2, 2, 2]]
def distinctStage3 : List (List (Fin 3)) := [[0, 1, 2, 0, 1, 1], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 2, 1], [0, 1, 2, 0, 2, 2], [0, 1, 2, 1, 1, 0], [0, 1, 2, 1, 1, 2], [0, 1, 2, 1, 2, 0], [0, 1, 2, 1, 2, 2], [0, 1, 2, 2, 1, 0], [0, 1, 2, 2, 1, 1], [0, 1, 2, 2, 2, 0], [0, 1, 2, 2, 2, 1]]
def distinctStage4 : List (List (Fin 3)) := [[0, 1, 2, 0, 1, 1, 0], [0, 1, 2, 0, 1, 1, 2], [0, 1, 2, 0, 1, 2, 0], [0, 1, 2, 0, 2, 1, 0], [0, 1, 2, 0, 2, 2, 0], [0, 1, 2, 1, 1, 0, 2], [0, 1, 2, 1, 1, 2, 0], [0, 1, 2, 1, 2, 2, 0], [0, 1, 2, 2, 1, 0, 2], [0, 1, 2, 2, 1, 1, 0], [0, 1, 2, 2, 1, 1, 2], [0, 1, 2, 2, 2, 1, 0]]
def distinctStage5 : List (List (Fin 3)) := [[0, 1, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 1, 0, 2], [0, 1, 2, 0, 1, 1, 2, 0], [0, 1, 2, 0, 1, 1, 2, 2], [0, 1, 2, 0, 1, 2, 0, 0], [0, 1, 2, 0, 1, 2, 0, 2], [0, 1, 2, 0, 2, 1, 0, 0], [0, 1, 2, 0, 2, 2, 0, 0], [0, 1, 2, 1, 1, 0, 2, 0], [0, 1, 2, 1, 1, 0, 2, 2], [0, 1, 2, 1, 1, 2, 0, 0], [0, 1, 2, 1, 1, 2, 0, 2], [0, 1, 2, 1, 2, 2, 0, 0], [0, 1, 2, 2, 1, 0, 2, 0], [0, 1, 2, 2, 1, 0, 2, 2], [0, 1, 2, 2, 1, 1, 0, 0], [0, 1, 2, 2, 1, 1, 0, 2], [0, 1, 2, 2, 1, 1, 2, 0], [0, 1, 2, 2, 1, 1, 2, 2], [0, 1, 2, 2, 2, 1, 0, 0]]
def distinctStage6 : List (List (Fin 3)) := [[0, 1, 2, 0, 1, 1, 0, 0, 2], [0, 1, 2, 0, 1, 1, 2, 0, 2], [0, 1, 2, 0, 2, 2, 0, 0, 1], [0, 1, 2, 1, 1, 0, 2, 0, 2], [0, 1, 2, 1, 1, 2, 0, 2, 0], [0, 1, 2, 2, 1, 1, 0, 2, 0], [0, 1, 2, 2, 1, 1, 2, 2, 0]]
def distinctStage7 : List (List (Fin 3)) := [[0, 1, 2, 0, 1, 1, 2, 0, 2, 0], [0, 1, 2, 0, 2, 2, 0, 0, 1, 1], [0, 1, 2, 1, 1, 0, 2, 0, 2, 0], [0, 1, 2, 2, 1, 1, 2, 2, 0, 0]]
def distinctStage8 : List (List (Fin 3)) := [[0, 1, 2, 0, 1, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 2, 2, 0, 0, 1, 1, 2], [0, 1, 2, 1, 1, 0, 2, 0, 2, 0, 0]]
def distinctStage9 : List (List (Fin 3)) := [[0, 1, 2, 0, 1, 1, 2, 0, 2, 0, 0, 1], [0, 1, 2, 0, 2, 2, 0, 0, 1, 1, 2, 1]]

theorem distinct_step0 : step distinctStage0 = distinctStage1 := by decide
theorem distinct_step1 : step distinctStage1 = distinctStage2 := by decide
theorem distinct_step2 : step distinctStage2 = distinctStage3 := by decide
theorem distinct_step3 : step distinctStage3 = distinctStage4 := by decide
theorem distinct_step4 : step distinctStage4 = distinctStage5 := by decide
theorem distinct_step5 : step distinctStage5 = distinctStage6 := by decide
theorem distinct_step6 : step distinctStage6 = distinctStage7 := by decide
theorem distinct_step7 : step distinctStage7 = distinctStage8 := by decide
theorem distinct_step8 : step distinctStage8 = distinctStage9 := by decide

def equalStage0 : List (List (Fin 3)) := [[0, 0, 1]]
def equalStage1 : List (List (Fin 3)) := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2]]
def equalStage2 : List (List (Fin 3)) := [[0, 0, 1, 0, 1], [0, 0, 1, 0, 2], [0, 0, 1, 1, 1], [0, 0, 1, 1, 2], [0, 0, 1, 2, 1], [0, 0, 1, 2, 2]]
def equalStage3 : List (List (Fin 3)) := [[0, 0, 1, 0, 1, 1], [0, 0, 1, 0, 1, 2], [0, 0, 1, 0, 2, 1], [0, 0, 1, 0, 2, 2], [0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 1, 2], [0, 0, 1, 1, 2, 0], [0, 0, 1, 1, 2, 2], [0, 0, 1, 2, 1, 0], [0, 0, 1, 2, 1, 1], [0, 0, 1, 2, 2, 0], [0, 0, 1, 2, 2, 1]]
def equalStage4 : List (List (Fin 3)) := [[0, 0, 1, 0, 1, 1, 2], [0, 0, 1, 0, 2, 2, 1], [0, 0, 1, 1, 1, 0, 2], [0, 0, 1, 1, 2, 0, 1], [0, 0, 1, 1, 2, 2, 1], [0, 0, 1, 2, 1, 0, 2], [0, 0, 1, 2, 1, 1, 2], [0, 0, 1, 2, 2, 0, 1]]
def equalStage5 : List (List (Fin 3)) := [[0, 0, 1, 0, 1, 1, 2, 2], [0, 0, 1, 0, 2, 2, 1, 1], [0, 0, 1, 1, 1, 0, 2, 2], [0, 0, 1, 1, 2, 0, 1, 1], [0, 0, 1, 1, 2, 2, 1, 1], [0, 0, 1, 2, 1, 0, 2, 2], [0, 0, 1, 2, 1, 1, 2, 2], [0, 0, 1, 2, 2, 0, 1, 1]]
def equalStage6 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0], [0, 0, 1, 2, 1, 1, 2, 2, 0]]
def equalStage7 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0, 0], [0, 0, 1, 2, 1, 1, 2, 2, 0, 0]]
def equalStage8 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0, 0, 2], [0, 0, 1, 2, 1, 1, 2, 2, 0, 0, 1]]
def equalStage9 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0, 0, 2, 2]]

theorem equal_step0 : step equalStage0 = equalStage1 := by decide
theorem equal_step1 : step equalStage1 = equalStage2 := by decide
theorem equal_step2 : step equalStage2 = equalStage3 := by decide
theorem equal_step3 : step equalStage3 = equalStage4 := by decide
theorem equal_step4 : step equalStage4 = equalStage5 := by decide
theorem equal_step5 : step equalStage5 = equalStage6 := by decide
theorem equal_step6 : step equalStage6 = equalStage7 := by decide
theorem equal_step7 : step equalStage7 = equalStage8 := by decide
theorem equal_step8 : step equalStage8 = equalStage9 := by decide

/-- The three trial values really contain every possible color. -/
theorem all_colors (x : Fin 3) : x ∈ ([0, 1, 2] : List (Fin 3)) := by
  fin_cases x <;> simp

/-- If a valid extension is built from a listed prefix, `step` includes it. -/
theorem step_complete (cs : List (List (Fin 3)))
    (c : List (Fin 3)) (x : Fin 3)
    (hc : c ∈ cs) (hv : validPrefix (c ++ [x]) = true) :
    c ++ [x] ∈ step cs := by
  unfold step
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_map.mpr
    exact ⟨x, all_colors x, rfl⟩
  · exact hv

/-- Repeating `step` from one of the two normalized first-three-color lists. -/
def iterStage (same : Bool) : Nat → List (List (Fin 3))
  | 0 => [if same then [0, 0, 1] else [0, 1, 2]]
  | n + 1 => step (iterStage same n)

theorem iter_distinct_0 : iterStage false 0 = distinctStage0 := by rfl

theorem iter_distinct_1 : iterStage false 1 = distinctStage1 := by
  change step (iterStage false 0) = distinctStage1
  exact (congrArg step iter_distinct_0).trans distinct_step0

theorem iter_distinct_2 : iterStage false 2 = distinctStage2 := by
  change step (iterStage false 1) = distinctStage2
  exact (congrArg step iter_distinct_1).trans distinct_step1

theorem iter_distinct_3 : iterStage false 3 = distinctStage3 := by
  change step (iterStage false 2) = distinctStage3
  exact (congrArg step iter_distinct_2).trans distinct_step2

theorem iter_distinct_4 : iterStage false 4 = distinctStage4 := by
  change step (iterStage false 3) = distinctStage4
  exact (congrArg step iter_distinct_3).trans distinct_step3

theorem iter_distinct_5 : iterStage false 5 = distinctStage5 := by
  change step (iterStage false 4) = distinctStage5
  exact (congrArg step iter_distinct_4).trans distinct_step4

theorem iter_distinct_6 : iterStage false 6 = distinctStage6 := by
  change step (iterStage false 5) = distinctStage6
  exact (congrArg step iter_distinct_5).trans distinct_step5

theorem iter_distinct_7 : iterStage false 7 = distinctStage7 := by
  change step (iterStage false 6) = distinctStage7
  exact (congrArg step iter_distinct_6).trans distinct_step6

theorem iter_distinct_8 : iterStage false 8 = distinctStage8 := by
  change step (iterStage false 7) = distinctStage8
  exact (congrArg step iter_distinct_7).trans distinct_step7

theorem iter_distinct_9 : iterStage false 9 = distinctStage9 := by
  change step (iterStage false 8) = distinctStage9
  exact (congrArg step iter_distinct_8).trans distinct_step8

theorem iter_equal_0 : iterStage true 0 = equalStage0 := by rfl

theorem iter_equal_1 : iterStage true 1 = equalStage1 := by
  change step (iterStage true 0) = equalStage1
  exact (congrArg step iter_equal_0).trans equal_step0

theorem iter_equal_2 : iterStage true 2 = equalStage2 := by
  change step (iterStage true 1) = equalStage2
  exact (congrArg step iter_equal_1).trans equal_step1

theorem iter_equal_3 : iterStage true 3 = equalStage3 := by
  change step (iterStage true 2) = equalStage3
  exact (congrArg step iter_equal_2).trans equal_step2

theorem iter_equal_4 : iterStage true 4 = equalStage4 := by
  change step (iterStage true 3) = equalStage4
  exact (congrArg step iter_equal_3).trans equal_step3

theorem iter_equal_5 : iterStage true 5 = equalStage5 := by
  change step (iterStage true 4) = equalStage5
  exact (congrArg step iter_equal_4).trans equal_step4

theorem iter_equal_6 : iterStage true 6 = equalStage6 := by
  change step (iterStage true 5) = equalStage6
  exact (congrArg step iter_equal_5).trans equal_step5

theorem iter_equal_7 : iterStage true 7 = equalStage7 := by
  change step (iterStage true 6) = equalStage7
  exact (congrArg step iter_equal_6).trans equal_step6

theorem iter_equal_8 : iterStage true 8 = equalStage8 := by
  change step (iterStage true 7) = equalStage8
  exact (congrArg step iter_equal_7).trans equal_step7

theorem iter_equal_9 : iterStage true 9 = equalStage9 := by
  change step (iterStage true 8) = equalStage9
  exact (congrArg step iter_equal_8).trans equal_step8

/-- Every sequence whose prefixes pass the edge check appears in the search. -/
theorem iter_complete (same : Bool) (c : List (Fin 3))
    (hbase : c.take 3 = (if same then [0, 0, 1] else [0, 1, 2]))
    (hvalid : ∀ i : Nat, 3 < i → i ≤ c.length →
      validPrefix (c.take i) = true) :
    ∀ n : Nat, 3 + n ≤ c.length →
      c.take (3 + n) ∈ iterStage same n := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa [iterStage, hbase]
  | succ n ih =>
      intro hlen
      have hlt : 3 + n < c.length := by omega
      have hprev : c.take (3 + n) ∈ iterStage same n := ih (by omega)
      have hnext : validPrefix (c.take (3 + (n + 1))) = true :=
        hvalid (3 + (n + 1)) (by omega) hlen
      have htake : c.take (3 + (n + 1)) =
          c.take (3 + n) ++ [c.get ⟨3 + n, hlt⟩] := by
        simpa [Nat.add_assoc] using
          (List.take_succ_eq_append_getElem (l := c) (i := 3 + n) hlt)
      change c.take (3 + (n + 1)) ∈ step (iterStage same n)
      rw [htake]
      apply step_complete (iterStage same n) (c.take (3 + n)) (c.get ⟨3 + n, hlt⟩) hprev
      simpa [htake] using hnext

/-- A 12-entry list with the distinct initial normalization and valid prefixes
    must be one of the two computed final lists. -/
theorem distinct_final_complete (c : List (Fin 3))
    (hlen : c.length = 12) (hbase : c.take 3 = [0, 1, 2])
    (hvalid : ∀ i : Nat, 3 < i → i ≤ c.length →
      validPrefix (c.take i) = true) :
    c ∈ distinctStage9 := by
  have h := iter_complete false c hbase hvalid 9 (by omega)
  rw [iter_distinct_9] at h
  have ht : c.take 12 = c := by simpa [hlen] using (List.take_length c)
  simpa [ht] using h

/-- The corresponding statement when vertices 0 and 1 have the same color. -/
theorem equal_final_complete (c : List (Fin 3))
    (hlen : c.length = 12) (hbase : c.take 3 = [0, 0, 1])
    (hvalid : ∀ i : Nat, 3 < i → i ≤ c.length →
      validPrefix (c.take i) = true) :
    c ∈ equalStage9 := by
  have h := iter_complete true c hbase hvalid 9 (by omega)
  rw [iter_equal_9] at h
  have ht : c.take 12 = c := by simpa [hlen] using (List.take_length c)
  simpa [ht] using h

/-- The listed colorings imply the rigidity claim in each normalization. -/
theorem distinct_final_rigidity (c : List (Fin 3))
    (h : c ∈ distinctStage9) : c.getD 3 0 = c.getD 0 0 := by
  simp [distinctStage9] at h
  rcases h with rfl | rfl <;> decide

theorem equal_final_rigidity (c : List (Fin 3))
    (h : c ∈ equalStage9) : c.getD 3 0 = c.getD 2 0 := by
  simp [equalStage9] at h
  subst c
  decide

/-- The input edge list is oriented from a smaller to a larger label. -/
theorem edgesOrdered :
    (edges.all fun e => decide (e.1 < e.2)) = true := by decide

/-- A valid full coloring also passes the check on every shorter prefix. -/
theorem validPrefix_take (c : List (Fin 3))
    (hv : validPrefix c = true) (i : Nat) :
    validPrefix (c.take i) = true := by
  unfold validPrefix at hv ⊢
  apply List.all_eq_true.mpr
  intro e he
  have hfull := (List.all_eq_true.mp hv) e he
  by_cases hskip : e = (0, 3) ∨ e = (0, 1)
  · have hguard : e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ (c.take i).length := by
      tauto
    simp only [if_pos hguard]
  by_cases hlate : e.2 ≥ (c.take i).length
  · have hguard : e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ (c.take i).length := by
      tauto
    simp only [if_pos hguard]
  have hlt2 : e.2 < (c.take i).length := by omega
  have horder : e.1 < e.2 := by
    have hh := (List.all_eq_true.mp edgesOrdered) e he
    simpa using hh
  have hlt1 : e.1 < (c.take i).length := by omega
  have hi1 : e.1 < i := by
    have hle := List.length_take_le i c
    omega
  have hi2 : e.2 < i := by
    have hle := List.length_take_le i c
    omega
  have hltFull : e.2 < c.length := by
    have hle := List.length_take_le' i c
    omega
  have heq1 : (c.take i).getD e.1 0 = c.getD e.1 0 := by
    simp [List.getD, List.getElem?_take, hi1]
  have heq2 : (c.take i).getD e.2 0 = c.getD e.2 0 := by
    simp [List.getD, List.getElem?_take, hi2]
  have hc : c.getD e.1 0 != c.getD e.2 0 := by
    simpa [hskip, show ¬ e.2 ≥ c.length by omega] using hfull
  have hnoguard :
      ¬(e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ (c.take i).length) := by
    tauto
  simpa only [if_neg hnoguard, heq1, heq2] using hc


/-- Full validity supplies every prefix hypothesis in the distinct case. -/
theorem distinct_full_rigidity (c : List (Fin 3))
    (hlen : c.length = 12) (hbase : c.take 3 = [0, 1, 2])
    (hv : validPrefix c = true) :
    c.getD 3 0 = c.getD 0 0 := by
  apply distinct_final_rigidity c
  apply distinct_final_complete c hlen hbase
  intro i _ _
  exact validPrefix_take c hv i

/-- Full validity supplies every prefix hypothesis in the equal case. -/
theorem equal_full_rigidity (c : List (Fin 3))
    (hlen : c.length = 12) (hbase : c.take 3 = [0, 0, 1])
    (hv : validPrefix c = true) :
    c.getD 3 0 = c.getD 2 0 := by
  apply equal_final_rigidity c
  apply equal_final_complete c hlen hbase
  intro i _ _
  exact validPrefix_take c hv i

/-- Search without choosing color names in advance. -/
def allStage0 : List (List (Fin 3)) := [[]]
def allStage1 : List (List (Fin 3)) := [[0], [1], [2]]
theorem all_step0 : step allStage0 = allStage1 := by decide
def allStage2 : List (List (Fin 3)) := [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]]
theorem all_step1 : step allStage1 = allStage2 := by decide
def allStage3 : List (List (Fin 3)) := [[0, 0, 1], [0, 0, 2], [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 1, 0], [1, 1, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0], [2, 2, 0], [2, 2, 1]]
theorem all_step2 : step allStage2 = allStage3 := by decide
def allStage4 : List (List (Fin 3)) := [[0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 0], [0, 0, 2, 1], [0, 0, 2, 2], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 2, 1, 0], [0, 2, 1, 1], [0, 2, 1, 2], [1, 0, 2, 0], [1, 0, 2, 1], [1, 0, 2, 2], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 0, 2], [1, 1, 2, 0], [1, 1, 2, 1], [1, 1, 2, 2], [1, 2, 0, 0], [1, 2, 0, 1], [1, 2, 0, 2], [2, 0, 1, 0], [2, 0, 1, 1], [2, 0, 1, 2], [2, 1, 0, 0], [2, 1, 0, 1], [2, 1, 0, 2], [2, 2, 0, 0], [2, 2, 0, 1], [2, 2, 0, 2], [2, 2, 1, 0], [2, 2, 1, 1], [2, 2, 1, 2]]
theorem all_step3 : step allStage3 = allStage4 := by decide
def allStage5 : List (List (Fin 3)) := [[0, 0, 1, 0, 1], [0, 0, 1, 0, 2], [0, 0, 1, 1, 1], [0, 0, 1, 1, 2], [0, 0, 1, 2, 1], [0, 0, 1, 2, 2], [0, 0, 2, 0, 1], [0, 0, 2, 0, 2], [0, 0, 2, 1, 1], [0, 0, 2, 1, 2], [0, 0, 2, 2, 1], [0, 0, 2, 2, 2], [0, 1, 2, 0, 1], [0, 1, 2, 0, 2], [0, 1, 2, 1, 1], [0, 1, 2, 1, 2], [0, 1, 2, 2, 1], [0, 1, 2, 2, 2], [0, 2, 1, 0, 1], [0, 2, 1, 0, 2], [0, 2, 1, 1, 1], [0, 2, 1, 1, 2], [0, 2, 1, 2, 1], [0, 2, 1, 2, 2], [1, 0, 2, 0, 0], [1, 0, 2, 0, 2], [1, 0, 2, 1, 0], [1, 0, 2, 1, 2], [1, 0, 2, 2, 0], [1, 0, 2, 2, 2], [1, 1, 0, 0, 0], [1, 1, 0, 0, 2], [1, 1, 0, 1, 0], [1, 1, 0, 1, 2], [1, 1, 0, 2, 0], [1, 1, 0, 2, 2], [1, 1, 2, 0, 0], [1, 1, 2, 0, 2], [1, 1, 2, 1, 0], [1, 1, 2, 1, 2], [1, 1, 2, 2, 0], [1, 1, 2, 2, 2], [1, 2, 0, 0, 0], [1, 2, 0, 0, 2], [1, 2, 0, 1, 0], [1, 2, 0, 1, 2], [1, 2, 0, 2, 0], [1, 2, 0, 2, 2], [2, 0, 1, 0, 0], [2, 0, 1, 0, 1], [2, 0, 1, 1, 0], [2, 0, 1, 1, 1], [2, 0, 1, 2, 0], [2, 0, 1, 2, 1], [2, 1, 0, 0, 0], [2, 1, 0, 0, 1], [2, 1, 0, 1, 0], [2, 1, 0, 1, 1], [2, 1, 0, 2, 0], [2, 1, 0, 2, 1], [2, 2, 0, 0, 0], [2, 2, 0, 0, 1], [2, 2, 0, 1, 0], [2, 2, 0, 1, 1], [2, 2, 0, 2, 0], [2, 2, 0, 2, 1], [2, 2, 1, 0, 0], [2, 2, 1, 0, 1], [2, 2, 1, 1, 0], [2, 2, 1, 1, 1], [2, 2, 1, 2, 0], [2, 2, 1, 2, 1]]
theorem all_step4 : step allStage4 = allStage5 := by decide
def allStage6 : List (List (Fin 3)) := [[0, 0, 1, 0, 1, 1], [0, 0, 1, 0, 1, 2], [0, 0, 1, 0, 2, 1], [0, 0, 1, 0, 2, 2], [0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 1, 2], [0, 0, 1, 1, 2, 0], [0, 0, 1, 1, 2, 2], [0, 0, 1, 2, 1, 0], [0, 0, 1, 2, 1, 1], [0, 0, 1, 2, 2, 0], [0, 0, 1, 2, 2, 1], [0, 0, 2, 0, 1, 1], [0, 0, 2, 0, 1, 2], [0, 0, 2, 0, 2, 1], [0, 0, 2, 0, 2, 2], [0, 0, 2, 1, 1, 0], [0, 0, 2, 1, 1, 2], [0, 0, 2, 1, 2, 0], [0, 0, 2, 1, 2, 2], [0, 0, 2, 2, 1, 0], [0, 0, 2, 2, 1, 1], [0, 0, 2, 2, 2, 0], [0, 0, 2, 2, 2, 1], [0, 1, 2, 0, 1, 1], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 2, 1], [0, 1, 2, 0, 2, 2], [0, 1, 2, 1, 1, 0], [0, 1, 2, 1, 1, 2], [0, 1, 2, 1, 2, 0], [0, 1, 2, 1, 2, 2], [0, 1, 2, 2, 1, 0], [0, 1, 2, 2, 1, 1], [0, 1, 2, 2, 2, 0], [0, 1, 2, 2, 2, 1], [0, 2, 1, 0, 1, 1], [0, 2, 1, 0, 1, 2], [0, 2, 1, 0, 2, 1], [0, 2, 1, 0, 2, 2], [0, 2, 1, 1, 1, 0], [0, 2, 1, 1, 1, 2], [0, 2, 1, 1, 2, 0], [0, 2, 1, 1, 2, 2], [0, 2, 1, 2, 1, 0], [0, 2, 1, 2, 1, 1], [0, 2, 1, 2, 2, 0], [0, 2, 1, 2, 2, 1], [1, 0, 2, 0, 0, 1], [1, 0, 2, 0, 0, 2], [1, 0, 2, 0, 2, 1], [1, 0, 2, 0, 2, 2], [1, 0, 2, 1, 0, 0], [1, 0, 2, 1, 0, 2], [1, 0, 2, 1, 2, 0], [1, 0, 2, 1, 2, 2], [1, 0, 2, 2, 0, 0], [1, 0, 2, 2, 0, 1], [1, 0, 2, 2, 2, 0], [1, 0, 2, 2, 2, 1], [1, 1, 0, 0, 0, 1], [1, 1, 0, 0, 0, 2], [1, 1, 0, 0, 2, 1], [1, 1, 0, 0, 2, 2], [1, 1, 0, 1, 0, 0], [1, 1, 0, 1, 0, 2], [1, 1, 0, 1, 2, 0], [1, 1, 0, 1, 2, 2], [1, 1, 0, 2, 0, 0], [1, 1, 0, 2, 0, 1], [1, 1, 0, 2, 2, 0], [1, 1, 0, 2, 2, 1], [1, 1, 2, 0, 0, 1], [1, 1, 2, 0, 0, 2], [1, 1, 2, 0, 2, 1], [1, 1, 2, 0, 2, 2], [1, 1, 2, 1, 0, 0], [1, 1, 2, 1, 0, 2], [1, 1, 2, 1, 2, 0], [1, 1, 2, 1, 2, 2], [1, 1, 2, 2, 0, 0], [1, 1, 2, 2, 0, 1], [1, 1, 2, 2, 2, 0], [1, 1, 2, 2, 2, 1], [1, 2, 0, 0, 0, 1], [1, 2, 0, 0, 0, 2], [1, 2, 0, 0, 2, 1], [1, 2, 0, 0, 2, 2], [1, 2, 0, 1, 0, 0], [1, 2, 0, 1, 0, 2], [1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 2], [1, 2, 0, 2, 0, 0], [1, 2, 0, 2, 0, 1], [1, 2, 0, 2, 2, 0], [1, 2, 0, 2, 2, 1], [2, 0, 1, 0, 0, 1], [2, 0, 1, 0, 0, 2], [2, 0, 1, 0, 1, 1], [2, 0, 1, 0, 1, 2], [2, 0, 1, 1, 0, 0], [2, 0, 1, 1, 0, 2], [2, 0, 1, 1, 1, 0], [2, 0, 1, 1, 1, 2], [2, 0, 1, 2, 0, 0], [2, 0, 1, 2, 0, 1], [2, 0, 1, 2, 1, 0], [2, 0, 1, 2, 1, 1], [2, 1, 0, 0, 0, 1], [2, 1, 0, 0, 0, 2], [2, 1, 0, 0, 1, 1], [2, 1, 0, 0, 1, 2], [2, 1, 0, 1, 0, 0], [2, 1, 0, 1, 0, 2], [2, 1, 0, 1, 1, 0], [2, 1, 0, 1, 1, 2], [2, 1, 0, 2, 0, 0], [2, 1, 0, 2, 0, 1], [2, 1, 0, 2, 1, 0], [2, 1, 0, 2, 1, 1], [2, 2, 0, 0, 0, 1], [2, 2, 0, 0, 0, 2], [2, 2, 0, 0, 1, 1], [2, 2, 0, 0, 1, 2], [2, 2, 0, 1, 0, 0], [2, 2, 0, 1, 0, 2], [2, 2, 0, 1, 1, 0], [2, 2, 0, 1, 1, 2], [2, 2, 0, 2, 0, 0], [2, 2, 0, 2, 0, 1], [2, 2, 0, 2, 1, 0], [2, 2, 0, 2, 1, 1], [2, 2, 1, 0, 0, 1], [2, 2, 1, 0, 0, 2], [2, 2, 1, 0, 1, 1], [2, 2, 1, 0, 1, 2], [2, 2, 1, 1, 0, 0], [2, 2, 1, 1, 0, 2], [2, 2, 1, 1, 1, 0], [2, 2, 1, 1, 1, 2], [2, 2, 1, 2, 0, 0], [2, 2, 1, 2, 0, 1], [2, 2, 1, 2, 1, 0], [2, 2, 1, 2, 1, 1]]
theorem all_step5 : step allStage5 = allStage6 := by decide
def allStage7 : List (List (Fin 3)) := [[0, 0, 1, 0, 1, 1, 2], [0, 0, 1, 0, 2, 2, 1], [0, 0, 1, 1, 1, 0, 2], [0, 0, 1, 1, 2, 0, 1], [0, 0, 1, 1, 2, 2, 1], [0, 0, 1, 2, 1, 0, 2], [0, 0, 1, 2, 1, 1, 2], [0, 0, 1, 2, 2, 0, 1], [0, 0, 2, 0, 1, 1, 2], [0, 0, 2, 0, 2, 2, 1], [0, 0, 2, 1, 1, 0, 2], [0, 0, 2, 1, 2, 0, 1], [0, 0, 2, 1, 2, 2, 1], [0, 0, 2, 2, 1, 0, 2], [0, 0, 2, 2, 1, 1, 2], [0, 0, 2, 2, 2, 0, 1], [0, 1, 2, 0, 1, 1, 0], [0, 1, 2, 0, 1, 1, 2], [0, 1, 2, 0, 1, 2, 0], [0, 1, 2, 0, 2, 1, 0], [0, 1, 2, 0, 2, 2, 0], [0, 1, 2, 1, 1, 0, 2], [0, 1, 2, 1, 1, 2, 0], [0, 1, 2, 1, 2, 2, 0], [0, 1, 2, 2, 1, 0, 2], [0, 1, 2, 2, 1, 1, 0], [0, 1, 2, 2, 1, 1, 2], [0, 1, 2, 2, 2, 1, 0], [0, 2, 1, 0, 1, 1, 0], [0, 2, 1, 0, 1, 2, 0], [0, 2, 1, 0, 2, 1, 0], [0, 2, 1, 0, 2, 2, 0], [0, 2, 1, 0, 2, 2, 1], [0, 2, 1, 1, 1, 2, 0], [0, 2, 1, 1, 2, 0, 1], [0, 2, 1, 1, 2, 2, 0], [0, 2, 1, 1, 2, 2, 1], [0, 2, 1, 2, 1, 1, 0], [0, 2, 1, 2, 2, 0, 1], [0, 2, 1, 2, 2, 1, 0], [1, 0, 2, 0, 0, 1, 2], [1, 0, 2, 0, 0, 2, 1], [1, 0, 2, 0, 2, 2, 1], [1, 0, 2, 1, 0, 0, 1], [1, 0, 2, 1, 0, 0, 2], [1, 0, 2, 1, 0, 2, 1], [1, 0, 2, 1, 2, 0, 1], [1, 0, 2, 1, 2, 2, 1], [1, 0, 2, 2, 0, 0, 1], [1, 0, 2, 2, 0, 0, 2], [1, 0, 2, 2, 0, 1, 2], [1, 0, 2, 2, 2, 0, 1], [1, 1, 0, 0, 0, 1, 2], [1, 1, 0, 0, 2, 1, 0], [1, 1, 0, 0, 2, 2, 0], [1, 1, 0, 1, 0, 0, 2], [1, 1, 0, 1, 2, 2, 0], [1, 1, 0, 2, 0, 0, 2], [1, 1, 0, 2, 0, 1, 2], [1, 1, 0, 2, 2, 1, 0], [1, 1, 2, 0, 0, 1, 2], [1, 1, 2, 0, 2, 1, 0], [1, 1, 2, 0, 2, 2, 0], [1, 1, 2, 1, 0, 0, 2], [1, 1, 2, 1, 2, 2, 0], [1, 1, 2, 2, 0, 0, 2], [1, 1, 2, 2, 0, 1, 2], [1, 1, 2, 2, 2, 1, 0], [1, 2, 0, 0, 0, 2, 1], [1, 2, 0, 0, 2, 1, 0], [1, 2, 0, 0, 2, 2, 0], [1, 2, 0, 0, 2, 2, 1], [1, 2, 0, 1, 0, 0, 1], [1, 2, 0, 1, 0, 2, 1], [1, 2, 0, 1, 2, 0, 1], [1, 2, 0, 1, 2, 2, 0], [1, 2, 0, 1, 2, 2, 1], [1, 2, 0, 2, 0, 0, 1], [1, 2, 0, 2, 2, 0, 1], [1, 2, 0, 2, 2, 1, 0], [2, 0, 1, 0, 0, 1, 2], [2, 0, 1, 0, 0, 2, 1], [2, 0, 1, 0, 1, 1, 2], [2, 0, 1, 1, 0, 0, 1], [2, 0, 1, 1, 0, 0, 2], [2, 0, 1, 1, 0, 2, 1], [2, 0, 1, 1, 1, 0, 2], [2, 0, 1, 2, 0, 0, 1], [2, 0, 1, 2, 0, 0, 2], [2, 0, 1, 2, 0, 1, 2], [2, 0, 1, 2, 1, 0, 2], [2, 0, 1, 2, 1, 1, 2], [2, 1, 0, 0, 0, 1, 2], [2, 1, 0, 0, 1, 1, 0], [2, 1, 0, 0, 1, 1, 2], [2, 1, 0, 0, 1, 2, 0], [2, 1, 0, 1, 0, 0, 2], [2, 1, 0, 1, 1, 0, 2], [2, 1, 0, 1, 1, 2, 0], [2, 1, 0, 2, 0, 0, 2], [2, 1, 0, 2, 0, 1, 2], [2, 1, 0, 2, 1, 0, 2], [2, 1, 0, 2, 1, 1, 0], [2, 1, 0, 2, 1, 1, 2], [2, 2, 0, 0, 0, 2, 1], [2, 2, 0, 0, 1, 1, 0], [2, 2, 0, 0, 1, 2, 0], [2, 2, 0, 1, 0, 0, 1], [2, 2, 0, 1, 0, 2, 1], [2, 2, 0, 1, 1, 2, 0], [2, 2, 0, 2, 0, 0, 1], [2, 2, 0, 2, 1, 1, 0], [2, 2, 1, 0, 0, 2, 1], [2, 2, 1, 0, 1, 1, 0], [2, 2, 1, 0, 1, 2, 0], [2, 2, 1, 1, 0, 0, 1], [2, 2, 1, 1, 0, 2, 1], [2, 2, 1, 1, 1, 2, 0], [2, 2, 1, 2, 0, 0, 1], [2, 2, 1, 2, 1, 1, 0]]
theorem all_step6 : step allStage6 = allStage7 := by decide
def allStage8 : List (List (Fin 3)) := [[0, 0, 1, 0, 1, 1, 2, 2], [0, 0, 1, 0, 2, 2, 1, 1], [0, 0, 1, 1, 1, 0, 2, 2], [0, 0, 1, 1, 2, 0, 1, 1], [0, 0, 1, 1, 2, 2, 1, 1], [0, 0, 1, 2, 1, 0, 2, 2], [0, 0, 1, 2, 1, 1, 2, 2], [0, 0, 1, 2, 2, 0, 1, 1], [0, 0, 2, 0, 1, 1, 2, 2], [0, 0, 2, 0, 2, 2, 1, 1], [0, 0, 2, 1, 1, 0, 2, 2], [0, 0, 2, 1, 2, 0, 1, 1], [0, 0, 2, 1, 2, 2, 1, 1], [0, 0, 2, 2, 1, 0, 2, 2], [0, 0, 2, 2, 1, 1, 2, 2], [0, 0, 2, 2, 2, 0, 1, 1], [0, 1, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 1, 0, 2], [0, 1, 2, 0, 1, 1, 2, 0], [0, 1, 2, 0, 1, 1, 2, 2], [0, 1, 2, 0, 1, 2, 0, 0], [0, 1, 2, 0, 1, 2, 0, 2], [0, 1, 2, 0, 2, 1, 0, 0], [0, 1, 2, 0, 2, 2, 0, 0], [0, 1, 2, 1, 1, 0, 2, 0], [0, 1, 2, 1, 1, 0, 2, 2], [0, 1, 2, 1, 1, 2, 0, 0], [0, 1, 2, 1, 1, 2, 0, 2], [0, 1, 2, 1, 2, 2, 0, 0], [0, 1, 2, 2, 1, 0, 2, 0], [0, 1, 2, 2, 1, 0, 2, 2], [0, 1, 2, 2, 1, 1, 0, 0], [0, 1, 2, 2, 1, 1, 0, 2], [0, 1, 2, 2, 1, 1, 2, 0], [0, 1, 2, 2, 1, 1, 2, 2], [0, 1, 2, 2, 2, 1, 0, 0], [0, 2, 1, 0, 1, 1, 0, 0], [0, 2, 1, 0, 1, 2, 0, 0], [0, 2, 1, 0, 2, 1, 0, 0], [0, 2, 1, 0, 2, 1, 0, 1], [0, 2, 1, 0, 2, 2, 0, 0], [0, 2, 1, 0, 2, 2, 0, 1], [0, 2, 1, 0, 2, 2, 1, 0], [0, 2, 1, 0, 2, 2, 1, 1], [0, 2, 1, 1, 1, 2, 0, 0], [0, 2, 1, 1, 2, 0, 1, 0], [0, 2, 1, 1, 2, 0, 1, 1], [0, 2, 1, 1, 2, 2, 0, 0], [0, 2, 1, 1, 2, 2, 0, 1], [0, 2, 1, 1, 2, 2, 1, 0], [0, 2, 1, 1, 2, 2, 1, 1], [0, 2, 1, 2, 1, 1, 0, 0], [0, 2, 1, 2, 2, 0, 1, 0], [0, 2, 1, 2, 2, 0, 1, 1], [0, 2, 1, 2, 2, 1, 0, 0], [0, 2, 1, 2, 2, 1, 0, 1], [1, 0, 2, 0, 0, 1, 2, 1], [1, 0, 2, 0, 0, 1, 2, 2], [1, 0, 2, 0, 0, 2, 1, 1], [1, 0, 2, 0, 0, 2, 1, 2], [1, 0, 2, 0, 2, 2, 1, 1], [1, 0, 2, 1, 0, 0, 1, 1], [1, 0, 2, 1, 0, 0, 1, 2], [1, 0, 2, 1, 0, 0, 2, 1], [1, 0, 2, 1, 0, 0, 2, 2], [1, 0, 2, 1, 0, 2, 1, 1], [1, 0, 2, 1, 0, 2, 1, 2], [1, 0, 2, 1, 2, 0, 1, 1], [1, 0, 2, 1, 2, 2, 1, 1], [1, 0, 2, 2, 0, 0, 1, 1], [1, 0, 2, 2, 0, 0, 1, 2], [1, 0, 2, 2, 0, 0, 2, 1], [1, 0, 2, 2, 0, 0, 2, 2], [1, 0, 2, 2, 0, 1, 2, 1], [1, 0, 2, 2, 0, 1, 2, 2], [1, 0, 2, 2, 2, 0, 1, 1], [1, 1, 0, 0, 0, 1, 2, 2], [1, 1, 0, 0, 2, 1, 0, 0], [1, 1, 0, 0, 2, 2, 0, 0], [1, 1, 0, 1, 0, 0, 2, 2], [1, 1, 0, 1, 2, 2, 0, 0], [1, 1, 0, 2, 0, 0, 2, 2], [1, 1, 0, 2, 0, 1, 2, 2], [1, 1, 0, 2, 2, 1, 0, 0], [1, 1, 2, 0, 0, 1, 2, 2], [1, 1, 2, 0, 2, 1, 0, 0], [1, 1, 2, 0, 2, 2, 0, 0], [1, 1, 2, 1, 0, 0, 2, 2], [1, 1, 2, 1, 2, 2, 0, 0], [1, 1, 2, 2, 0, 0, 2, 2], [1, 1, 2, 2, 0, 1, 2, 2], [1, 1, 2, 2, 2, 1, 0, 0], [1, 2, 0, 0, 0, 2, 1, 1], [1, 2, 0, 0, 2, 1, 0, 0], [1, 2, 0, 0, 2, 1, 0, 1], [1, 2, 0, 0, 2, 2, 0, 0], [1, 2, 0, 0, 2, 2, 0, 1], [1, 2, 0, 0, 2, 2, 1, 0], [1, 2, 0, 0, 2, 2, 1, 1], [1, 2, 0, 1, 0, 0, 1, 1], [1, 2, 0, 1, 0, 2, 1, 1], [1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 1], [1, 2, 0, 1, 2, 2, 0, 0], [1, 2, 0, 1, 2, 2, 0, 1], [1, 2, 0, 1, 2, 2, 1, 0], [1, 2, 0, 1, 2, 2, 1, 1], [1, 2, 0, 2, 0, 0, 1, 1], [1, 2, 0, 2, 2, 0, 1, 0], [1, 2, 0, 2, 2, 0, 1, 1], [1, 2, 0, 2, 2, 1, 0, 0], [1, 2, 0, 2, 2, 1, 0, 1], [2, 0, 1, 0, 0, 1, 2, 1], [2, 0, 1, 0, 0, 1, 2, 2], [2, 0, 1, 0, 0, 2, 1, 1], [2, 0, 1, 0, 0, 2, 1, 2], [2, 0, 1, 0, 1, 1, 2, 2], [2, 0, 1, 1, 0, 0, 1, 1], [2, 0, 1, 1, 0, 0, 1, 2], [2, 0, 1, 1, 0, 0, 2, 1], [2, 0, 1, 1, 0, 0, 2, 2], [2, 0, 1, 1, 0, 2, 1, 1], [2, 0, 1, 1, 0, 2, 1, 2], [2, 0, 1, 1, 1, 0, 2, 2], [2, 0, 1, 2, 0, 0, 1, 1], [2, 0, 1, 2, 0, 0, 1, 2], [2, 0, 1, 2, 0, 0, 2, 1], [2, 0, 1, 2, 0, 0, 2, 2], [2, 0, 1, 2, 0, 1, 2, 1], [2, 0, 1, 2, 0, 1, 2, 2], [2, 0, 1, 2, 1, 0, 2, 2], [2, 0, 1, 2, 1, 1, 2, 2], [2, 1, 0, 0, 0, 1, 2, 2], [2, 1, 0, 0, 1, 1, 0, 0], [2, 1, 0, 0, 1, 1, 0, 2], [2, 1, 0, 0, 1, 1, 2, 0], [2, 1, 0, 0, 1, 1, 2, 2], [2, 1, 0, 0, 1, 2, 0, 0], [2, 1, 0, 0, 1, 2, 0, 2], [2, 1, 0, 1, 0, 0, 2, 2], [2, 1, 0, 1, 1, 0, 2, 0], [2, 1, 0, 1, 1, 0, 2, 2], [2, 1, 0, 1, 1, 2, 0, 0], [2, 1, 0, 1, 1, 2, 0, 2], [2, 1, 0, 2, 0, 0, 2, 2], [2, 1, 0, 2, 0, 1, 2, 2], [2, 1, 0, 2, 1, 0, 2, 0], [2, 1, 0, 2, 1, 0, 2, 2], [2, 1, 0, 2, 1, 1, 0, 0], [2, 1, 0, 2, 1, 1, 0, 2], [2, 1, 0, 2, 1, 1, 2, 0], [2, 1, 0, 2, 1, 1, 2, 2], [2, 2, 0, 0, 0, 2, 1, 1], [2, 2, 0, 0, 1, 1, 0, 0], [2, 2, 0, 0, 1, 2, 0, 0], [2, 2, 0, 1, 0, 0, 1, 1], [2, 2, 0, 1, 0, 2, 1, 1], [2, 2, 0, 1, 1, 2, 0, 0], [2, 2, 0, 2, 0, 0, 1, 1], [2, 2, 0, 2, 1, 1, 0, 0], [2, 2, 1, 0, 0, 2, 1, 1], [2, 2, 1, 0, 1, 1, 0, 0], [2, 2, 1, 0, 1, 2, 0, 0], [2, 2, 1, 1, 0, 0, 1, 1], [2, 2, 1, 1, 0, 2, 1, 1], [2, 2, 1, 1, 1, 2, 0, 0], [2, 2, 1, 2, 0, 0, 1, 1], [2, 2, 1, 2, 1, 1, 0, 0]]
theorem all_step7 : step allStage7 = allStage8 := by decide
def allStage9 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0], [0, 0, 1, 2, 1, 1, 2, 2, 0], [0, 0, 2, 1, 2, 2, 1, 1, 0], [0, 0, 2, 2, 1, 1, 2, 2, 0], [0, 1, 2, 0, 1, 1, 0, 0, 2], [0, 1, 2, 0, 1, 1, 2, 0, 2], [0, 1, 2, 0, 2, 2, 0, 0, 1], [0, 1, 2, 1, 1, 0, 2, 0, 2], [0, 1, 2, 1, 1, 2, 0, 2, 0], [0, 1, 2, 2, 1, 1, 0, 2, 0], [0, 1, 2, 2, 1, 1, 2, 2, 0], [0, 2, 1, 0, 1, 1, 0, 0, 2], [0, 2, 1, 0, 2, 2, 0, 0, 1], [0, 2, 1, 0, 2, 2, 1, 0, 1], [0, 2, 1, 1, 2, 2, 0, 1, 0], [0, 2, 1, 1, 2, 2, 1, 1, 0], [0, 2, 1, 2, 2, 0, 1, 0, 1], [0, 2, 1, 2, 2, 1, 0, 1, 0], [1, 0, 2, 0, 0, 1, 2, 1, 2], [1, 0, 2, 0, 0, 2, 1, 2, 1], [1, 0, 2, 1, 0, 0, 1, 1, 2], [1, 0, 2, 1, 0, 0, 2, 1, 2], [1, 0, 2, 1, 2, 2, 1, 1, 0], [1, 0, 2, 2, 0, 0, 1, 2, 1], [1, 0, 2, 2, 0, 0, 2, 2, 1], [1, 1, 0, 0, 2, 2, 0, 0, 1], [1, 1, 0, 2, 0, 0, 2, 2, 1], [1, 1, 2, 0, 2, 2, 0, 0, 1], [1, 1, 2, 2, 0, 0, 2, 2, 1], [1, 2, 0, 0, 2, 2, 0, 0, 1], [1, 2, 0, 0, 2, 2, 1, 0, 1], [1, 2, 0, 1, 0, 0, 1, 1, 2], [1, 2, 0, 1, 2, 2, 0, 1, 0], [1, 2, 0, 1, 2, 2, 1, 1, 0], [1, 2, 0, 2, 2, 0, 1, 0, 1], [1, 2, 0, 2, 2, 1, 0, 1, 0], [2, 0, 1, 0, 0, 1, 2, 1, 2], [2, 0, 1, 0, 0, 2, 1, 2, 1], [2, 0, 1, 1, 0, 0, 1, 1, 2], [2, 0, 1, 1, 0, 0, 2, 1, 2], [2, 0, 1, 2, 0, 0, 1, 2, 1], [2, 0, 1, 2, 0, 0, 2, 2, 1], [2, 0, 1, 2, 1, 1, 2, 2, 0], [2, 1, 0, 0, 1, 1, 0, 0, 2], [2, 1, 0, 0, 1, 1, 2, 0, 2], [2, 1, 0, 1, 1, 0, 2, 0, 2], [2, 1, 0, 1, 1, 2, 0, 2, 0], [2, 1, 0, 2, 0, 0, 2, 2, 1], [2, 1, 0, 2, 1, 1, 0, 2, 0], [2, 1, 0, 2, 1, 1, 2, 2, 0], [2, 2, 0, 0, 1, 1, 0, 0, 2], [2, 2, 0, 1, 0, 0, 1, 1, 2], [2, 2, 1, 0, 1, 1, 0, 0, 2], [2, 2, 1, 1, 0, 0, 1, 1, 2]]
theorem all_step8 : step allStage8 = allStage9 := by decide
def allStage10 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0, 0], [0, 0, 1, 2, 1, 1, 2, 2, 0, 0], [0, 0, 2, 1, 2, 2, 1, 1, 0, 0], [0, 0, 2, 2, 1, 1, 2, 2, 0, 0], [0, 1, 2, 0, 1, 1, 2, 0, 2, 0], [0, 1, 2, 0, 2, 2, 0, 0, 1, 1], [0, 1, 2, 1, 1, 0, 2, 0, 2, 0], [0, 1, 2, 2, 1, 1, 2, 2, 0, 0], [0, 2, 1, 0, 1, 1, 0, 0, 2, 2], [0, 2, 1, 0, 2, 2, 1, 0, 1, 0], [0, 2, 1, 1, 2, 2, 1, 1, 0, 0], [0, 2, 1, 2, 2, 0, 1, 0, 1, 0], [1, 0, 2, 0, 0, 1, 2, 1, 2, 1], [1, 0, 2, 1, 0, 0, 2, 1, 2, 1], [1, 0, 2, 1, 2, 2, 1, 1, 0, 0], [1, 0, 2, 2, 0, 0, 2, 2, 1, 1], [1, 1, 0, 0, 2, 2, 0, 0, 1, 1], [1, 1, 0, 2, 0, 0, 2, 2, 1, 1], [1, 1, 2, 0, 2, 2, 0, 0, 1, 1], [1, 1, 2, 2, 0, 0, 2, 2, 1, 1], [1, 2, 0, 0, 2, 2, 0, 0, 1, 1], [1, 2, 0, 1, 0, 0, 1, 1, 2, 2], [1, 2, 0, 1, 2, 2, 0, 1, 0, 1], [1, 2, 0, 2, 2, 1, 0, 1, 0, 1], [2, 0, 1, 0, 0, 2, 1, 2, 1, 2], [2, 0, 1, 1, 0, 0, 1, 1, 2, 2], [2, 0, 1, 2, 0, 0, 1, 2, 1, 2], [2, 0, 1, 2, 1, 1, 2, 2, 0, 0], [2, 1, 0, 0, 1, 1, 0, 0, 2, 2], [2, 1, 0, 1, 1, 2, 0, 2, 0, 2], [2, 1, 0, 2, 0, 0, 2, 2, 1, 1], [2, 1, 0, 2, 1, 1, 0, 2, 0, 2], [2, 2, 0, 0, 1, 1, 0, 0, 2, 2], [2, 2, 0, 1, 0, 0, 1, 1, 2, 2], [2, 2, 1, 0, 1, 1, 0, 0, 2, 2], [2, 2, 1, 1, 0, 0, 1, 1, 2, 2]]
theorem all_step9 : step allStage9 = allStage10 := by decide
def allStage11 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0, 0, 2], [0, 0, 1, 2, 1, 1, 2, 2, 0, 0, 1], [0, 0, 2, 1, 2, 2, 1, 1, 0, 0, 2], [0, 0, 2, 2, 1, 1, 2, 2, 0, 0, 1], [0, 1, 2, 0, 1, 1, 2, 0, 2, 0, 0], [0, 1, 2, 0, 2, 2, 0, 0, 1, 1, 2], [0, 1, 2, 1, 1, 0, 2, 0, 2, 0, 0], [0, 2, 1, 0, 1, 1, 0, 0, 2, 2, 1], [0, 2, 1, 0, 2, 2, 1, 0, 1, 0, 0], [0, 2, 1, 2, 2, 0, 1, 0, 1, 0, 0], [1, 0, 2, 0, 0, 1, 2, 1, 2, 1, 1], [1, 0, 2, 1, 0, 0, 2, 1, 2, 1, 1], [1, 0, 2, 1, 2, 2, 1, 1, 0, 0, 2], [1, 1, 0, 0, 2, 2, 0, 0, 1, 1, 2], [1, 1, 0, 2, 0, 0, 2, 2, 1, 1, 0], [1, 1, 2, 0, 2, 2, 0, 0, 1, 1, 2], [1, 1, 2, 2, 0, 0, 2, 2, 1, 1, 0], [1, 2, 0, 1, 0, 0, 1, 1, 2, 2, 0], [1, 2, 0, 1, 2, 2, 0, 1, 0, 1, 1], [1, 2, 0, 2, 2, 1, 0, 1, 0, 1, 1], [2, 0, 1, 0, 0, 2, 1, 2, 1, 2, 2], [2, 0, 1, 2, 0, 0, 1, 2, 1, 2, 2], [2, 0, 1, 2, 1, 1, 2, 2, 0, 0, 1], [2, 1, 0, 1, 1, 2, 0, 2, 0, 2, 2], [2, 1, 0, 2, 0, 0, 2, 2, 1, 1, 0], [2, 1, 0, 2, 1, 1, 0, 2, 0, 2, 2], [2, 2, 0, 0, 1, 1, 0, 0, 2, 2, 1], [2, 2, 0, 1, 0, 0, 1, 1, 2, 2, 0], [2, 2, 1, 0, 1, 1, 0, 0, 2, 2, 1], [2, 2, 1, 1, 0, 0, 1, 1, 2, 2, 0]]
theorem all_step10 : step allStage10 = allStage11 := by decide
def allStage12 : List (List (Fin 3)) := [[0, 0, 1, 1, 2, 2, 1, 1, 0, 0, 2, 2], [0, 0, 2, 2, 1, 1, 2, 2, 0, 0, 1, 1], [0, 1, 2, 0, 1, 1, 2, 0, 2, 0, 0, 1], [0, 1, 2, 0, 2, 2, 0, 0, 1, 1, 2, 1], [0, 2, 1, 0, 1, 1, 0, 0, 2, 2, 1, 2], [0, 2, 1, 0, 2, 2, 1, 0, 1, 0, 0, 2], [1, 0, 2, 1, 0, 0, 2, 1, 2, 1, 1, 0], [1, 0, 2, 1, 2, 2, 1, 1, 0, 0, 2, 0], [1, 1, 0, 0, 2, 2, 0, 0, 1, 1, 2, 2], [1, 1, 2, 2, 0, 0, 2, 2, 1, 1, 0, 0], [1, 2, 0, 1, 0, 0, 1, 1, 2, 2, 0, 2], [1, 2, 0, 1, 2, 2, 0, 1, 0, 1, 1, 2], [2, 0, 1, 2, 0, 0, 1, 2, 1, 2, 2, 0], [2, 0, 1, 2, 1, 1, 2, 2, 0, 0, 1, 0], [2, 1, 0, 2, 0, 0, 2, 2, 1, 1, 0, 1], [2, 1, 0, 2, 1, 1, 0, 2, 0, 2, 2, 1], [2, 2, 0, 0, 1, 1, 0, 0, 2, 2, 1, 1], [2, 2, 1, 1, 0, 0, 1, 1, 2, 2, 0, 0]]
theorem all_step11 : step allStage11 = allStage12 := by decide

/-- Every coloring in the last table has the forced equality. -/
theorem all_final_rigidity (c : List (Fin 3)) (h : c ∈ allStage12) :
    (c.getD 0 0 = c.getD 1 0 → c.getD 3 0 = c.getD 2 0) ∧
    (c.getD 0 0 ≠ c.getD 1 0 → c.getD 3 0 = c.getD 0 0) := by
  simp [allStage12] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide


/-- A search from the empty list includes every prefix of a valid coloring. -/
def allIter : Nat → List (List (Fin 3))
  | 0 => allStage0
  | n + 1 => step (allIter n)

theorem all_complete (c : List (Fin 3)) (hv : validPrefix c = true) :
    ∀ n : Nat, n ≤ c.length → c.take n ∈ allIter n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [allIter, allStage0]
  | succ n ih =>
      intro hlen
      have hlt : n < c.length := by omega
      have hprev : c.take n ∈ allIter n := ih (by omega)
      have hnext : validPrefix (c.take (n + 1)) = true :=
        validPrefix_take c hv (n + 1)
      have htake : c.take (n + 1) =
          c.take n ++ [c.get ⟨n, hlt⟩] := by
        simpa using (List.take_succ_eq_append_getElem (l := c) (i := n) hlt)
      change c.take (n + 1) ∈ step (allIter n)
      rw [htake]
      apply step_complete (allIter n) (c.take n) (c.get ⟨n, hlt⟩) hprev
      rw [← htake]
      exact hnext

theorem all_iter_0 : allIter 0 = allStage0 := by rfl
theorem all_iter_1 : allIter 1 = allStage1 := by
  change step (allIter 0) = allStage1
  exact (congrArg step all_iter_0).trans all_step0
theorem all_iter_2 : allIter 2 = allStage2 := by
  change step (allIter 1) = allStage2
  exact (congrArg step all_iter_1).trans all_step1
theorem all_iter_3 : allIter 3 = allStage3 := by
  change step (allIter 2) = allStage3
  exact (congrArg step all_iter_2).trans all_step2
theorem all_iter_4 : allIter 4 = allStage4 := by
  change step (allIter 3) = allStage4
  exact (congrArg step all_iter_3).trans all_step3
theorem all_iter_5 : allIter 5 = allStage5 := by
  change step (allIter 4) = allStage5
  exact (congrArg step all_iter_4).trans all_step4
theorem all_iter_6 : allIter 6 = allStage6 := by
  change step (allIter 5) = allStage6
  exact (congrArg step all_iter_5).trans all_step5
theorem all_iter_7 : allIter 7 = allStage7 := by
  change step (allIter 6) = allStage7
  exact (congrArg step all_iter_6).trans all_step6
theorem all_iter_8 : allIter 8 = allStage8 := by
  change step (allIter 7) = allStage8
  exact (congrArg step all_iter_7).trans all_step7
theorem all_iter_9 : allIter 9 = allStage9 := by
  change step (allIter 8) = allStage9
  exact (congrArg step all_iter_8).trans all_step8
theorem all_iter_10 : allIter 10 = allStage10 := by
  change step (allIter 9) = allStage10
  exact (congrArg step all_iter_9).trans all_step9
theorem all_iter_11 : allIter 11 = allStage11 := by
  change step (allIter 10) = allStage11
  exact (congrArg step all_iter_10).trans all_step10
theorem all_iter_12 : allIter 12 = allStage12 := by
  change step (allIter 11) = allStage12
  exact (congrArg step all_iter_11).trans all_step11

/-- The finite rigidity statement holds for every valid full coloring. -/
theorem full_rigidity (c : List (Fin 3))
    (hlen : c.length = 12) (hv : validPrefix c = true) :
    (c.getD 0 0 = c.getD 1 0 → c.getD 3 0 = c.getD 2 0) ∧
    (c.getD 0 0 ≠ c.getD 1 0 → c.getD 3 0 = c.getD 0 0) := by
  apply all_final_rigidity c
  have h := all_complete c hv 12 (by omega)
  rw [all_iter_12] at h
  have ht : c.take 12 = c := by simpa [hlen] using (List.take_length c)
  simpa [ht] using h

end DiracHajos

import D5Structure

/-!
An explicit edge-set construction for the whole Dirac--Hajos output family.
Here `r = k - 4`; the output has `21 + 2*r` labeled vertices. The theorem
at the end checks that `r = 1` is exactly the 68-edge D5 list already used.

This file defines the family. Its chromatic and criticality claims require
additional theorems.
-/

namespace DiracHajos

/-- Edges within a clique whose labels are supplied as a list. -/
def cliqueEdges (xs : List Nat) : Finset (Nat × Nat) :=
  (xs.flatMap fun x =>
    xs.filterMap fun y => if x < y then some (x, y) else none).toFinset

/-- Edges joining two lists of vertices, with the first endpoint in `xs`. -/
def crossEdges (xs ys : List Nat) : Finset (Nat × Nat) :=
  (xs.flatMap fun x => ys.map fun y => (x, y)).toFinset

def firstClique (r : Nat) : List Nat :=
  (List.range r).map fun i => 21 + i

def secondClique (r : Nat) : List Nat :=
  (List.range r).map fun i => 21 + r + i

def secondBase : List Nat :=
  (List.range 12).map secondIndex

/-- First and second copies of B, with their shared triangle identified. -/
def baseCopyEdges : Finset (Nat × Nat) :=
  edges.toFinset ∪
    (edges.map fun e => (secondIndex e.1, secondIndex e.2)).toFinset

/-- Edges of the output graph with two joined clique copies of size `r`.
The 03 edge is removed in each copy and the two vertices labeled 3 and 12
are joined. -/
def dEdges (r : Nat) : Finset (Nat × Nat) :=
  let q₁ := firstClique r
  let q₂ := secondClique r
  let allEdges := baseCopyEdges ∪
    cliqueEdges q₁ ∪ cliqueEdges q₂ ∪
    crossEdges (List.range 12) q₁ ∪ crossEdges secondBase q₂
  insert (3, 12) ((allEdges.erase (0, 3)).erase (0, 12))

/-- The symbolic family agrees with the concrete verified edge list at k=5. -/
theorem dEdges_one_eq_d5 :
    dEdges 1 = d5OutputEdges.toFinset := by
  native_decide

end DiracHajos

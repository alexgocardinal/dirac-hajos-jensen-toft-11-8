import GeneralColorPullback

/-!
The two added cliques use distinct colors, and their incident base copies
avoid all those colors in any proper coloring of the output graph.
-/

namespace DiracHajos

def firstCliqueColors (r : Nat) (c : Nat → Fin (r + 3)) :
    Fin r → Fin (r + 3) := fun j => c (21 + j.val)

def secondCliqueColors (r : Nat) (c : Nat → Fin (r + 3)) :
    Fin r → Fin (r + 3) := fun j => c (21 + r + j.val)

theorem firstCliqueColors_injective (r : Nat) (c : Nat → Fin (r + 3))
    (hp : ProperOutput r c) : Function.Injective (firstCliqueColors r c) := by
  intro i j heq
  by_contra hne
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (hp _ (dEdges_first_clique r i j hij)) heq
  · exact hne hij
  · exact (hp _ (dEdges_first_clique r j i hji)) heq.symm

theorem secondCliqueColors_injective (r : Nat) (c : Nat → Fin (r + 3))
    (hp : ProperOutput r c) : Function.Injective (secondCliqueColors r c) := by
  intro i j heq
  by_contra hne
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (hp _ (dEdges_second_clique r i j hij)) heq
  · exact hne hij
  · exact (hp _ (dEdges_second_clique r j i hji)) heq.symm

theorem firstColors_avoid_clique (r : Nat) (c : Nat → Fin (r + 3))
    (hp : ProperOutput r c) :
    ∀ i : Nat, i < (firstColors r c).length →
      ∀ j : Fin r, (firstColors r c).getD i default ≠
        firstCliqueColors r c j := by
  intro i hi j
  have hi' : i < 12 := by simpa [firstColors] using hi
  have hget : (firstColors r c).getD i default = c i := by
    simp [firstColors, List.getD, hi']
  rw [hget]
  exact hp _ (dEdges_first_join r i (by simpa [firstColors] using hi) j)

theorem secondColors_avoid_clique (r : Nat) (c : Nat → Fin (r + 3))
    (hp : ProperOutput r c) :
    ∀ i : Nat, i < (secondColors r c).length →
      ∀ j : Fin r, (secondColors r c).getD i default ≠
        secondCliqueColors r c j := by
  intro i hi j
  have hi' : i < 12 := by simpa [secondColors] using hi
  have hget : (secondColors r c).getD i default = c (secondIndex i) := by
    simp [secondColors, List.getD, hi']
  rw [hget]
  exact hp _ (dEdges_second_join r i (by simpa [secondColors] using hi) j)

end DiracHajos

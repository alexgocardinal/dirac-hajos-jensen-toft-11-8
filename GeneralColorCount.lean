import Mathlib

/-!
Pigeonhole step for the all-k construction. A clique of `r` vertices uses `r`
different colors from a palette of `r + 3` colors. Four further colors all
different from the clique colors cannot exist.
-/

namespace DiracHajos

/-- There cannot be disjoint sets of `r` and four distinct colors inside
`Fin (r + 3)`. The second set is presented by an injective map from `Fin 4`. -/
theorem no_four_colors_outside_clique (r : Nat)
    (clique : Fin r → Fin (r + 3))
    (four : Fin 4 → Fin (r + 3))
    (hc : Function.Injective clique)
    (hf : Function.Injective four)
    (hdisjoint : ∀ i j, clique i ≠ four j) : False := by
  let combined : (Fin r ⊕ Fin 4) → Fin (r + 3) := fun x =>
    match x with
    | Sum.inl i => clique i
    | Sum.inr j => four j
  have hcombined : Function.Injective combined := by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        change clique i = clique j at h
        exact congrArg Sum.inl (hc h)
      | inr j =>
        change clique i = four j at h
        exact False.elim ((hdisjoint i j) h)
    | inr i =>
      cases y with
      | inl j =>
        change four i = clique j at h
        exact False.elim ((hdisjoint j i) h.symm)
      | inr j =>
        change four i = four j at h
        exact congrArg Sum.inr (hf h)
  have hcard := Fintype.card_le_of_injective combined hcombined
  have impossible : r + 4 ≤ r + 3 := by simpa using hcard
  omega

end DiracHajos

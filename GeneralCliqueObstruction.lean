import GeneralRemainingPalette
import GeneralTwoCopy

/-!
For any `r`, two base copies cannot be colored with `r + 3` colors if each
copy avoids the colors of its own injectively colored `r`-clique, its base
edges are properly colored, and the bridge joins their distinguished
vertices. The graph-specific step is to derive these hypotheses from a
coloring of the edge set `dEdges r`.
-/

namespace DiracHajos

theorem general_clique_obstruction (r : Nat)
    [Inhabited (Fin (r + 3))]
    (clique₁ clique₂ : Fin r → Fin (r + 3))
    (left right : List (Fin (r + 3)))
    (hinj₁ : Function.Injective clique₁)
    (hinj₂ : Function.Injective clique₂)
    (hlen₁ : left.length = 12)
    (hlen₂ : right.length = 12)
    (havoid₁ : ∀ i : Nat, i < left.length →
      ∀ j : Fin r, left.getD i default ≠ clique₁ j)
    (havoid₂ : ∀ i : Nat, i < right.length →
      ∀ j : Fin r, right.getD i default ≠ clique₂ j)
    (hvalid₁ : (edges.all fun e =>
      if e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ left.length then true
      else left.getD e.1 default != left.getD e.2 default) = true)
    (hvalid₂ : (edges.all fun e =>
      if e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ right.length then true
      else right.getD e.1 default != right.getD e.2 default) = true)
    (h0 : left.getD 0 default = right.getD 0 default)
    (h1 : left.getD 1 default = right.getD 1 default)
    (h2 : left.getD 2 default = right.getD 2 default)
    (hbridge : left.getD 3 default ≠ right.getD 3 default) : False := by
  obtain ⟨palette₁, hpalette₁⟩ := remaining_three_palette r clique₁ hinj₁
  obtain ⟨palette₂, hpalette₂⟩ := remaining_three_palette r clique₂ hinj₂
  apply general_two_copy_from_palettes palette₁ palette₂ left right
    hlen₁ hlen₂
  · intro i hi
    exact hpalette₁ (left.getD i default) (havoid₁ i hi)
  · intro i hi
    exact hpalette₂ (right.getD i default) (havoid₂ i hi)
  · exact hvalid₁
  · exact hvalid₂
  · exact h0
  · exact h1
  · exact h2
  · exact hbridge

end DiracHajos

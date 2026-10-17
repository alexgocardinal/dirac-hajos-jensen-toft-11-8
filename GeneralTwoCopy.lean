import GeneralPaletteRigidity
import GeneralObstruction

/-!
The two-copy contradiction for an arbitrary ambient color type. Each copy
may have its own three-color palette. A separate graph-construction theorem
must establish the hypotheses for D_k.
-/

namespace DiracHajos

theorem general_two_copy_from_palettes
    {Color : Type*} [Inhabited Color] [DecidableEq Color]
    (palette₁ palette₂ : Fin 3 → Color)
    (left right : List Color)
    (hlen₁ : left.length = 12)
    (hlen₂ : right.length = 12)
    (hpalette₁ : ∀ i : Nat, i < left.length →
      ∃ j : Fin 3, palette₁ j = left.getD i default)
    (hpalette₂ : ∀ i : Nat, i < right.length →
      ∃ j : Fin 3, palette₂ j = right.getD i default)
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
  have hr₁ := general_palette_rigidity palette₁ left hlen₁ hpalette₁ hvalid₁
  have hr₂ := general_palette_rigidity palette₂ right hlen₂ hpalette₂ hvalid₂
  exact general_two_copy_obstruction
    (fun i => left.getD i default) (fun i => right.getD i default)
    h0 h1 h2 hr₁.1 hr₁.2 hr₂.1 hr₂.2 hbridge

end DiracHajos

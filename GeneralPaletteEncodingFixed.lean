import Mathlib

/-!
The same three-color certificate can be used with any ambient color type.
When the colors of a base-graph copy all lie in the image of `palette`,
`encodePalette` translates them to Fin 3. The decode theorem ensures this
translation cannot identify two different colors from that image.

This is an intermediate lemma. It does not yet prove the all-k graph theorem.
-/

namespace DiracHajos

/-- Choose a name in `Fin 3` for a color in the given three-color palette.
For colors outside the palette, the result is arbitrarily set to zero. -/
noncomputable def encodePalette {Color : Type*}
    (palette : Fin 3 → Color) (x : Color) : Fin 3 := by
  classical
  exact if h : ∃ i : Fin 3, palette i = x then Classical.choose h else 0

theorem decode_encode_palette {Color : Type*}
    (palette : Fin 3 → Color) (x : Color)
    (hx : ∃ i : Fin 3, palette i = x) :
    palette (encodePalette palette x) = x := by
  classical
  unfold encodePalette
  simp only [dif_pos hx]
  exact Classical.choose_spec hx

/-- On the palette, encoding cannot merge two distinct colors. -/
theorem encode_palette_eq_iff {Color : Type*}
    (palette : Fin 3 → Color) (x y : Color)
    (hx : ∃ i : Fin 3, palette i = x)
    (hy : ∃ i : Fin 3, palette i = y) :
    encodePalette palette x = encodePalette palette y ↔ x = y := by
  constructor
  · intro heq
    calc
      x = palette (encodePalette palette x) := (decode_encode_palette palette x hx).symm
      _ = palette (encodePalette palette y) := congrArg palette heq
      _ = y := decode_encode_palette palette y hy
  · intro heq
    exact congrArg (encodePalette palette) heq

end DiracHajos

import AllColorRigidityFixed
import GeneralPaletteEncodingFixed

/-!
Transfer the verified three-color rigidity of the base graph to an arbitrary
ambient color type, provided that all twelve base vertices use colors from
one three-element palette.

This is a bridge lemma for the all-k construction; the construction and its
criticality are not claimed here.
-/

namespace DiracHajos

private theorem getD_map_encode {Color : Type*} [Inhabited Color]
    (palette : Fin 3 → Color) (c : List Color)
    (i : Nat) (hi : i < c.length) :
    (c.map (encodePalette palette)).getD i 0 =
      encodePalette palette (c.getD i default) := by
  simp [List.getD, List.getElem?_map, hi]

/-- Base rigidity holds for any color type once the base uses at most three
colors and its retained edges are properly colored. -/
theorem general_palette_rigidity
    {Color : Type*} [Inhabited Color] [DecidableEq Color]
    (palette : Fin 3 → Color) (c : List Color)
    (hlen : c.length = 12)
    (hpalette : ∀ i : Nat, i < c.length →
      ∃ j : Fin 3, palette j = c.getD i default)
    (hv : (edges.all fun e =>
      if e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ c.length then true
      else c.getD e.1 default != c.getD e.2 default) = true) :
    (c.getD 0 default = c.getD 1 default →
      c.getD 3 default = c.getD 2 default) ∧
    (c.getD 0 default ≠ c.getD 1 default →
      c.getD 3 default = c.getD 0 default) := by
  classical
  let d : List (Fin 3) := c.map (encodePalette palette)
  have hdlen : d.length = 12 := by simp [d, hlen]
  have hdvalid : validPrefix d = true := by
    unfold validPrefix
    apply List.all_eq_true.mpr
    intro e he
    have hfull := (List.all_eq_true.mp hv) e he
    by_cases hskip : e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ d.length
    · simp only [if_pos hskip]
    have hskipC : ¬(e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ c.length) := by
      simpa [d] using hskip
    have hlt2 : e.2 < c.length := by omega
    have horder : e.1 < e.2 := by
      have hh := (List.all_eq_true.mp edgesOrdered) e he
      simpa using hh
    have hlt1 : e.1 < c.length := by omega
    have hsrcB : c.getD e.1 default != c.getD e.2 default := by
      simpa only [if_neg hskipC] using hfull
    have hsrc : c.getD e.1 default ≠ c.getD e.2 default := by
      simpa using hsrcB
    have hdst : encodePalette palette (c.getD e.1 default) ≠
        encodePalette palette (c.getD e.2 default) := by
      intro heq
      exact hsrc ((encode_palette_eq_iff palette
        (c.getD e.1 default) (c.getD e.2 default)
        (hpalette e.1 hlt1) (hpalette e.2 hlt2)).mp heq)
    have hdstB : encodePalette palette (c.getD e.1 default) !=
        encodePalette palette (c.getD e.2 default) := by
      simpa using hdst
    have hmap1 : d.getD e.1 0 = encodePalette palette (c.getD e.1 default) :=
      getD_map_encode palette c e.1 hlt1
    have hmap2 : d.getD e.2 0 = encodePalette palette (c.getD e.2 default) :=
      getD_map_encode palette c e.2 hlt2
    simpa only [if_neg hskip, hmap1, hmap2] using hdstB
  have hr := full_rigidity d hdlen hdvalid
  have h0 : d.getD 0 0 = encodePalette palette (c.getD 0 default) :=
    getD_map_encode palette c 0 (by omega)
  have h1 : d.getD 1 0 = encodePalette palette (c.getD 1 default) :=
    getD_map_encode palette c 1 (by omega)
  have h2 : d.getD 2 0 = encodePalette palette (c.getD 2 default) :=
    getD_map_encode palette c 2 (by omega)
  have h3 : d.getD 3 0 = encodePalette palette (c.getD 3 default) :=
    getD_map_encode palette c 3 (by omega)
  constructor
  · intro heq
    have hmap : d.getD 0 0 = d.getD 1 0 := by
      rw [h0, h1]
      exact congrArg (encodePalette palette) heq
    have hresult := hr.1 hmap
    apply (encode_palette_eq_iff palette
      (c.getD 3 default) (c.getD 2 default)
      (hpalette 3 (by omega)) (hpalette 2 (by omega))).mp
    simpa only [h3, h2] using hresult
  · intro hne
    have hmap : d.getD 0 0 ≠ d.getD 1 0 := by
      rw [h0, h1]
      intro heq
      exact hne ((encode_palette_eq_iff palette
        (c.getD 0 default) (c.getD 1 default)
        (hpalette 0 (by omega)) (hpalette 1 (by omega))).mp heq)
    have hresult := hr.2 hmap
    apply (encode_palette_eq_iff palette
      (c.getD 3 default) (c.getD 0 default)
      (hpalette 3 (by omega)) (hpalette 0 (by omega))).mp
    simpa only [h3, h0] using hresult

end DiracHajos

import AllColorRigidityFixed

/-!
This imports the previously verified three-color rigidity from its compiled
.olean file and proves the palette transfer without rerunning the large search.
Run: lake env lean PaletteBridgeImported.lean
-/

namespace DiracHajos

/-- The relaxed edge check when four color names are available. -/
def validPrefixFour (c : List (Fin 4)) : Bool :=
  edges.all fun e =>
    if e = (0, 3) ∨ e = (0, 1) ∨ e.2 ≥ c.length then true
    else c.getD e.1 0 != c.getD e.2 0

/-- Encode the three colors other than q in Fin 3. -/
def eraseColor (q x : Fin 4) : Fin 3 :=
  if q = 0 then
    if x = 1 then 0 else if x = 2 then 1 else 2
  else if q = 1 then
    if x = 0 then 0 else if x = 2 then 1 else 2
  else if q = 2 then
    if x = 0 then 0 else if x = 1 then 1 else 2
  else
    if x = 0 then 0 else if x = 1 then 1 else 2

theorem eraseColor_eq_iff :
    ∀ q x y : Fin 4, x ≠ q → y ≠ q →
      (eraseColor q x = eraseColor q y ↔ x = y) := by
  decide

private theorem getD_map_erase (q : Fin 4) (c : List (Fin 4))
    (i : Nat) (hi : i < c.length) :
    (c.map (eraseColor q)).getD i 0 = eraseColor q (c.getD i 0) := by
  simp [List.getD, List.getElem?_map, hi]

/-- An available three-color palette inherits the checked rigidity theorem. -/
theorem four_palette_rigidity (q : Fin 4) (c : List (Fin 4))
    (hlen : c.length = 12)
    (havoid : ∀ i : Nat, i < c.length → c.getD i 0 ≠ q)
    (hv : validPrefixFour c = true) :
    (c.getD 0 0 = c.getD 1 0 → c.getD 3 0 = c.getD 2 0) ∧
    (c.getD 0 0 ≠ c.getD 1 0 → c.getD 3 0 = c.getD 0 0) := by
  let d : List (Fin 3) := c.map (eraseColor q)
  have hdlen : d.length = 12 := by simp [d, hlen]
  have hdvalid : validPrefix d = true := by
    unfold validPrefixFour at hv
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
    have hsrcB : c.getD e.1 0 != c.getD e.2 0 := by
      simpa only [if_neg hskipC] using hfull
    have hsrc : c.getD e.1 0 ≠ c.getD e.2 0 := by
      simpa using hsrcB
    have hdst : eraseColor q (c.getD e.1 0) ≠
        eraseColor q (c.getD e.2 0) := by
      intro h
      exact hsrc ((eraseColor_eq_iff q (c.getD e.1 0)
        (c.getD e.2 0) (havoid e.1 hlt1) (havoid e.2 hlt2)).mp h)
    have hdstB : eraseColor q (c.getD e.1 0) !=
        eraseColor q (c.getD e.2 0) := by
      simpa using hdst
    have hmap1 : d.getD e.1 0 = eraseColor q (c.getD e.1 0) :=
      getD_map_erase q c e.1 hlt1
    have hmap2 : d.getD e.2 0 = eraseColor q (c.getD e.2 0) :=
      getD_map_erase q c e.2 hlt2
    simpa only [if_neg hskip, hmap1, hmap2] using hdstB
  have hr := full_rigidity d hdlen hdvalid
  have h0 : d.getD 0 0 = eraseColor q (c.getD 0 0) :=
    getD_map_erase q c 0 (by omega)
  have h1 : d.getD 1 0 = eraseColor q (c.getD 1 0) :=
    getD_map_erase q c 1 (by omega)
  have h2 : d.getD 2 0 = eraseColor q (c.getD 2 0) :=
    getD_map_erase q c 2 (by omega)
  have h3 : d.getD 3 0 = eraseColor q (c.getD 3 0) :=
    getD_map_erase q c 3 (by omega)
  constructor
  · intro heq
    have hmap : d.getD 0 0 = d.getD 1 0 := by
      rw [h0, h1]
      exact congrArg (eraseColor q) heq
    have hresult := hr.1 hmap
    apply (eraseColor_eq_iff q (c.getD 3 0) (c.getD 2 0)
      (havoid 3 (by omega)) (havoid 2 (by omega))).mp
    simpa only [h3, h2] using hresult
  · intro hne
    have hmap : d.getD 0 0 ≠ d.getD 1 0 := by
      rw [h0, h1]
      intro heq
      exact hne ((eraseColor_eq_iff q (c.getD 0 0) (c.getD 1 0)
        (havoid 0 (by omega)) (havoid 1 (by omega))).mp heq)
    have hresult := hr.2 hmap
    apply (eraseColor_eq_iff q (c.getD 3 0) (c.getD 0 0)
      (havoid 3 (by omega)) (havoid 0 (by omega))).mp
    simpa only [h3, h0] using hresult

end DiracHajos

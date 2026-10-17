import Mathlib

/-!
For a palette of `r + 3` colors, an injectively colored `r`-clique leaves
exactly three colors. This selects those three colors as a function `Fin 3 →
Fin (r + 3)` and shows that every color avoiding the clique is in its image.
-/

namespace DiracHajos

theorem remaining_three_palette (r : Nat)
    (clique : Fin r → Fin (r + 3))
    (hc : Function.Injective clique) :
    ∃ palette : Fin 3 → Fin (r + 3),
      ∀ x : Fin (r + 3),
        (∀ i : Fin r, x ≠ clique i) →
          ∃ j : Fin 3, palette j = x := by
  let used : Finset (Fin (r + 3)) := Finset.univ.image clique
  have hused : used.card = r := by
    simpa [used] using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin r)) hc)
  let spare : Finset (Fin (r + 3)) := usedᶜ
  have hspare : spare.card = 3 := by
    have hsum : used.card + spare.card = r + 3 := by
      simpa [spare] using (Finset.card_add_card_compl used)
    omega
  let e := spare.orderIsoOfFin hspare
  refine ⟨fun j => (e j).val, ?_⟩
  intro x hx
  have hxnot : x ∉ used := by
    intro hm
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hm
    exact hx i heq.symm
  have hxspare : x ∈ spare := Finset.mem_compl.mpr hxnot
  let y : spare := ⟨x, hxspare⟩
  refine ⟨e.symm y, ?_⟩
  change (e (e.symm y)).val = x
  simpa [y] using congrArg Subtype.val (e.apply_symm_apply y)

end DiracHajos

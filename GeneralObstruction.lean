import Mathlib

/-!
The final logical step of the Dirac--Hajos obstruction, for an arbitrary color
type. No finite enumeration or fixed palette is involved here.

The graph-specific work still needed for the all-k theorem is to obtain the
two rigidity hypotheses from a coloring of the family D_k and to prove the
input graphs are k-critical. This file does not claim those results.
-/

namespace DiracHajos

/-- Two copies that agree on 0, 1, and 2 and each satisfy the base rigidity
rule must give vertex 3 the same color, contradicting a bridge edge. -/
theorem general_two_copy_obstruction
    {Color : Type*} (left right : Nat → Color)
    (h0 : left 0 = right 0)
    (h1 : left 1 = right 1)
    (h2 : left 2 = right 2)
    (hleft_same : left 0 = left 1 → left 3 = left 2)
    (hleft_diff : left 0 ≠ left 1 → left 3 = left 0)
    (hright_same : right 0 = right 1 → right 3 = right 2)
    (hright_diff : right 0 ≠ right 1 → right 3 = right 0)
    (hbridge : left 3 ≠ right 3) : False := by
  classical
  by_cases h : left 0 = left 1
  · have h' : right 0 = right 1 := h0.symm.trans (h.trans h1)
    exact hbridge ((hleft_same h).trans (h2.trans (hright_same h').symm))
  · have h' : right 0 ≠ right 1 := by
      intro heq
      exact h (h0.trans (heq.trans h1.symm))
    exact hbridge ((hleft_diff h).trans (h0.trans (hright_diff h').symm))

end DiracHajos

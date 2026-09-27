import CoboundaryK3.Basic
open CoboundaryK3
-- A single transposition (the F₂ witness) does not reach 4/3 at k = 4: some gauge costs 2 < 3.
example : ∀ β, 3 ≤ cost (cochain 4 [((0, 1), t01)]) β :=
  gauge_lower _ 3 (by decide)

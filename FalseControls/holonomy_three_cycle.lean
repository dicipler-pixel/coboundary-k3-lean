import CoboundaryK3.Basic
open CoboundaryK3
-- The holonomy of three distinct transpositions is a transposition, not a 3-cycle.
example : moved (t12 * t02 * t01⁻¹) = 3 := by decide

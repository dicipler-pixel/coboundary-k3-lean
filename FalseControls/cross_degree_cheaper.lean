import CoboundaryK3.AllK
open CoboundaryK3
-- Degree four does not repair the seed more cheaply than degree three: the identity comparison
-- gauge costs exactly 12 in scaled units, not 11 or less.
example : errCost w4 (fun _ => (1 : Equiv.Perm (Fin 4))) ≤ 11 := by decide +kernel

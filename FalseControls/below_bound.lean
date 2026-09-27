import CoboundaryK3.Basic
open CoboundaryK3
-- No gauge of the k = 4 witness costs 7 or more at the identity gauge: its cost is exactly 6.
example : 7 ≤ cost w4 (fun _ => 1) := by decide

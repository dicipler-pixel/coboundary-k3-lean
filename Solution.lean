/-
The proofs of the statements of `Challenge.lean`.

Jeromie Beasley. Released under the MIT licence (file LICENSE).
-/
module

public import CoboundaryK3.Staircase

/-!
# The proofs of the statements of `Challenge.lean`

The library declares the definitions and theorems of `Challenge.lean` under the same names, with
proofs: `gaugeDist_eq_zero_iff` and `gaugeDist_mul_le` in `CoboundaryK3/Constant.lean`, and
`h1_eq_all` in `CoboundaryK3/Staircase.lean`, which imports the rest. This module imports it.
Comparator checks that each of the three states exactly what `Challenge.lean` states and depends
only on `propext`, `Classical.choice` and `Quot.sound`.
-/

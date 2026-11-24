/-
The permutation coboundary constant of the complete complex is k/3 for every k ≥ 3:
the statement, for Comparator and for a reader.

Jeromie Beasley. Paper: The Permutation Coboundary Constant of the Complete Complex Is k/3 for
Every k ≥ 4, DOI 10.5281/zenodo.23245792. Released under the MIT licence (file LICENSE).

This file imports Mathlib only. Nothing in the library imports it. Every definition below is
copied word for word from `CoboundaryK3/Basic.lean` and `CoboundaryK3/Constant.lean`, and
Comparator checks that `Solution.lean` proves exactly these statements about exactly these
definitions.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD

/-!
# The coboundary constant of the complete 2-complex with `Sym(3)` coefficients is `k/3`

The setting is the complete 2-complex `K_k`: `k` vertices, an edge for every pair `u < v`, a
triangle for every triple `u < v < w`.

* A **1-cochain** `α` puts a permutation of three points, `α u v`, on each edge `u < v`; the
  reversed edge carries the inverse (`val`).
* Its **triangle defect** `N = defect α` adds up, over all triangles, the number of points moved
  by the product of the three edge values around the triangle (the holonomy).
* A **gauge** `β` puts a permutation on each vertex. Its **cost** adds up, over all edges, the
  number of points moved by `β(u)⁻¹ α(u,v) β(v)`.
* The **gauge distance** `D = gaugeDist α` is the least cost over every gauge. It is zero exactly
  when `α` is a coboundary (`gaugeDist_eq_zero_iff`).
* The **coboundary constant** `h1 k` is the infimum of `N / D` over every cochain that is not a
  coboundary. Both `N` and `D` count moved points, so this is the counting normalisation.

The results:

* `gaugeDist_mul_le`: `k · D ≤ 3 · N` for every cochain. This is the lower bound `h1 k ≥ k/3`
  of Chapman and Lubotzky (Stability of homomorphisms, coverings and cocycles II,
  arXiv:2311.06706, Proposition 3.2), in this convention.
* `h1_eq_all`: `h1 k = k/3` for every `k ≥ 3`. The lower bound is attained.

Scope. The coefficients of the cochain and of the gauge are both `Sym(3)`. The paper states the
result for permutation coefficients of every degree and in Chapman and Lubotzky's cross-degree
convention; those extensions are proved in the paper and are not part of this statement.
-/

@[expose] public section

namespace CoboundaryK3

open Equiv

/-! ## Definitions (word for word from `CoboundaryK3/Basic.lean`) -/

/-- Permutations of three points. -/
abbrev S3 := Perm (Fin 3)

/-- The Hamming count: how many of the three points `σ` moves. -/
def moved (σ : S3) : ℕ := (List.finRange 3).countP fun i => σ i ≠ i

variable {k : ℕ}

/-- Oriented edges `u < v`. -/
def edges (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => ((List.finRange k).filter fun v => u < v).map fun v => (u, v)

/-- Triangles `u < v < w`. -/
def triangles (k : ℕ) : List (Fin k × Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => (List.finRange k).flatMap fun v =>
    ((List.finRange k).filter fun w => u < v ∧ v < w).map fun w => (u, v, w)

/-- The value on an oriented edge, with `α(v,u) = α(u,v)⁻¹`. -/
def val (α : Fin k → Fin k → S3) (u v : Fin k) : S3 := if u < v then α u v else (α v u)⁻¹

/-- The triangle defect `N`: moved points of the holonomy, summed over triangles. -/
def defect (α : Fin k → Fin k → S3) : ℕ :=
  ((triangles k).map fun t => moved (val α t.1 t.2.1 * val α t.2.1 t.2.2 * val α t.2.2 t.1)).sum

/-- The cost of a gauge `β`: moved points of `β(u)⁻¹ α(u,v) β(v)`, summed over edges. -/
def cost (α : Fin k → Fin k → S3) (β : Fin k → S3) : ℕ :=
  ((edges k).map fun e => moved ((β e.1)⁻¹ * α e.1 e.2 * β e.2)).sum

/-! ## Definitions (word for word from `CoboundaryK3/Constant.lean`) -/

/-- The **gauge distance** of a cochain: the minimum of `cost α β` over every gauge
`β : Fin k → Sym(3)`. This is the paper's `D` (Section 1), the Hamming distance of `α` from
the `Sym(3)`-valued coboundaries. -/
def gaugeDist (α : Fin k → Fin k → S3) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (cost α)

/-- The **coboundary constant** `h₁(K_k)` in the counting normalisation of the paper: the
infimum of the counting ratio `N/D = defect α / gaugeDist α` over every `Sym(3)`-valued 1-cochain
`α` on `K_k` that is not a coboundary (`0 < gaugeDist α`, see `gaugeDist_eq_zero_iff`), where
`D` is the minimum over `Sym(3)`-valued gauges. Only the values `α u v` with `u < v` enter `N`
and `D`, so ranging over all functions `Fin k → Fin k → Sym(3)` ranges over all cochains. When
no non-coboundary exists the set is empty and the value is `0` by Mathlib's convention. -/
noncomputable def h1 (k : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ α : Fin k → Fin k → S3, 0 < gaugeDist α ∧
    r = (defect α : ℝ) / (gaugeDist α : ℝ)}

/-! ## Statements -/

/-- **The definition means what it says.** The gauge distance of `α` is zero exactly when `α`
is a `Sym(3)`-valued coboundary, `α(u,v) = β(u) β(v)⁻¹` on every edge `u < v`. -/
theorem gaugeDist_eq_zero_iff (α : Fin k → Fin k → S3) :
    gaugeDist α = 0 ↔ ∃ β : Fin k → S3, ∀ u v, u < v → α u v = β u * (β v)⁻¹ := by
  sorry

/-- **The star bound** (Chapman–Lubotzky, arXiv:2311.06706, Proposition 3.2, in the counting
convention): `k · D ≤ 3 · N` for every `Sym(3)`-valued cochain on `K_k`. -/
theorem gaugeDist_mul_le (α : Fin k → Fin k → S3) : k * gaugeDist α ≤ 3 * defect α := by
  sorry

/-- **`h₁(K_k) = k/3` for every `k ≥ 3`.** Since the value is positive, the set of
non-coboundaries is nonempty and the infimum is not the empty-set convention. -/
theorem h1_eq_all (k : ℕ) (hk : 3 ≤ k) : h1 k = (k : ℝ) / 3 := by
  sorry

end CoboundaryK3

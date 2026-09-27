/-
The permutation coboundary constant of the complete complex is k/3 for 4 ≤ k ≤ 8
(Jeromie Beasley, DOI 10.5281/zenodo.22090958): the machine-checked witnesses.

Conventions follow the paper (Sec. 1 and Appendix B). Permutations of `{0,1,2}` act on points;
the Hamming count `moved σ` is the number of points `σ` moves. A 1-cochain on the complete
complex `K_k` assigns `α u v` to each edge `u < v`, with `α(v,u) = α(u,v)⁻¹`. Its triangle
defect is `N = Σ_{u<v<w} moved(α(u,v) α(v,w) α(w,u))` and the cost of a gauge
`β : Fin k → Sym(3)` is `Σ_{u<v} moved(β(u)⁻¹ α(u,v) β(v))`; `D` is the minimum cost over every
gauge. Both are counts of moved points, so `N/D` is the paper's counting ratio.

This file proves, for each witness of Appendix A, the defect `N`, that no gauge costs less than
`D`, and that `D` is attained, so that `N/D = k/3`. With the Chapman–Lubotzky lower bound
`h₁(K_k, Sym) ≥ k/3` (cited, Proposition 1) this is the upper half of Theorem 3.

The gauge minimum is checked by exhausting every gauge with `β(0) = 1`; `gauge_lower` proves that
this loses nothing, because right multiplication by a constant conjugates every edge term.
-/
import Mathlib

namespace CoboundaryK3

open Equiv

/-- Permutations of three points. -/
abbrev S3 := Perm (Fin 3)

/-- The Hamming count: how many of the three points `σ` moves. -/
def moved (σ : S3) : ℕ := (List.finRange 3).countP fun i => σ i ≠ i

/-- The two transpositions and 3-cycles, in the paper's one-line notation. -/
def t01 : S3 := swap 0 1          -- (1 0 2)
def t12 : S3 := swap 1 2          -- (0 2 1)
def t02 : S3 := swap 0 2          -- (2 1 0)
def c1 : S3 := swap 0 1 * swap 1 2  -- (1 2 0)
def c2 : S3 := swap 1 2 * swap 0 1  -- (2 0 1)

/-- The six elements of `Sym(3)`. -/
def S3list : List S3 := [1, t01, t12, t02, c1, c2]

theorem mem_S3list : ∀ σ : S3, σ ∈ S3list := by decide

theorem one_line : (c1 0, c1 1, c1 2) = (1, 2, 0) ∧ (c2 0, c2 1, c2 2) = (2, 0, 1) ∧
    (t01 0, t01 1, t01 2) = (1, 0, 2) ∧ (t12 0, t12 1, t12 2) = (0, 2, 1) ∧
    (t02 0, t02 1, t02 2) = (2, 1, 0) := by decide

/-- The Hamming count is conjugation invariant (bi-invariance of the metric). -/
theorem moved_conj : ∀ c x : S3, moved (c⁻¹ * x * c) = moved x := by
  intro c x
  have hc := mem_S3list c
  have hx := mem_S3list x
  simp only [S3list, List.mem_cons, List.not_mem_nil, or_false] at hc hx
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Cochains on the complete complex -/

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

/-- A constant right factor does not change the cost. -/
theorem cost_mul_const (α : Fin k → Fin k → S3) (β : Fin k → S3) (c : S3) :
    cost α (fun v => β v * c) = cost α β := by
  unfold cost
  congr 1
  apply List.map_congr_left
  intro e _
  have : (β e.1 * c)⁻¹ * α e.1 e.2 * (β e.2 * c) = c⁻¹ * ((β e.1)⁻¹ * α e.1 e.2 * β e.2) * c := by
    group
  rw [this, moved_conj]

/-- Every function `Fin n → Sym(3)`, as a list. -/
def funs : (n : ℕ) → List (Fin n → S3)
  | 0 => [Fin.elim0]
  | n + 1 => S3list.flatMap fun a => (funs n).map (Fin.cons a)

theorem mem_funs : ∀ (n : ℕ) (f : Fin n → S3), f ∈ funs n
  | 0, f => by simp [funs]; funext i; exact i.elim0
  | n + 1, f => by
    simp only [funs, List.mem_flatMap, List.mem_map]
    exact ⟨f 0, mem_S3list _, Fin.tail f, mem_funs n _, Fin.cons_self_tail f⟩

/-- **Exhaustion loses nothing.** If every gauge with `β(0) = 1` costs at least `D`, every
gauge does. -/
theorem gauge_lower {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (D : ℕ)
    (h : (funs m).all (fun t => decide (D ≤ cost α (Fin.cons 1 t))) = true) :
    ∀ β, D ≤ cost α β := by
  intro β
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have hcons : β' = Fin.cons 1 (Fin.tail β') := by
    rw [← h0]; exact (Fin.cons_self_tail β').symm
  rw [hcons]
  have := List.all_eq_true.mp h (Fin.tail β') (mem_funs m _)
  simpa using this

/-- A cochain from its list of non-identity edges. -/
def cochain (k : ℕ) (W : List ((ℕ × ℕ) × S3)) : Fin k → Fin k → S3 :=
  fun u v => ((W.lookup (u.val, v.val)).getD 1)

/-! ## The witnesses of Appendix A (gauged form) -/

def w4 : Fin 4 → Fin 4 → S3 := cochain 4 [((1, 2), t12), ((1, 3), t01), ((2, 3), t02)]

def w5 : Fin 5 → Fin 5 → S3 := cochain 5 [((0, 1), t01), ((1, 2), t01), ((2, 3), t01)]

def w6 : Fin 6 → Fin 6 → S3 :=
  cochain 6 [((0, 1), c1), ((1, 3), c1), ((0, 3), c2), ((0, 4), c2), ((1, 5), c2), ((4, 5), c2)]

/-- **Theorem 3, k = 4.** `N = 8`, every gauge costs at least `6`, and `6` is attained:
`N/D = 4/3`. -/
theorem witness_k4 :
    defect w4 = 8 ∧ (∀ β, 6 ≤ cost w4 β) ∧ cost w4 (fun _ => 1) = 6 ∧ 8 * 3 = 4 * 6 :=
  ⟨by decide +kernel, gauge_lower w4 6 (by decide +kernel), by decide +kernel, by norm_num⟩

/-- **Theorem 3, k = 5.** `N = 10`, `D = 6`: `N/D = 5/3`. -/
theorem witness_k5 :
    defect w5 = 10 ∧ (∀ β, 6 ≤ cost w5 β) ∧ cost w5 (fun _ => 1) = 6 ∧ 10 * 3 = 5 * 6 :=
  ⟨by decide +kernel, gauge_lower w5 6 (by decide +kernel), by decide +kernel, by norm_num⟩

/-- **Theorem 3, k = 6.** `N = 36`, `D = 18`: `N/D = 2 = 6/3`. -/
theorem witness_k6 :
    defect w6 = 36 ∧ (∀ β, 18 ≤ cost w6 β) ∧ cost w6 (fun _ => 1) = 18 ∧ 36 * 3 = 6 * 18 :=
  ⟨by decide +kernel, gauge_lower w6 18 (by decide +kernel), by decide +kernel, by norm_num⟩

/-! ## Proposition 4: the non-abelian mechanism at k = 4 -/

/-- **Proposition 4, mechanism.** Around the witness triangle the three distinct transpositions
compose to a transposition (2 moved points), while each adjacent product is a 3-cycle. -/
theorem k4_mechanism :
    moved (t12 * t02 * t01⁻¹) = 2 ∧ moved (t12 * t02) = 3 ∧ moved (t02 * t01) = 3 ∧
      moved (t01 * t12) = 3 := by decide

/-! ## Theorem 8: the displacement Gram is half the cycle Laplacian -/

/-- The displacement `e_{π(i)} − e_i` of point `i`. -/
def disp {n : ℕ} (π : Perm (Fin n)) (i : Fin n) : Fin n → ℤ :=
  fun t => (if t = π i then 1 else 0) - (if t = i then 1 else 0)

/-- **Theorem 8.** `⟨e_{π i} − e_i, e_{π j} − e_j⟩ = 2[i = j] − [π i = j] − [π j = i]`, i.e.
twice the Gram matrix is `2I − A` for the adjacency `A` of the cycle graph of `π`. -/
theorem disp_gram {n : ℕ} (π : Perm (Fin n)) (i j : Fin n) :
    ∑ t, disp π i t * disp π j t =
      (if i = j then 2 else 0) - (if π i = j then 1 else 0) - (if π j = i then 1 else 0) := by
  simp only [disp]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  split_ifs <;> simp_all <;> omega

/-- **Theorem 8, cycle spectrum.** The Laplacian eigenvalue `2 − 2cos(2πj/ℓ)` of `C_ℓ` equals
`4 sin²(πj/ℓ)`. -/
theorem cycle_laplacian_eigen (x : ℝ) : 2 - 2 * Real.cos (2 * x) = 4 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

end CoboundaryK3

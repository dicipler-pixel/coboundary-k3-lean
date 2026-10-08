/-
The permutation coboundary constant of the complete complex is k/3 for every k ≥ 4
(Jeromie Beasley, version 8, DOI 10.5281/zenodo.23245792 for version 7): the machine-checked steps added for
the all-k version.

`Basic.lean` checks the five computed witnesses for k = 4, …, 8. This file adds what the all-k
proof uses that a kernel can check:

* the parity retraction `r(g) = t^parity(g)` and, for every `k`, that retracting a `Sym(3)` gauge
  of a binary cochain into `{1, t}` never raises its cost (the step of Theorem 8 for the k not
  divisible by four);
* the equality case of the star bound (Corollary 2) on every witness: each star gauge costs
  exactly `D`, and the star costs add up to `3N`;
* the replicated seed on `K₈` (Corollary 7 at q = 2): `N = 64`, `D = 24`, every gauge searched;
* the cross-degree convention on the seed (Proposition 11): against comparison permutations of
  degree 2, 3 and 4 the cheapest repair is `10/3`, `2` and `3`, so degree three is cheapest.

The general replication lemma and the star-gauge identity for every cochain are proved in the
paper and not formalized here; see `LIMITATIONS.md`.
-/
import CoboundaryK3.Basic

namespace CoboundaryK3

open Equiv

/-! ## The parity retraction (Theorem 8)

For `k` not a multiple of four the paper embeds Kozlov's binary witness through the subgroup
`H = {1, t}` with `t = (0 1)`, and needs that gauges outside `H` do no better. The tool is the
retraction `r(g) = t^parity(g)`: even elements go to `1`, odd ones to `t`. In `Sym(3)` the odd
elements are exactly the three transpositions, the elements moving two points. -/

/-- The parity retraction `r : Sym(3) → {1, t}`. -/
def retr (g : S3) : S3 := if moved g = 2 then t01 else 1

/-- `r` is the sign map read in `{1, t}`. -/
theorem retr_eq_sign : ∀ g : S3, retr g = if Perm.sign g = 1 then 1 else t01 := by decide

private theorem cases_S3 {P : S3 → Prop} (h1 : P 1) (h2 : P t01) (h3 : P t12) (h4 : P t02)
    (h5 : P c1) (h6 : P c2) : ∀ g, P g := by
  intro g
  have hg := mem_S3list g
  simp only [S3list, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- `r` is a homomorphism. -/
theorem retr_mul : ∀ g h : S3, retr (g * h) = retr g * retr h := by
  apply cases_S3 <;> apply cases_S3 <;> decide

/-- `r` commutes with inverses. -/
theorem retr_inv : ∀ g : S3, retr g⁻¹ = (retr g)⁻¹ := by
  apply cases_S3 <;> decide

/-- `r` takes values in `H = {1, t}` and fixes `H`. -/
theorem retr_mem : ∀ g : S3, retr g = 1 ∨ retr g = t01 := by
  apply cases_S3 <;> decide

theorem retr_fix : retr 1 = 1 ∧ retr t01 = t01 := by decide

/-- `r` never moves more points: an even element goes to `1` (cost 0), and an odd one is a
transposition of cost 2 that goes to `t`, also of cost 2. -/
theorem retr_moved : ∀ g : S3, moved (retr g) ≤ moved g := by
  apply cases_S3 <;> decide

variable {k : ℕ}

/-- A binary cochain: every edge carries `1` or `t`. -/
def Binary (α : Fin k → Fin k → S3) : Prop := ∀ u v, α u v = 1 ∨ α u v = t01

/-- **The retraction step of Theorem 8, for every `k`.** For a binary cochain, retracting any
`Sym(3)` gauge into `H` never raises the cost. -/
theorem retract_cost (α : Fin k → Fin k → S3) (hα : Binary α) (β : Fin k → S3) :
    cost α (fun v => retr (β v)) ≤ cost α β := by
  unfold cost
  apply sum_map_le
  intro e _
  have ha : retr (α e.1 e.2) = α e.1 e.2 := by
    rcases hα e.1 e.2 with h | h <;> rw [h] <;> decide
  have : (retr (β e.1))⁻¹ * α e.1 e.2 * retr (β e.2)
      = retr ((β e.1)⁻¹ * α e.1 e.2 * β e.2) := by
    rw [retr_mul, retr_mul, retr_inv, ha]
  rw [this]
  exact retr_moved _

/-- **Gauges outside `H` do no better (Theorem 8).** Every `Sym(3)` gauge of a binary cochain is
matched or beaten by a gauge with values in `H`. -/
theorem binary_gauge_suffices (α : Fin k → Fin k → S3) (hα : Binary α) (β : Fin k → S3) :
    ∃ β' : Fin k → S3, (∀ v, β' v = 1 ∨ β' v = t01) ∧ cost α β' ≤ cost α β :=
  ⟨fun v => retr (β v), fun v => retr_mem _, retract_cost α hα β⟩

/-! ## The equality case of the star bound (Corollary 2)

The star gauge at `x` makes every edge at `x` cost nothing; every other edge then carries the
holonomy of the triangle it spans with `x`. Summed over `x` the star costs give `3N`, and a
cochain meets `k/3` exactly when every star gauge is optimal. Here both facts are checked on every
witness of Appendix A. -/

/-- The star gauge at `x`. -/
def star (α : Fin k → Fin k → S3) (x : Fin k) : Fin k → S3 :=
  fun u => if u = x then 1 else val α u x

/-- Sum of the `k` star costs. -/
def starSum (α : Fin k → Fin k → S3) : ℕ :=
  ((List.finRange k).map fun x => cost α (star α x)).sum

theorem stars_k4 : (∀ x, cost w4 (star w4 x) = 6) ∧ starSum w4 = 3 * defect w4 := by
  decide +kernel

theorem stars_k5 : (∀ x, cost w5 (star w5 x) = 6) ∧ starSum w5 = 3 * defect w5 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem stars_k6 : (∀ x, cost w6 (star w6 x) = 18) ∧ starSum w6 = 3 * defect w6 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem stars_k7 : (∀ x, cost w7 (star w7 x) = 12) ∧ starSum w7 = 3 * defect w7 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem stars_k8 : (∀ x, cost w8 (star w8 x) = 27) ∧ starSum w8 = 3 * defect w8 := by
  decide +kernel

/-! ## The replicated seed at `q = 2` (Corollary 7)

Clusters `{0,1}, {2,3}, {4,5}, {6,7}`; between `{2,3}` and `{4,5}` the value `(1 0 2)`, between
`{2,3}` and `{6,7}` the value `(2 1 0)`, between `{4,5}` and `{6,7}` the value `(0 2 1)`. -/

def wr8 : Fin 8 → Fin 8 → S3 :=
  cochain 8 [((2, 4), t01), ((2, 5), t01), ((3, 4), t01), ((3, 5), t01),
    ((2, 6), t02), ((2, 7), t02), ((3, 6), t02), ((3, 7), t02),
    ((4, 6), t12), ((4, 7), t12), ((5, 6), t12), ((5, 7), t12)]

set_option maxHeartbeats 0 in
theorem stars_r8 : (∀ x, cost wr8 (star wr8 x) = 24) ∧ starSum wr8 = 3 * defect wr8 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_0_0 : search wr8 24 4 [1, 1, 1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_0_1 : search wr8 24 4 [1, 1, 1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_0_2 : search wr8 24 4 [1, 1, 1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_0_3 : search wr8 24 4 [1, 1, 1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_0_4 : search wr8 24 4 [1, 1, 1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_0_5 : search wr8 24 4 [1, 1, 1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_1_0 : search wr8 24 4 [1, 1, t01, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_1_1 : search wr8 24 4 [1, 1, t01, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_1_2 : search wr8 24 4 [1, 1, t01, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_1_3 : search wr8 24 4 [1, 1, t01, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_1_4 : search wr8 24 4 [1, 1, t01, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_1_5 : search wr8 24 4 [1, 1, t01, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_2_0 : search wr8 24 4 [1, 1, t12, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_2_1 : search wr8 24 4 [1, 1, t12, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_2_2 : search wr8 24 4 [1, 1, t12, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_2_3 : search wr8 24 4 [1, 1, t12, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_2_4 : search wr8 24 4 [1, 1, t12, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_2_5 : search wr8 24 4 [1, 1, t12, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_3_0 : search wr8 24 4 [1, 1, t02, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_3_1 : search wr8 24 4 [1, 1, t02, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_3_2 : search wr8 24 4 [1, 1, t02, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_3_3 : search wr8 24 4 [1, 1, t02, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_3_4 : search wr8 24 4 [1, 1, t02, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_3_5 : search wr8 24 4 [1, 1, t02, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_4_0 : search wr8 24 4 [1, 1, c1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_4_1 : search wr8 24 4 [1, 1, c1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_4_2 : search wr8 24 4 [1, 1, c1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_4_3 : search wr8 24 4 [1, 1, c1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_4_4 : search wr8 24 4 [1, 1, c1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_4_5 : search wr8 24 4 [1, 1, c1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_5_0 : search wr8 24 4 [1, 1, c2, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_5_1 : search wr8 24 4 [1, 1, c2, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_5_2 : search wr8 24 4 [1, 1, c2, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_5_3 : search wr8 24 4 [1, 1, c2, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_5_4 : search wr8 24 4 [1, 1, c2, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_0_5_5 : search wr8 24 4 [1, 1, c2, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_0_0 : search wr8 24 4 [1, t01, 1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_0_1 : search wr8 24 4 [1, t01, 1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_0_2 : search wr8 24 4 [1, t01, 1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_0_3 : search wr8 24 4 [1, t01, 1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_0_4 : search wr8 24 4 [1, t01, 1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_0_5 : search wr8 24 4 [1, t01, 1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_1_0 : search wr8 24 4 [1, t01, t01, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_1_1 : search wr8 24 4 [1, t01, t01, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_1_2 : search wr8 24 4 [1, t01, t01, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_1_3 : search wr8 24 4 [1, t01, t01, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_1_4 : search wr8 24 4 [1, t01, t01, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_1_5 : search wr8 24 4 [1, t01, t01, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_2_0 : search wr8 24 4 [1, t01, t12, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_2_1 : search wr8 24 4 [1, t01, t12, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_2_2 : search wr8 24 4 [1, t01, t12, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_2_3 : search wr8 24 4 [1, t01, t12, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_2_4 : search wr8 24 4 [1, t01, t12, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_2_5 : search wr8 24 4 [1, t01, t12, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_3_0 : search wr8 24 4 [1, t01, t02, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_3_1 : search wr8 24 4 [1, t01, t02, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_3_2 : search wr8 24 4 [1, t01, t02, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_3_3 : search wr8 24 4 [1, t01, t02, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_3_4 : search wr8 24 4 [1, t01, t02, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_3_5 : search wr8 24 4 [1, t01, t02, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_4_0 : search wr8 24 4 [1, t01, c1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_4_1 : search wr8 24 4 [1, t01, c1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_4_2 : search wr8 24 4 [1, t01, c1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_4_3 : search wr8 24 4 [1, t01, c1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_4_4 : search wr8 24 4 [1, t01, c1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_4_5 : search wr8 24 4 [1, t01, c1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_5_0 : search wr8 24 4 [1, t01, c2, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_5_1 : search wr8 24 4 [1, t01, c2, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_5_2 : search wr8 24 4 [1, t01, c2, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_5_3 : search wr8 24 4 [1, t01, c2, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_5_4 : search wr8 24 4 [1, t01, c2, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_1_5_5 : search wr8 24 4 [1, t01, c2, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_0_0 : search wr8 24 4 [1, t12, 1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_0_1 : search wr8 24 4 [1, t12, 1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_0_2 : search wr8 24 4 [1, t12, 1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_0_3 : search wr8 24 4 [1, t12, 1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_0_4 : search wr8 24 4 [1, t12, 1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_0_5 : search wr8 24 4 [1, t12, 1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_1_0 : search wr8 24 4 [1, t12, t01, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_1_1 : search wr8 24 4 [1, t12, t01, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_1_2 : search wr8 24 4 [1, t12, t01, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_1_3 : search wr8 24 4 [1, t12, t01, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_1_4 : search wr8 24 4 [1, t12, t01, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_1_5 : search wr8 24 4 [1, t12, t01, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_2_0 : search wr8 24 4 [1, t12, t12, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_2_1 : search wr8 24 4 [1, t12, t12, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_2_2 : search wr8 24 4 [1, t12, t12, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_2_3 : search wr8 24 4 [1, t12, t12, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_2_4 : search wr8 24 4 [1, t12, t12, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_2_5 : search wr8 24 4 [1, t12, t12, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_3_0 : search wr8 24 4 [1, t12, t02, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_3_1 : search wr8 24 4 [1, t12, t02, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_3_2 : search wr8 24 4 [1, t12, t02, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_3_3 : search wr8 24 4 [1, t12, t02, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_3_4 : search wr8 24 4 [1, t12, t02, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_3_5 : search wr8 24 4 [1, t12, t02, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_4_0 : search wr8 24 4 [1, t12, c1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_4_1 : search wr8 24 4 [1, t12, c1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_4_2 : search wr8 24 4 [1, t12, c1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_4_3 : search wr8 24 4 [1, t12, c1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_4_4 : search wr8 24 4 [1, t12, c1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_4_5 : search wr8 24 4 [1, t12, c1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_5_0 : search wr8 24 4 [1, t12, c2, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_5_1 : search wr8 24 4 [1, t12, c2, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_5_2 : search wr8 24 4 [1, t12, c2, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_5_3 : search wr8 24 4 [1, t12, c2, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_5_4 : search wr8 24 4 [1, t12, c2, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_2_5_5 : search wr8 24 4 [1, t12, c2, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_0_0 : search wr8 24 4 [1, t02, 1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_0_1 : search wr8 24 4 [1, t02, 1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_0_2 : search wr8 24 4 [1, t02, 1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_0_3 : search wr8 24 4 [1, t02, 1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_0_4 : search wr8 24 4 [1, t02, 1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_0_5 : search wr8 24 4 [1, t02, 1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_1_0 : search wr8 24 4 [1, t02, t01, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_1_1 : search wr8 24 4 [1, t02, t01, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_1_2 : search wr8 24 4 [1, t02, t01, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_1_3 : search wr8 24 4 [1, t02, t01, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_1_4 : search wr8 24 4 [1, t02, t01, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_1_5 : search wr8 24 4 [1, t02, t01, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_2_0 : search wr8 24 4 [1, t02, t12, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_2_1 : search wr8 24 4 [1, t02, t12, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_2_2 : search wr8 24 4 [1, t02, t12, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_2_3 : search wr8 24 4 [1, t02, t12, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_2_4 : search wr8 24 4 [1, t02, t12, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_2_5 : search wr8 24 4 [1, t02, t12, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_3_0 : search wr8 24 4 [1, t02, t02, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_3_1 : search wr8 24 4 [1, t02, t02, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_3_2 : search wr8 24 4 [1, t02, t02, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_3_3 : search wr8 24 4 [1, t02, t02, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_3_4 : search wr8 24 4 [1, t02, t02, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_3_5 : search wr8 24 4 [1, t02, t02, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_4_0 : search wr8 24 4 [1, t02, c1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_4_1 : search wr8 24 4 [1, t02, c1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_4_2 : search wr8 24 4 [1, t02, c1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_4_3 : search wr8 24 4 [1, t02, c1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_4_4 : search wr8 24 4 [1, t02, c1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_4_5 : search wr8 24 4 [1, t02, c1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_5_0 : search wr8 24 4 [1, t02, c2, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_5_1 : search wr8 24 4 [1, t02, c2, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_5_2 : search wr8 24 4 [1, t02, c2, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_5_3 : search wr8 24 4 [1, t02, c2, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_5_4 : search wr8 24 4 [1, t02, c2, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_3_5_5 : search wr8 24 4 [1, t02, c2, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_0_0 : search wr8 24 4 [1, c1, 1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_0_1 : search wr8 24 4 [1, c1, 1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_0_2 : search wr8 24 4 [1, c1, 1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_0_3 : search wr8 24 4 [1, c1, 1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_0_4 : search wr8 24 4 [1, c1, 1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_0_5 : search wr8 24 4 [1, c1, 1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_1_0 : search wr8 24 4 [1, c1, t01, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_1_1 : search wr8 24 4 [1, c1, t01, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_1_2 : search wr8 24 4 [1, c1, t01, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_1_3 : search wr8 24 4 [1, c1, t01, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_1_4 : search wr8 24 4 [1, c1, t01, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_1_5 : search wr8 24 4 [1, c1, t01, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_2_0 : search wr8 24 4 [1, c1, t12, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_2_1 : search wr8 24 4 [1, c1, t12, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_2_2 : search wr8 24 4 [1, c1, t12, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_2_3 : search wr8 24 4 [1, c1, t12, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_2_4 : search wr8 24 4 [1, c1, t12, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_2_5 : search wr8 24 4 [1, c1, t12, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_3_0 : search wr8 24 4 [1, c1, t02, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_3_1 : search wr8 24 4 [1, c1, t02, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_3_2 : search wr8 24 4 [1, c1, t02, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_3_3 : search wr8 24 4 [1, c1, t02, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_3_4 : search wr8 24 4 [1, c1, t02, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_3_5 : search wr8 24 4 [1, c1, t02, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_4_0 : search wr8 24 4 [1, c1, c1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_4_1 : search wr8 24 4 [1, c1, c1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_4_2 : search wr8 24 4 [1, c1, c1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_4_3 : search wr8 24 4 [1, c1, c1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_4_4 : search wr8 24 4 [1, c1, c1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_4_5 : search wr8 24 4 [1, c1, c1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_5_0 : search wr8 24 4 [1, c1, c2, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_5_1 : search wr8 24 4 [1, c1, c2, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_5_2 : search wr8 24 4 [1, c1, c2, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_5_3 : search wr8 24 4 [1, c1, c2, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_5_4 : search wr8 24 4 [1, c1, c2, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_4_5_5 : search wr8 24 4 [1, c1, c2, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_0_0 : search wr8 24 4 [1, c2, 1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_0_1 : search wr8 24 4 [1, c2, 1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_0_2 : search wr8 24 4 [1, c2, 1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_0_3 : search wr8 24 4 [1, c2, 1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_0_4 : search wr8 24 4 [1, c2, 1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_0_5 : search wr8 24 4 [1, c2, 1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_1_0 : search wr8 24 4 [1, c2, t01, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_1_1 : search wr8 24 4 [1, c2, t01, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_1_2 : search wr8 24 4 [1, c2, t01, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_1_3 : search wr8 24 4 [1, c2, t01, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_1_4 : search wr8 24 4 [1, c2, t01, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_1_5 : search wr8 24 4 [1, c2, t01, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_2_0 : search wr8 24 4 [1, c2, t12, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_2_1 : search wr8 24 4 [1, c2, t12, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_2_2 : search wr8 24 4 [1, c2, t12, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_2_3 : search wr8 24 4 [1, c2, t12, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_2_4 : search wr8 24 4 [1, c2, t12, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_2_5 : search wr8 24 4 [1, c2, t12, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_3_0 : search wr8 24 4 [1, c2, t02, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_3_1 : search wr8 24 4 [1, c2, t02, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_3_2 : search wr8 24 4 [1, c2, t02, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_3_3 : search wr8 24 4 [1, c2, t02, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_3_4 : search wr8 24 4 [1, c2, t02, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_3_5 : search wr8 24 4 [1, c2, t02, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_4_0 : search wr8 24 4 [1, c2, c1, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_4_1 : search wr8 24 4 [1, c2, c1, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_4_2 : search wr8 24 4 [1, c2, c1, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_4_3 : search wr8 24 4 [1, c2, c1, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_4_4 : search wr8 24 4 [1, c2, c1, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_4_5 : search wr8 24 4 [1, c2, c1, c2] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_5_0 : search wr8 24 4 [1, c2, c2, 1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_5_1 : search wr8 24 4 [1, c2, c2, t01] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_5_2 : search wr8 24 4 [1, c2, c2, t12] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_5_3 : search wr8 24 4 [1, c2, c2, t02] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_5_4 : search wr8 24 4 [1, c2, c2, c1] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem r8_leaf_5_5_5 : search wr8 24 4 [1, c2, c2, c2] = true := by
  decide +kernel

private theorem r8_node_0_0 : search wr8 24 5 [1, 1, 1] = true :=
  search_split wr8 24 4 [1, 1, 1] r8_leaf_0_0_0 r8_leaf_0_0_1 r8_leaf_0_0_2 r8_leaf_0_0_3 r8_leaf_0_0_4 r8_leaf_0_0_5

private theorem r8_node_0_1 : search wr8 24 5 [1, 1, t01] = true :=
  search_split wr8 24 4 [1, 1, t01] r8_leaf_0_1_0 r8_leaf_0_1_1 r8_leaf_0_1_2 r8_leaf_0_1_3 r8_leaf_0_1_4 r8_leaf_0_1_5

private theorem r8_node_0_2 : search wr8 24 5 [1, 1, t12] = true :=
  search_split wr8 24 4 [1, 1, t12] r8_leaf_0_2_0 r8_leaf_0_2_1 r8_leaf_0_2_2 r8_leaf_0_2_3 r8_leaf_0_2_4 r8_leaf_0_2_5

private theorem r8_node_0_3 : search wr8 24 5 [1, 1, t02] = true :=
  search_split wr8 24 4 [1, 1, t02] r8_leaf_0_3_0 r8_leaf_0_3_1 r8_leaf_0_3_2 r8_leaf_0_3_3 r8_leaf_0_3_4 r8_leaf_0_3_5

private theorem r8_node_0_4 : search wr8 24 5 [1, 1, c1] = true :=
  search_split wr8 24 4 [1, 1, c1] r8_leaf_0_4_0 r8_leaf_0_4_1 r8_leaf_0_4_2 r8_leaf_0_4_3 r8_leaf_0_4_4 r8_leaf_0_4_5

private theorem r8_node_0_5 : search wr8 24 5 [1, 1, c2] = true :=
  search_split wr8 24 4 [1, 1, c2] r8_leaf_0_5_0 r8_leaf_0_5_1 r8_leaf_0_5_2 r8_leaf_0_5_3 r8_leaf_0_5_4 r8_leaf_0_5_5

private theorem r8_node_1_0 : search wr8 24 5 [1, t01, 1] = true :=
  search_split wr8 24 4 [1, t01, 1] r8_leaf_1_0_0 r8_leaf_1_0_1 r8_leaf_1_0_2 r8_leaf_1_0_3 r8_leaf_1_0_4 r8_leaf_1_0_5

private theorem r8_node_1_1 : search wr8 24 5 [1, t01, t01] = true :=
  search_split wr8 24 4 [1, t01, t01] r8_leaf_1_1_0 r8_leaf_1_1_1 r8_leaf_1_1_2 r8_leaf_1_1_3 r8_leaf_1_1_4 r8_leaf_1_1_5

private theorem r8_node_1_2 : search wr8 24 5 [1, t01, t12] = true :=
  search_split wr8 24 4 [1, t01, t12] r8_leaf_1_2_0 r8_leaf_1_2_1 r8_leaf_1_2_2 r8_leaf_1_2_3 r8_leaf_1_2_4 r8_leaf_1_2_5

private theorem r8_node_1_3 : search wr8 24 5 [1, t01, t02] = true :=
  search_split wr8 24 4 [1, t01, t02] r8_leaf_1_3_0 r8_leaf_1_3_1 r8_leaf_1_3_2 r8_leaf_1_3_3 r8_leaf_1_3_4 r8_leaf_1_3_5

private theorem r8_node_1_4 : search wr8 24 5 [1, t01, c1] = true :=
  search_split wr8 24 4 [1, t01, c1] r8_leaf_1_4_0 r8_leaf_1_4_1 r8_leaf_1_4_2 r8_leaf_1_4_3 r8_leaf_1_4_4 r8_leaf_1_4_5

private theorem r8_node_1_5 : search wr8 24 5 [1, t01, c2] = true :=
  search_split wr8 24 4 [1, t01, c2] r8_leaf_1_5_0 r8_leaf_1_5_1 r8_leaf_1_5_2 r8_leaf_1_5_3 r8_leaf_1_5_4 r8_leaf_1_5_5

private theorem r8_node_2_0 : search wr8 24 5 [1, t12, 1] = true :=
  search_split wr8 24 4 [1, t12, 1] r8_leaf_2_0_0 r8_leaf_2_0_1 r8_leaf_2_0_2 r8_leaf_2_0_3 r8_leaf_2_0_4 r8_leaf_2_0_5

private theorem r8_node_2_1 : search wr8 24 5 [1, t12, t01] = true :=
  search_split wr8 24 4 [1, t12, t01] r8_leaf_2_1_0 r8_leaf_2_1_1 r8_leaf_2_1_2 r8_leaf_2_1_3 r8_leaf_2_1_4 r8_leaf_2_1_5

private theorem r8_node_2_2 : search wr8 24 5 [1, t12, t12] = true :=
  search_split wr8 24 4 [1, t12, t12] r8_leaf_2_2_0 r8_leaf_2_2_1 r8_leaf_2_2_2 r8_leaf_2_2_3 r8_leaf_2_2_4 r8_leaf_2_2_5

private theorem r8_node_2_3 : search wr8 24 5 [1, t12, t02] = true :=
  search_split wr8 24 4 [1, t12, t02] r8_leaf_2_3_0 r8_leaf_2_3_1 r8_leaf_2_3_2 r8_leaf_2_3_3 r8_leaf_2_3_4 r8_leaf_2_3_5

private theorem r8_node_2_4 : search wr8 24 5 [1, t12, c1] = true :=
  search_split wr8 24 4 [1, t12, c1] r8_leaf_2_4_0 r8_leaf_2_4_1 r8_leaf_2_4_2 r8_leaf_2_4_3 r8_leaf_2_4_4 r8_leaf_2_4_5

private theorem r8_node_2_5 : search wr8 24 5 [1, t12, c2] = true :=
  search_split wr8 24 4 [1, t12, c2] r8_leaf_2_5_0 r8_leaf_2_5_1 r8_leaf_2_5_2 r8_leaf_2_5_3 r8_leaf_2_5_4 r8_leaf_2_5_5

private theorem r8_node_3_0 : search wr8 24 5 [1, t02, 1] = true :=
  search_split wr8 24 4 [1, t02, 1] r8_leaf_3_0_0 r8_leaf_3_0_1 r8_leaf_3_0_2 r8_leaf_3_0_3 r8_leaf_3_0_4 r8_leaf_3_0_5

private theorem r8_node_3_1 : search wr8 24 5 [1, t02, t01] = true :=
  search_split wr8 24 4 [1, t02, t01] r8_leaf_3_1_0 r8_leaf_3_1_1 r8_leaf_3_1_2 r8_leaf_3_1_3 r8_leaf_3_1_4 r8_leaf_3_1_5

private theorem r8_node_3_2 : search wr8 24 5 [1, t02, t12] = true :=
  search_split wr8 24 4 [1, t02, t12] r8_leaf_3_2_0 r8_leaf_3_2_1 r8_leaf_3_2_2 r8_leaf_3_2_3 r8_leaf_3_2_4 r8_leaf_3_2_5

private theorem r8_node_3_3 : search wr8 24 5 [1, t02, t02] = true :=
  search_split wr8 24 4 [1, t02, t02] r8_leaf_3_3_0 r8_leaf_3_3_1 r8_leaf_3_3_2 r8_leaf_3_3_3 r8_leaf_3_3_4 r8_leaf_3_3_5

private theorem r8_node_3_4 : search wr8 24 5 [1, t02, c1] = true :=
  search_split wr8 24 4 [1, t02, c1] r8_leaf_3_4_0 r8_leaf_3_4_1 r8_leaf_3_4_2 r8_leaf_3_4_3 r8_leaf_3_4_4 r8_leaf_3_4_5

private theorem r8_node_3_5 : search wr8 24 5 [1, t02, c2] = true :=
  search_split wr8 24 4 [1, t02, c2] r8_leaf_3_5_0 r8_leaf_3_5_1 r8_leaf_3_5_2 r8_leaf_3_5_3 r8_leaf_3_5_4 r8_leaf_3_5_5

private theorem r8_node_4_0 : search wr8 24 5 [1, c1, 1] = true :=
  search_split wr8 24 4 [1, c1, 1] r8_leaf_4_0_0 r8_leaf_4_0_1 r8_leaf_4_0_2 r8_leaf_4_0_3 r8_leaf_4_0_4 r8_leaf_4_0_5

private theorem r8_node_4_1 : search wr8 24 5 [1, c1, t01] = true :=
  search_split wr8 24 4 [1, c1, t01] r8_leaf_4_1_0 r8_leaf_4_1_1 r8_leaf_4_1_2 r8_leaf_4_1_3 r8_leaf_4_1_4 r8_leaf_4_1_5

private theorem r8_node_4_2 : search wr8 24 5 [1, c1, t12] = true :=
  search_split wr8 24 4 [1, c1, t12] r8_leaf_4_2_0 r8_leaf_4_2_1 r8_leaf_4_2_2 r8_leaf_4_2_3 r8_leaf_4_2_4 r8_leaf_4_2_5

private theorem r8_node_4_3 : search wr8 24 5 [1, c1, t02] = true :=
  search_split wr8 24 4 [1, c1, t02] r8_leaf_4_3_0 r8_leaf_4_3_1 r8_leaf_4_3_2 r8_leaf_4_3_3 r8_leaf_4_3_4 r8_leaf_4_3_5

private theorem r8_node_4_4 : search wr8 24 5 [1, c1, c1] = true :=
  search_split wr8 24 4 [1, c1, c1] r8_leaf_4_4_0 r8_leaf_4_4_1 r8_leaf_4_4_2 r8_leaf_4_4_3 r8_leaf_4_4_4 r8_leaf_4_4_5

private theorem r8_node_4_5 : search wr8 24 5 [1, c1, c2] = true :=
  search_split wr8 24 4 [1, c1, c2] r8_leaf_4_5_0 r8_leaf_4_5_1 r8_leaf_4_5_2 r8_leaf_4_5_3 r8_leaf_4_5_4 r8_leaf_4_5_5

private theorem r8_node_5_0 : search wr8 24 5 [1, c2, 1] = true :=
  search_split wr8 24 4 [1, c2, 1] r8_leaf_5_0_0 r8_leaf_5_0_1 r8_leaf_5_0_2 r8_leaf_5_0_3 r8_leaf_5_0_4 r8_leaf_5_0_5

private theorem r8_node_5_1 : search wr8 24 5 [1, c2, t01] = true :=
  search_split wr8 24 4 [1, c2, t01] r8_leaf_5_1_0 r8_leaf_5_1_1 r8_leaf_5_1_2 r8_leaf_5_1_3 r8_leaf_5_1_4 r8_leaf_5_1_5

private theorem r8_node_5_2 : search wr8 24 5 [1, c2, t12] = true :=
  search_split wr8 24 4 [1, c2, t12] r8_leaf_5_2_0 r8_leaf_5_2_1 r8_leaf_5_2_2 r8_leaf_5_2_3 r8_leaf_5_2_4 r8_leaf_5_2_5

private theorem r8_node_5_3 : search wr8 24 5 [1, c2, t02] = true :=
  search_split wr8 24 4 [1, c2, t02] r8_leaf_5_3_0 r8_leaf_5_3_1 r8_leaf_5_3_2 r8_leaf_5_3_3 r8_leaf_5_3_4 r8_leaf_5_3_5

private theorem r8_node_5_4 : search wr8 24 5 [1, c2, c1] = true :=
  search_split wr8 24 4 [1, c2, c1] r8_leaf_5_4_0 r8_leaf_5_4_1 r8_leaf_5_4_2 r8_leaf_5_4_3 r8_leaf_5_4_4 r8_leaf_5_4_5

private theorem r8_node_5_5 : search wr8 24 5 [1, c2, c2] = true :=
  search_split wr8 24 4 [1, c2, c2] r8_leaf_5_5_0 r8_leaf_5_5_1 r8_leaf_5_5_2 r8_leaf_5_5_3 r8_leaf_5_5_4 r8_leaf_5_5_5

private theorem r8_node_0 : search wr8 24 6 [1, 1] = true :=
  search_split wr8 24 5 [1, 1] r8_node_0_0 r8_node_0_1 r8_node_0_2 r8_node_0_3 r8_node_0_4 r8_node_0_5

private theorem r8_node_1 : search wr8 24 6 [1, t01] = true :=
  search_split wr8 24 5 [1, t01] r8_node_1_0 r8_node_1_1 r8_node_1_2 r8_node_1_3 r8_node_1_4 r8_node_1_5

private theorem r8_node_2 : search wr8 24 6 [1, t12] = true :=
  search_split wr8 24 5 [1, t12] r8_node_2_0 r8_node_2_1 r8_node_2_2 r8_node_2_3 r8_node_2_4 r8_node_2_5

private theorem r8_node_3 : search wr8 24 6 [1, t02] = true :=
  search_split wr8 24 5 [1, t02] r8_node_3_0 r8_node_3_1 r8_node_3_2 r8_node_3_3 r8_node_3_4 r8_node_3_5

private theorem r8_node_4 : search wr8 24 6 [1, c1] = true :=
  search_split wr8 24 5 [1, c1] r8_node_4_0 r8_node_4_1 r8_node_4_2 r8_node_4_3 r8_node_4_4 r8_node_4_5

private theorem r8_node_5 : search wr8 24 6 [1, c2] = true :=
  search_split wr8 24 5 [1, c2] r8_node_5_0 r8_node_5_1 r8_node_5_2 r8_node_5_3 r8_node_5_4 r8_node_5_5

private theorem r8_root : search wr8 24 7 [1] = true :=
  search_split wr8 24 6 [1] r8_node_0 r8_node_1 r8_node_2 r8_node_3 r8_node_4 r8_node_5

/-- **Corollary 7 at `q = 2`.** The replicated seed on `K₈`: `N = 64 = 8q³`, every gauge costs at
least `24 = 6q²`, and `24` is attained, so `N/D = 8/3`. -/
theorem witness_r8 :
    defect wr8 = 64 ∧ (∀ β, 24 ≤ cost wr8 β) ∧ cost wr8 (fun _ => 1) = 24 ∧ 64 * 3 = 8 * 24 :=
  ⟨by decide +kernel, gauge_lower_bb wr8 24 r8_root, by decide +kernel, by norm_num⟩


/-! ## The cross-degree convention (Proposition 11)

Chapman–Lubotzky also compare a degree-3 permutation `σ` with a degree-`m` one `τ`, by
`1 − #{j < min(3, m) : σ j = τ j} / max(3, m)`. Multiplying by `max(3, m)` keeps everything in
integers: the scaled cost of a comparison gauge `β : Fin k → Sym(m)` is
`Σ_{u<v} (max(3, m) − agree(α(u,v), β(u)⁻¹ β(v)))`. For the seed `w4` the minimum is `10`, `6`
and `12` at `m = 2, 3, 4`, that is `10/3`, `2` and `3` in edge units: no other degree repairs the
seed more cheaply than degree three, whose minimum is `2`. -/

/-- Points `j < min(3, m)` on which `σ` and `τ` agree. -/
def agree {m : ℕ} (σ : S3) (τ : Perm (Fin m)) : ℕ :=
  (List.finRange 3).countP fun j =>
    if h : j.val < m then decide ((τ ⟨j.val, h⟩).val = (σ j).val) else false

/-- The scaled cross-degree cost of the comparison coboundary `β(u)⁻¹ β(v)`. -/
def errCost {m : ℕ} (α : Fin k → Fin k → S3) (β : Fin k → Perm (Fin m)) : ℕ :=
  ((edges k).map fun e => max 3 m - agree (α e.1 e.2) ((β e.1)⁻¹ * β e.2)).sum

/-- A constant left factor does not change the comparison coboundary, so fixing `β(0) = 1`
loses nothing. -/
theorem errCost_mul_left {m : ℕ} (α : Fin k → Fin k → S3) (β : Fin k → Perm (Fin m))
    (c : Perm (Fin m)) : errCost α (fun v => c * β v) = errCost α β := by
  unfold errCost
  congr 1
  apply List.map_congr_left
  intro e _
  have : (c * β e.1)⁻¹ * (c * β e.2) = (β e.1)⁻¹ * β e.2 := by group
  rw [this]

/-- Check a Boolean test on every function `Fin n → G`, given a complete list of `G`. -/
def allL {G : Type} (L : List G) : (n : ℕ) → ((Fin n → G) → Bool) → Bool
  | 0, p => p Fin.elim0
  | n + 1, p => L.all fun a => allL L n (fun t => p (Fin.cons a t))

theorem allL_sound {G : Type} (L : List G) (hL : ∀ g, g ∈ L) :
    ∀ (n : ℕ) (p : (Fin n → G) → Bool), allL L n p = true → ∀ f, p f = true
  | 0, p, h, f => by
    have : f = Fin.elim0 := funext fun i => i.elim0
    rw [this]; exact h
  | n + 1, p, h, f => by
    simp only [allL, List.all_eq_true] at h
    have := allL_sound L hL n _ (h (f 0) (hL _)) (Fin.tail f)
    simpa [Fin.cons_self_tail] using this

/-- Exhausting comparison gauges with `β(0) = 1` covers every comparison gauge. -/
theorem err_lower {m n : ℕ} (L : List (Perm (Fin m))) (hL : ∀ g, g ∈ L)
    (α : Fin (n + 1) → Fin (n + 1) → S3) (D : ℕ)
    (h : allL L n (fun t => decide (D ≤ errCost α (Fin.cons (1 : Perm (Fin m)) t))) = true) :
    ∀ β : Fin (n + 1) → Perm (Fin m), D ≤ errCost α β := by
  intro β
  rw [← errCost_mul_left α β (β 0)⁻¹]
  set β' : Fin (n + 1) → Perm (Fin m) := fun v => (β 0)⁻¹ * β v with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have hcons : β' = Fin.cons 1 (Fin.tail β') := by
    rw [← h0]; exact (Fin.cons_self_tail β').symm
  rw [hcons]
  have := allL_sound L hL n _ h (Fin.tail β')
  simpa using this

def perms2 : List (Perm (Fin 2)) := [1, swap 0 1]
theorem mem_perms2 : ∀ g : Perm (Fin 2), g ∈ perms2 := by decide

def perms3 : List (Perm (Fin 3)) := S3list
theorem mem_perms3 : ∀ g : Perm (Fin 3), g ∈ perms3 := mem_S3list

def perms4 : List (Perm (Fin 4)) :=
  [(1 : Perm (Fin 4)) ,
    (swap 0 1 : Perm (Fin 4)) ,
    (swap 0 2 : Perm (Fin 4)) ,
    (swap 0 3 : Perm (Fin 4)) ,
    (swap 1 2 : Perm (Fin 4)) ,
    (swap 1 3 : Perm (Fin 4)) ,
    (swap 2 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 0 2 : Perm (Fin 4)) ,
    (swap 0 1 * swap 0 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 1 2 : Perm (Fin 4)) ,
    (swap 0 1 * swap 1 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 2 3 : Perm (Fin 4)) ,
    (swap 0 2 * swap 0 3 : Perm (Fin 4)) ,
    (swap 0 2 * swap 1 3 : Perm (Fin 4)) ,
    (swap 0 2 * swap 2 3 : Perm (Fin 4)) ,
    (swap 0 3 * swap 1 2 : Perm (Fin 4)) ,
    (swap 1 2 * swap 1 3 : Perm (Fin 4)) ,
    (swap 1 2 * swap 2 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 0 2 * swap 0 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 0 2 * swap 1 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 0 2 * swap 2 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 0 3 * swap 1 2 : Perm (Fin 4)) ,
    (swap 0 1 * swap 1 2 * swap 1 3 : Perm (Fin 4)) ,
    (swap 0 1 * swap 1 2 * swap 2 3 : Perm (Fin 4))]
theorem mem_perms4 : ∀ g : Perm (Fin 4), g ∈ perms4 := by decide

set_option maxHeartbeats 0 in
private theorem c4_leaf_0 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (1 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_1 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_2 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 2 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_3 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_4 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 1 2 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_5 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 1 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_6 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 2 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_7 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 0 2 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_8 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 0 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_9 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 1 2 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_10 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 1 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_11 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 2 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_12 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 2 * swap 0 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_13 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 2 * swap 1 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_14 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 2 * swap 2 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_15 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 3 * swap 1 2 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_16 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 1 2 * swap 1 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_17 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 1 2 * swap 2 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_18 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 0 2 * swap 0 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_19 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 0 2 * swap 1 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_20 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 0 2 * swap 2 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_21 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 0 3 * swap 1 2 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_22 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 1 2 * swap 1 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem c4_leaf_23 : allL perms4 2 (fun t => decide (12 ≤ errCost w4
    (Fin.cons (1 : Perm (Fin 4)) (Fin.cons (swap 0 1 * swap 1 2 * swap 2 3 : Perm (Fin 4)) t)))) = true := by
  decide +kernel

/-- The degree-4 exhaustion, split by the comparison gauge on vertex 1 into 24 kernel checks. -/
theorem cross_m4_lower : ∀ β : Fin 4 → Perm (Fin 4), 12 ≤ errCost w4 β := by
  apply err_lower perms4 mem_perms4 w4 12
  rw [allL, List.all_eq_true]
  intro a ha
  simp only [perms4, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [c4_leaf_0, c4_leaf_1, c4_leaf_2, c4_leaf_3, c4_leaf_4, c4_leaf_5, c4_leaf_6, c4_leaf_7, c4_leaf_8, c4_leaf_9, c4_leaf_10, c4_leaf_11, c4_leaf_12, c4_leaf_13, c4_leaf_14, c4_leaf_15, c4_leaf_16, c4_leaf_17, c4_leaf_18, c4_leaf_19, c4_leaf_20, c4_leaf_21, c4_leaf_22, c4_leaf_23]

/-- **Proposition 11, the seed.** Against comparison permutations of degree 2, 3 and 4 the seed's
cheapest scaled repair is `10`, `6` and `12`, that is `10/3`, `2` and `3` in edge units, each
attained. Degree three, the seed's own degree, is the cheapest. -/
theorem cross_degree_seed :
    ((∀ β : Fin 4 → Perm (Fin 2), 10 ≤ errCost w4 β) ∧ ∃ β : Fin 4 → Perm (Fin 2), errCost w4 β = 10) ∧
    ((∀ β : Fin 4 → Perm (Fin 3), 6 ≤ errCost w4 β) ∧ ∃ β : Fin 4 → Perm (Fin 3), errCost w4 β = 6) ∧
    ((∀ β : Fin 4 → Perm (Fin 4), 12 ≤ errCost w4 β) ∧ ∃ β : Fin 4 → Perm (Fin 4), errCost w4 β = 12) :=
  ⟨⟨err_lower perms2 mem_perms2 w4 10 (by decide +kernel), fun _ => 1, by decide +kernel⟩,
    ⟨err_lower perms3 mem_perms3 w4 6 (by decide +kernel), fun _ => 1, by decide +kernel⟩,
    ⟨cross_m4_lower, fun _ => 1, by decide +kernel⟩⟩

end CoboundaryK3

/-
Layer 7: Kozlov's staircase seeds, and `h₁(K_k) = k/3` for every `k ≥ 3`.

Author: Jeromie Beasley (dicipler-pixel). Drafted with AI assistance (Grok Bot); every
statement below is checked by the Lean kernel in CI.

The seeds are the staircase graphs of D. N. Kozlov (arXiv:1610.07136), built from the partition
`(t, t-1, …, 1)`: on `m = 2t + 1` vertices `u, v₁, …, v_t, y₁, …, y_t`, join `vᵢ` to `y_j`
exactly when `i ≤ j`, and put the transposition `t01` on those edges and the identity elsewhere.
Here the vertices are numbered `u = 0`, `vᵢ = 2i - 1`, `y_j = 2j`, so an edge `p < q` carries
`t01` exactly when `p` is odd and `q` is even (`stair`). The witnesses `w5` and `w7` of `Basic`
are the staircases for `t = 2, 3` up to relabelling.

All counts are moved-point counts, as in `Basic`: a staircase edge costs `2`.

* `stair_gaugeDist`: the gauge distance of the staircase on `K_{2t+1}` is exactly `t(t+1)`,
  twice its number of edges. The lower bound is the parity retraction (a `Sym(3)` gauge costs at
  least twice the `F₂` count of its signs, `stair_cost_ge`) followed by cut-minimality: adding
  the two newest vertices adds at least `t + 1` to every `F₂` count (`st_cutF_ge`).
* `stair_defect_mul`: `3N = (2t+1) D`, from the triangle count
  `N = 2(1² + 2² + … + t²) = t(t+1)(2t+1)/3` (`st_tri`).
* `h1_mul_of_seed`: balanced replication (`rep_defect`, `rep_attain`, `rep_lower`) turns any
  seed with `3N = mD` into `h₁(K_{mq}) = mq/3` for every `q ≥ 1`.
* `h1_eq_all`: every `k ≥ 3` is `4q` or `(2t+1)q` with `t ≥ 1`, so `h₁(K_k) = k/3` for every
  `k ≥ 3` (`h1_eq_k_div_three_ge_four`: the paper's Theorem 8, every `k ≥ 4`).
-/
import CoboundaryK3.Replication

namespace CoboundaryK3

open Finset

/-! ## Indicator, parity and the staircase -/

/-- `1` for `true`, `0` for `false`. -/
def bnat (b : Bool) : ℕ := if b then 1 else 0

/-- The staircase edge predicate on positions `p < q`: `p` odd and `q` even. -/
def stEdge (p q : ℕ) : Bool := decide (p % 2 = 1) && decide (q % 2 = 0)

/-- **Kozlov's staircase cochain** on `K_k`: `t01` on the edges `p < q` with `p` odd and `q`
even, the identity elsewhere. For `k = 2t + 1` this is the staircase of the partition
`(t, …, 1)` with one loose vertex `0`. -/
def stair (k : ℕ) : Fin k → Fin k → S3 := fun p q => if stEdge p.val q.val then t01 else 1

/-- The sign of a permutation of three points, as a Boolean (`true` for a transposition). -/
def oddPerm (σ : S3) : Bool := decide (σ = t01) || decide (σ = t12) || decide (σ = t02)

/-- **Parity retraction, one edge.** An odd edge term moves at least two points. -/
theorem st_par_bound (a b : S3) (e : Bool) :
    2 * bnat (xor (xor (oddPerm a) (oddPerm b)) e) ≤
      moved (a⁻¹ * (if e then t01 else 1) * b) := by
  have ha := mem_S3list a
  have hb := mem_S3list b
  simp only [S3list, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> cases e <;> decide

theorem st_moved_one (b : Bool) :
    moved ((1 : S3)⁻¹ * (if b then t01 else 1) * 1) = 2 * bnat b := by
  cases b <;> decide

theorem st_moved_tri (a b c : Bool) :
    moved ((if a then t01 else 1) * (if b then t01 else 1) * (if c then t01 else 1)⁻¹) =
      2 * bnat (xor (xor a b) c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem st_se_odd (p q : ℕ) (hq : q % 2 = 1) : stEdge p q = false := by
  unfold stEdge
  rw [hq]
  simp

theorem st_se_even (p q : ℕ) (hq : q % 2 = 0) : stEdge p q = decide (p % 2 = 1) := by
  unfold stEdge
  rw [hq]
  simp

/-! ## From `Fin` sums to sums over `range` -/

theorem st_sum_lt (n v : ℕ) (hv : v ≤ n) (f : ℕ → ℕ) :
    (∑ u ∈ range n, if u < v then f u else 0) = ∑ u ∈ range v, f u := by
  rw [← Finset.sum_filter]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨lt_of_lt_of_le h hv, h⟩

/-- A sum over the edges `u < v` of `K_n`, as a sum over `range`. -/
theorem st_fin_pair (n : ℕ) (G : ℕ → ℕ → ℕ) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then G u.val v.val else 0) =
      ∑ v ∈ range n, ∑ u ∈ range v, G u v := by
  have hA : (∑ u : Fin n, ∑ v : Fin n, if u < v then G u.val v.val else 0) =
      ∑ u ∈ range n, ∑ v ∈ range n, if u < v then G u v else 0 := by
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun u => ∑ v ∈ range n, if u < v then G u v else 0) n)
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun v => if u.val < v then G u.val v else 0) n)
    refine Finset.sum_congr rfl fun v _ => ?_
    show (if u < v then G u.val v.val else 0) = (if u.val < v.val then G u.val v.val else 0)
    by_cases h : u < v
    · rw [if_pos h, if_pos (show u.val < v.val from h)]
    · rw [if_neg h, if_neg (show ¬ (u.val < v.val) from h)]
  rw [hA, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  exact st_sum_lt n v (Finset.mem_range.mp hv).le (fun u => G u v)

/-- A sum over the triangles `u < v < w` of `K_n`, as a sum over `range`. -/
theorem st_fin_triple (n : ℕ) (Y : ℕ → ℕ → ℕ → ℕ) :
    (∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
      if u < v ∧ v < w then Y u.val v.val w.val else 0) =
      ∑ w ∈ range n, ∑ v ∈ range w, ∑ u ∈ range v, Y u v w := by
  have hA : (∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
      if u < v ∧ v < w then Y u.val v.val w.val else 0) =
      ∑ u ∈ range n, ∑ v ∈ range n, ∑ w ∈ range n,
        if u < v ∧ v < w then Y u v w else 0 := by
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun u => ∑ v ∈ range n, ∑ w ∈ range n, if u < v ∧ v < w then Y u v w else 0) n)
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun v => ∑ w ∈ range n, if u.val < v ∧ v < w then Y u.val v w else 0) n)
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range
      (fun w => if u.val < v.val ∧ v.val < w then Y u.val v.val w else 0) n)
    refine Finset.sum_congr rfl fun w _ => ?_
    show (if u < v ∧ v < w then Y u.val v.val w.val else 0) =
      (if u.val < v.val ∧ v.val < w.val then Y u.val v.val w.val else 0)
    by_cases h : u < v ∧ v < w
    · rw [if_pos h, if_pos (show u.val < v.val ∧ v.val < w.val from h)]
    · rw [if_neg h, if_neg (show ¬ (u.val < v.val ∧ v.val < w.val) from h)]
  have hB : (∑ u ∈ range n, ∑ v ∈ range n, ∑ w ∈ range n,
        if u < v ∧ v < w then Y u v w else 0) =
      ∑ w ∈ range n, ∑ v ∈ range n, ∑ u ∈ range n,
        if u < v ∧ v < w then Y u v w else 0 := by
    calc _ = ∑ v ∈ range n, ∑ u ∈ range n, ∑ w ∈ range n,
          (if u < v ∧ v < w then Y u v w else 0) := Finset.sum_comm
      _ = ∑ v ∈ range n, ∑ w ∈ range n, ∑ u ∈ range n,
          (if u < v ∧ v < w then Y u v w else 0) :=
          Finset.sum_congr rfl fun v _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hA, hB]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : w < n := Finset.mem_range.mp hw
  have e : ∀ v, (∑ u ∈ range n, if u < v ∧ v < w then Y u v w else 0) =
      if v < w then ∑ u ∈ range v, Y u v w else 0 := by
    intro v
    by_cases hv : v < w
    · rw [if_pos hv]
      refine Eq.trans ?_ (st_sum_lt n v (by omega) (fun u => Y u v w))
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u < v
      · rw [if_pos (And.intro hu hv), if_pos hu]
      · rw [if_neg (show ¬ (u < v ∧ v < w) from fun h => hu h.1), if_neg hu]
    · rw [if_neg hv]
      exact Finset.sum_eq_zero fun u _ => if_neg (show ¬ (u < v ∧ v < w) from fun h => hv h.2)
  simp only [e]
  exact st_sum_lt n w hw'.le (fun v => ∑ u ∈ range v, Y u v w)

/-! ## The `F₂` counts on positions -/

/-- The term of the pair `p < q` under the sign pattern `σ`: odd exactly when the edge term
is a transposition. -/
def gx (σ : ℕ → Bool) (p q : ℕ) : ℕ := bnat (xor (xor (σ p) (σ q)) (stEdge p q))

/-- The `F₂` cost of the sign pattern `σ` on the first `n` positions. -/
def cutF (σ : ℕ → Bool) (n : ℕ) : ℕ := ∑ q ∈ range n, ∑ p ∈ range q, gx σ p q

/-- The number of staircase edges among the first `n` positions. -/
def stE (n : ℕ) : ℕ := ∑ q ∈ range n, ∑ p ∈ range q, bnat (stEdge p q)

/-- The pairs `u < v < n` with `u` even and `v` odd, written as the triangle term at an even
third vertex. -/
def stP (n : ℕ) : ℕ :=
  ∑ v ∈ range n, ∑ u ∈ range v, bnat (xor (xor (stEdge u v) (decide (v % 2 = 1))) (decide (u % 2 = 1)))

/-- The number of broken triangles (an odd number of staircase edges) among the first `n`
positions. -/
def stT (n : ℕ) : ℕ :=
  ∑ w ∈ range n, ∑ v ∈ range w, ∑ u ∈ range v, bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w))

theorem st_cutF_succ (σ : ℕ → Bool) (n : ℕ) :
    cutF σ (n + 1) = cutF σ n + ∑ p ∈ range n, gx σ p n := by
  unfold cutF
  exact Finset.sum_range_succ (fun q => ∑ p ∈ range q, gx σ p q) n

theorem st_stE_succ (n : ℕ) : stE (n + 1) = stE n + ∑ p ∈ range n, bnat (stEdge p n) := by
  unfold stE
  exact Finset.sum_range_succ (fun q => ∑ p ∈ range q, bnat (stEdge p q)) n

theorem st_stP_succ (n : ℕ) : stP (n + 1) = stP n +
    ∑ u ∈ range n, bnat (xor (xor (stEdge u n) (decide (n % 2 = 1))) (decide (u % 2 = 1))) := by
  unfold stP
  exact Finset.sum_range_succ (fun v => ∑ u ∈ range v,
    bnat (xor (xor (stEdge u v) (decide (v % 2 = 1))) (decide (u % 2 = 1)))) n

theorem st_stT_succ (n : ℕ) : stT (n + 1) = stT n +
    ∑ v ∈ range n, ∑ u ∈ range v, bnat (xor (xor (stEdge u v) (stEdge v n)) (stEdge u n)) := by
  unfold stT
  exact Finset.sum_range_succ (fun w => ∑ v ∈ range w, ∑ u ∈ range v,
    bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w))) n

/-- Among the positions `0, …, 2t`, exactly `t` are odd. -/
theorem st_cnt_odd (t : ℕ) : ∑ p ∈ range (2 * t + 1), bnat (decide (p % 2 = 1)) = t := by
  induction t with
  | zero => simp [bnat]
  | succ t ih =>
    have h1 : (2 * t + 1) % 2 = 1 := by omega
    have h2 : (2 * t + 1 + 1) % 2 = 0 := by omega
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, h1, h2]
    all_goals first | rfl | simp [bnat]

/-- Among the positions `0, …, 2t`, exactly `t + 1` are even. -/
theorem st_cnt_even (t : ℕ) : ∑ p ∈ range (2 * t + 1), bnat (!decide (p % 2 = 1)) = t + 1 := by
  induction t with
  | zero => first | rfl | decide | (rw [Finset.sum_range_one]; rfl)
  | succ t ih =>
    have h1 : (2 * t + 1) % 2 = 1 := by omega
    have h2 : (2 * t + 1 + 1) % 2 = 0 := by omega
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, h1, h2]
    all_goals first | rfl | simp [bnat]

theorem st_pair_bound (x A B o : Bool) :
    (if A = B then bnat o else bnat (!o)) ≤ bnat (xor (xor x A) false) + bnat (xor (xor x B) o) := by
  cases x <;> cases A <;> cases B <;> cases o <;> decide

theorem st_ab_bound (A B : Bool) :
    (if A = B then 1 else 0) ≤ bnat (xor (xor A B) (decide (1 = 1))) := by
  cases A <;> cases B <;> decide

/-- **Cut-minimality.** Every sign pattern on the staircase of `K_{2t+1}` costs at least the
number of edges `t(t+1)/2`. Adding the two newest positions `2t+1` (a new `v`, joined to every
earlier `y`) and `2t+2` (a new `y`, joined only to it) adds at least `t + 1`: if their signs agree,
each of the `t` odd earlier positions contributes one and the new edge one; if they differ, each of
the `t + 1` even earlier positions contributes one. -/
theorem st_cutF_ge (t : ℕ) : ∀ σ : ℕ → Bool, t * (t + 1) ≤ 2 * cutF σ (2 * t + 1) := by
  induction t with
  | zero => intro σ; simp
  | succ t ih =>
    intro σ
    have ha : (2 * t + 1) % 2 = 1 := by omega
    have hb : (2 * t + 1 + 1) % 2 = 0 := by omega
    have hp : ∀ p, (if σ (2 * t + 1) = σ (2 * t + 1 + 1) then bnat (decide (p % 2 = 1))
        else bnat (!decide (p % 2 = 1))) ≤ gx σ p (2 * t + 1) + gx σ p (2 * t + 1 + 1) := by
      intro p
      unfold gx
      rw [st_se_odd p _ ha, st_se_even p _ hb]
      exact st_pair_bound _ _ _ _
    have hab : (if σ (2 * t + 1) = σ (2 * t + 1 + 1) then 1 else 0) ≤
        gx σ (2 * t + 1) (2 * t + 1 + 1) := by
      unfold gx
      rw [st_se_even _ _ hb, ha]
      exact st_ab_bound _ _
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, st_cutF_succ, st_cutF_succ,
      Finset.sum_range_succ _ (2 * t + 1)]
    have hi := ih σ
    by_cases h : σ (2 * t + 1) = σ (2 * t + 1 + 1)
    · have hc := st_cnt_odd t
      have hle : ∑ p ∈ range (2 * t + 1), bnat (decide (p % 2 = 1)) ≤
          ∑ p ∈ range (2 * t + 1), (gx σ p (2 * t + 1) + gx σ p (2 * t + 1 + 1)) :=
        Finset.sum_le_sum fun p _ => by
          have := hp p
          rwa [if_pos h] at this
      rw [Finset.sum_add_distrib] at hle
      have h3 : 1 ≤ gx σ (2 * t + 1) (2 * t + 1 + 1) := by
        have := hab
        rwa [if_pos h] at this
      nlinarith
    · have hc := st_cnt_even t
      have hle : ∑ p ∈ range (2 * t + 1), bnat (!decide (p % 2 = 1)) ≤
          ∑ p ∈ range (2 * t + 1), (gx σ p (2 * t + 1) + gx σ p (2 * t + 1 + 1)) :=
        Finset.sum_le_sum fun p _ => by
          have := hp p
          rwa [if_neg h] at this
      rw [Finset.sum_add_distrib] at hle
      nlinarith

/-- The staircase on `K_{2t+1}` has `t(t+1)/2` edges. -/
theorem st_edges (t : ℕ) : 2 * stE (2 * t + 1) = t * (t + 1) := by
  induction t with
  | zero => simp [stE]
  | succ t ih =>
    have ha : (2 * t + 1) % 2 = 1 := by omega
    have hb : (2 * t + 1 + 1) % 2 = 0 := by omega
    have r1 : ∑ p ∈ range (2 * t + 1), bnat (stEdge p (2 * t + 1)) = 0 :=
      Finset.sum_eq_zero fun p _ => by rw [st_se_odd p _ ha]; all_goals rfl
    have hs : ∀ p, bnat (stEdge p (2 * t + 1 + 1)) = bnat (decide (p % 2 = 1)) := fun p => by
      rw [st_se_even p _ hb]
    have r2 : ∑ p ∈ range (2 * t + 1 + 1), bnat (stEdge p (2 * t + 1 + 1)) = t + 1 := by
      rw [Finset.sum_range_succ]
      simp only [hs]
      rw [st_cnt_odd t, ha]
      all_goals first | rfl | simp [bnat]
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, st_stE_succ, st_stE_succ, r1, r2]
    nlinarith

theorem st_row_odd (u q : ℕ) (hq : q % 2 = 1) :
    bnat (xor (xor (stEdge u q) (decide (q % 2 = 1))) (decide (u % 2 = 1))) =
      bnat (!decide (u % 2 = 1)) := by
  rw [st_se_odd u q hq, hq]
  generalize decide (u % 2 = 1) = o
  cases o <;> rfl

theorem st_row_even (u q : ℕ) (hq : q % 2 = 0) :
    bnat (xor (xor (stEdge u q) (decide (q % 2 = 1))) (decide (u % 2 = 1))) = 0 := by
  rw [st_se_even u q hq, hq]
  generalize decide (u % 2 = 1) = o
  cases o <;> rfl

/-- `2 · #{u < v < 2t+2 : u even, v odd} = (t+1)(t+2)`. -/
theorem st_P (t : ℕ) : 2 * stP (2 * t + 2) = (t + 1) * (t + 2) := by
  induction t with
  | zero => first | decide | rfl | simp [stP, Finset.sum_range_succ, stEdge, bnat]
  | succ t ih =>
    have hc : (2 * t + 2) % 2 = 0 := by omega
    have hd : (2 * t + 2 + 1) % 2 = 1 := by omega
    have r1 : ∑ u ∈ range (2 * t + 2),
        bnat (xor (xor (stEdge u (2 * t + 2)) (decide ((2 * t + 2) % 2 = 1))) (decide (u % 2 = 1)))
          = 0 :=
      Finset.sum_eq_zero fun u _ => st_row_even u _ hc
    have hce := st_cnt_even (t + 1)
    rw [show 2 * (t + 1) + 1 = 2 * t + 2 + 1 by ring] at hce
    have r2 : ∑ u ∈ range (2 * t + 2 + 1),
        bnat (xor (xor (stEdge u (2 * t + 2 + 1)) (decide ((2 * t + 2 + 1) % 2 = 1)))
          (decide (u % 2 = 1))) = t + 1 + 1 :=
      (Finset.sum_congr rfl fun u _ => st_row_odd u _ hd).trans hce
    rw [show 2 * (t + 1) + 2 = 2 * t + 2 + 1 + 1 by ring, st_stP_succ, st_stP_succ, r1, r2]
    nlinarith

theorem st_tri_odd (u v w : ℕ) (hw : w % 2 = 1) :
    bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w)) = bnat (stEdge u v) := by
  rw [st_se_odd v w hw, st_se_odd u w hw]
  simp

theorem st_tri_even (u v w : ℕ) (hw : w % 2 = 0) :
    bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w)) =
      bnat (xor (xor (stEdge u v) (decide (v % 2 = 1))) (decide (u % 2 = 1))) := by
  rw [st_se_even v w hw, st_se_even u w hw]

/-- **The triangle count.** `6 · #{broken triangles} = t(t+1)(2t+1)`: adding the two newest
positions breaks `(t+1)²` new triangles. -/
theorem st_tri (t : ℕ) : 6 * stT (2 * t + 1) = t * (t + 1) * (2 * t + 1) := by
  induction t with
  | zero => simp [stT]
  | succ t ih =>
    have ha : (2 * t + 1) % 2 = 1 := by omega
    have hb : (2 * t + 1 + 1) % 2 = 0 := by omega
    have r1 : ∑ v ∈ range (2 * t + 1), ∑ u ∈ range v,
        bnat (xor (xor (stEdge u v) (stEdge v (2 * t + 1))) (stEdge u (2 * t + 1))) = stE (2 * t + 1) := by
      unfold stE
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
        st_tri_odd u v _ ha
    have r2 : ∑ v ∈ range (2 * t + 1 + 1), ∑ u ∈ range v,
        bnat (xor (xor (stEdge u v) (stEdge v (2 * t + 1 + 1))) (stEdge u (2 * t + 1 + 1))) =
          stP (2 * t + 1 + 1) := by
      unfold stP
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
        st_tri_even u v _ hb
    have hE := st_edges t
    have hP := st_P t
    rw [show 2 * t + 2 = 2 * t + 1 + 1 by ring] at hP
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, st_stT_succ, st_stT_succ, r1, r2]
    nlinarith

/-! ## The staircase cochain: gauge distance and defect -/

/-- The sign pattern of a gauge, on positions. -/
def sgnPat {n : ℕ} (β : Fin n → S3) (i : ℕ) : Bool :=
  if h : i < n then oddPerm (β ⟨i, h⟩) else false

theorem sig_val {n : ℕ} (β : Fin n → S3) (u : Fin n) : sgnPat β u.val = oddPerm (β u) := by
  unfold sgnPat
  rw [dif_pos u.isLt]
  all_goals rfl

/-- **Parity retraction.** A `Sym(3)` gauge of the staircase costs at least twice the `F₂` count
of its sign pattern. -/
theorem stair_cost_ge (n : ℕ) (β : Fin n → S3) : 2 * cutF (sgnPat β) n ≤ cost (stair n) β := by
  calc 2 * cutF (sgnPat β) n = ∑ v ∈ range n, ∑ u ∈ range v, 2 * gx (sgnPat β) u v := by
        simp only [cutF, Finset.mul_sum]
    _ = ∑ u : Fin n, ∑ v : Fin n, (if u < v then 2 * gx (sgnPat β) u.val v.val else 0) :=
        (st_fin_pair n (fun a b => 2 * gx (sgnPat β) a b)).symm
    _ ≤ ∑ u : Fin n, ∑ v : Fin n,
          (if u < v then moved ((β u)⁻¹ * stair n u v * β v) else 0) := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        by_cases huv : u < v
        · rw [if_pos huv, if_pos huv]
          unfold gx
          rw [sig_val, sig_val]
          exact st_par_bound (β u) (β v) (stEdge u.val v.val)
        · simp [huv]
    _ = cost (stair n) β := (cost_eq _ _).symm

/-- The identity gauge costs twice the number of staircase edges. -/
theorem stair_cost_one (n : ℕ) : cost (stair n) (fun _ => 1) = 2 * stE n := by
  calc cost (stair n) (fun _ => 1) = ∑ u : Fin n, ∑ v : Fin n,
        (if u < v then moved ((1 : S3)⁻¹ * stair n u v * 1) else 0) := cost_eq _ _
    _ = ∑ u : Fin n, ∑ v : Fin n, (if u < v then 2 * bnat (stEdge u.val v.val) else 0) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        by_cases huv : u < v
        · rw [if_pos huv, if_pos huv]
          exact st_moved_one (stEdge u.val v.val)
        · simp [huv]
    _ = ∑ v ∈ range n, ∑ u ∈ range v, 2 * bnat (stEdge u v) :=
        st_fin_pair n (fun a b => 2 * bnat (stEdge a b))
    _ = 2 * stE n := by simp only [stE, Finset.mul_sum]

/-- Every gauge of the staircase on `K_{2t+1}` costs at least `t(t+1)`. -/
theorem stair_cost_lower (t : ℕ) (β : Fin (2 * t + 1) → S3) :
    t * (t + 1) ≤ cost (stair (2 * t + 1)) β :=
  (st_cutF_ge t (sgnPat β)).trans (stair_cost_ge _ β)

theorem stair_cost_id (t : ℕ) : cost (stair (2 * t + 1)) (fun _ => 1) = t * (t + 1) := by
  rw [stair_cost_one]
  exact st_edges t

/-- **The gauge distance of the staircase** on `K_{2t+1}` is exactly `t(t+1)`: leaving the
cochain alone is optimal. -/
theorem stair_gaugeDist (t : ℕ) : gaugeDist (stair (2 * t + 1)) = t * (t + 1) :=
  gaugeDist_eq_of (stair_cost_lower t) _ (stair_cost_id t)

theorem stair_tri_term (n : ℕ) (u v w : Fin n) :
    (if u < v ∧ v < w then
      moved (val (stair n) u v * val (stair n) v w * val (stair n) w u) else 0) =
      if u < v ∧ v < w then
        2 * bnat (xor (xor (stEdge u.val v.val) (stEdge v.val w.val)) (stEdge u.val w.val)) else 0 := by
  by_cases h : u < v ∧ v < w
  · rw [if_pos h, if_pos h]
    have huw : ¬ w < u := not_lt.mpr (h.1.trans h.2).le
    unfold CoboundaryK3.val
    rw [if_pos h.1, if_pos h.2, if_neg huw]
    exact st_moved_tri (stEdge u.val v.val) (stEdge v.val w.val) (stEdge u.val w.val)
  · rw [if_neg h, if_neg h]

/-- The defect of the staircase is twice its number of broken triangles. -/
theorem stair_defect (n : ℕ) : defect (stair n) = 2 * stT n := by
  calc defect (stair n) = ∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
        (if u < v ∧ v < w then
          2 * bnat (xor (xor (stEdge u.val v.val) (stEdge v.val w.val)) (stEdge u.val w.val)) else 0) := by
        rw [defect_eq]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun w _ => stair_tri_term n u v w
    _ = ∑ w ∈ range n, ∑ v ∈ range w, ∑ u ∈ range v,
          2 * bnat (xor (xor (stEdge u v) (stEdge v w)) (stEdge u w)) :=
        st_fin_triple n (fun a b c => 2 * bnat (xor (xor (stEdge a b) (stEdge b c)) (stEdge a c)))
    _ = 2 * stT n := by simp only [stT, Finset.mul_sum]

/-- **`N/D = m/3` for the staircase.** `3N = (2t+1) · D` with `D = t(t+1)`. -/
theorem stair_defect_mul (t : ℕ) :
    3 * defect (stair (2 * t + 1)) = (2 * t + 1) * (t * (t + 1)) := by
  rw [stair_defect]
  have h := st_tri t
  nlinarith

/-- The general formula agrees with the kernel-checked witnesses' sizes (`t = 1, 2, 3`). -/
theorem stair_small : defect (stair 3) = 2 ∧ defect (stair 5) = 10 ∧ defect (stair 7) = 28 ∧
    gaugeDist (stair 5) = 6 ∧ gaugeDist (stair 7) = 12 := by
  have h1 : 3 * defect (stair 3) = 6 := stair_defect_mul 1
  have h2 : 3 * defect (stair 5) = 30 := stair_defect_mul 2
  have h3 : 3 * defect (stair 7) = 84 := stair_defect_mul 3
  exact ⟨by omega, by omega, by omega, stair_gaugeDist 2, stair_gaugeDist 3⟩

/-! ## Replication of any seed, and every `k ≥ 3` -/

/-- **Any seed replicates.** If a cochain on `K_m` has gauge distance `D > 0` (attained by the
identity gauge) and `3N = mD`, then `h₁(K_{mq}) = mq/3` for every `q ≥ 1`. -/
theorem h1_mul_of_seed {m : ℕ} (α : Fin m → Fin m → S3) (D : ℕ)
    (hlow : ∀ β, D ≤ cost α β) (hatt : cost α (fun _ => 1) = D) (hD : 0 < D)
    (hratio : 3 * defect α = m * D) (q : ℕ) (hq : 0 < q) :
    h1 (m * q) = ((m * q : ℕ) : ℝ) / 3 := by
  have hatt' : cost (rep q α) (fun _ => 1) = q ^ 2 * D := by
    have h := rep_attain q α (fun _ => 1)
    rw [hatt] at h
    exact h
  have hlow' : ∀ γ, q ^ 2 * D ≤ cost (rep q α) γ := rep_lower q hq α D hlow
  have hG : gaugeDist (rep q α) = q ^ 2 * D := gaugeDist_eq_of hlow' _ hatt'
  have hpos : 0 < gaugeDist (rep q α) := by
    rw [hG]
    exact Nat.mul_pos (pow_pos hq 2) hD
  apply le_antisymm
  · have h := h1_le_of_pos hpos
    rw [hG, rep_defect] at h
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have h3 : (3 : ℝ) * (defect α : ℝ) = (m : ℝ) * (D : ℝ) := by exact_mod_cast hratio
    have hdef : (defect α : ℝ) = (m : ℝ) * (D : ℝ) / 3 := by linarith
    calc h1 (m * q) ≤ ((q ^ 3 * defect α : ℕ) : ℝ) / ((q ^ 2 * D : ℕ) : ℝ) := h
      _ = ((m * q : ℕ) : ℝ) / 3 := by
        push_cast
        rw [hdef, div_eq_iff (mul_ne_zero (pow_ne_zero 2 hq0) hD0)]
        ring
  · exact k_div_three_le_h1 ⟨rep q α, hpos⟩

/-- **Odd seeds.** `h₁(K_{(2t+1)q}) = (2t+1)q/3` for every `t ≥ 1` and `q ≥ 1`, from Kozlov's
staircase. -/
theorem h1_stair_mul (t q : ℕ) (ht : 1 ≤ t) (hq : 0 < q) :
    h1 ((2 * t + 1) * q) = (((2 * t + 1) * q : ℕ) : ℝ) / 3 :=
  h1_mul_of_seed (stair (2 * t + 1)) (t * (t + 1)) (stair_cost_lower t) (stair_cost_id t)
    (Nat.mul_pos (by omega) (by omega)) (stair_defect_mul t) q hq

/-- Every `k ≥ 3` is `4q` or `(2t+1)q` with `t ≥ 1` and `q ≥ 1` (halve while even). -/
theorem st_decomp (n : ℕ) : ∀ k, k ≤ n → 3 ≤ k →
    ∃ m q, 0 < q ∧ k = m * q ∧ (m = 4 ∨ ∃ t, 1 ≤ t ∧ m = 2 * t + 1) := by
  induction n with
  | zero => intro k hk h3; omega
  | succ n ih =>
    intro k hk h3
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨t, ht⟩
    · by_cases hj2 : j = 2
      · exact ⟨4, 1, by norm_num, by omega, Or.inl rfl⟩
      · obtain ⟨m, q, hq, hjm, hm⟩ := ih j (by omega) (by omega)
        exact ⟨m, 2 * q, by omega, by rw [hj, hjm]; ring, hm⟩
    · exact ⟨k, 1, by norm_num, by ring, Or.inr ⟨t, by omega, ht⟩⟩

/-- **`h₁(K_k) = k/3` for every `k ≥ 3`.** Powers of two times one come from the replicated
`k = 4` witness (`h1_eq_four_mul`); everything else from a replicated staircase. -/
theorem h1_eq_all (k : ℕ) (hk : 3 ≤ k) : h1 k = (k : ℝ) / 3 := by
  obtain ⟨m, q, hq, rfl, hm⟩ := st_decomp k k le_rfl hk
  rcases hm with rfl | ⟨t, ht, rfl⟩
  · exact h1_eq_four_mul q hq
  · exact h1_stair_mul t q ht hq

/-- **Theorem 8.** `h₁(K_k) = k/3` for every `k ≥ 4`. -/
theorem h1_eq_k_div_three_ge_four (k : ℕ) (hk : 4 ≤ k) : h1 k = (k : ℝ) / 3 :=
  h1_eq_all k (by omega)

end CoboundaryK3

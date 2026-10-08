# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The lower bound `h₁(K_k, Sym) ≥ k/3` (Proposition 1, Chapman–Lubotzky's Proposition 3.2) is
  proved in the paper and not formalized for general `k`. Its equality case is checked on every
  witness here (`stars_*`): each star gauge costs exactly `D` and the star costs add up to `3N`.
* The balanced replication lemma (Lemma 6) is formalized for every cochain, every `k` and every
  `q` (`rep_defect`, `rep_attain`, `rep_lower`), and with it Corollary 7: the gauge minimum of the
  replicated seed on `K_{4q}` is exactly `6q²` and its defect `8q³`, for every `q` (`rep_seed`).
  What turns that into `h₁ = k/3` at every multiple of four is the lower bound above, which is
  cited.
* Theorem 8 at the `k` that are not multiples of four combines Kozlov's theorem for `F₂` (cited)
  and the parity retraction. The retraction step is proved here for every `k` (`retract_cost`,
  `binary_gauge_suffices`); Kozlov's theorem and the assembly into Theorem 8 are not formalized.
* The gauge minimum is over `Sym(3)`-valued gauges. Proposition 10 (cross-degree) is checked on the
  seed against comparison permutations of degree 2, 3 and 4; the baselines for degree `≥ 5`, the
  replicated seeds and the binary witnesses are argued in the paper.
* The coefficient-subgroup minima of Proposition 5 (`Sym(2)` gives 2, `ℤ/3` gives 3/2) are
  computed in the paper's scripts and not formalized.
* Section 5 beyond Theorem 13's Gram formula (torsion, cycle-type recovery, Schreier aggregates,
  entropy and its zeta expansion, graph projectors and principal angles, the fixed probe) is
  proved or computed in the paper and not formalized. The eigenvalues `2 − 2cos(2πj/ℓ)` of the
  cycle Laplacian are not formalized; only their rewriting as `4 sin²(πj/ℓ)` is.

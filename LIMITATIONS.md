# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The lower bound `h₁(K_k, Sym) ≥ k/3` is Chapman–Lubotzky's Proposition 3.2 (README, reference [2]). It is formalized
  here only for `Sym(3)`-valued cochains and gauges in the same-degree counting convention
  (`h1`, the infimum of the moved-point ratio `N/D`; `k_div_three_le_h1`), which with the
  witnesses gives `h1 k = k/3` for `k = 4, …, 8`. The general symmetric-group statement and the
  paper's cross-degree convention are not formalized; for those the bound remains cited.
* `k_div_three_le_h1` takes the existence of a non-coboundary as a hypothesis; it is supplied
  by the witnesses for `k = 4, …, 8` and by the replicated seed at every multiple of four.
* The gauge minimum is taken over `Sym(3)`-valued gauges, as in Section 1 of the paper.
* The coefficient-subgroup minima of Proposition 5 (`Sym(2)` gives 2, `ℤ/3` gives 3/2) and the
  all-cochain exhaustion at `k = 4` are not formalized.
* The balanced replication of Lemma 6 and Corollary 7 is formalized, so `h1 k = k/3` is proved
  for `k = 4, …, 8` and for every multiple of four. The rest of Theorem 8 (`h₁ = k/3` for every
  `k ≥ 4`) is not: Kozlov's binary witnesses for `k` not a power of two and the parity retraction
  that embeds them, and the cross-degree comparison of Proposition 10.
* Section 5 beyond the Gram formula of Theorem 13 is not formalized (the twisted torsion, cycle-type
  recovery, Schreier aggregates, the entropy and its deficit, graph projectors, the fixed probe).
  The eigenvalues `2 − 2cos(2πj/ℓ)` of the cycle Laplacian are cited; only their rewriting as
  `4 sin²(πj/ℓ)` is proved.

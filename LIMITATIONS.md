# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The lower bound `h₁(K_k, Sym) ≥ k/3` is Chapman–Lubotzky's Proposition 3.2 (README, reference [2]). It is formalized
  here only for `Sym(3)`-valued cochains and gauges in the same-degree counting convention
  (`h1`, the infimum of the moved-point ratio `N/D`; `k_div_three_le_h1`), which with the
  witnesses gives `h1 k = k/3` for `k = 4, …, 8`. The general symmetric-group statement and the
  paper's cross-degree convention are not formalized; for those the bound remains cited.
* `k_div_three_le_h1` takes the existence of a non-coboundary as a hypothesis; it is supplied
  by the witnesses for `k = 4, …, 8` and not proved for other `k`.
* The gauge minimum is taken over `Sym(3)`-valued gauges, as in the paper's Appendix B.
* The coefficient-subgroup minima of Proposition 4 (`Sym(2)` gives 2, `ℤ/3` gives 3/2), the
  all-cochain exhaustion at `k = 4`, and Conjecture 5 are not formalized.
* Section 5.1 (twisted torsion) and Corollary 9 and Remark 10 (spectral determination, the
  entropy integral) are not formalized. Theorem 8's Gram formula is proved; the eigenvalues
  `2 − 2cos(2πj/ℓ)` of the cycle Laplacian are cited, and only their rewriting as
  `4 sin²(πj/ℓ)` is proved.

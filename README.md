<div align="center">

# The Permutation Coboundary Constant of the Complete Complex Is k/3 — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/coboundary-k3-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/coboundary-k3-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-48-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22090958-blue)](https://doi.org/10.5281/zenodo.22090958)

Jeromie Beasley

</div>

---

## The idea in one line

Chapman and Lubotzky prove `h₁(K_k, Sym) ≥ k/3`. The paper shows the bound is the truth for
**every** `k ≥ 4`, attained by `Sym(3)` cochains: an explicit witness at `k = 4, …, 8`, a balanced
replication of the `k = 4` seed at every multiple of four, and Kozlov's binary witnesses with a
parity retraction everywhere else. At `k = 4` the bound needs the non-abelian group: `F₂` gives 2,
`ℤ/3` gives 3/2, and only `Sym(3)` reaches 4/3.

## What is proved

[`CoboundaryK3/Basic.lean`](CoboundaryK3/Basic.lean): the five computed witnesses.

| Paper (v7) | Result | Theorem |
| :--- | :--- | :--- |
| Theorem 4, `k = 4` | Witness: defect `N = 8`; every gauge costs `≥ 6`; `6` attained; `N/D = 4/3` | `witness_k4` |
| Theorem 4, `k = 5` | `N = 10`, `D = 6`, `N/D = 5/3` | `witness_k5` |
| Theorem 4, `k = 6` | `N = 36`, `D = 18`, `N/D = 2` | `witness_k6` |
| Theorem 4, `k = 7` | `N = 28`, `D = 12`, `N/D = 7/3` | `witness_k7` |
| Theorem 4, `k = 8` | `N = 72`, `D = 27`, `N/D = 8/3`; the residual has twelve transpositions and one 3-cycle | `witness_k8` |
| Sec. 3 | Exhausting gauges with `β(0) = 1` loses nothing: a constant right factor conjugates every edge term, and the Hamming count is conjugation-invariant | `moved_conj`, `cost_mul_const`, `gauge_lower`, `gauge_lower'`, `gauge_lower_bb` |
| Sec. 3 | The branch-and-bound search used for `k = 6, 7, 8` is sound: once the cost of the assigned edges reaches `D`, every completion does | `pcost_mono`, `search_sound`, `search_step`, `search_split`, `pcost_ofFn` |
| Prop. 5 | Around the `k = 4` witness triangle the three distinct transpositions compose to a transposition, while each adjacent product is a 3-cycle | `k4_mechanism` |
| Theorem 13 | `⟨e_{πi}−e_i, e_{πj}−e_j⟩ = 2[i=j] − [πi=j] − [πj=i]`, the entries of `2I − A`, the Laplacian of the cycle graph; and `2 − 2cos 2x = 4 sin² x` | `delta_prod`, `disp_gram`, `cycle_laplacian_eigen` |

[`CoboundaryK3/AllK.lean`](CoboundaryK3/AllK.lean): the steps of the all-`k` proof that a kernel
can check.

| Paper (v7) | Result | Theorem |
| :--- | :--- | :--- |
| Theorem 8 | The parity retraction `r(g) = t^parity(g)` is the sign map read in `{1, t}`; it is a homomorphism, commutes with inverses, fixes `{1, t}` and never moves more points | `retr_eq_sign`, `retr_mul`, `retr_inv`, `retr_mem`, `retr_fix`, `retr_moved` |
| Theorem 8 | **For every `k`:** retracting any `Sym(3)` gauge of a binary cochain into `{1, t}` never raises the cost, so gauges outside `{1, t}` do no better | `retract_cost`, `binary_gauge_suffices` |
| Corollary 2 | The equality case of the star bound on every witness: each of the `k` star gauges costs exactly `D`, and the star costs add up to `3N` | `stars_k4`, `stars_k5`, `stars_k6`, `stars_k7`, `stars_k8`, `stars_r8` |
| Corollary 7 | The replicated seed on `K₈` (`q = 2`): `N = 64 = 8q³`, every one of the `6⁷` root-fixed gauges costs `≥ 24 = 6q²`, `24` attained, `N/D = 8/3` | `witness_r8` |
| Proposition 10 | The cross-degree convention on the seed: against comparison permutations of degree 2, 3 and 4 the cheapest repair is `10/3`, `2` and `3` (scaled: 10, 6, 12), each attained; fixing `β(0) = 1` loses nothing | `cross_degree_seed`, `cross_m4_lower`, `errCost_mul_left`, `err_lower`, `allL_sound`, `mem_perms2`, `mem_perms3`, `mem_perms4` |

The exhaustions run in the Lean kernel (`decide +kernel`), not in compiled code: no
`native_decide`, and the axiom audit still passes. Large searches are split into kernel-checked
pieces (216 for each `K₈` witness, 24 for the degree-4 comparison) and assembled by proved
lemmas. What is not proved is in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay of every module in Lean's kernel checker, an axiom audit of
every named theorem (only `propext`, `Classical.choice`, `Quot.sound`), and four deliberately
false statements that must fail for a mathematical reason.

## The paper, its scripts, and the mixer

* [`paper/permutation-coboundary-k3-v7.pdf`](paper/permutation-coboundary-k3-v7.pdf): version 7,
  8 October 2026, with its LaTeX source and figures.
* [`paper/scripts/`](paper/scripts): every computation in the paper as a runnable script, with
  the output of its last run, including an independent adversarial re-check
  (`K3-V7-ADVERSARIAL`).
* [`mixer/k3_mixer.html`](mixer/k3_mixer.html): an interactive page with one live eye per
  result; every number on it is computed in the page. Download and open it in a browser.

DOI [10.5281/zenodo.22090958](https://doi.org/10.5281/zenodo.22090958) always opens the newest
version deposited on Zenodo.

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).

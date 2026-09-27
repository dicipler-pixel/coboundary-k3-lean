<div align="center">

# The Permutation Coboundary Constant of the Complete Complex Is k/3 for 4 ≤ k ≤ 8 — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/coboundary-k3-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/coboundary-k3-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-25-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22090958-blue)](https://doi.org/10.5281/zenodo.22090958)

Jeromie Beasley

</div>

---

## The idea in one line

Chapman and Lubotzky prove `h₁(K_k, Sym) ≥ k/3`. The paper shows the bound is attained for
`k = 4, …, 8` by explicit `Sym(3)` cochains. Each witness gives an equality only if its gauge
minimum is the true minimum over every gauge. Lean now checks that exhaustively, so each
`N/D = k/3` is a kernel-checked fact rather than a program's output.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Theorem 3, `k = 4` | Witness: defect `N = 8`; every gauge costs `≥ 6`; `6` attained; `N/D = 4/3` | `witness_k4` |
| Theorem 3, `k = 5` | `N = 10`, `D = 6`, `N/D = 5/3` | `witness_k5` |
| Theorem 3, `k = 6` | `N = 36`, `D = 18`, `N/D = 2` | `witness_k6` |
| Theorem 3, `k = 7` | `N = 28`, `D = 12`, `N/D = 7/3` | `witness_k7` |
| Theorem 3, `k = 8` | `N = 72`, `D = 27`, `N/D = 8/3`; the residual has twelve transpositions and one 3-cycle | `witness_k8` |
| Sec. 3.1 | Exhausting gauges with `β(0) = 1` loses nothing: a constant right factor conjugates every edge term, and the Hamming count is conjugation-invariant | `moved_conj`, `cost_mul_const`, `gauge_lower`, `gauge_lower'`, `gauge_lower_bb` |
| Sec. 3.1 | The branch-and-bound search used for `k = 6, 7, 8` is sound: once the cost of the assigned edges reaches `D`, every completion does | `pcost_mono`, `search_sound`, `search_step`, `search_split`, `pcost_ofFn` |
| Prop. 4 | Three distinct transpositions around a triangle compose to a transposition, while each adjacent product is a 3-cycle | `k4_mechanism` |
| Theorem 8 | `⟨e_{πi}−e_i, e_{πj}−e_j⟩ = 2[i=j] − [πi=j] − [πj=i]`: the displacement Gram is half the cycle-graph Laplacian; its eigenvalues `2 − 2cos 2x = 4 sin² x` | `delta_prod`, `disp_gram`, `cycle_laplacian_eigen` |

The file is [`CoboundaryK3/Basic.lean`](CoboundaryK3/Basic.lean). The exhaustions run in the
Lean kernel (`decide +kernel`), not in compiled code: no `native_decide`, and the axiom audit
still passes. For `k = 7` and `k = 8` the search is split by the gauge on the first vertices
(36 and 216 kernel-checked pieces), and the pieces are assembled by `search_split`. The full
check takes about twenty minutes. What is not proved is in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*The Permutation Coboundary Constant of the Complete Complex Is k/3 for 4 ≤ k ≤ 8*, Jeromie Beasley. DOI
[10.5281/zenodo.22090958](https://doi.org/10.5281/zenodo.22090958) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).

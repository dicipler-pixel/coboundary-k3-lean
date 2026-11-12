# Scratch branch: Tau Ceti piece-one build (not for merge)

Compile check for the first piece of the split of TauCetiProject/TauCeti PR 29489, built on
GitHub's runners against TauCeti main pinned at `5b875ab`.

- `A-as-pushed/`: `Defs.lean`, `Cochain.lean` and `TwoComplex/Basic.lean` exactly as pushed at
  `0f40385`.
- `B-with-gauge/`: the same three files plus `Gauge.lean`, Claude's draft of the two items of
  roadmap Layer 2.2 the pushed files lack (`Cochain.IsCoboundary` and the gauge action with
  its identity and composition laws).

Nothing here is pushed to Tau Ceti.

## Second round (after the split was pushed to the PR at `10d8fce`)

Built against TauCeti main pinned at `396c3bd`.

- `T-theirs-10d8fce/`: the three files exactly as pushed to PR 29489 at `10d8fce`.
- `C-review-fixes/`: Claude's version of the same piece with the four changes the 12 November
  review asked for (no `@[expose]`, `@[ext]` on `ext_edges`, the two unused imports replaced).
- `D-review-fixes-gauge/`: `C` plus `Gauge.lean`.

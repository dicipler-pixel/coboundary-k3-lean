# Scratch branch: Tau Ceti piece-one build (not for merge)

Compile check for the first piece of the split of TauCetiProject/TauCeti PR 29489, built on
GitHub's runners against TauCeti main pinned at `5b875ab`.

- `A-as-pushed/`: `Defs.lean`, `Cochain.lean` and `TwoComplex/Basic.lean` exactly as pushed at
  `0f40385`.
- `B-with-gauge/`: the same three files plus `Gauge.lean`, Claude's draft of the two items of
  roadmap Layer 2.2 the pushed files lack (`Cochain.IsCoboundary` and the gauge action with
  its identity and composition laws).

Nothing here is pushed to Tau Ceti.

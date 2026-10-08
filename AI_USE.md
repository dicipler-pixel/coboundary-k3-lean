# AI use

The research questions and the physics behind this library are Jeromie
Beasley's. AI tools (Claude, ChatGPT and Grok) were used to search the literature,
write and repair Lean proofs, and organise this repository. Grok drafted the structure of
`CoboundaryK3/Replication.lean`; Claude completed its counting lemmas and compiled it.

No statement here rests on an AI's say-so. Every proof is checked by the Lean
kernel and replayed by an independent kernel checker on every push, every
theorem's axioms are audited, and every false control must be rejected for the
check to pass. What the statements mean, and what they do not claim, is set
out in plain words in `README.md` and `LIMITATIONS.md`.

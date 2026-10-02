# Low-error NLQC lower bounds - companion to "Perfect non-local quantum computation is impossible"

This repository contains files to accompany the recent preprint [Perfect non-local quantum computation is impossible](https://arxiv.org/abs/2609.40228) by Marten Folkertsma, Dmitry Grinko, Gina Muuss, and Florian Speelman.

The [companion notes](companion-notes.pdf) file presents robust extensions to the (exact) results of the paper. The extensions were the result of human questions and human selection, but the proofs and presentation are (currently still) AI generated.

The [Lean folder](Lean/) contains formal proofs of the exact impossibility and finite-orbit results, the main robust resource bounds, and the diagonal-gate application. It includes build instructions and uses Lean and Mathlib v4.34.1.

The [coverage guide](docs/robust-companion-lean.md) describes the proved statements, models and constants. The main bounds include standard-Borel classical outcomes and measurable shared randomness, and their geometric input is proved in the library. Only the effective bound for the named controlled-phase gate in Appendix C retains two explicit arithmetic hypotheses.

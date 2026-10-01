# Low-error NLQC lower bounds - companion to "Perfect non-local quantum computation is impossible"

This repository contains files to accompany the recent preprint [Perfect non-local quantum computation is impossible](https://arxiv.org/abs/2609.40228) by Marten Folkertsma, Dmitry Grinko, Gina Muuss, and Florian Speelman.

The [companion notes](companion-notes.pdf) file presents robust extensions to the (exact) results of the paper. The extensions were the result of human questions and human selection, but the proofs and presentation are (currently still) AI generated.

A formalization of many of the results can be found in the [Lean folder](Lean/), we intend to update this formalization in the coming days to cover more of the paper's (and companion notes') results.

The [coverage guide](docs/robust-companion-lean.md) describes the proved statements and remaining assumptions. The supplied formalization includes the exact controlled-phase example with identity spectators, algebraicity of local-unitary invariants, and robust bounds for standard-Borel outcomes and shared randomness. Quantitative bounds retain three explicit geometry hypotheses.

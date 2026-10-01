# NLQC Lean

Lean 4 proofs of resource bounds for one-round nonlocal quantum computation,
for unitary operations and two-sided ordered rank-one projective measurements.
The models allow arbitrary finite original registers and pure or common-map
finite-mixed shared resources. The charged footprint counts resource Schmidt
rank and both communicated messages.

This library uses Lean/Mathlib v4.33.1 and formalizes results from the
exact paper and its robust companion. The
[source-to-theorem map](docs/PUBLIC_RESULTS.md) lists the covered statements
and their restrictions.

| Result | Assumptions |
|---|---|
| Almost-every exact impossibility, fixed-target qualitative gaps, compact score optima and spectral footprint floors, for both models | Unconditional |
| Full-group Haar estimates and universal and almost-every precision bounds, for both models | Three explicit geometry premises |
| Universal unitary precision bound K≥c d²√ln(1/ε), and the corresponding 2n qubit term | Three explicit geometry premises |
| Strong unitary Haar estimate on a neighborhood of SWAP | Three explicit geometry premises |
| Finite classical score compression and finite pure/common-map mixed precision and phase bounds | Compression unconditional; quantitative rates use the three geometry premises |
| Pure/common-map mixed standard-Borel CP/TP and rank-sized score compression | Unconditional; charged score reachability at 4d⁴Kq⁵; full shared-randomness transfers remain open |
| Direct finite classical spectral floors | Unconditional; SWAP d²(1−ε) and Bell PVM d(1−ε), quantum messages and resource rank only |
| Universal unitary max and regional near-SWAP AE bounds | Exactly three geometry premises; regional threshold precedes every budget and original register |

The three premises are `LRTTheorem44`,
`SemialgebraicSmoothStratificationTheorem`, and
`SemialgebraicComponentBoundTheorem`, described with source citations in
[Mathematical assumptions](docs/ASSUMPTIONS.md). Semialgebraic projection
closure is proved from the vendored Sundog quantifier-elimination slice.
The almost-every exact conclusions use vector Sard without geometry premises.

Unitary errors use normalized Choi score or diamond error; measurement errors
use projective score or worst-case joint total variation. Haar estimates use
outer measure where reachability measurability is unavailable. Almost-every
thresholds depend on the fixed target. Finite score selection preserves the
selected score, and operational accuracy enters the resulting bounds through
an error-to-score inequality.

Import [NLQCLean.Results.Unitary](NLQCLean/Results/Unitary.lean) or
[NLQCLean.Results.PVM](NLQCLean/Results/PVM.lean) for the public APIs.
`import NLQCLean` imports the complete library. The code follows the
mathematical dependencies through Models, LinearAlgebra, Rigidity, Approx,
Invariants, Geometry, Semialgebraic, Arithmetic and Bounds.

On a Linux workstation with [Elan](https://github.com/leanprover/elan)
installed, run the following from the directory containing `lakefile.toml`
and `lean-toolchain` (the Lean subfolder if this library is part of a larger
repository). Use the supplied dependency manifest:

```bash
lake exe cache get
lake build NLQCLean.All NLQCTests
```

The [example Linux CI workflow](.github/workflows/lean.yml) uses these same
targets. When placing the library in a subfolder, configure the workflow in
the hosting repository to run from that folder. Do not update the pinned
dependencies to
reproduce the checked results. Vendor licenses and port provenance are in
[Tau Ceti](NLQCLean/Vendor/TauCeti/README.md) and
[Sundog](NLQCLean/Vendor/Sundog/README.md).

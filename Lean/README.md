# NLQC Lean

Lean 4 proofs of resource bounds for one-round nonlocal quantum computation,
for unitary operations and two-sided ordered rank-one projective measurements.
The models allow arbitrary finite original registers and pure or common-map
finite-mixed shared resources. The charged footprint counts resource Schmidt
rank and both communicated messages.

This library uses Lean/Mathlib v4.34.1 and formalizes results from the
exact paper and its robust companion. The
[source-to-theorem map](docs/PUBLIC_RESULTS.md) lists the covered statements
and their restrictions.

| Result | Assumptions |
|---|---|
| Rational polynomial local-unitary orbit invariants at exactly implemented targets | Unconditional algebraicity for arbitrary finite pure/common-map mixed architectures |
| Named first-qubit controlled phase for every positive qubit count, every nonzero algebraic angle and full local-unitary orbits | Unconditional exact exclusion for arbitrary finite pure/common-map mixed architectures |
| Almost-every exact impossibility, fixed-target qualitative gaps, compact score optima and spectral footprint floors, for both models | Unconditional |
| Full-group Haar estimates and universal and almost-every precision bounds, for both models | Unconditional |
| Universal unitary precision bound K≥c d²√ln(1/ε), and the corresponding 2n qubit term | Unconditional |
| Strong unitary Haar estimate on a neighborhood of SWAP | Unconditional |
| Finite classical score compression and finite pure/common-map mixed precision and phase bounds | Unconditional |
| Pure/common-map mixed standard-Borel CP/TP and rank-sized score compression | Unconditional; charged score reachability at d⁴Kq⁵; measurable shared randomness and branch-dependent finite systems are covered |
| Direct finite classical spectral floors | Unconditional; SWAP d²(1−ε) and Bell PVM d(1−ε), quantum messages and resource rank only |
| Universal unitary max and regional near-SWAP AE bounds | Unconditional; regional threshold precedes every budget and original register |
| Universal measurement precision near Bell bases, including the 2n charged and −2n/5 free-classical dimension terms | Unconditional |
| Finite-orbit structure for exact unitary and projective-measurement targets | Unconditional |
| Rectangular diagonal-gate bounds, standard-Borel localization and shared-randomness extensions | Unconditional |
| Effective bound for the named controlled-phase gate (Appendix C) | One explicit premise (one-block quantifier elimination) for the stated rate at every nonzero algebraic angle; the polynomial-type transcendence measure for `e^{iθ}` is proved by Gelfond's method. For `C₁`, quantifier elimination alone also gives the stated double-exponential rate and the free-classical `exp(-exp(C R⁴ Kq²))` / `Kq⁶` refinement, and no input gives `exp(-exp(exp(175 K²)))` |

The quantitative bounds rest on the polynomial image-volume bound
(`DirectVolume.polynomialImageVolumeBound`), proved by a Lagrange-maximum
argument with Sard's theorem and an elementary point count. For the library's fixed format budget, the explicit image-volume base is 35248 (`polynomialImageVolumeBoundWith_imageVolumeConstant`, a barrier-function proof); the direct proof, which covers every format budget, gives 450240. The premise of the effective controlled-phase bound is described with
source citations in [Mathematical assumptions](docs/ASSUMPTIONS.md).
Semialgebraic projection closure is proved from the vendored Sundog
quantifier-elimination slice.

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

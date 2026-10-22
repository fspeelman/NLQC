# NLQC Lean

Lean 4 proofs of resource bounds for one-round nonlocal quantum computation,
for unitary operations and two-sided ordered rank-one projective measurements.
The models allow arbitrary finite original registers and pure or common-map
finite-mixed shared resources. The charged footprint counts resource Schmidt
rank and both communicated messages.

This library uses Lean/Mathlib v4.35.0 and formalizes results from the
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
| Effective bound for the named controlled-phase gate (Appendix C) | Unconditional at the stated rate `exp(-exp(C K²))` for every nonzero algebraic angle: the epigraph eliminant is proved by a deformed critical-point argument and the polynomial-type transcendence measure for `e^{iθ}` by Gelfond's method. With free classical messages the general bound is `exp(-exp(C Kq¹⁰))`. For `C₁` the constant is explicit, `g_K(1) ≥ exp(-exp(9400 K²))`, and the free-classical `exp(-exp(C R⁴ Kq²))` / `Kq⁶` / LOSCC refinements are unconditional too; their sixth-power extension to other angles is not formalized |

The quantitative bounds rest on the polynomial image-volume bound
(`DirectVolume.polynomialImageVolumeBound`), proved by a Lagrange-maximum
argument with Sard's theorem and an elementary point count. For the library's fixed format budget, the explicit image-volume base is 35248 (`polynomialImageVolumeBoundWith_imageVolumeConstant`, a barrier-function proof); the direct proof, which covers every format budget, gives 450240. How the effective controlled-phase bound became unconditional, and the
former external premises with their source citations, are described in
[Mathematical assumptions](docs/ASSUMPTIONS.md).
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
`import NLQCLean` imports the complete library. Every file uses the Lean module
system, so the library can be imported from module and non-module files alike;
all declarations are public and definitions keep their bodies visible. The code follows the
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
reproduce the checked results.

## License

The Lean sources (`NLQCLean/`, `NLQCTests/` and the root Lean and Lake files),
this README and the documentation in `docs/PUBLIC_RESULTS.md` and
`docs/ASSUMPTIONS.md` are licensed under the
[Apache License, Version 2.0](LICENSE).

Code vendored under `NLQCLean/Vendor/` keeps its upstream license and
notices; each directory has its own `LICENSE` and a README with provenance
and modification notes:
[Tau Ceti](NLQCLean/Vendor/TauCeti/README.md),
[Sundog](NLQCLean/Vendor/Sundog/README.md) and
[Hermite–Lindemann](NLQCLean/Vendor/HermiteLindemann/README.md)
(all Apache-2.0). Mathlib and the other Lake dependencies are fetched
separately under their own licenses. Material outside these files, such as
reference documents and manuscript sources, is not covered by this license.

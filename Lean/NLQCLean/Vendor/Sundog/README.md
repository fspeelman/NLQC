# Sundog quantifier-elimination slice

These Lean files are derived from
[sundogcert](https://github.com/humiliati/sundogcert/tree/c5c8d2b21cc118a2f1be1138b9800a991b57e084)
at immutable commit `c5c8d2b21cc118a2f1be1138b9800a991b57e084`.
The 25 modules `CircuitNet.lean` through `DiagramAssembly.lean` are the upstream import
closure of the one-variable sign-vector elimination `Sundog.TarskiQE.elim_signVector`.
`SemialgebraicProjection.lean` extracts two declarations from the upstream
`Sundogcert/SemialgebraicStructure.lean`: the sign characterization
`Sundog.TarskiQE.sadef_sign_char` and the projection theorem `Sundog.TarskiQE.sadef_proj`.

`Sundog.TarskiQE.SADef n` is the inductive Boolean closure (complement and union) of the
sets `{g : Fin n → ℝ | 0 < MvPolynomial.eval g f}` for arbitrary real polynomials `f`.
`sadef_proj` proves, without any quantifier-elimination premise, that eliminating the last
coordinate (`Fin.snoc g y`) preserves `SADef`. This vendored slice does not by itself prove the
project proposition `SemialgebraicProjectionTheorem`; that needs a separate proved equivalence
between `SADef` and the project's finite polynomial-sign descriptions.

## License and provenance

The copied material is licensed under the Apache License, Version 2.0. The upstream
`LICENSE` is reproduced verbatim in [LICENSE](LICENSE); its appendix carries the upstream
copyright notice, which is preserved there unchanged. The upstream source files have no
per-file copyright or author headers. The root of the upstream Git tree at this commit
contains no `NOTICE` file.

Each vendored file begins with a short notice identifying the upstream repository, commit
and license and stating that it was modified for NLQCLean (Apache-2.0 section 4(b)).
The upstream module comments, docstrings and proofs are otherwise retained.

Upstream files used, relative to the upstream repository root, with their Git blob SHA-1
(the upstream Git object hash)
and the SHA-256 of the unmodified bytes:

| Upstream file (`Sundogcert/`) | Lines | Git blob SHA-1 | SHA-256 |
|---|---:|---|---|
| `CircuitNet.lean` | 583 | `e11c7ee72979f9eda2c963721fde7fe82f1daff9` | `0146cc0e08e47e70f1d2add87d3999895247f20f6b56ee2331e29213b1ab04fc` |
| `PieceCover.lean` | 182 | `70ab834e1a56abd1281f8028ee77eed70d0ef949` | `9b543bf864e6b0b4e75e77d0bedd5a8a21fc0db526dae295243424efb9d6ff0b` |
| `RegionCount.lean` | 130 | `180b2f9ef63d2613a331bd5f3289c5a10e434b7f` | `985f6f790caf143dfa5080072f9b3bf28b451f2e992d0021c2aa53637f39c010` |
| `CancellationFree.lean` | 216 | `1dd3a8efd283e29f4acfd54643beef2699832924` | `e276addef0887d478fb600028609e6a7fc28eccd7355368b7508f0ce9906e6b3` |
| `RegionPoly.lean` | 657 | `fd56efaf4476a6a5a9c3d20bfe634219c793d375` | `36a50a043b5ba9242be0e7b66388c9b68acc764ae7389b6d2da829c67cef95d3` |
| `ExactRepr.lean` | 521 | `d10201cf796baecc2044422ae5f165f2f0a2fccd` | `7ab93db7203d12875700a95e9b2e9ae1193269ff825873e67eda5162752e8dab` |
| `AnalyticGate.lean` | 168 | `439fe8d6ce0b410204cabcef8c35896549385d7a` | `b1aa597bf0b6d65ef9f13182b0c8ba23675939a31f7c8c99ab9be3419949e571` |
| `DefinableRate.lean` | 87 | `a285d869c92323cc6ea8bc76e22615a3dcdb3d87` | `4be5c7a899956407dddd64f8c983d91034b5f1fc8745f642ca5984db9bc78b1f` |
| `OMinimalOne.lean` | 284 | `19a4a1ecd22113f06ce6efbb2c00e779f2b757c8` | `d87f5a2b90de30f0face4fa6f2d1023906fb19bbcaf88e6767231f514c1b4b4b` |
| `PolySignPartition.lean` | 117 | `2c64c256d069ed4e3bbb316b397bae4dcd51d9d9` | `da6c27031c394ac471702c96537aabf7c44b583414a4359ccb9b4146fc009755` |
| `PolyBranchTrees.lean` | 273 | `348dc98eb24bf2eeb88c52a3d5c326abd2dd65a0` | `f301454c833a4cc1f234df0e16c5b9dbc2120bf5708cbae982f4e7098c463da1` |
| `PseudoRemainder.lean` | 278 | `86c155ef10e64f2e3f989bf30225f1b03a19ef0c` | `058fcce953ec0f8d092ccd639e1093a00ced95987a6cd0c7182894a87f941183` |
| `PolyDerivZones.lean` | 224 | `f9f9482ef1458872facf66ac1ff1965db712a7d4` | `23d9b6ae31092fc513b0cfa5ac7de6c61c4d33e248c39bc84cda6a5309d9385c` |
| `SignDiagrams.lean` | 522 | `832d1aa0ac8ba2246afb2d5692d487793f5bcbdc` | `2027fbbec809c5b2b72d8d77049ba0638cd8bd1b31ccc2db14b281c3fc156b42` |
| `DiagramNormalize.lean` | 412 | `a12a642cf6436df26cc050a444579737f1e1042b` | `faeecc908078258206103f994cc9b9f59d226ce1c733fe216fe02d24d56a5449` |
| `DiagramAugment.lean` | 138 | `0fe9958e2a93fd3e66389173f5c8b748ba4164b1` | `2fd8e281938063fc1d48e052f55820981bb1fd8ee4c2c22e81e1105b5b63483c` |
| `DiagramGraft.lean` | 355 | `2cd2db1713086f3853995136af1eb2a90ee58926` | `bf4905bcafef96f066fd8dc15ec428db1b12c19d96ce1f1e0e8478698f5ad6db` |
| `DiagramWalk.lean` | 310 | `ab269cce12ca39d6fd8f0ccab3b9a1b25b7dfceb` | `54db194ce69139168206999d6d82d75c88a3fa4dc2829f063ff1900fa549db76` |
| `DiagramAnnotate.lean` | 586 | `09ac5fba3a144b6568ce345d04bbac3775b3ea72` | `0c7fd0931e1c47a3451a379985c2b6f1aa73ae5b4d69165ac9f8d7d4345cc6c3` |
| `DiagramDescent.lean` | 299 | `33dea10763939706fe9e44e7461d430f3a8bb41f` | `eb963c48f3d0702e21fca8289a256370cab811169a49fc940eae8ce66b5ac782` |
| `DiagramReads.lean` | 203 | `a7609db31bc7f0f4b4b279577e2b3312bd6fd799` | `67b9e6c4bf9b0989ebc16c0e5450dae8bf8068253b5af8bbf3510f6540efa704` |
| `DiagramMaster.lean` | 515 | `d0f198283047fc3b37695684c448cc73513dffc8` | `39be03c958c110c286f9266c7cd0191d63c88bfcf1835fcaefad164ed08331dd` |
| `DiagramSelect.lean` | 135 | `c32e1f1e365726c5e7b8d4b95bb1ff507eebb695` | `b7ff1f699833743d8eb67d1c7309bae60906edb06296b6981d5536982f9336c8` |
| `DiagramBranches.lean` | 277 | `915f271108c4d2eea7c4ceb8f4c81b1101f64885` | `b12b5131f0a75f1a31aecead6ded234b3f0707b8a88d1393deb064cd66451eed` |
| `DiagramAssembly.lean` | 375 | `6ed6885937679ac92a07ff9ad7374d802d53f5d8` | `17618b476fa6a82e21b3e8ecbb0764efc9c1733caf27d609eec6c0aa77432885` |
| `SemialgebraicStructure.lean` (extract only) | 304 | `c12b08d074bf25bda6bc841d66fe4ef25cf68a3b` | `5724d3ca4e904c011a5c17eec8e44c2925db0cbf7ddddc2d17eb31ff33aaa383` |

The repository-root `LICENSE` has Git blob SHA-1 `ce20e42e01ffbb22abd6540b69d95e5aa13681b2`
and SHA-256 `a3f6974544a969e429e2df9aa5e72e95df50f8a3e9ef168f533bdc778ae008f8`;
the copy here is byte-identical.

Each module `Sundogcert/X.lean` is vendored as `NLQCLean/Vendor/Sundog/X.lean`, so the Lean
module `Sundogcert.X` becomes `NLQCLean.Vendor.Sundog.X`. The extract is
`NLQCLean.Vendor.Sundog.SemialgebraicProjection`. The 25 modules total 7,847 upstream lines
(`wc -l`, as in the table).
The Lean declaration namespaces (`Sundog.CircuitNet`, `Sundog.PieceCover`, `Sundog.RegionCount`,
`Sundog.CancellationFree`, `Sundog.RegionPoly`, `Sundog.ExactRepr`, `Sundog.OMinimalOne`,
`Sundog.TarskiQE`, and the others used upstream) are unchanged. No other project file declares
anything in the `Sundog` namespace. The closure has not been pruned: it also contains upstream
material on ReLU networks and tropical circuits that the projection theorem imports but does not
otherwise need.

## Pins and configuration

Upstream uses Lean `v4.30.0` and Mathlib `v4.30.0` (upstream `lake-manifest.json` revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`). This port targets the unchanged project Lean
`v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No package
dependency is added, and `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are unchanged.

The upstream `lakefile.toml` sets `relaxedAutoImplicit = false`, `maxSynthPendingDepth = 3`,
`pp.unicode.fun = true`, `weak.linter.mathlibStandardSet = true` and
`weak.linter.style.header = false`. These options are not replicated. No vendored file needed
`maxSynthPendingDepth 3`, so no `set_option` was added anywhere.

The project uses Lean's default `relaxedAutoImplicit = true`. Upstream compiling under the
stricter setting does not by itself exclude a problem: an identifier that upstream resolved but
that is missing from Mathlib v4.33.1 could, under the relaxed default, silently become an
automatically bound implicit argument of a statement instead of causing an error. This was
checked directly: each of the 26 vendored files elaborates with exit code 0,
no errors and no warnings under upstream's setting, via
`lake env lean -DrelaxedAutoImplicit=false NLQCLean/Vendor/Sundog/<File>.lean`. So no vendored
declaration depends on a relaxed automatic implicit. As a control, a file whose binder names an
unbound multi-letter identifier is rejected with this option and accepted without it.

## Local modifications

The complete list of changes relative to the unmodified upstream bytes follows.

1. **Notice.** Each of the 26 vendored Lean files starts with the derivation and
   modification notice described above. In the 25 modules one blank line separates it from
   the unchanged upstream text.
2. **Imports.** Every `import Sundogcert.X` is rewritten to `import NLQCLean.Vendor.Sundog.X`
   in 23 of the 25 modules (26 import lines). `CircuitNet` and `PieceCover` import only
   Mathlib, and their imports are unchanged.
3. **Compatibility edits in the 25 modules.** These edits appear only in proof bodies:

| File | Declaration | Old → new | Reason |
|---|---|---|---|
| `PieceCover.lean` | `Sundog.PieceCover.hasPieceCover_comp_mono` | `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (in `simp only`) | deprecated in Mathlib v4.33.1 |
| `RegionPoly.lean` | `Sundog.RegionPoly.hasPieceCover_max_line` | `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (in `simp only`) | deprecated |
| `OMinimalOne.lean` | `Sundog.OMinimalOne.frontier_superlevel_subset` | `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (in `simp only`) | deprecated |
| `OMinimalOne.lean` | `Sundog.OMinimalOne.poly_levelSet_tame` | `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (in `simp only`); `Polynomial.finite_setOf_isRoot` → `Polynomial.finite_setOfPred_isRoot` | deprecated |
| `PolySignPartition.lean` | `Sundog.TarskiQE.finite_familyRoots` | `Polynomial.finite_setOf_isRoot` → `Polynomial.finite_setOfPred_isRoot` | deprecated |
| `PolySignPartition.lean` | `Sundog.TarskiQE.tame_zeroSet` | `Polynomial.finite_setOf_isRoot` → `Polynomial.finite_setOfPred_isRoot` | deprecated |
| `PolyBranchTrees.lean` | `Sundog.TarskiQE.resolve_mem_truncChain` | the three tactics `change (0 : Polynomial (MvPolynomial (Fin n) ℝ)) ∈ truncChain 0`, `change P ∈ truncChain P` and `change resolve g P.eraseLead ∈ truncChain P` are removed; the first bullet now starts with the following `rw` | under Lean v4.33.1 the goals produced by `refine resolve_cases …` are already in these forms, and the unused-tactic linter warns that each `change` does nothing |
| `SignDiagrams.lean` | `Sundog.TarskiQE.SADef.zero` | `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (in `simp only`) | deprecated |
| `SignDiagrams.lean` | `Sundog.TarskiQE.finite_specRoots` | `Polynomial.finite_setOf_isRoot` → `Polynomial.finite_setOfPred_isRoot` | deprecated |
| `SignDiagrams.lean` | `Sundog.TarskiQE.elim_of_diagramPartition` | `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (in `simp only`) | deprecated |
| `SignDiagrams.lean` | `Sundog.TarskiQE.diagramPartition_of_constants` | `rw [Set.mem_setOf_eq, Set.mem_setOf_eq, …]` → `rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, …]` | deprecated |
| `DiagramNormalize.lean` | `Sundog.TarskiQE.paddingFree_cons` | `simp only [PaddingFreeAux]` → `simp only [List.length_cons, PaddingFreeAux]` | under Lean v4.33.1, `simp only [PaddingFreeAux]` made no progress on the goal with fuel `(c :: cpt :: rest).length` (a build error); rewriting the length with `List.length_cons` first lets the equation lemmas of `PaddingFreeAux` apply |
| `DiagramAugment.lean` | `Sundog.TarskiQE.spec_eq_zero_of_gap_roots` | `Polynomial.finite_setOf_isRoot` → `Polynomial.finite_setOfPred_isRoot` | deprecated |
| `DiagramBranches.lean` | `Sundog.TarskiQE.sadef_resolve_fiber` | `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (in `simp only`) | deprecated |

4. **Extract `SemialgebraicProjection.lean`.**
   - The imports `Sundogcert.DiagramAssembly` and `Sundogcert.OMinimalCellDecomp` are replaced
     by the single import `NLQCLean.Vendor.Sundog.DiagramAssembly`.
   - The upstream module comment (lines 1–22, which describe the whole file and its o-minimal
     structure) is replaced by a module docstring for the extract. It quotes the upstream list
     item on projection (upstream lines 8–12) verbatim, except that the item's closing `;`
     becomes `.`.
   - `open Polynomial Sundog.OMinimalOne Sundog.OMinimalAbstract` becomes
     `open Polynomial Sundog.OMinimalOne`; the omitted namespace comes from the unvendored
     `OMinimalCellDecomp` closure and is unused by the extracted declarations.
   - Retained upstream lines: 26 (namespace), 30 (`variable {n : ℕ}`), 32–92 (section heading
     and `sadef_sign_char`) and 116–154 (section heading and `sadef_proj`), followed by
     `end Sundog.TarskiQE`. Upstream lines 94–115 (`sadef_subst`) and 156–304 (the atoms,
     the one-dimensional tameness and the `OMinStructure` instance) are omitted.
   - Compatibility edits: in `Sundog.TarskiQE.sadef_sign_char` (upstream line 42) and in
     `Sundog.TarskiQE.sadef_proj` (upstream line 143), `Set.mem_setOf_eq` →
     `Set.mem_ofPred_eq` in `simp only`, because the old name is deprecated.

**Statements.** No edit changed a theorem, lemma or definition statement, a definition body,
or a declaration name. Every change above is in a proof body, an import, an `open` command
or a comment, or omits whole upstream declarations from the extract. The retained upstream
diagnostic commands are unchanged: `#print axioms` in `CircuitNet` (6), `RegionCount` (3) and
`CancellationFree` (4), and two `example`s in `DefinableRate`. The `#print axioms` commands
emit 13 informational messages during builds, each reporting exactly
`[propext, Classical.choice, Quot.sound]`.

## Interfaces and audits

[SundogProjectionAudit.lean](../../../NLQCTests/SundogProjectionAudit.lean)
checks `SADef`, `sadef_proj`, `sadef_sign_char` and `elim_signVector`,
including the explicit projection theorem type. The guarded axiom checks
report only `propext`, `Classical.choice` and `Quot.sound`.

The project root imports all 26 vendored modules, and
[ProjectionTheorem.lean](../../Semialgebraic/ProjectionTheorem.lean) applies
`sadef_proj` to prove `SemialgebraicProjectionTheorem`. The audit is included
in `NLQCTests`. Build the complete library and audits with
`lake build NLQCLean.All NLQCTests`.

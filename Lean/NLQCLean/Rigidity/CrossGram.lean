/-
The cross-Gram orbit-rigidity lemma.
-/
import NLQCLean.Rigidity.RangeDefect
import NLQCLean.Geometry.LocalOrbit

/-!
# Cross-Gram orbit rigidity

This is `lem:cross-gram-rigidity` of the snapshot (statement L697-735, proof
L737-770), the single infinitesimal statement that both the exact and the
approximate half of the paper are built on.

For differentiable isometries `A(t), B(t) : ℂ^D → 𝒦` with a common domain and
codomain, and `H = B†A`, `ℓ_in = A†Ȧ`, `ℓ_out = B†Ḃ`,
`α = ‖(I - BB†)A‖_op`:

* `NLQCLean.crossGram_hasDerivAt` — the velocity identity
  `Ḣ = -ℓ_out H + H ℓ_in + E` (eq:cross-gram-velocity, L714-719);
* `NLQCLean.norm_crossGramResidual_le` — the residual bound
  `‖E‖_F ≤ α (‖Ȧ‖_F + ‖Ḃ‖_F)`;
* `NLQCLean.crossGram_infDist_le` — the orbit-distance conclusion
  `dist_F(Ḣ, E_{𝔞,𝔟}(H)) ≤ α (‖Ȧ‖_F + ‖Ḃ‖_F)`
  (eq:cross-gram-orbit-distance, L722-727).

The residual `E` is *defined* by the displayed decomposition rather than
merely asserted to exist, as the statement matrix requires (row 3).

## Two domain index types, and local hypotheses

Two generalizations were added for `prop:exact-velocity` (snapshot L786-873).
Neither changes any statement of `lem:cross-gram-rigidity`; the square,
globally-hypothesized forms are all still available with their original
signatures.

* `A` and `B` may have **different domain index types** `ι` and `ι'`, so that
  `H = B†A` and the target `T` are rectangular *as typed* even when they are
  square as matrices.  This is forced by the architecture: the input logical
  space `H_A ⊗ H_B` and the output logical space `H_{A'} ⊗ H_{B'}` are
  distinct spaces of the same dimension (issue **F4** of `paper/FEEDBACK.md`),
  so a unitary target is a `Matrix (ιA' × ιB') (ιA × ιB) ℂ` and cannot be a
  member of `Matrix.unitaryGroup`.  Two-sided unitarity is therefore taken as
  the pair of equations `T†T = 1` and `TT† = 1`.
  The three statements that use the principal-angle symmetry
  eq:principal-angle-symmetry — `NLQCLean.defect`,
  `NLQCLean.norm_crossGramResidual_le`, `NLQCLean.crossGram_infDist_le` — stay
  square, because that symmetry genuinely needs `H = B†A` to be square.
* The isometry and factorization hypotheses of the derivative lemmas hold
  `∀ᶠ s in 𝓝 t` rather than for all `s : ℝ`.  See the docstring of
  `NLQCLean.isometry_hasDerivAt_skew_of_eventually` for why: `thm:finite-orbit`
  (L906-913) applies these lemmas on open subintervals between finitely many
  breakpoints.  The `∀ s` forms are kept as one-line corollaries.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {ι' : Type*} [Fintype ι'] [DecidableEq ι']

/-- The largest principal-angle defect `α = ‖(I - BB†)A‖_op` of
eq:cross-gram-data (snapshot L705-712). -/
noncomputable def defect (A B : Matrix κ ι ℂ) : ℝ :=
  opNorm (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A)

theorem defect_nonneg (A B : Matrix κ ι ℂ) : 0 ≤ defect A B := opNorm_nonneg _

/-- The residual `E = N_B† A + B† N_A` of eq:cross-gram-velocity, with
`N_A = (I - AA†)Ȧ` and `N_B = (I - BB†)Ḃ` as in the proof (snapshot L739-745). -/
def crossGramResidual (A : Matrix κ ι ℂ) (B : Matrix κ ι' ℂ) (A' : Matrix κ ι ℂ)
    (B' : Matrix κ ι' ℂ) : Matrix ι' ι ℂ :=
  B'ᴴ * (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A)
    + Bᴴ * (((1 : Matrix κ κ ℂ) - A * Aᴴ) * A')

omit [DecidableEq ι] in
/-- **eq:cross-gram-velocity** (snapshot L714-719), derivative part.

Only `B` is required to be an isometry, and only near `t`: the identity closes
because `Ḃ†B + B†Ḃ = 0`. -/
theorem crossGram_hasDerivAt_of_eventually {A : ℝ → Matrix κ ι ℂ}
    {B : ℝ → Matrix κ ι' ℂ} {A' : Matrix κ ι ℂ} {B' : Matrix κ ι' ℂ} {t : ℝ}
    (hB : ∀ᶠ s in nhds t, IsIsometry (B s))
    (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) :
    HasDerivAt (fun s => (B s)ᴴ * A s)
      (-(((B t)ᴴ * B') * ((B t)ᴴ * A t)) + ((B t)ᴴ * A t) * ((A t)ᴴ * A')
        + crossGramResidual (A t) (B t) A' B') t := by
  have hprod : HasDerivAt (fun s => (B s)ᴴ * A s) ((B t)ᴴ * A' + B'ᴴ * A t) t :=
    HasDerivAt.matrixMul (HasDerivAt.matrixConjTranspose hB') hA'
  have hskew : (B t)ᴴ * B' + B'ᴴ * B t = 0 :=
    isometry_hasDerivAt_skew_of_eventually hB hB'
  have halg : -(((B t)ᴴ * B') * ((B t)ᴴ * A t)) + ((B t)ᴴ * A t) * ((A t)ᴴ * A')
      + crossGramResidual (A t) (B t) A' B' = (B t)ᴴ * A' + B'ᴴ * A t := by
    have hexp : ((B t)ᴴ * B' + B'ᴴ * B t) * ((B t)ᴴ * A t) = 0 := by
      rw [hskew, Matrix.zero_mul]
    simp only [crossGramResidual, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.one_mul, Matrix.add_mul, Matrix.mul_assoc] at hexp ⊢
    linear_combination (norm := module) -hexp
  rw [halg]
  exact hprod

omit [DecidableEq ι] in
/-- The global form of `NLQCLean.crossGram_hasDerivAt_of_eventually`. -/
theorem crossGram_hasDerivAt {A : ℝ → Matrix κ ι ℂ} {B : ℝ → Matrix κ ι' ℂ}
    {A' : Matrix κ ι ℂ} {B' : Matrix κ ι' ℂ} {t : ℝ}
    (hB : ∀ s, IsIsometry (B s)) (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) :
    HasDerivAt (fun s => (B s)ᴴ * A s)
      (-(((B t)ᴴ * B') * ((B t)ᴴ * A t)) + ((B t)ᴴ * A t) * ((A t)ᴴ * A')
        + crossGramResidual (A t) (B t) A' B') t :=
  crossGram_hasDerivAt_of_eventually (Filter.Eventually.of_forall hB) hA' hB'

/-- **eq:cross-gram-velocity** (snapshot L714-719), norm part:
`‖E‖_F ≤ α (‖Ȧ‖_F + ‖Ḃ‖_F)`.

The two summands are contracted on opposite sides, which is why both mixed
norm bounds of `NLQCLean.LinearAlgebra.Basic` are needed; the second one is
recognised as the same `α` only through eq:principal-angle-symmetry. -/
theorem norm_crossGramResidual_le {A B A' B' : Matrix κ ι ℂ}
    (hA : IsIsometry A) (hB : IsIsometry B) :
    ‖crossGramResidual A B A' B'‖ ≤ defect A B * (‖A'‖ + ‖B'‖) := by
  have h1 : ‖B'ᴴ * (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A)‖ ≤ defect A B * ‖B'‖ := by
    have := frobNorm_mul_le' B'ᴴ (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A)
    rwa [Matrix.frobenius_norm_conjTranspose, mul_comm] at this
  have hop : opNorm ((B : Matrix κ ι ℂ)ᴴ * ((1 : Matrix κ κ ℂ) - A * Aᴴ)) = defect A B := by
    have hct : ((B : Matrix κ ι ℂ)ᴴ * ((1 : Matrix κ κ ℂ) - A * Aᴴ))ᴴ
        = ((1 : Matrix κ κ ℂ) - A * Aᴴ) * B := by
      rw [Matrix.conjTranspose_mul, complProj_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    rw [← opNorm_conjTranspose, hct, defect, principal_angle_symm hA hB]
  have h2 : ‖(B : Matrix κ ι ℂ)ᴴ * (((1 : Matrix κ κ ℂ) - A * Aᴴ) * A')‖
      ≤ defect A B * ‖A'‖ := by
    rw [← Matrix.mul_assoc, ← hop]
    exact frobNorm_mul_le _ _
  calc ‖crossGramResidual A B A' B'‖
      ≤ ‖B'ᴴ * (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A)‖
        + ‖(B : Matrix κ ι ℂ)ᴴ * (((1 : Matrix κ κ ℂ) - A * Aᴴ) * A')‖ :=
        norm_add_le _ _
    _ ≤ defect A B * ‖B'‖ + defect A B * ‖A'‖ := add_le_add h1 h2
    _ = defect A B * (‖A'‖ + ‖B'‖) := by ring

/-- **eq:cross-gram-orbit-distance** (snapshot L722-727).

`dist_F(Ḣ, E_{𝔞,𝔟}(H)) ≤ α (‖Ȧ‖_F + ‖Ḃ‖_F)` whenever `ℓ_in ∈ 𝔞` and
`ℓ_out ∈ 𝔟`.  The witness is the allowed tangent vector `-ℓ_out H + H ℓ_in`,
whose difference from `Ḣ` is exactly the residual. -/
theorem crossGram_infDist_le {A B : ℝ → Matrix κ ι ℂ} {A' B' : Matrix κ ι ℂ}
    {H' : Matrix ι ι ℂ} {t : ℝ} {𝔞 𝔟 : Submodule ℝ (Matrix ι ι ℂ)}
    (hA : IsIsometry (A t)) (hB : ∀ s, IsIsometry (B s))
    (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t)
    (hH : HasDerivAt (fun s => (B s)ᴴ * A s) H' t)
    (hin : (A t)ᴴ * A' ∈ 𝔞) (hout : (B t)ᴴ * B' ∈ 𝔟) :
    Metric.infDist H' (allowedTangent 𝔞 𝔟 ((B t)ᴴ * A t) : Set (Matrix ι ι ℂ))
      ≤ defect (A t) (B t) * (‖A'‖ + ‖B'‖) := by
  have hEq := (crossGram_hasDerivAt hB hA' hB').unique hH
  have hy : -(((B t)ᴴ * B') * ((B t)ᴴ * A t)) + ((B t)ᴴ * A t) * ((A t)ᴴ * A')
      ∈ allowedTangent 𝔞 𝔟 ((B t)ᴴ * A t) :=
    mem_allowedTangent_iff.mpr ⟨(A t)ᴴ * A', hin, (B t)ᴴ * B', hout, rfl⟩
  refine infDist_le_of_mem hy ?_
  have hdiff : H' - (-(((B t)ᴴ * B') * ((B t)ᴴ * A t)) + ((B t)ᴴ * A t) * ((A t)ᴴ * A'))
      = crossGramResidual (A t) (B t) A' B' := by
    rw [← hEq]; abel
  rw [hdiff]
  exact norm_crossGramResidual_le hA (hB t)

/-- If the two ranges agree the residual vanishes identically.

Range equality is expressed as equality of the range projections `A A† = B B†`,
which for isometries is exactly equality of the ranges. -/
theorem crossGramResidual_eq_zero {A A' : Matrix κ ι ℂ} {B B' : Matrix κ ι' ℂ}
    (hA : IsIsometry A) (hB : IsIsometry B) (h : A * Aᴴ = B * Bᴴ) :
    crossGramResidual A B A' B' = 0 := by
  have h1 : ((1 : Matrix κ κ ℂ) - B * Bᴴ) * A = 0 := by
    rw [← h, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hA.conjTranspose_mul_self,
      Matrix.mul_one, sub_self]
  have h2 : ((1 : Matrix κ κ ℂ) - A * Aᴴ) * B = 0 := by
    rw [h, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hB.conjTranspose_mul_self,
      Matrix.mul_one, sub_self]
  have h3 : (B : Matrix κ ι' ℂ)ᴴ * ((1 : Matrix κ κ ℂ) - A * Aᴴ) = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, complProj_conjTranspose, Matrix.conjTranspose_zero] at this
  rw [crossGramResidual, h1, ← Matrix.mul_assoc, h3, Matrix.mul_zero, Matrix.zero_mul,
    add_zero]

/-- **Zero-defect specialisation.**  Equal ranges make `α = 0`
(snapshot L728-730). -/
theorem defect_eq_zero_of_rangeProj_eq {A B : Matrix κ ι ℂ} (hA : IsIsometry A)
    (h : A * Aᴴ = B * Bᴴ) : defect A B = 0 := by
  have h1 : ((1 : Matrix κ κ ℂ) - B * Bᴴ) * A = 0 := by
    rw [← h, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hA.conjTranspose_mul_self,
      Matrix.mul_one, sub_self]
  rw [defect, h1, opNorm, toCLM]
  simp

/-- **eq:exact-cross-gram-velocity** (snapshot L730-734).  With equal ranges the
velocity lies exactly in the allowed tangent space. -/
theorem crossGram_hasDerivAt_exact_of_eventually {A : ℝ → Matrix κ ι ℂ}
    {B : ℝ → Matrix κ ι' ℂ} {A' : Matrix κ ι ℂ} {B' : Matrix κ ι' ℂ} {t : ℝ}
    (hA : IsIsometry (A t)) (hB : ∀ᶠ s in nhds t, IsIsometry (B s))
    (hrange : A t * (A t)ᴴ = B t * (B t)ᴴ)
    (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) :
    HasDerivAt (fun s => (B s)ᴴ * A s)
      (-(((B t)ᴴ * B') * ((B t)ᴴ * A t)) + ((B t)ᴴ * A t) * ((A t)ᴴ * A')) t := by
  have h := crossGram_hasDerivAt_of_eventually hB hA' hB'
  rwa [crossGramResidual_eq_zero hA hB.self_of_nhds hrange, add_zero] at h

/-- The global form of `NLQCLean.crossGram_hasDerivAt_exact_of_eventually`. -/
theorem crossGram_hasDerivAt_exact {A : ℝ → Matrix κ ι ℂ} {B : ℝ → Matrix κ ι' ℂ}
    {A' : Matrix κ ι ℂ} {B' : Matrix κ ι' ℂ} {t : ℝ}
    (hA : IsIsometry (A t)) (hB : ∀ s, IsIsometry (B s))
    (hrange : A t * (A t)ᴴ = B t * (B t)ᴴ)
    (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) :
    HasDerivAt (fun s => (B s)ᴴ * A s)
      (-(((B t)ᴴ * B') * ((B t)ᴴ * A t)) + ((B t)ᴴ * A t) * ((A t)ᴴ * A')) t :=
  crossGram_hasDerivAt_exact_of_eventually hA (Filter.Eventually.of_forall hB)
    hrange hA' hB'

omit [Fintype ι] [DecidableEq ι] in
omit [DecidableEq κ] in
/-- If `A = B T` then the cross-Gram matrix *is* the target: `H = T`
(snapshot L731-733). -/
theorem crossGram_eq_of_eq_mul {A : Matrix κ ι ℂ} {B : Matrix κ ι' ℂ}
    {T : Matrix ι' ι ℂ} (hB : IsIsometry B) (h : A = B * T) : Bᴴ * A = T := by
  rw [h, ← Matrix.mul_assoc, hB.conjTranspose_mul_self, Matrix.one_mul]

omit [DecidableEq κ] in
/-- With equal ranges the cross-Gram matrix is unitary (snapshot L728-730).
Both identities are needed: `H` is square, but unitarity is not automatic from
one side alone without that remark. -/
theorem crossGram_unitary_of_rangeProj_eq {A : Matrix κ ι ℂ} {B : Matrix κ ι' ℂ}
    (hA : IsIsometry A) (hB : IsIsometry B) (h : A * Aᴴ = B * Bᴴ) :
    (Bᴴ * A)ᴴ * (Bᴴ * A) = 1 ∧ (Bᴴ * A) * (Bᴴ * A)ᴴ = 1 := by
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc B, ← h, Matrix.mul_assoc A, ← Matrix.mul_assoc Aᴴ,
      hA.conjTranspose_mul_self, Matrix.one_mul]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc A, h, Matrix.mul_assoc B, ← Matrix.mul_assoc Bᴴ,
      hB.conjTranspose_mul_self, Matrix.one_mul]

/-- **eq:exact-cross-gram-velocity** (snapshot L730-734) in the paper's stated
form: if `A = B T` near `t` with `T` unitary at `t`, then `H = T` and
`Ṫ = -ℓ_out T + T ℓ_in`.

This is the form `prop:exact-velocity` consumes.  The target `T` is typed as a
`Matrix ι' ι ℂ` and its unitarity is the pair of equations `T†T = 1`,
`TT† = 1` at the single point `t`; membership in `Matrix.unitaryGroup` is not
available, because for a unitary target the input and output logical spaces
are distinct types (`paper/FEEDBACK.md` issue **F4**).  The equations are
taken as hypotheses rather than imported from
`NLQCLean.Models.UnitaryTask`, which would reverse the dependency between the
cross-Gram engine and the protocol model. -/
theorem exact_hasDerivAt_target_of_eventually {A : ℝ → Matrix κ ι ℂ}
    {B : ℝ → Matrix κ ι' ℂ} {T : ℝ → Matrix ι' ι ℂ}
    {A' : Matrix κ ι ℂ} {B' : Matrix κ ι' ℂ} {T' : Matrix ι' ι ℂ} {t : ℝ}
    (hB : ∀ᶠ s in nhds t, IsIsometry (B s))
    (hTiso : (T t)ᴴ * T t = 1) (hTco : T t * (T t)ᴴ = 1)
    (hmul : ∀ᶠ s in nhds t, A s = B s * T s)
    (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) (hT' : HasDerivAt T T' t) :
    T' = -(((B t)ᴴ * B') * T t) + T t * ((A t)ᴴ * A') := by
  have hBt : IsIsometry (B t) := hB.self_of_nhds
  have hmt : A t = B t * T t := hmul.self_of_nhds
  have hA : IsIsometry (A t) := by
    show (A t)ᴴ * A t = 1
    rw [hmt, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (B t)ᴴ,
      hBt.conjTranspose_mul_self, Matrix.one_mul, hTiso]
  have hrange : A t * (A t)ᴴ = B t * (B t)ᴴ := by
    rw [hmt, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (T t),
      hTco, Matrix.one_mul]
  have hev : T =ᶠ[nhds t] fun s => (B s)ᴴ * A s := by
    filter_upwards [hB, hmul] with s hBs hms
    exact (crossGram_eq_of_eq_mul hBs hms).symm
  have h := crossGram_hasDerivAt_exact_of_eventually hA hB hrange hA' hB'
  rw [crossGram_eq_of_eq_mul hBt hmt] at h
  exact hT'.unique (h.congr_of_eventuallyEq hev)

/-- The square, globally-hypothesized form of
`NLQCLean.exact_hasDerivAt_target_of_eventually`, with `T` a member of
`Matrix.unitaryGroup`. -/
theorem exact_hasDerivAt_target {A B : ℝ → Matrix κ ι ℂ} {T : ℝ → Matrix ι ι ℂ}
    {A' B' : Matrix κ ι ℂ} {T' : Matrix ι ι ℂ} {t : ℝ}
    (hB : ∀ s, IsIsometry (B s)) (hTu : ∀ s, T s ∈ Matrix.unitaryGroup ι ℂ)
    (hmul : ∀ s, A s = B s * T s)
    (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) (hT' : HasDerivAt T T' t) :
    T' = -(((B t)ᴴ * B') * T t) + T t * ((A t)ᴴ * A') :=
  exact_hasDerivAt_target_of_eventually (Filter.Eventually.of_forall hB)
    ((Matrix.mem_unitaryGroup_iff' (n := ι) (α := ℂ)).mp (hTu t))
    ((Matrix.mem_unitaryGroup_iff (n := ι) (α := ℂ)).mp (hTu t))
    (Filter.Eventually.of_forall hmul) hA' hB' hT'

end NLQCLean

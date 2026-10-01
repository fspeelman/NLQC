/-
Scalar Sard and unconditional exact exclusion.
-/
import NLQCLean.Geometry.ScalarSard
import NLQCLean.Invariants.OperatorSchmidtPurity
import NLQCLean.Models.ForwardReindex
import NLQCLean.Models.UnitaryScore
import NLQCLean.Models.UnitaryTask
import NLQCLean.Rigidity.ForwardWitnessCalculus
import NLQCLean.Geometry.CubicExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# One fixed controlled phase excludes every finite exact implementation

`NLQCLean.scalarCriticalImage_volume_eq_zero` consumes a `ContDiff ℝ ∞`
map with **vanishing full Fréchet derivative** on a set. The rigidity lemmas
supply directional derivatives of `t ↦ f (x + t • v)` at `0`.

The general directional-to-Fréchet lemmas live in `LinearAlgebra.Calculus`.
For a differentiable `f`, the Fréchet derivative applied to `v` is the
directional derivative along the line through `x` in direction `v`, so
vanishing in every direction is the same as a vanishing full derivative.

The cubic six-block extension has zero full derivative at exact witnesses.
Scalar Sard makes each fixed shape's critical image null. `ForwardReindex`
transports arbitrary finite register types to their cardinalities, so the
countable union `exactPurityValues` covers every exact pure implementation.
The explicit controlled-phase interval supplies a target outside this union.
Score-one exactness and score affinity then exclude finite mixed
implementations as well.

In `exists_unitary_no_finite_exact_implementation`, the target precedes all
architectures and has no extra mathematical premise.
Compactness gives the positive uniform gap at each fixed footprint in the
module `NLQCLean.Bounds.QualitativeDivergence`.
-/

namespace NLQCLean

open MeasureTheory

section NullCriticalValues

/-- The critical images over a countable family of
dimension tuples form a Lebesgue-null set. -/
theorem volume_iUnion_eq_zero {ι : Type*} [Countable ι] {s : ι → Set ℝ}
    (h : ∀ i, volume (s i) = 0) : volume (⋃ i, s i) = 0 :=
  measure_iUnion_null h

/-- A null set cannot contain an interval of positive
length, so a scalar value can be chosen inside the interval and outside the
null set. -/
theorem exists_mem_Ioo_not_mem_of_volume_eq_zero {N : Set ℝ} (hN : volume N = 0)
    {a b : ℝ} (hab : a < b) : ∃ v ∈ Set.Ioo a b, v ∉ N := by
  by_contra hcon
  have hsub : Set.Ioo a b ⊆ N := by
    intro x hx
    by_contra hxN
    exact hcon ⟨x, hx, hxN⟩
  have hle := measure_mono (μ := (volume : Measure ℝ)) hsub
  rw [hN, nonpos_iff_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hle
  linarith

end NullCriticalValues


section QP6

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- The smoothness index `∞`, pinned locally (see `LinearAlgebra/RealCoordinates`). -/
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Along any curve of blocks through an exact
witness whose velocities satisfy the six linearized constraints, the purity of
the forward overlap has zero derivative.

`forwardDifferential_local_full` turns the block velocities into `Ḣ = bU + Ua`
with `a, b` local, and `hasDerivAt_purity_local` annihilates this motion.
The varied witness need not stay exact. -/
theorem hasDerivAt_purity_forwardOverlap_zero (c : ℝ)
    {η : ℝ → ρA × ρB → ℂ} {η' : ρA × ρB → ℂ}
    {g : ℝ → εA × εB → ℂ} {g' : εA × εB → ℂ}
    {VA : ℝ → Matrix (κA × μA) (Fin d × ρA) ℂ} {VA' : Matrix (κA × μA) (Fin d × ρA) ℂ}
    {VB : ℝ → Matrix (κB × μB) (Fin d × ρB) ℂ} {VB' : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : ℝ → Matrix (Fin d × εA) (κA × μB) ℂ} {DA' : Matrix (Fin d × εA) (κA × μB) ℂ}
    {DB : ℝ → Matrix (Fin d × εB) (κB × μA) ℂ} {DB' : Matrix (Fin d × εB) (κB × μA) ℂ}
    (hη : HasDerivAt η η' 0) (hg : HasDerivAt g g' 0)
    (hVA : HasDerivAt VA VA' 0) (hVB : HasDerivAt VB VB' 0)
    (hDA : HasDerivAt DA DA' 0) (hDB : HasDerivAt DB DB' 0)
    (hVAiso : IsIsometry (VA 0)) (hVBiso : IsIsometry (VB 0))
    (hDAiso : IsIsometry (DA 0)) (hDBiso : IsIsometry (DB 0))
    (hVAlin : (VA 0)ᴴ * VA' + VA'ᴴ * (VA 0) = 0)
    (hVBlin : (VB 0)ᴴ * VB' + VB'ᴴ * (VB 0) = 0)
    (hDAlin : (DA 0)ᴴ * DA' + DA'ᴴ * (DA 0) = 0)
    (hDBlin : (DB 0)ᴴ * DB' + DB'ᴴ * (DB 0) = 0)
    (hηlin : (vecInner (η 0) η').re = 0) (hglin : (vecInner g' (g 0)).re = 0)
    (hWiso : IsIsometry
      ((decoder (DA 0) (DB 0)).submatrix (outputRegroup (Fin d) (Fin d) εA εB) id))
    (hUco : forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0)
        * (forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0))ᴴ = 1)
    (hexact : (decoder (DA 0) (DB 0)).submatrix (outputRegroup (Fin d) (Fin d) εA εB) id
        * encodedState (η 0) (VA 0) (VB 0)
      = insertVector (Fin d × Fin d) (g 0)
        * forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0)) :
    HasDerivAt
      (fun t => purity c (forwardOverlap (η t) (g t) (VA t) (VB t) (DA t) (DB t)))
      0 0 := by
  set U := forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0) with hUdef
  set W := (decoder (DA 0) (DB 0)).submatrix (outputRegroup (Fin d) (Fin d) εA εB) id
    with hWdef
  have hH := hasDerivAt_forwardOverlap hη hg hVA hVB hDA hDB
  -- The decoder velocity is a global skew generator acting on `W`.
  have hbij : Function.Bijective (outputRegroup (Fin d) (Fin d) εA εB) :=
    (outputRegroup (Fin d) (Fin d) εA εB).bijective
  have hWdot : ((DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0).submatrix
        (outputRegroup (Fin d) (Fin d) εA εB) id)
      = (ampLeft (Fin d × εA) (Fin d × εB) (skewLift (DA 0) DA')
          + ampRight (Fin d × εA) (Fin d × εB) (skewLift (DB 0) DB')).submatrix
          (outputRegroup (Fin d) (Fin d) εA εB) (outputRegroup (Fin d) (Fin d) εA εB)
        * W := by
    rw [hWdef, decoder, ← Matrix.submatrix_mul _ _ _ _ _ hbij, ampLeft_apply,
      ampRight_apply, skewLift_kronecker_mul hDAiso hDAlin hDBiso hDBlin]
    congr 1
    abel
  rw [hWdot] at hH
  -- The derivative is `b U + U a` with `a, b` local.
  obtain ⟨a, ha, b, hb, hval⟩ := forwardDifferential_local_full
    (VA := VA 0) (VB := VB 0) (VA' := VA') (VB' := VB')
    (W := W) (XA := skewLift (DA 0) DA') (XB := skewLift (DB 0) DB')
    (η := η 0) (η' := η') (g := g 0) (gdot := g') (U := U)
    hVAiso hVBiso hVAlin hVBlin hηlin hWiso hUco hexact rfl
    (skewLift_conjTranspose hDAlin) (skewLift_conjTranspose hDBlin) hglin
  rw [hval] at hH
  obtain ⟨aA, haA, aB, haB, harep⟩ := mem_localSkew_iff.mp ha
  obtain ⟨bA, hbA, bB, hbB, hbrep⟩ := mem_localSkew_iff.mp hb
  -- Purity has zero derivative along local motion.
  have hcd : ContDiff ℝ (⊤ : WithTop ℕ∞) (purity (ι := Fin d) c) :=
    ContDiff.purity c (contDiff_id (𝕜 := ℝ)
      (E := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
  have hdiff : Differentiable ℝ (purity (ι := Fin d) c) := hcd.differentiable (by simp)
  have hzero : fderiv ℝ (purity (ι := Fin d) c) U (b * U + U * a) = 0 := by
    have hline := fderiv_apply_eq_line_deriv (hdiff U) (b * U + U * a)
    have hlocal : HasDerivAt
        (fun t : ℝ => purity c (U + t • ((bA ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
            + (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ bB) * U
          + U * (aA ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
            + (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ aB)))) 0 0 :=
      hasDerivAt_purity_local c U haA haB hbA hbB
    rw [← harep, ← hbrep] at hlocal
    exact hline.unique hlocal
  have hfd : HasFDerivAt (purity (ι := Fin d) c)
      (fderiv ℝ (purity (ι := Fin d) c) U) U := (hdiff U).hasFDerivAt
  have hcomp : HasDerivAt
      (fun t => purity c (forwardOverlap (η t) (g t) (VA t) (VB t) (DA t) (DB t)))
      (fderiv ℝ (purity (ι := Fin d) c) U (b * U + U * a)) 0 := by
    have h := hfd.comp_hasDerivAt 0 hH
    simp only [Function.comp_def] at h
    exact h
  rw [hzero] at hcomp
  exact hcomp

/-- Conjugate symmetry of the real part of the vector inner product. -/
theorem vecInner_re_comm {ε : Type*} [Fintype ε] (z w : ε → ℂ) :
    (vecInner w z).re = (vecInner z w).re := by
  have h : vecInner z w = star (vecInner w z) := by
    rw [vecInner, vecInner, star_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [star_mul', star_star]; ring
  rw [h, Complex.star_def, Complex.conj_re]

/-- The balanced six-block parameter space at logical dimension `d`. -/
abbrev BalancedBlocks (d : ℕ) (ρA ρB κA κB μA μB εA εB : Type*) :=
  ForwardBlocks (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB

/-- The global cubic extension `Q`, applied blockwise: the two sphere
maps on the resource and the witness, the four Stiefel maps on the encoders
and decoders. -/
noncomputable def cubicBlocks (x : BalancedBlocks d ρA ρB κA κB μA μB εA εB) :
    BalancedBlocks d ρA ρB κA κB μA μB εA εB :=
  (cubicSphere x.1, cubicSphere x.2.1, cubicStiefel x.2.2.1,
    cubicStiefel x.2.2.2.1, cubicStiefel x.2.2.2.2.1, cubicStiefel x.2.2.2.2.2)

/-- The scalar ambient polynomial `φ = p ∘ H ∘ Q`. -/
noncomputable def scalarPhi (c : ℝ)
    (x : BalancedBlocks d ρA ρB κA κB μA μB εA εB) : ℝ :=
  purity c (forwardOverlapOn (cubicBlocks x))

/-- A point of the ambient space at which every block constraint holds, the
forward overlap is unitary, and the frozen exactness identity holds. -/
structure IsExactWitness (x : BalancedBlocks d ρA ρB κA κB μA μB εA εB) : Prop where
  resource_unit : IsUnitVector x.1
  witness_unit : IsUnitVector x.2.1
  encA_isometry : IsIsometry x.2.2.1
  encB_isometry : IsIsometry x.2.2.2.1
  decA_isometry : IsIsometry x.2.2.2.2.1
  decB_isometry : IsIsometry x.2.2.2.2.2
  decoder_isometry : IsIsometry
    ((decoder x.2.2.2.2.1 x.2.2.2.2.2).submatrix
      (outputRegroup (Fin d) (Fin d) εA εB) id)
  overlap_coisometry :
    forwardOverlapOn x * (forwardOverlapOn x)ᴴ = 1
  exact :
    (decoder x.2.2.2.2.1 x.2.2.2.2.2).submatrix
        (outputRegroup (Fin d) (Fin d) εA εB) id
      * encodedState x.1 x.2.2.1 x.2.2.2.1
    = insertVector (Fin d × Fin d) x.2.1 * forwardOverlapOn x

omit [DecidableEq εA] [DecidableEq εB] in
/-- `Q` is the identity on the constraint set. -/
theorem cubicBlocks_of_isExactWitness {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB}
    (hx : IsExactWitness x) : cubicBlocks x = x := by
  rw [cubicBlocks, cubicSphere_of_isUnitVector hx.resource_unit,
    cubicSphere_of_isUnitVector hx.witness_unit,
    cubicStiefel_of_isometry hx.encA_isometry,
    cubicStiefel_of_isometry hx.encB_isometry,
    cubicStiefel_of_isometry hx.decA_isometry,
    cubicStiefel_of_isometry hx.decB_isometry]

/-- Along *every* straight line
through an exact witness -- with no tangency hypothesis on the direction --
the ambient polynomial `φ` has zero derivative. The cubic
extension makes `DQ_x[v]` satisfy the linearized constraints for
every `v`, so the exact-witness derivative lemma applies. -/
theorem hasDerivAt_scalarPhi_line (c : ℝ)
    {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactWitness x)
    (v : BalancedBlocks d ρA ρB κA κB μA μB εA εB) :
    HasDerivAt (fun t : ℝ => scalarPhi c (x + t • v)) 0 0 := by
  have hη0 : cubicSphere (x.1 + (0 : ℝ) • v.1) = x.1 := by
    rw [zero_smul, add_zero, cubicSphere_of_isUnitVector hx.resource_unit]
  have hg0 : cubicSphere (x.2.1 + (0 : ℝ) • v.2.1) = x.2.1 := by
    rw [zero_smul, add_zero, cubicSphere_of_isUnitVector hx.witness_unit]
  have hVA0 : cubicStiefel (x.2.2.1 + (0 : ℝ) • v.2.2.1) = x.2.2.1 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.encA_isometry]
  have hVB0 : cubicStiefel (x.2.2.2.1 + (0 : ℝ) • v.2.2.2.1) = x.2.2.2.1 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.encB_isometry]
  have hDA0 : cubicStiefel (x.2.2.2.2.1 + (0 : ℝ) • v.2.2.2.2.1) = x.2.2.2.2.1 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.decA_isometry]
  have hDB0 : cubicStiefel (x.2.2.2.2.2 + (0 : ℝ) • v.2.2.2.2.2) = x.2.2.2.2.2 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.decB_isometry]
  exact hasDerivAt_purity_forwardOverlap_zero c
    (η := fun t => cubicSphere (x.1 + t • v.1)) (η' := dCubicSphere x.1 v.1)
    (g := fun t => cubicSphere (x.2.1 + t • v.2.1)) (g' := dCubicSphere x.2.1 v.2.1)
    (VA := fun t => cubicStiefel (x.2.2.1 + t • v.2.2.1))
    (VA' := dCubicStiefel x.2.2.1 v.2.2.1)
    (VB := fun t => cubicStiefel (x.2.2.2.1 + t • v.2.2.2.1))
    (VB' := dCubicStiefel x.2.2.2.1 v.2.2.2.1)
    (DA := fun t => cubicStiefel (x.2.2.2.2.1 + t • v.2.2.2.2.1))
    (DA' := dCubicStiefel x.2.2.2.2.1 v.2.2.2.2.1)
    (DB := fun t => cubicStiefel (x.2.2.2.2.2 + t • v.2.2.2.2.2))
    (DB' := dCubicStiefel x.2.2.2.2.2 v.2.2.2.2.2)
    (hasDerivAt_cubicSphere hx.resource_unit v.1)
    (hasDerivAt_cubicSphere hx.witness_unit v.2.1)
    (hasDerivAt_cubicStiefel hx.encA_isometry v.2.2.1)
    (hasDerivAt_cubicStiefel hx.encB_isometry v.2.2.2.1)
    (hasDerivAt_cubicStiefel hx.decA_isometry v.2.2.2.2.1)
    (hasDerivAt_cubicStiefel hx.decB_isometry v.2.2.2.2.2)
    (by rw [hVA0]; exact hx.encA_isometry)
    (by rw [hVB0]; exact hx.encB_isometry)
    (by rw [hDA0]; exact hx.decA_isometry)
    (by rw [hDB0]; exact hx.decB_isometry)
    (by rw [hVA0]; exact dCubicStiefel_linearized hx.encA_isometry _)
    (by rw [hVB0]; exact dCubicStiefel_linearized hx.encB_isometry _)
    (by rw [hDA0]; exact dCubicStiefel_linearized hx.decA_isometry _)
    (by rw [hDB0]; exact dCubicStiefel_linearized hx.decB_isometry _)
    (by rw [hη0]; exact dCubicSphere_linearized hx.resource_unit _)
    (by rw [hg0, vecInner_re_comm]; exact dCubicSphere_linearized hx.witness_unit _)
    (by rw [hDA0, hDB0]; exact hx.decoder_isometry)
    (by rw [hη0, hg0, hVA0, hVB0, hDA0, hDB0]; exact hx.overlap_coisometry)
    (by rw [hη0, hg0, hVA0, hVB0, hDA0, hDB0]; exact hx.exact)

/-- The full ambient Fréchet derivative of `φ` vanishes at every
exact witness. -/
theorem fderiv_scalarPhi_eq_zero (c : ℝ)
    {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactWitness x)
    (hdiff : DifferentiableAt ℝ (scalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) c) x) :
    fderiv ℝ (scalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) c) x = 0 :=
  fderiv_eq_zero_of_hasDerivAt_lines hdiff fun v => hasDerivAt_scalarPhi_line c hx v

/-!
### Smoothness of `φ`, and the Sard step
-/

theorem contDiff_cubicBlocks :
    ContDiff ℝ ∞ (cubicBlocks (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)) := by
  refine ContDiff.prodMk (contDiff_cubicSphere.comp contDiff_fst) ?_
  refine ContDiff.prodMk (contDiff_cubicSphere.comp (contDiff_fst.comp contDiff_snd)) ?_
  refine ContDiff.prodMk
    (contDiff_cubicStiefel.comp (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))) ?_
  refine ContDiff.prodMk
    (contDiff_cubicStiefel.comp
      (contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))) ?_
  exact ContDiff.prodMk
    (contDiff_cubicStiefel.comp (contDiff_fst.comp
      (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))))
    (contDiff_cubicStiefel.comp
      (contDiff_snd.comp (contDiff_snd.comp
        (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))))

/-- `φ` is a real polynomial map, hence smooth. -/
theorem contDiff_scalarPhi (c : ℝ) :
    ContDiff ℝ ∞ (scalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) c) :=
  (contDiff_purityForwardOverlap c).comp contDiff_cubicBlocks

/-- For one dimension tuple, the critical image of the exact witnesses
is Lebesgue-null.  This is scalar Sard applied to `φ`; no measurability or
regularity of the witness set is required. -/
theorem volume_scalarPhi_image_eq_zero (c : ℝ)
    (s : Set (BalancedBlocks d ρA ρB κA κB μA μB εA εB))
    (hs : ∀ x ∈ s, IsExactWitness x) :
    volume (scalarPhi (d := d) c '' s) = 0 := by
  refine scalarCriticalImage_volume_eq_zero (contDiff_scalarPhi c) ?_
  intro x hx
  exact fderiv_scalarPhi_eq_zero c (hs x hx)
    ((contDiff_scalarPhi c).differentiable (by simp) x)

end QP6

section AllArchitectures

open Matrix
open scoped Kronecker

/-- The eight internal dimensions, in the order
`R_A, R_B, K_A, K_B, M_A, M_B, E_A, E_B`. All natural tuples are included;
there is no footprint or private-dimension restriction in this enumeration. -/
abbrev ForwardShape := Fin 8 → ℕ

/-- The ambient witness space for a tuple of cardinalities. -/
abbrev ShapeBlocks (d : ℕ) (s : ForwardShape) :=
  BalancedBlocks d (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
    (Fin (s 4)) (Fin (s 5)) (Fin (s 6)) (Fin (s 7))

/-- The union over *all* internal finite dimensions, before any target or
footprint budget is chosen. The purity normalization is `D⁻² = d⁻⁴`. -/
def exactPurityValues (d : ℕ) : Set ℝ :=
  ⋃ s : ForwardShape,
    scalarPhi ((d : ℝ) ^ 4)⁻¹ '' {x : ShapeBlocks d s | IsExactWitness x}

/-- The set of all exact witness values is null, without assumptions on the
regularity of any witness locus. -/
theorem volume_exactPurityValues_eq_zero (d : ℕ) :
    volume (exactPurityValues d) = 0 := by
  apply volume_iUnion_eq_zero
  intro s
  exact volume_scalarPhi_image_eq_zero _ _ (fun _ hx => hx)

variable {d : ℕ}
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq εA] [DecidableEq εB] in
/-- Every exact witness on arbitrary finite
register types has its invariant value in the same countable union. -/
theorem purity_mem_exactPurityValues {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB}
    (hx : IsExactWitness x) :
    purity ((d : ℝ) ^ 4)⁻¹ (forwardOverlapOn x) ∈ exactPurityValues d := by
  let rA := (Fintype.equivFin ρA).symm
  let rB := (Fintype.equivFin ρB).symm
  let kA := (Fintype.equivFin κA).symm
  let kB := (Fintype.equivFin κB).symm
  let mA := (Fintype.equivFin μA).symm
  let mB := (Fintype.equivFin μB).symm
  let eA := (Fintype.equivFin εA).symm
  let eB := (Fintype.equivFin εB).symm
  let s : ForwardShape := ![Fintype.card ρA, Fintype.card ρB,
    Fintype.card κA, Fintype.card κB, Fintype.card μA, Fintype.card μB,
    Fintype.card εA, Fintype.card εB]
  let y : ShapeBlocks d s := reindexForwardBlocks rA rB kA kB mA mB eA eB x
  have hH : forwardOverlapOn y = forwardOverlapOn x :=
    forwardOverlapOn_reindex rA rB kA kB mA mB eA eB x
  have hy : IsExactWitness y := by
    refine ⟨hx.resource_unit.comp_equiv (rA.prodCongr rB),
      hx.witness_unit.comp_equiv (eA.prodCongr eB),
      hx.encA_isometry.submatrix_equiv _ _, hx.encB_isometry.submatrix_equiv _ _,
      hx.decA_isometry.submatrix_equiv _ _, hx.decB_isometry.submatrix_equiv _ _,
      ?_, ?_, ?_⟩
    · exact (isIsometry_decoder
        (hx.decA_isometry.submatrix_equiv _ _)
        (hx.decB_isometry.submatrix_equiv _ _)).submatrix_equiv
          (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) (Equiv.refl _)
    · rw [hH]
      exact hx.overlap_coisometry
    · rw [← globalIsometryRegrouped_eq]
      have hreg : globalIsometryRegrouped y.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2 =
          (globalIsometryRegrouped x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2).submatrix
            ((Equiv.refl (Fin d × Fin d)).prodCongr (eA.prodCongr eB)) id :=
        globalIsometryRegrouped_reindex rA rB kA kB mA mB eA eB x
      rw [hreg, globalIsometryRegrouped_eq, hx.exact, hH]
      exact (Matrix.submatrix_mul _ _ _ id id Function.bijective_id).trans (by
        rw [Matrix.submatrix_id_id]
        rfl)
  apply Set.mem_iUnion.mpr
  refine ⟨s, y, hy, ?_⟩
  rw [scalarPhi, cubicBlocks_of_isExactWitness hy, hH]

/-- A score-one physical protocol gives an exact witness, so its target
purity belongs to the union over all finite shapes. This uses the existing
normalized Choi score and the exact-freezing identity. -/
theorem PureProtocol.purity_mem_exactPurityValues_of_score_eq_one [NeZero d]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hscore : scoreU U P.operationalChannel = 1) :
    purity ((d : ℝ) ^ 4)⁻¹ U ∈ exactPurityValues d := by
  let F := globalIsometryRegrouped P.resource P.encA P.encB P.decA P.decB
  have hF : IsIsometry F :=
    P.isIsometry_globalIsometry.submatrix_equiv
      (outputRegroup (Fin d) (Fin d) εA εB) (Equiv.refl _)
  let g := scoreVector U F
  have hg : IsUnitVector g := (isUnitVector_scoreVector_iff U F).mpr hscore
  have hfreeze : F = insertVector (Fin d × Fin d) g * U :=
    (scoreU_eq_one_iff hU.isIsometry hF).mp hscore
  let x : BalancedBlocks d ρA ρB κA κB μA μB εA εB :=
    (P.resource, g, P.encA, P.encB, P.decA, P.decB)
  have hH : forwardOverlapOn x = U := by
    change (insertVector (Fin d × Fin d) g)ᴴ * F = U
    rw [hfreeze, ← Matrix.mul_assoc,
      (isIsometry_insertVector g hg).conjTranspose_mul_self, Matrix.one_mul]
  have hx : IsExactWitness x := by
    refine ⟨P.resource_unit, hg, P.encA_isometry, P.encB_isometry,
      P.decA_isometry, P.decB_isometry, ?_, ?_, ?_⟩
    · exact (isIsometry_decoder P.decA_isometry P.decB_isometry).submatrix_equiv
        (outputRegroup (Fin d) (Fin d) εA εB) (Equiv.refl _)
    · rw [hH]
      exact hU.self_mul_conjTranspose
    · rw [← globalIsometryRegrouped_eq, hH]
      exact hfreeze
  simpa only [hH] using purity_mem_exactPurityValues hx

end AllArchitectures

section ExactExclusion

open Matrix

/-- Choose a controlled phase using the countable union over all shapes.
This statement has no register types or footprint budget among its inputs. -/
theorem exists_phase_purity_not_mem (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ t : ℝ, t ^ 2 ≤ 1 ∧
      purity ((d : ℝ) ^ 4)⁻¹ (phaseFamily d t) ∉ exactPurityValues d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hlength : 1 - 8 * ((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 4 < 1 := by
    have hpos : 0 < 8 * ((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 4 := by positivity
    linarith
  obtain ⟨v, hv, hvN⟩ := exists_mem_Ioo_not_mem_of_volume_eq_zero
    (volume_exactPurityValues_eq_zero d) hlength
  obtain ⟨t, ht, hval⟩ := exists_purity_phaseFamily_eq hd hv.1.le hv.2.le
  exact ⟨t, ht, hval ▸ hvN⟩

variable {d : ℕ} [NeZero d]
variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}

/-- Each finite pure protocol has score strictly below one for a target whose
purity avoids the union of exact witness values. -/
theorem PureProtocol.scoreU_lt_one_of_purity_not_mem
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (hU : UnitaryTarget U) (hN : purity ((d : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues d) :
    scoreU U P.operationalChannel < 1 := by
  have hF := P.isIsometry_globalIsometry.submatrix_equiv
    (outputRegroup (Fin d) (Fin d) εA εB) (Equiv.refl _)
  exact lt_of_le_of_ne (scoreU_le_one hU.isIsometry hF)
    (fun h => hN (P.purity_mem_exactPurityValues_of_score_eq_one hU h))

/-- Exact exclusion for the operational unitary predicate. -/
theorem PureProtocol.not_performsUnitary_of_purity_not_mem
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    (hU : UnitaryTarget U) (hN : purity ((d : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues d) :
    ¬ P.PerformsUnitary U := by
  intro h
  have hlt := P.scoreU_lt_one_of_purity_not_mem hU hN
  change P.operationalChannel = adConj U at h
  rw [h, scoreU_adConj_self hU.isIsometry] at hlt
  exact (lt_irrefl 1) hlt

/-- Finite mixing cannot attain score one: select a pure component
with at least the mixed score. No bound on the resource support is used. -/
theorem MixedResource.scoreU_lt_one_of_purity_not_mem {n : ℕ}
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix (Fin d × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin d × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hU : UnitaryTarget U) (hN : purity ((d : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues d) :
    scoreU U (m.mixedChannel VA VB DA DB) < 1 := by
  obtain ⟨k, hk⟩ := m.exists_component_scoreU_ge VA VB DA DB U
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  exact hk.trans_lt (P.scoreU_lt_one_of_purity_not_mem hU hN)

/-- Operational exact exclusion for arbitrary finite mixed resources. -/
theorem MixedResource.mixedChannel_ne_adConj_of_purity_not_mem {n : ℕ}
    (m : MixedResource ρA ρB n)
    {VA : Matrix (κA × μA) (Fin d × ρA) ℂ}
    {VB : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : Matrix (Fin d × εA) (κA × μB) ℂ}
    {DB : Matrix (Fin d × εB) (κB × μA) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hU : UnitaryTarget U) (hN : purity ((d : ℝ) ^ 4)⁻¹ U ∉ exactPurityValues d) :
    m.mixedChannel VA VB DA DB ≠ adConj U := by
  intro h
  have hlt := m.scoreU_lt_one_of_purity_not_mem hVA hVB hDA hDB hU hN
  rw [h, scoreU_adConj_self hU.isIsometry] at hlt
  exact (lt_irrefl 1) hlt

end ExactExclusion

/-- No exact pure implementation on any finite internal register types.
The types are independently universe-polymorphic and their cardinalities
are unrestricted. In particular this includes every finite footprint budget. -/
def NoFinitePureImplementation {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB),
    ¬ P.PerformsUnitary U

/-- No exact implementation using any finite mixed-resource decomposition
and four physical isometries on arbitrary finite internal registers. -/
def NoFiniteMixedImplementation {d : ℕ}
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∀ (ρA ρB κA κB μA μB εA εB : Type*)
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (n : ℕ) (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
    (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
    IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
      m.mixedChannel VA VB DA DB ≠ adConj U

/-- Exact exclusion in the rank-one controlled-phase family.
One parameter is chosen before all finite pure and mixed architectures. The
only side condition is `d ≥ 2`; `NeZero d` merely makes the basis projector's
index available. -/
theorem exists_phase_no_finite_exact_implementation (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ t : ℝ, t ^ 2 ≤ 1 ∧ UnitaryTarget (phaseFamily d t) ∧
      NoFinitePureImplementation (phaseFamily d t) ∧
      NoFiniteMixedImplementation (phaseFamily d t) := by
  obtain ⟨t, ht, hN⟩ := exists_phase_purity_not_mem d hd
  have hU : UnitaryTarget (phaseFamily d t) :=
    ⟨(phaseFamily_unitary ht).1, (phaseFamily_unitary ht).2⟩
  refine ⟨t, ht, hU, ?_, ?_⟩
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
    exact P.not_performsUnitary_of_purity_not_mem hU hN
  · intro ρA ρB κA κB μA μB εA εB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n m VA VB DA DB
      hVA hVB hDA hDB
    exact m.mixedChannel_ne_adConj_of_purity_not_mem hVA hVB hDA hDB hU hN

/-- For each balanced logical dimension `d ≥ 2`,
there is one unitary that no finite pure or finite mixed one-round protocol
implements exactly, at any footprint. A uniform positive approximation gap
at fixed footprint is proved in `NLQCLean.Bounds.QualitativeDivergence`. -/
theorem exists_unitary_no_finite_exact_implementation (d : ℕ) (hd : 2 ≤ d) :
    ∃ U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      UnitaryTarget U ∧ NoFinitePureImplementation U ∧ NoFiniteMixedImplementation U := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨t, _, hU, hPure, hMixed⟩ := exists_phase_no_finite_exact_implementation d hd
  exact ⟨phaseFamily d t, hU, hPure, hMixed⟩

end NLQCLean

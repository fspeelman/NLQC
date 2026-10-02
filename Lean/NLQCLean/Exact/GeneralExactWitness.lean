import NLQCLean.Exact.InvariantCriticalValues
import NLQCLean.Exact.LocalOrbitSaturation
import NLQCLean.Exact.PolynomialWitnessMaps

/-!
# Exact witnesses for arbitrary local dimensions

The exact-witness locus, its cubic extension and the critical-value argument
for smooth local-unitary invariants, for input/output spaces `ι_A ⊗ ι_B` of
arbitrary finite local dimensions. This is the setting of `rem:qudits`.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Kronecker

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Witness

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

variable (ιA ιB) in
/-- The six-block parameter space with input and output spaces `ι_A ⊗ ι_B`. -/
abbrev GenBlocks (ρA ρB κA κB μA μB εA εB : Type*) :=
  ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA ιB εA εB

/-- The blockwise cubic extension. -/
def cubicBlocksGen (x : GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB) :
    GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB :=
  (cubicSphere x.1, cubicSphere x.2.1, cubicStiefel x.2.2.1,
    cubicStiefel x.2.2.2.1, cubicStiefel x.2.2.2.2.1, cubicStiefel x.2.2.2.2.2)

/-- An exact witness: physical blocks, unit garbage vector, unitary overlap and
the frozen-dilation identity. -/
structure IsExactWitnessGen (x : GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB) : Prop where
  resource_unit : IsUnitVector x.1
  witness_unit : IsUnitVector x.2.1
  encA_isometry : IsIsometry x.2.2.1
  encB_isometry : IsIsometry x.2.2.2.1
  decA_isometry : IsIsometry x.2.2.2.2.1
  decB_isometry : IsIsometry x.2.2.2.2.2
  decoder_isometry : IsIsometry
    ((decoder x.2.2.2.2.1 x.2.2.2.2.2).submatrix (outputRegroup ιA ιB εA εB) id)
  overlap_coisometry : forwardOverlapOn x * (forwardOverlapOn x)ᴴ = 1
  exact :
    (decoder x.2.2.2.2.1 x.2.2.2.2.2).submatrix (outputRegroup ιA ιB εA εB) id
        * encodedState x.1 x.2.2.1 x.2.2.2.1
    = insertVector (ιA × ιB) x.2.1 * forwardOverlapOn x

omit [DecidableEq εA] [DecidableEq εB] in
theorem cubicBlocksGen_of_isExactWitnessGen {x : GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB}
    (hx : IsExactWitnessGen x) : cubicBlocksGen x = x := by
  rw [cubicBlocksGen, cubicSphere_of_isUnitVector hx.resource_unit,
    cubicSphere_of_isUnitVector hx.witness_unit,
    cubicStiefel_of_isometry hx.encA_isometry,
    cubicStiefel_of_isometry hx.encB_isometry,
    cubicStiefel_of_isometry hx.decA_isometry,
    cubicStiefel_of_isometry hx.decB_isometry]

theorem contDiff_cubicBlocksGen :
    ContDiff ℝ ∞ (cubicBlocksGen (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB) (κA := κA)
      (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)) := by
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

theorem hasDerivAt_invariant_forwardOverlap_zero_gen (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    (hdiff : Differentiable ℝ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (ιA × ιB) ℂ,
      ∀ V ∈ unitaryDoubleOrbit ιA ιB U, f V = f U)
    {η : ℝ → ρA × ρB → ℂ} {η' : ρA × ρB → ℂ}
    {g : ℝ → εA × εB → ℂ} {g' : εA × εB → ℂ}
    {VA : ℝ → Matrix (κA × μA) (ιA × ρA) ℂ} {VA' : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : ℝ → Matrix (κB × μB) (ιB × ρB) ℂ} {VB' : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : ℝ → Matrix (ιA × εA) (κA × μB) ℂ} {DA' : Matrix (ιA × εA) (κA × μB) ℂ}
    {DB : ℝ → Matrix (ιB × εB) (κB × μA) ℂ} {DB' : Matrix (ιB × εB) (κB × μA) ℂ}
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
      ((decoder (DA 0) (DB 0)).submatrix (outputRegroup ιA ιB εA εB) id))
    (hUco : forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0)
        * (forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0))ᴴ = 1)
    (hexact : (decoder (DA 0) (DB 0)).submatrix (outputRegroup ιA ιB εA εB) id
        * encodedState (η 0) (VA 0) (VB 0)
      = insertVector (ιA × ιB) (g 0)
        * forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0)) :
    HasDerivAt
      (fun t => f (forwardOverlap (η t) (g t) (VA t) (VB t) (DA t) (DB t)))
      0 0 := by
  set U := forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0) with hUdef
  set W := (decoder (DA 0) (DB 0)).submatrix (outputRegroup ιA ιB εA εB) id
    with hWdef
  have hH := hasDerivAt_forwardOverlap hη hg hVA hVB hDA hDB
  -- The decoder velocity is a global skew generator acting on `W`.
  have hbij : Function.Bijective (outputRegroup ιA ιB εA εB) :=
    (outputRegroup ιA ιB εA εB).bijective
  have hWdot : ((DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0).submatrix
        (outputRegroup ιA ιB εA εB) id)
      = (ampLeft (ιA × εA) (ιB × εB) (skewLift (DA 0) DA')
          + ampRight (ιA × εA) (ιB × εB) (skewLift (DB 0) DB')).submatrix
          (outputRegroup ιA ιB εA εB) (outputRegroup ιA ιB εA εB)
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
  have hzero : fderiv ℝ f U (b * U + U * a) = 0 :=
    fderiv_eq_zero_of_localSkew f (hdiff U)
      (hinv U (Matrix.mem_unitaryGroup_iff.mpr hUco)) ha hb
  have hfd : HasFDerivAt f
      (fderiv ℝ f U) U := (hdiff U).hasFDerivAt
  have hcomp : HasDerivAt
      (fun t => f (forwardOverlap (η t) (g t) (VA t) (VB t) (DA t) (DB t)))
      (fderiv ℝ f U (b * U + U * a)) 0 := by
    have h := hfd.comp_hasDerivAt 0 hH
    simp only [Function.comp_def] at h
    exact h
  rw [hzero] at hcomp
  exact hcomp

/-- The smooth scalar extension `φ = f ∘ H ∘ Q`. -/
noncomputable def invariantScalarPhiGen (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    (x : GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB) : ℝ :=
  f (forwardOverlapOn (cubicBlocksGen x))

/-- Along *every* straight line
through an exact witness -- with no tangency hypothesis on the direction --
the ambient scalar function `φ` has zero derivative. The cubic
extension makes `DQ_x[v]` satisfy the linearized constraints for
every `v`, so the exact-witness derivative lemma applies. -/
theorem hasDerivAt_invariantScalarPhiGen_line (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    (hdiff : Differentiable ℝ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (ιA × ιB) ℂ,
      ∀ V ∈ unitaryDoubleOrbit ιA ιB U, f V = f U)
    {x : GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB} (hx : IsExactWitnessGen x)
    (v : GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB) :
    HasDerivAt (fun t : ℝ => invariantScalarPhiGen f (x + t • v)) 0 0 := by
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
  exact hasDerivAt_invariant_forwardOverlap_zero_gen f hdiff hinv
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
theorem fderiv_invariantScalarPhiGen_eq_zero (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    (hdiff : Differentiable ℝ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (ιA × ιB) ℂ,
      ∀ V ∈ unitaryDoubleOrbit ιA ιB U, f V = f U)
    {x : GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB} (hx : IsExactWitnessGen x)
    (hphi : DifferentiableAt ℝ (invariantScalarPhiGen (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) x) :
    fderiv ℝ (invariantScalarPhiGen (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) x = 0 :=
  fderiv_eq_zero_of_hasDerivAt_lines hphi fun v =>
    hasDerivAt_invariantScalarPhiGen_line f hdiff hinv hx v

/-!
### Smoothness of `φ`, and the Sard step
-/

/-- A smooth scalar invariant remains smooth after the cubic forward map. -/
theorem contDiff_invariantScalarPhiGen (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (invariantScalarPhiGen (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) :=
  (hf.comp contDiff_forwardOverlapOn).comp contDiff_cubicBlocksGen

/-- For one dimension tuple, the critical image of the exact witnesses
is Lebesgue-null.  This is scalar Sard applied to `φ`; no measurability or
regularity of the witness set is required. -/
theorem volume_invariantScalarPhiGen_image_eq_zero (f : Matrix (ιA × ιB) (ιA × ιB) ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (ιA × ιB) ℂ,
      ∀ V ∈ unitaryDoubleOrbit ιA ιB U, f V = f U)
    (s : Set (GenBlocks ιA ιB ρA ρB κA κB μA μB εA εB))
    (hs : ∀ x ∈ s, IsExactWitnessGen x) :
    volume (invariantScalarPhiGen (ιA := ιA) (ιB := ιB) f '' s) = 0 := by
  refine scalarCriticalImage_volume_eq_zero (contDiff_invariantScalarPhiGen f hf) ?_
  intro x hx
  exact fderiv_invariantScalarPhiGen_eq_zero f (hf.differentiable (by simp)) hinv (hs x hx)
    ((contDiff_invariantScalarPhiGen f hf).differentiable (by simp) x)


end Witness

end NLQCLean

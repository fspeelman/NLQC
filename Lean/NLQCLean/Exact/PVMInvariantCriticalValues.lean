import NLQCLean.Exact.PVMScalarCriticalValues
import NLQCLean.Invariants.PVMOrbitDifferential

/-!
# Critical values of smooth measurement-orbit invariants

The exact PVM forward differential is a left-local, right-diagonal skew
motion of the basis matrix. A smooth scalar function constant on measurement
orbits annihilates it, and the cubic extension supplies all constrained
velocities, so scalar Sard makes its exact image null for each architecture.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Kronecker

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Assembly

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Along any curve of blocks through an exact PVM witness whose velocities
satisfy the linearized constraints, every differentiable measurement-orbit
invariant of the adjoint flagged overlap has zero derivative. -/
theorem hasDerivAt_invariant_pvmOverlap_zero
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) (hdiff : Differentiable ℝ f)
    (hinv : ∀ M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ N ∈ pvmBasisOrbit (Fin d) (Fin d) M, f N = f M)
    {η : ℝ → ρA × ρB → ℂ} {η' : ρA × ρB → ℂ}
    {ω : ℝ → (Fin d × Fin d) → εA × εB → ℂ} {ω' : (Fin d × Fin d) → εA × εB → ℂ}
    {VA : ℝ → Matrix (κA × μA) (Fin d × ρA) ℂ} {VA' : Matrix (κA × μA) (Fin d × ρA) ℂ}
    {VB : ℝ → Matrix (κB × μB) (Fin d × ρB) ℂ} {VB' : Matrix (κB × μB) (Fin d × ρB) ℂ}
    {DA : ℝ → Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ}
    {DA' : Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ}
    {DB : ℝ → Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ}
    {DB' : Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ}
    (hη : HasDerivAt η η' 0) (hω : HasDerivAt ω ω' 0)
    (hVA : HasDerivAt VA VA' 0) (hVB : HasDerivAt VB VB' 0)
    (hDA : HasDerivAt DA DA' 0) (hDB : HasDerivAt DB DB' 0)
    (hVAiso : IsIsometry (VA 0)) (hVBiso : IsIsometry (VB 0))
    (hDAiso : IsIsometry (DA 0)) (hDBiso : IsIsometry (DB 0))
    (hVAlin : (VA 0)ᴴ * VA' + VA'ᴴ * (VA 0) = 0)
    (hVBlin : (VB 0)ᴴ * VB' + VB'ᴴ * (VB 0) = 0)
    (hDAlin : (DA 0)ᴴ * DA' + DA'ᴴ * (DA 0) = 0)
    (hDBlin : (DB 0)ᴴ * DB' + DB'ᴴ * (DB 0) = 0)
    (hηlin : (vecInner (η 0) η').re = 0) (hωlin : ∀ i, (vecInner (ω' i) (ω 0 i)).re = 0)
    (hTco : ((flagIsometry (ω 0))ᴴ * globalIsometry (η 0) (VA 0) (VB 0) (DA 0) (DB 0)) *
        ((flagIsometry (ω 0))ᴴ * globalIsometry (η 0) (VA 0) (VB 0) (DA 0) (DB 0))ᴴ = 1)
    (hexact : globalIsometry (η 0) (VA 0) (VB 0) (DA 0) (DB 0) =
        flagIsometry (ω 0) *
          ((flagIsometry (ω 0))ᴴ * globalIsometry (η 0) (VA 0) (VB 0) (DA 0) (DB 0))) :
    HasDerivAt (fun t => f
      ((flagIsometry (ω t))ᴴ * globalIsometry (η t) (VA t) (VB t) (DA t) (DB t))ᴴ) 0 0 := by
  show HasDerivAt (fun t => f ((flagIsometry (ω t))ᴴ *
    (decoder (DA t) (DB t) * encodedState (η t) (VA t) (VB t)))ᴴ) 0 0
  set T := (flagIsometry (ω 0))ᴴ * globalIsometry (η 0) (VA 0) (VB 0) (DA 0) (DB 0) with hTdef
  have hY := hasDerivAt_encodedState (ιA := Fin d) (ιB := Fin d) hη hVA hVB
  have hWd : HasDerivAt (fun t => decoder (DA t) (DB t)) (DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0) 0 :=
    HasDerivAt.matrixKronecker hDA hDB
  have hC : HasDerivAt (fun t => (flagIsometry (ω t))ᴴ) (flagIsometry ω')ᴴ 0 :=
    HasDerivAt.matrixConjTranspose (HasDerivAt.flagIsometry hω)
  have hWY := HasDerivAt.matrixMul hWd hY
  have hH := HasDerivAt.matrixMul hC hWY
  have hWdot : DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0 =
      (ampLeft ((Fin d × Fin d) × εA) ((Fin d × Fin d) × εB) (skewLift (DA 0) DA')
        + ampRight ((Fin d × Fin d) × εA) ((Fin d × Fin d) × εB) (skewLift (DB 0) DB'))
        * decoder (DA 0) (DB 0) := by
    rw [ampLeft_apply, ampRight_apply, decoder, skewLift_kronecker_mul hDAiso hDAlin hDBiso hDBlin]
    abel
  obtain ⟨a, ha, b, hb, hval⟩ := pvmForwardDifferential_local_full
    (VA := VA 0) (VB := VB 0) (VA' := VA') (VB' := VB')
    (W := decoder (DA 0) (DB 0)) (Wdot := DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0)
    (XA := skewLift (DA 0) DA') (XB := skewLift (DB 0) DB')
    (η := η 0) (η' := η') (ω := ω 0) (ωdot := ω') (T := T)
    hVAiso hVBiso hVAlin hVBlin hηlin (isIsometry_decoder hDAiso hDBiso) hTco hexact hWdot
    (skewLift_conjTranspose hDAlin) (skewLift_conjTranspose hDBlin) hωlin
  have hderiv : (flagIsometry (ω 0))ᴴ * (decoder (DA 0) (DB 0) *
        encodedStateVelocity (η 0) η' (VA 0) VA' (VB 0) VB' +
        (DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0) * encodedState (η 0) (VA 0) (VB 0)) +
      (flagIsometry ω')ᴴ * (decoder (DA 0) (DB 0) * encodedState (η 0) (VA 0) (VB 0)) =
      b * T + T * a := by
    rw [← hval, Matrix.mul_add]
    abel
  rw [hderiv] at hH
  obtain ⟨aA, haA, aB, haB, harep⟩ := mem_localSkew_iff.mp ha
  have haskew : aᴴ = -a := mem_skewHermitian_iff.mp (localSkew_le_skewHermitian ha)
  have hbskew : bᴴ = -b := (mem_diagSkew_iff.mp hb).2
  have hneg : (-aA) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) + (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (-aB) =
      -a := by
    rw [harep]
    ext p q
    simp [Matrix.kroneckerMap_apply]
    ring
  have hvel : ∀ S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, (b * S + S * a)ᴴ =
      ((-aA) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) + (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (-aB)) * Sᴴ +
        Sᴴ * (-b) := by
    intro S
    rw [hneg, Matrix.conjTranspose_add, Matrix.conjTranspose_mul b S, Matrix.conjTranspose_mul S a,
      haskew, hbskew]
    abel
  have hHc := HasDerivAt.matrixConjTranspose hH
  rw [hvel T] at hHc
  have haA' : (-aA)ᴴ = -(-aA) := by rw [Matrix.conjTranspose_neg, haA]
  have haB' : (-aB)ᴴ = -(-aB) := by rw [Matrix.conjTranspose_neg, haB]
  have hb' : -b ∈ diagSkew (Fin d × Fin d) := Submodule.neg_mem _ hb
  have hTu : Tᴴ ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    change Tᴴᴴ * Tᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact hTco
  have hfd := (hdiff Tᴴ).hasFDerivAt
  have hzero := fderiv_eq_zero_of_pvmMotion f (hdiff Tᴴ) (hinv Tᴴ hTu) haA' haB' hb'
  have hcomp := hfd.comp_hasDerivAt 0 hHc
  simp only [Function.comp_def] at hcomp
  exact hcomp.congr_deriv hzero

/-- The smooth scalar extension `f ∘ (C_ω† F)† ∘ Q`. -/
noncomputable def pvmInvariantScalarPhi (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) : ℝ :=
  f (pvmOverlapOn (cubicPVMBlocks x))ᴴ

/-- Along every straight line through an
exact PVM witness every invariant scalar extension has zero derivative. -/
theorem hasDerivAt_pvmInvariantScalarPhi_line
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) (hdiff : Differentiable ℝ f)
    (hinv : ∀ M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ N ∈ pvmBasisOrbit (Fin d) (Fin d) M, f N = f M)
    {x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactPVMWitness x)
    (v : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) :
    HasDerivAt (fun t : ℝ => pvmInvariantScalarPhi f (x + t • v)) 0 0 := by
  have hη0 : cubicSphere (x.1 + (0 : ℝ) • v.1) = x.1 := by
    rw [zero_smul, add_zero, cubicSphere_of_isUnitVector hx.resource_unit]
  have hω0 : (fun i => cubicSphere (x.2.1 i + (0 : ℝ) • v.2.1 i)) = x.2.1 :=
    funext fun i => by rw [zero_smul, add_zero, cubicSphere_of_isUnitVector (hx.flag_unit i)]
  have hVA0 : cubicStiefel (x.2.2.1 + (0 : ℝ) • v.2.2.1) = x.2.2.1 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.encA_isometry]
  have hVB0 : cubicStiefel (x.2.2.2.1 + (0 : ℝ) • v.2.2.2.1) = x.2.2.2.1 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.encB_isometry]
  have hDA0 : cubicStiefel (x.2.2.2.2.1 + (0 : ℝ) • v.2.2.2.2.1) = x.2.2.2.2.1 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.decA_isometry]
  have hDB0 : cubicStiefel (x.2.2.2.2.2 + (0 : ℝ) • v.2.2.2.2.2) = x.2.2.2.2.2 := by
    rw [zero_smul, add_zero, cubicStiefel_of_isometry hx.decB_isometry]
  have hωd : HasDerivAt (fun t : ℝ => fun i => cubicSphere (x.2.1 i + t • v.2.1 i))
      (fun i => dCubicSphere (x.2.1 i) (v.2.1 i)) 0 :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_cubicSphere (hx.flag_unit i) (v.2.1 i)
  exact hasDerivAt_invariant_pvmOverlap_zero f hdiff hinv
    (η := fun t => cubicSphere (x.1 + t • v.1)) (η' := dCubicSphere x.1 v.1)
    (ω := fun t => fun i => cubicSphere (x.2.1 i + t • v.2.1 i))
    (ω' := fun i => dCubicSphere (x.2.1 i) (v.2.1 i))
    (VA := fun t => cubicStiefel (x.2.2.1 + t • v.2.2.1))
    (VA' := dCubicStiefel x.2.2.1 v.2.2.1)
    (VB := fun t => cubicStiefel (x.2.2.2.1 + t • v.2.2.2.1))
    (VB' := dCubicStiefel x.2.2.2.1 v.2.2.2.1)
    (DA := fun t => cubicStiefel (x.2.2.2.2.1 + t • v.2.2.2.2.1))
    (DA' := dCubicStiefel x.2.2.2.2.1 v.2.2.2.2.1)
    (DB := fun t => cubicStiefel (x.2.2.2.2.2 + t • v.2.2.2.2.2))
    (DB' := dCubicStiefel x.2.2.2.2.2 v.2.2.2.2.2)
    (hasDerivAt_cubicSphere hx.resource_unit v.1) hωd
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
    (fun i => by
      rw [zero_smul, add_zero, cubicSphere_of_isUnitVector (hx.flag_unit i), vecInner_re_comm]
      exact dCubicSphere_linearized (hx.flag_unit i) _)
    (by rw [hη0, hω0, hVA0, hVB0, hDA0, hDB0]; exact hx.overlap_coisometry)
    (by rw [hη0, hω0, hVA0, hVB0, hDA0, hDB0]; exact hx.exact)

/-- The full ambient Fréchet derivative vanishes at every exact PVM witness. -/
theorem fderiv_pvmInvariantScalarPhi_eq_zero
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) (hdiff : Differentiable ℝ f)
    (hinv : ∀ M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ N ∈ pvmBasisOrbit (Fin d) (Fin d) M, f N = f M)
    {x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactPVMWitness x)
    (hphi : DifferentiableAt ℝ (pvmInvariantScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) x) :
    fderiv ℝ (pvmInvariantScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) x = 0 :=
  fderiv_eq_zero_of_hasDerivAt_lines hphi fun v =>
    hasDerivAt_pvmInvariantScalarPhi_line f hdiff hinv hx v

theorem contDiff_pvmInvariantScalarPhi (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pvmInvariantScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) :=
  (hf.comp (ContDiff.matrixConjTranspose contDiff_pvmOverlapOn)).comp contDiff_cubicPVMBlocks

/-- For one dimension tuple, invariant values at exact PVM witnesses are null. -/
theorem volume_pvmInvariantScalarPhi_image_eq_zero
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hinv : ∀ M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ N ∈ pvmBasisOrbit (Fin d) (Fin d) M, f N = f M)
    (s : Set (PVMForwardBlocks d ρA ρB κA κB μA μB εA εB))
    (hs : ∀ x ∈ s, IsExactPVMWitness x) :
    volume (pvmInvariantScalarPhi (d := d) f '' s) = 0 := by
  refine scalarCriticalImage_volume_eq_zero (contDiff_pvmInvariantScalarPhi f hf) ?_
  intro x hx
  exact fderiv_pvmInvariantScalarPhi_eq_zero f (hf.differentiable (by simp)) hinv (hs x hx)
    ((contDiff_pvmInvariantScalarPhi f hf).differentiable (by simp) x)

end Assembly

end NLQCLean

import NLQCLean.Exact.ScalarCriticalValues
import NLQCLean.Invariants.PVMMeanPurity
import NLQCLean.Rigidity.PVMFlagDifferential
import NLQCLean.Models.ProjectiveProtocolScore
import NLQCLean.Models.ProjectiveTask

/-!
# Scalar Sard for exact two-sided PVM witnesses

On the full ambient space of PVM blocks (resource, one flag vector
per outcome label, two encoders, two decoders), apply the unchanged cubic
extension blockwise, with an independent sphere cubic for every label.
The scalar is the mean reduced purity of the adjoint forward overlap. Its
Fréchet derivative vanishes at every exact frozen PVM witness, so scalar Sard
makes the attained values null for each finite shape, and the countable union
over all shapes is null. A score-one protocol with arbitrary finite registers
places its target's invariant in that union.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Kronecker

/-- The smoothness index `∞`, pinned locally. -/
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section FlagSmooth

variable {δ εA εB : Type*} [Fintype δ] [DecidableEq δ] [Fintype εA] [Fintype εB]
variable [DecidableEq εA] [DecidableEq εB]

/-- `ω ↦ C_ω` as a `ℂ`-linear map. -/
def flagIsometryLM : (δ → εA × εB → ℂ) →ₗ[ℂ] Matrix ((δ × εA) × (δ × εB)) δ ℂ where
  toFun := flagIsometry
  map_add' := flagIsometry_add
  map_smul' := flagIsometry_smul

omit [DecidableEq εA] [DecidableEq εB] in
theorem HasDerivAt.flagIsometry {f : ℝ → δ → εA × εB → ℂ} {f' : δ → εA × εB → ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => NLQCLean.flagIsometry (f s)) (NLQCLean.flagIsometry f') t :=
  HasDerivAt.ofLinearMap ((flagIsometryLM (δ := δ) (εA := εA) (εB := εB)).restrictScalars ℝ) h

omit [DecidableEq εA] [DecidableEq εB] in
theorem ContDiff.flagIsometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : WithTop ℕ∞} {f : E → δ → εA × εB → ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => NLQCLean.flagIsometry (f x)) :=
  ContDiff.linearMapFD ((flagIsometryLM (δ := δ) (εA := εA) (εB := εB)).restrictScalars ℝ) hf

end FlagSmooth

section Assembly

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- The ambient PVM blocks: resource, per-label flags, encoders and decoders with
`D = d²` outcome labels on each side. -/
abbrev PVMForwardBlocks (d : ℕ) (ρA ρB κA κB μA μB εA εB : Type*) :=
  (ρA × ρB → ℂ) × ((Fin d × Fin d) → εA × εB → ℂ) ×
    Matrix (κA × μA) (Fin d × ρA) ℂ × Matrix (κB × μB) (Fin d × ρB) ℂ ×
    Matrix ((Fin d × Fin d) × εA) (κA × μB) ℂ × Matrix ((Fin d × Fin d) × εB) (κB × μA) ℂ

/-- The flagged forward overlap `C_ω† F` read off the ambient blocks. -/
def pvmOverlapOn (x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (flagIsometry x.2.1)ᴴ * globalIsometry x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

omit [DecidableEq ρA] [DecidableEq εA] [DecidableEq εB] in
theorem contDiff_pvmOverlapOn :
    ContDiff ℝ ∞ (pvmOverlapOn (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
      (μA := μA) (μB := μB) (εA := εA) (εB := εB)) := by
  have hη : ContDiff ℝ ∞ (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB => x.1) :=
    contDiff_fst
  have hω : ContDiff ℝ ∞ (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB => x.2.1) :=
    contDiff_fst.snd'
  have hVA : ContDiff ℝ ∞ (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB => x.2.2.1) :=
    contDiff_fst.snd'.snd'
  have hVB : ContDiff ℝ ∞ (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB => x.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'
  have hDA : ContDiff ℝ ∞
      (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB => x.2.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'.snd'
  have hDB : ContDiff ℝ ∞
      (fun x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB => x.2.2.2.2.2) :=
    contDiff_snd.snd'.snd'.snd'.snd'
  have hEeta := ContDiff.insertResource (ιA := Fin d) (ιB := Fin d) hη
  have hC := ContDiff.flagIsometry hω
  have hVV := ContDiff.matrixKronecker hVA hVB
  have hEx : ContDiff ℝ ∞ (fun _ : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB =>
      exchangeMatrix κA μA κB μB) := contDiff_const
  have hDD := ContDiff.matrixKronecker hDA hDB
  have hF := ContDiff.matrixMul hDD (ContDiff.matrixMul hEx (ContDiff.matrixMul hVV hEeta))
  exact ContDiff.matrixMul (ContDiff.matrixConjTranspose hC) hF

/-- The blockwise cubic extension, with one sphere cubic per outcome flag. -/
noncomputable def cubicPVMBlocks (x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) :
    PVMForwardBlocks d ρA ρB κA κB μA μB εA εB :=
  (cubicSphere x.1, fun i => cubicSphere (x.2.1 i), cubicStiefel x.2.2.1,
    cubicStiefel x.2.2.2.1, cubicStiefel x.2.2.2.2.1, cubicStiefel x.2.2.2.2.2)

/-- The ambient scalar: mean reduced purity of the adjoint flagged overlap. -/
noncomputable def pvmScalarPhi (c : ℝ) (x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) : ℝ :=
  pvmMeanPurity c (pvmOverlapOn (cubicPVMBlocks x))ᴴ

/-- An exact frozen PVM witness in the ambient block space. -/
structure IsExactPVMWitness (x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) : Prop where
  resource_unit : IsUnitVector x.1
  flag_unit : ∀ i, IsUnitVector (x.2.1 i)
  encA_isometry : IsIsometry x.2.2.1
  encB_isometry : IsIsometry x.2.2.2.1
  decA_isometry : IsIsometry x.2.2.2.2.1
  decB_isometry : IsIsometry x.2.2.2.2.2
  overlap_coisometry : pvmOverlapOn x * (pvmOverlapOn x)ᴴ = 1
  exact : globalIsometry x.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 =
    flagIsometry x.2.1 * pvmOverlapOn x

omit [DecidableEq εA] [DecidableEq εB] in
theorem cubicPVMBlocks_of_isExactPVMWitness
    {x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactPVMWitness x) :
    cubicPVMBlocks x = x := by
  have hω : (fun i => cubicSphere (x.2.1 i)) = x.2.1 :=
    funext fun i => cubicSphere_of_isUnitVector (hx.flag_unit i)
  rw [cubicPVMBlocks, cubicSphere_of_isUnitVector hx.resource_unit, hω,
    cubicStiefel_of_isometry hx.encA_isometry, cubicStiefel_of_isometry hx.encB_isometry,
    cubicStiefel_of_isometry hx.decA_isometry, cubicStiefel_of_isometry hx.decB_isometry]

/-- Along any curve of blocks through an exact PVM
witness whose velocities satisfy the linearized constraints, the invariant of the
adjoint flagged overlap has zero derivative. -/
theorem hasDerivAt_pvmMeanPurity_overlap_zero (c : ℝ)
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
    HasDerivAt (fun t => pvmMeanPurity c
      ((flagIsometry (ω t))ᴴ * globalIsometry (η t) (VA t) (VB t) (DA t) (DB t))ᴴ) 0 0 := by
  show HasDerivAt (fun t => pvmMeanPurity c ((flagIsometry (ω t))ᴴ *
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
  have hcd : ContDiff ℝ ∞ (pvmMeanPurity (ι := Fin d) c) :=
    ContDiff.pvmMeanPurity c (contDiff_id (𝕜 := ℝ) (E := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))
  have hdiff : Differentiable ℝ (pvmMeanPurity (ι := Fin d) c) := hcd.differentiable (by simp)
  have hfd := (hdiff Tᴴ).hasFDerivAt
  have hline := hfd.comp_hasDerivAt_of_eq (x := (0 : ℝ))
    (hasDerivAt_line Tᴴ (((-aA) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) +
      (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (-aB)) * Tᴴ + Tᴴ * (-b))) (by simp)
  have hzero := hline.unique (hasDerivAt_pvmMeanPurity_motion c Tᴴ haA' haB' hb')
  have hcomp := hfd.comp_hasDerivAt 0 hHc
  rw [hzero] at hcomp
  simp only [Function.comp_def] at hcomp
  exact hcomp

/-- Along every straight line through an
exact PVM witness the ambient scalar has zero derivative. -/
theorem hasDerivAt_pvmScalarPhi_line (c : ℝ)
    {x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactPVMWitness x)
    (v : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) :
    HasDerivAt (fun t : ℝ => pvmScalarPhi c (x + t • v)) 0 0 := by
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
  exact hasDerivAt_pvmMeanPurity_overlap_zero c
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
theorem fderiv_pvmScalarPhi_eq_zero (c : ℝ)
    {x : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactPVMWitness x)
    (hdiff : DifferentiableAt ℝ (pvmScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) c) x) :
    fderiv ℝ (pvmScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) c) x = 0 :=
  fderiv_eq_zero_of_hasDerivAt_lines hdiff fun v => hasDerivAt_pvmScalarPhi_line c hx v

theorem contDiff_cubicPVMBlocks :
    ContDiff ℝ ∞ (cubicPVMBlocks (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB)) := by
  refine ContDiff.prodMk (contDiff_cubicSphere.comp contDiff_fst) ?_
  refine ContDiff.prodMk (contDiff_pi.mpr fun i =>
    contDiff_cubicSphere.comp ((contDiff_pi.mp (contDiff_id (𝕜 := ℝ)) i).comp
      (contDiff_fst.comp contDiff_snd))) ?_
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

theorem contDiff_pvmScalarPhi (c : ℝ) :
    ContDiff ℝ ∞ (pvmScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) c) :=
  (ContDiff.pvmMeanPurity c (ContDiff.matrixConjTranspose contDiff_pvmOverlapOn)).comp
    contDiff_cubicPVMBlocks

/-- For one shape, invariant values at exact PVM witnesses are null by scalar Sard. -/
theorem volume_pvmScalarPhi_image_eq_zero (c : ℝ)
    (s : Set (PVMForwardBlocks d ρA ρB κA κB μA μB εA εB))
    (hs : ∀ x ∈ s, IsExactPVMWitness x) :
    volume (pvmScalarPhi (d := d) c '' s) = 0 := by
  refine scalarCriticalImage_volume_eq_zero (contDiff_pvmScalarPhi c) ?_
  intro x hx
  exact fderiv_pvmScalarPhi_eq_zero c (hs x hx)
    ((contDiff_pvmScalarPhi c).differentiable (by simp) x)

end Assembly

section AllArchitectures

/-- The ambient PVM blocks for a tuple of cardinalities `R_A,R_B,K_A,K_B,M_A,M_B,E_A,E_B`. -/
abbrev PVMShapeBlocks (d : ℕ) (s : Fin 8 → ℕ) :=
  PVMForwardBlocks d (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
    (Fin (s 4)) (Fin (s 5)) (Fin (s 6)) (Fin (s 7))

/-- The union over **all** finite shapes of exact-witness invariant values,
chosen before any target or resource budget. Normalization `D⁻¹ = d⁻²`. -/
def exactPVMPurityValues (d : ℕ) : Set ℝ :=
  ⋃ s : Fin 8 → ℕ,
    pvmScalarPhi ((d : ℝ) ^ 2)⁻¹ '' {x : PVMShapeBlocks d s | IsExactPVMWitness x}

theorem volume_exactPVMPurityValues_eq_zero (d : ℕ) :
    volume (exactPVMPurityValues d) = 0 := by
  apply volume_iUnion_eq_zero
  intro s
  exact volume_pvmScalarPhi_image_eq_zero _ _ (fun _ hx => hx)

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- A score-one pure PVM protocol with arbitrary finite registers
places the target's mean reduced purity in the null union. -/
theorem PureProtocol.pvmMeanPurity_mem_of_scorePVM_eq_one [NeZero d]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : IsIsometry M)
    (hscore : scorePVM M P.operationalChannel = 1) :
    pvmMeanPurity ((d : ℝ) ^ 2)⁻¹ M ∈ exactPVMPurityValues d := by
  let s : Fin 8 → ℕ := ![Fintype.card ρA, Fintype.card ρB, Fintype.card κA, Fintype.card κB,
    Fintype.card μA, Fintype.card μB, Fintype.card εA, Fintype.card εB]
  let Q := P.reindex (Fintype.equivFin ρA).symm (Fintype.equivFin ρB).symm
    (Fintype.equivFin κA).symm (Fintype.equivFin κB).symm (Fintype.equivFin μA).symm
    (Fintype.equivFin μB).symm (Fintype.equivFin εA).symm (Fintype.equivFin εB).symm
  have hQscore : scorePVM M Q.operationalChannel = 1 := by
    rw [P.operationalChannel_reindex]; exact hscore
  have htask : Q.PerformsPVM M := (Q.scorePVM_eq_one_iff_performsPVM hM).mp hQscore
  have hM' : M * Mᴴ = 1 := mul_eq_one_comm.mp hM
  obtain ⟨ω, hω, hF, -⟩ := Q.exists_frozen_pvm hM hM' htask
  let x : PVMShapeBlocks d s := (Q.resource, ω, Q.encA, Q.encB, Q.decA, Q.decB)
  have hCC : (flagIsometry ω)ᴴ * flagIsometry ω = 1 := isIsometry_flagIsometry ω hω
  have hT : pvmOverlapOn x = Mᴴ := by
    change (flagIsometry ω)ᴴ * Q.globalIsometry = Mᴴ
    rw [hF, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
  have hx : IsExactPVMWitness x := by
    refine ⟨Q.resource_unit, hω, Q.encA_isometry, Q.encB_isometry, Q.decA_isometry,
      Q.decB_isometry, ?_, ?_⟩
    · rw [hT, Matrix.conjTranspose_conjTranspose]; exact hM
    · rw [hT]; exact hF
  apply Set.mem_iUnion.mpr
  refine ⟨s, x, hx, ?_⟩
  rw [pvmScalarPhi, cubicPVMBlocks_of_isExactPVMWitness hx, hT, Matrix.conjTranspose_conjTranspose]

end AllArchitectures

end NLQCLean

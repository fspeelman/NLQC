import NLQCLean.Exact.ScalarCriticalValues
import NLQCLean.Invariants.LocalOrbitDifferential

/-!
# Critical values of smooth local-unitary invariants

The exact forward differential has a local-unitary orbit tangent. A smooth
scalar invariant annihilates this tangent, and the cubic extension supplies
all constrained velocities. Scalar Sard therefore makes its exact image null.
-/

namespace NLQCLean
open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Kronecker
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)
variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

theorem hasDerivAt_invariant_forwardOverlap_zero (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (hdiff : Differentiable ℝ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, f V = f U)
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
      (fun t => f (forwardOverlap (η t) (g t) (VA t) (VB t) (DA t) (DB t)))
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
noncomputable def invariantScalarPhi (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (x : BalancedBlocks d ρA ρB κA κB μA μB εA εB) : ℝ :=
  f (forwardOverlapOn (cubicBlocks x))

/-- Along *every* straight line
through an exact witness -- with no tangency hypothesis on the direction --
the ambient scalar function `φ` has zero derivative. The cubic
extension makes `DQ_x[v]` satisfy the linearized constraints for
every `v`, so the exact-witness derivative lemma applies. -/
theorem hasDerivAt_invariantScalarPhi_line (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (hdiff : Differentiable ℝ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, f V = f U)
    {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactWitness x)
    (v : BalancedBlocks d ρA ρB κA κB μA μB εA εB) :
    HasDerivAt (fun t : ℝ => invariantScalarPhi f (x + t • v)) 0 0 := by
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
  exact hasDerivAt_invariant_forwardOverlap_zero f hdiff hinv
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
theorem fderiv_invariantScalarPhi_eq_zero (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (hdiff : Differentiable ℝ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, f V = f U)
    {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB} (hx : IsExactWitness x)
    (hphi : DifferentiableAt ℝ (invariantScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) x) :
    fderiv ℝ (invariantScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) x = 0 :=
  fderiv_eq_zero_of_hasDerivAt_lines hphi fun v =>
    hasDerivAt_invariantScalarPhi_line f hdiff hinv hx v

/-!
### Smoothness of `φ`, and the Sard step
-/

/-- A smooth scalar invariant remains smooth after the cubic forward map. -/
theorem contDiff_invariantScalarPhi (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (invariantScalarPhi (d := d) (ρA := ρA) (ρB := ρB)
      (κA := κA) (κB := κB) (μA := μA) (μB := μB) (εA := εA) (εB := εB) f) :=
  (hf.comp contDiff_forwardOverlapOn).comp contDiff_cubicBlocks

/-- For one dimension tuple, the critical image of the exact witnesses
is Lebesgue-null.  This is scalar Sard applied to `φ`; no measurability or
regularity of the witness set is required. -/
theorem volume_invariantScalarPhi_image_eq_zero (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hinv : ∀ U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      ∀ V ∈ unitaryDoubleOrbit (Fin d) (Fin d) U, f V = f U)
    (s : Set (BalancedBlocks d ρA ρB κA κB μA μB εA εB))
    (hs : ∀ x ∈ s, IsExactWitness x) :
    volume (invariantScalarPhi (d := d) f '' s) = 0 := by
  refine scalarCriticalImage_volume_eq_zero (contDiff_invariantScalarPhi f hf) ?_
  intro x hx
  exact fderiv_invariantScalarPhi_eq_zero f (hf.differentiable (by simp)) hinv (hs x hx)
    ((contDiff_invariantScalarPhi f hf).differentiable (by simp) x)


section AllArchitectures

/-- Every finite architecture's values, with no restriction on internal dimensions. -/
def exactInvariantValues (d : ℕ)
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) : Set ℝ :=
  ⋃ s : ForwardShape,
    invariantScalarPhi f '' {x : ShapeBlocks d s | IsExactWitness x}

omit [DecidableEq εA] [DecidableEq εB] in
/-- Every exact witness on arbitrary finite
register types has its invariant value in the same countable union. -/
theorem invariant_mem_exactInvariantValues
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ) {x : BalancedBlocks d ρA ρB κA κB μA μB εA εB}
    (hx : IsExactWitness x) :
    f (forwardOverlapOn x) ∈ exactInvariantValues d f := by
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
  rw [invariantScalarPhi, cubicBlocks_of_isExactWitness hy, hH]

/-- A score-one physical protocol gives an exact witness, so its target
invariant value belongs to the union over all finite shapes. This uses the existing
normalized Choi score and the exact-freezing identity. -/
theorem PureProtocol.invariant_mem_exactInvariantValues_of_score_eq_one [NeZero d]
    (f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℝ)
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB)
    {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hU : UnitaryTarget U) (hscore : scoreU U P.operationalChannel = 1) :
    f U ∈ exactInvariantValues d f := by
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
  simpa only [hH] using invariant_mem_exactInvariantValues f hx


end AllArchitectures

end NLQCLean

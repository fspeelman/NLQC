import NLQCLean.Exact.PVMFiniteOrbits
import NLQCLean.Exact.InvariantCriticalValues
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Derivatives along differentiable families of exact strategies

Along a family of exact strategies differentiable at `t`, the constraint
equations hold near `t`, so their linearizations hold at `t`. The forward
differential then gives `prop:derivative`: the implemented unitary moves by
`U̇ = -b U + U a` with local skew-Hermitian `a, b`. For measurement strategies
the generators are explicit polynomials in the blocks and their velocities:
`Ṁ = -a M + M b` with `a` local and `b` diagonal skew-Hermitian, and both
depend continuously on time along a continuously differentiable family
(`prop:derivative-pvm`).
-/

noncomputable section

namespace NLQCLean

open Matrix Filter
open scoped Matrix.Norms.Frobenius Kronecker Topology

section Linearization

/-- A family of isometries satisfies the linearized isometry constraint. -/
theorem linearized_isometry_of_eventually {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {V : ℝ → Matrix m n ℂ} {V' : Matrix m n ℂ} {t : ℝ} (hV : HasDerivAt V V' t)
    (h : ∀ᶠ τ in 𝓝 t, IsIsometry (V τ)) : (V t)ᴴ * V' + V'ᴴ * V t = 0 := by
  have hd := HasDerivAt.matrixMul (HasDerivAt.matrixConjTranspose hV) hV
  have hc : HasDerivAt (fun τ => (V τ)ᴴ * V τ) 0 t :=
    (hasDerivAt_const t (1 : Matrix n n ℂ)).congr_of_eventuallyEq (h.mono fun τ hτ => hτ)
  exact hd.unique hc

/-- The column matrix of a vector. -/
def colMatrix {ε : Type*} (v : ε → ℂ) : Matrix ε Unit ℂ := Matrix.of fun e _ => v e

/-- `v ↦ col v` as a real linear map. -/
def colMatrixLM (ε : Type*) : (ε → ℂ) →ₗ[ℝ] Matrix ε Unit ℂ where
  toFun := colMatrix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isIsometry_colMatrix {ε : Type*} [Fintype ε] {v : ε → ℂ} (hv : IsUnitVector v) :
    IsIsometry (colMatrix v) := by
  ext i j
  have h := (isUnitVector_iff_sum v).mp hv
  simp only [colMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply, Subsingleton.elim i j, ite_true]
  rw [← h]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

/-- A family of unit vectors satisfies the linearized normalization. -/
theorem linearized_unit_of_eventually {ε : Type*} [Fintype ε]
    {η : ℝ → ε → ℂ} {η' : ε → ℂ} {t : ℝ} (hη : HasDerivAt η η' t)
    (h : ∀ᶠ τ in 𝓝 t, IsUnitVector (η τ)) : (vecInner (η t) η').re = 0 := by
  have hc : HasDerivAt (fun τ => colMatrix (η τ)) (colMatrix η') t :=
    HasDerivAt.ofLinearMap (colMatrixLM ε) hη
  have hlin := linearized_isometry_of_eventually hc (h.mono fun τ hτ => isIsometry_colMatrix hτ)
  have hentry := congrFun (congrFun hlin ()) ()
  simp only [colMatrix, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.zero_apply] at hentry
  have h1 : vecInner (η t) η' + vecInner η' (η t) = 0 := by
    rw [← hentry]
    simp [vecInner]
  have h2 := congrArg Complex.re h1
  rw [Complex.add_re, Complex.zero_re, vecInner_re_comm (η t) η'] at h2
  linarith

end Linearization

section Components

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem HasDerivAt.prodFst' {γ : ℝ → E × F} {γ' : E × F} {t : ℝ} (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun τ => (γ τ).1) γ'.1 t :=
  HasDerivAt.ofLinearMap (LinearMap.fst ℝ E F) h

theorem HasDerivAt.prodSnd' {γ : ℝ → E × F} {γ' : E × F} {t : ℝ} (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun τ => (γ τ).2) γ'.2 t :=
  HasDerivAt.ofLinearMap (LinearMap.snd ℝ E F) h

end Components

section UnitaryDerivative

variable {d : ℕ}

/-- **`prop:derivative`.** Along a family of exact strategies of one
architecture, differentiable at `t`, the implemented unitary has velocity
`U̇ = -b U + U a` with `a, b` in the local skew-Hermitian algebra. -/
theorem exists_localSkew_target_velocity (s : ForwardShape)
    {γ : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s}
    {γ' : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) (hmem : ∀ᶠ τ in 𝓝 t, γ τ ∈ targetExactWitnessSet d s) :
    ∃ a ∈ localSkew (Fin d) (Fin d), ∃ b ∈ localSkew (Fin d) (Fin d),
      γ'.1 = -b * (γ t).1 + (γ t).1 * a := by
  -- Time-shifted block families.
  let η : ℝ → _ := fun u => (γ (t + u)).2.1
  let g : ℝ → _ := fun u => (γ (t + u)).2.2.1
  let VA : ℝ → _ := fun u => (γ (t + u)).2.2.2.1
  let VB : ℝ → _ := fun u => (γ (t + u)).2.2.2.2.1
  let DA : ℝ → _ := fun u => (γ (t + u)).2.2.2.2.2.1
  let DB : ℝ → _ := fun u => (γ (t + u)).2.2.2.2.2.2
  have hγ0 : HasDerivAt (fun u => γ (t + u)) γ' 0 :=
    HasDerivAt.comp_const_add t 0 (by rw [add_zero]; exact hγ)
  have hmem0 : ∀ᶠ u in 𝓝 (0 : ℝ), γ (t + u) ∈ targetExactWitnessSet d s := by
    have hc : Tendsto (fun u : ℝ => t + u) (𝓝 0) (𝓝 t) := by
      simpa using (continuous_const_add t).tendsto 0
    exact hc.eventually hmem
  have hη : HasDerivAt η γ'.2.1 0 := (HasDerivAt.prodFst' (HasDerivAt.prodSnd' hγ0))
  have hg : HasDerivAt g γ'.2.2.1 0 := (HasDerivAt.prodFst' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0)))
  have hVA : HasDerivAt VA γ'.2.2.2.1 0 := (HasDerivAt.prodFst' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0))))
  have hVB : HasDerivAt VB γ'.2.2.2.2.1 0 := (HasDerivAt.prodFst' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0)))))
  have hDA : HasDerivAt DA γ'.2.2.2.2.2.1 0 :=
    (HasDerivAt.prodFst' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0))))))
  have hDB : HasDerivAt DB γ'.2.2.2.2.2.2 0 :=
    (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0))))))
  have hU : HasDerivAt (fun u => (γ (t + u)).1) γ'.1 0 := (HasDerivAt.prodFst' hγ0)
  obtain ⟨⟨⟨hη0, hVA0, hVB0, hDA0, hDB0⟩, hg0, hU0, hfreeze0⟩⟩ :=
    (⟨hmem0.self_of_nhds⟩ : Nonempty (γ (t + 0) ∈ targetExactWitnessSet d s))
  have hx0 := ((mem_targetExactWitnessSet_iff d s _).mp hmem0.self_of_nhds)
  -- Linearized constraints at time zero.
  have hηlin := linearized_unit_of_eventually hη (hmem0.mono fun u hu => hu.1.1)
  have hglin := linearized_unit_of_eventually hg (hmem0.mono fun u hu => hu.2.1)
  have hVAlin := linearized_isometry_of_eventually hVA (hmem0.mono fun u hu => hu.1.2.1)
  have hVBlin := linearized_isometry_of_eventually hVB (hmem0.mono fun u hu => hu.1.2.2.1)
  have hDAlin := linearized_isometry_of_eventually hDA (hmem0.mono fun u hu => hu.1.2.2.2.1)
  have hDBlin := linearized_isometry_of_eventually hDB (hmem0.mono fun u hu => hu.1.2.2.2.2)
  -- The target agrees with the forward overlap near zero.
  have hfun : (fun u => (γ (t + u)).1) =ᶠ[𝓝 0]
      fun u => forwardOverlap (η u) (g u) (VA u) (VB u) (DA u) (DB u) :=
    hmem0.mono fun u hu => ((mem_targetExactWitnessSet_iff d s _).mp hu).2.symm
  have hH := hasDerivAt_forwardOverlap hη hg hVA hVB hDA hDB
  have hval := hU.unique (hH.congr_of_eventuallyEq hfun)
  set W := (decoder (DA 0) (DB 0)).submatrix (outputRegroup (Fin d) (Fin d)
    (Fin (s 6)) (Fin (s 7))) id with hWdef
  have hbij : Function.Bijective (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) :=
    (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))).bijective
  have hWdot : ((DA 0 ⊗ₖ γ'.2.2.2.2.2.2 + γ'.2.2.2.2.2.1 ⊗ₖ DB 0).submatrix
        (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) id)
      = (ampLeft (Fin d × Fin (s 6)) (Fin d × Fin (s 7)) (skewLift (DA 0) γ'.2.2.2.2.2.1)
          + ampRight (Fin d × Fin (s 6)) (Fin d × Fin (s 7)) (skewLift (DB 0) γ'.2.2.2.2.2.2)).submatrix
          (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)))
          (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)))
        * W := by
    rw [hWdef, decoder, ← Matrix.submatrix_mul _ _ _ _ _ hbij, ampLeft_apply,
      ampRight_apply, skewLift_kronecker_mul hDA0 hDAlin hDB0 hDBlin]
    congr 1
    abel
  rw [hWdot] at hval
  have hU' : (γ (t + 0)).1 = forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0) :=
    hx0.2.symm
  obtain ⟨a, ha, b, hb, hab⟩ := forwardDifferential_local_full
    (VA := VA 0) (VB := VB 0) (VA' := γ'.2.2.2.1) (VB' := γ'.2.2.2.2.1)
    (W := W) (XA := skewLift (DA 0) γ'.2.2.2.2.2.1) (XB := skewLift (DB 0) γ'.2.2.2.2.2.2)
    (η := η 0) (η' := γ'.2.1) (g := g 0) (gdot := γ'.2.2.1)
    (U := forwardOverlap (η 0) (g 0) (VA 0) (VB 0) (DA 0) (DB 0))
    hVA0 hVB0 hVAlin hVBlin hηlin
    ((isIsometry_decoder hDA0 hDB0).submatrix_equiv _ (Equiv.refl _))
    (by rw [← hU']; exact hU0)
    (by rw [← globalIsometryRegrouped_eq, ← hU']; exact hfreeze0) rfl
    (skewLift_conjTranspose hDAlin) (skewLift_conjTranspose hDBlin)
    (by rw [vecInner_re_comm]; exact hglin)
  refine ⟨a, ha, -b, Submodule.neg_mem _ hb, ?_⟩
  rw [hval, hab, ← hU', show t + 0 = t by ring, neg_neg]

end UnitaryDerivative

section MeasurementDerivative

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- The input generator `a = Y† Ẏ` of a measurement strategy `x` moving with
velocity `v`. -/
def pvmInputGenerator (x v : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (encodedState (ιA := Fin d) (ιB := Fin d) x.1 x.2.2.1 x.2.2.2.1)ᴴ *
    encodedStateVelocity x.1 v.1 x.2.2.1 v.2.2.1 x.2.2.2.1 v.2.2.2.1

/-- The decoder-side local generator. -/
def pvmDecoderGenerator (x v : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) :
    Matrix (((Fin d × Fin d) × εA) × ((Fin d × Fin d) × εB))
      (((Fin d × Fin d) × εA) × ((Fin d × Fin d) × εB)) ℂ :=
  ampLeft ((Fin d × Fin d) × εA) ((Fin d × Fin d) × εB) (skewLift x.2.2.2.2.1 v.2.2.2.2.1) +
    ampRight ((Fin d × Fin d) × εA) ((Fin d × Fin d) × εB) (skewLift x.2.2.2.2.2 v.2.2.2.2.2)

/-- The outcome generator `b`, diagonal skew-Hermitian, in the source's sign. -/
def pvmOutcomeGenerator (x v : PVMForwardBlocks d ρA ρB κA κB μA μB εA εB) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  -((flagIsometry v.2.1)ᴴ * flagIsometry x.2.1 +
    (flagIsometry x.2.1)ᴴ * pvmDecoderGenerator x v * flagIsometry x.2.1)

section Continuity

local notation "PB" => PVMForwardBlocks d ρA ρB κA κB μA μB εA εB

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

omit [DecidableEq εA] [DecidableEq εB] in
theorem contDiff_skewLift {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V Z : E → Matrix m n ℂ} (hV : ContDiff ℝ ∞ V) (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (fun p => skewLift (V p) (Z p)) := by
  unfold skewLift
  exact ((ContDiff.matrixMul hZ (ContDiff.matrixConjTranspose hV)).sub
    (ContDiff.matrixMul hV (ContDiff.matrixConjTranspose hZ))).sub
    (ContDiff.matrixMul (ContDiff.matrixMul hV (ContDiff.matrixMul
      (ContDiff.matrixConjTranspose hV) hZ)) (ContDiff.matrixConjTranspose hV))

omit [DecidableEq ρA] in
theorem contDiff_pvmGenerators :
    ContDiff ℝ ∞ (fun p : PB × PB => pvmInputGenerator p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : PB × PB => pvmOutcomeGenerator p.1 p.2) := by
  have h1 : ContDiff ℝ ∞ (fun p : PB × PB => p.1) := contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun p : PB × PB => p.2) := contDiff_snd
  have hη := h1.fst
  have hη' := h2.fst
  have hω := h1.snd.fst
  have hω' := h2.snd.fst
  have hVA := h1.snd.snd.fst
  have hVA' := h2.snd.snd.fst
  have hVB := h1.snd.snd.snd.fst
  have hVB' := h2.snd.snd.snd.fst
  have hDA := h1.snd.snd.snd.snd.fst
  have hDA' := h2.snd.snd.snd.snd.fst
  have hDB := h1.snd.snd.snd.snd.snd
  have hDB' := h2.snd.snd.snd.snd.snd
  have hEx : ContDiff ℝ ∞ (fun _ : PB × PB => exchangeMatrix κA μA κB μB) := contDiff_const
  have hY : ContDiff ℝ ∞ (fun p : PB × PB =>
      encodedState (ιA := Fin d) (ιB := Fin d) p.1.1 p.1.2.2.1 p.1.2.2.2.1) :=
    ContDiff.matrixMul hEx (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB)
      (ContDiff.insertResource hη))
  have hYdot : ContDiff ℝ ∞ (fun p : PB × PB =>
      encodedStateVelocity (ιA := Fin d) (ιB := Fin d) p.1.1 p.2.1 p.1.2.2.1 p.2.2.2.1
        p.1.2.2.2.1 p.2.2.2.2.1) :=
    ContDiff.matrixMul hEx (ContDiff.add (ContDiff.matrixMul (ContDiff.add
      (ContDiff.matrixKronecker hVA hVB') (ContDiff.matrixKronecker hVA' hVB))
      (ContDiff.insertResource hη))
      (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB) (ContDiff.insertResource hη')))
  have hC := ContDiff.flagIsometry (εA := εA) (εB := εB) hω
  have hC' := ContDiff.flagIsometry (εA := εA) (εB := εB) hω'
  have hG : ContDiff ℝ ∞ (fun p : PB × PB => pvmDecoderGenerator p.1 p.2) := by
    simp only [pvmDecoderGenerator, ampLeft_apply, ampRight_apply]
    exact (ContDiff.matrixKronecker (contDiff_skewLift hDA hDA') contDiff_const).add
      (ContDiff.matrixKronecker contDiff_const (contDiff_skewLift hDB hDB'))
  refine ⟨ContDiff.matrixMul (ContDiff.matrixConjTranspose hY) hYdot, ?_⟩
  exact ((ContDiff.matrixMul (ContDiff.matrixConjTranspose hC') hC).add
    (ContDiff.matrixMul (ContDiff.matrixMul (ContDiff.matrixConjTranspose hC) hG) hC)).neg

omit [DecidableEq ρA] in
theorem ContDiffOn.pvmGenerators {J : Set ℝ} {x v : ℝ → PB}
    (hx : ContDiffOn ℝ 0 x J) (hv : ContDiffOn ℝ 0 v J) :
    ContinuousOn (fun t => pvmInputGenerator (x t) (v t)) J ∧
      ContinuousOn (fun t => pvmOutcomeGenerator (x t) (v t)) J := by
  have h := contDiff_pvmGenerators (d := d) (ρA := ρA) (ρB := ρB) (κA := κA) (κB := κB)
    (μA := μA) (μB := μB) (εA := εA) (εB := εB)
  have hxv : ContDiffOn ℝ 0 (fun t => (x t, v t)) J := hx.prodMk hv
  have h1 : ContDiff ℝ 0 (fun p : PB × PB => pvmInputGenerator p.1 p.2) := h.1.of_le (by simp)
  have h2 : ContDiff ℝ 0 (fun p : PB × PB => pvmOutcomeGenerator p.1 p.2) := h.2.of_le (by simp)
  have c1 : ContDiffOn ℝ 0 ((fun p : PB × PB => pvmInputGenerator p.1 p.2) ∘
      (fun t => (x t, v t))) J := h1.comp_contDiffOn hxv
  have c2 : ContDiffOn ℝ 0 ((fun p : PB × PB => pvmOutcomeGenerator p.1 p.2) ∘
      (fun t => (x t, v t))) J := h2.comp_contDiffOn hxv
  exact ⟨(contDiffOn_zero.mp c1).congr fun t _ => rfl,
    (contDiffOn_zero.mp c2).congr fun t _ => rfl⟩

end Continuity

/-- **`prop:derivative-pvm`, pointwise.** Along a family of exact measurement
strategies differentiable at `t`, the basis matrix moves by `Ṁ = -a M + M b`
with `a` local and `b` diagonal skew-Hermitian, given by the explicit
generators. -/
theorem pvm_target_velocity (s : Fin 8 → ℕ)
    {γ : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s}
    {γ' : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) (hmem : ∀ᶠ τ in 𝓝 t, γ τ ∈ pvmTargetWitnessSet d s) :
    pvmInputGenerator (γ t).2 γ'.2 ∈ localSkew (Fin d) (Fin d) ∧
      pvmOutcomeGenerator (γ t).2 γ'.2 ∈ diagSkew (Fin d × Fin d) ∧
      γ'.1 = -pvmInputGenerator (γ t).2 γ'.2 * (γ t).1 +
        (γ t).1 * pvmOutcomeGenerator (γ t).2 γ'.2 := by
  let η : ℝ → _ := fun u => (γ (t + u)).2.1
  let ω : ℝ → _ := fun u => (γ (t + u)).2.2.1
  let VA : ℝ → _ := fun u => (γ (t + u)).2.2.2.1
  let VB : ℝ → _ := fun u => (γ (t + u)).2.2.2.2.1
  let DA : ℝ → _ := fun u => (γ (t + u)).2.2.2.2.2.1
  let DB : ℝ → _ := fun u => (γ (t + u)).2.2.2.2.2.2
  have hγ0 : HasDerivAt (fun u => γ (t + u)) γ' 0 :=
    HasDerivAt.comp_const_add t 0 (by rw [add_zero]; exact hγ)
  have hmem0 : ∀ᶠ u in 𝓝 (0 : ℝ), γ (t + u) ∈ pvmTargetWitnessSet d s := by
    have hc : Tendsto (fun u : ℝ => t + u) (𝓝 0) (𝓝 t) := by
      simpa using (continuous_const_add t).tendsto 0
    exact hc.eventually hmem
  have hη : HasDerivAt η γ'.2.1 0 := HasDerivAt.prodFst' (HasDerivAt.prodSnd' hγ0)
  have hω : HasDerivAt ω γ'.2.2.1 0 :=
    HasDerivAt.prodFst' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0))
  have hVA : HasDerivAt VA γ'.2.2.2.1 0 :=
    HasDerivAt.prodFst' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0)))
  have hVB : HasDerivAt VB γ'.2.2.2.2.1 0 := HasDerivAt.prodFst' (HasDerivAt.prodSnd'
    (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0))))
  have hDA : HasDerivAt DA γ'.2.2.2.2.2.1 0 := HasDerivAt.prodFst' (HasDerivAt.prodSnd'
    (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0)))))
  have hDB : HasDerivAt DB γ'.2.2.2.2.2.2 0 := HasDerivAt.prodSnd' (HasDerivAt.prodSnd'
    (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' (HasDerivAt.prodSnd' hγ0)))))
  have hM : HasDerivAt (fun u => (γ (t + u)).1) γ'.1 0 := HasDerivAt.prodFst' hγ0
  have hx0 : γ (t + 0) ∈ pvmTargetWitnessSet d s := hmem0.self_of_nhds
  rw [add_zero] at hx0
  have hw := hx0.1
  have hT : pvmOverlapOn (γ t).2 = (γ t).1ᴴ := by
    rw [← hx0.2, Matrix.conjTranspose_conjTranspose]
  -- Linearized constraints.
  have hηlin := linearized_unit_of_eventually hη (hmem0.mono fun u hu => hu.1.resource_unit)
  have hωlin : ∀ i, (vecInner (γ'.2.2.1 i) (ω 0 i)).re = 0 := by
    intro i
    rw [vecInner_re_comm]
    exact linearized_unit_of_eventually (HasDerivAt.ofLinearMap
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin d × Fin d => Fin (s 6) × Fin (s 7) → ℂ) i) hω)
      (hmem0.mono fun u hu => hu.1.flag_unit i)
  have hVAlin := linearized_isometry_of_eventually hVA
    (hmem0.mono fun u hu => hu.1.encA_isometry)
  have hVBlin := linearized_isometry_of_eventually hVB
    (hmem0.mono fun u hu => hu.1.encB_isometry)
  have hDAlin := linearized_isometry_of_eventually hDA
    (hmem0.mono fun u hu => hu.1.decA_isometry)
  have hDBlin := linearized_isometry_of_eventually hDB
    (hmem0.mono fun u hu => hu.1.decB_isometry)
  simp only [η, ω, VA, VB, DA, DB, add_zero] at hηlin hωlin hVAlin hVBlin hDAlin hDBlin
  -- Derivative of the flagged overlap.
  have hY := hasDerivAt_encodedState (ιA := Fin d) (ιB := Fin d) hη hVA hVB
  have hWd : HasDerivAt (fun u => decoder (DA u) (DB u))
      (DA 0 ⊗ₖ γ'.2.2.2.2.2.2 + γ'.2.2.2.2.2.1 ⊗ₖ DB 0) 0 :=
    HasDerivAt.matrixKronecker hDA hDB
  have hC : HasDerivAt (fun u => (flagIsometry (ω u))ᴴ) (flagIsometry γ'.2.2.1)ᴴ 0 :=
    HasDerivAt.matrixConjTranspose (HasDerivAt.flagIsometry hω)
  have hH := HasDerivAt.matrixMul hC (HasDerivAt.matrixMul hWd hY)
  have hfun : (fun u => (γ (t + u)).1) =ᶠ[𝓝 0]
      fun u => ((flagIsometry (ω u))ᴴ * (decoder (DA u) (DB u) *
        encodedState (η u) (VA u) (VB u)))ᴴ := by
    refine hmem0.mono fun u hu => ?_
    show (γ (t + u)).1 = _
    rw [← hu.2]
    rfl
  have hval := hM.unique ((HasDerivAt.matrixConjTranspose hH).congr_of_eventuallyEq hfun)
  simp only [η, ω, VA, VB, DA, DB, add_zero] at hval
  set x := (γ t).2
  have hWdot : x.2.2.2.2.1 ⊗ₖ γ'.2.2.2.2.2.2 + γ'.2.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2 =
      pvmDecoderGenerator x γ'.2 * decoder x.2.2.2.2.1 x.2.2.2.2.2 := by
    rw [pvmDecoderGenerator, ampLeft_apply, ampRight_apply, decoder,
      skewLift_kronecker_mul hw.decA_isometry hDAlin hw.decB_isometry hDBlin]
    abel
  have hexact : decoder x.2.2.2.2.1 x.2.2.2.2.2 * encodedState x.1 x.2.2.1 x.2.2.2.1 =
      flagIsometry x.2.1 * pvmOverlapOn x := hw.exact
  have hTco : pvmOverlapOn x * (pvmOverlapOn x)ᴴ = 1 := hw.overlap_coisometry
  have hdiff := pvmForwardDifferential_eq (isIsometry_decoder hw.decA_isometry hw.decB_isometry)
    hTco hexact hWdot (ωdot := γ'.2.2.1) (Ydot := encodedStateVelocity x.1 γ'.2.1 x.2.2.1
      γ'.2.2.2.1 x.2.2.2.1 γ'.2.2.2.2.1)
  have ha := encodedState_velocity_mem_localSkew (ιA := Fin d) (ιB := Fin d)
    hw.encA_isometry hw.encB_isometry x.1 γ'.2.1 hVAlin hVBlin hηlin
  have hbL := Submodule.add_mem _ (flagIsometry_conjTranspose_mul_mem_diagSkew _ _ hωlin)
    (flag_local_compression_mem_diagSkew x.2.1 (skewLift_conjTranspose hDAlin)
      (skewLift_conjTranspose hDBlin))
  refine ⟨ha, Submodule.neg_mem _ hbL, ?_⟩
  have haskew : (pvmInputGenerator x γ'.2)ᴴ = -pvmInputGenerator x γ'.2 :=
    mem_skewHermitian_iff.mp (localSkew_le_skewHermitian ha)
  have hbskew := (mem_diagSkew_iff.mp hbL).2
  have hD : (flagIsometry x.2.1)ᴴ * (decoder x.2.2.2.2.1 x.2.2.2.2.2 *
        encodedStateVelocity x.1 γ'.2.1 x.2.2.1 γ'.2.2.2.1 x.2.2.2.1 γ'.2.2.2.2.1 +
        (x.2.2.2.2.1 ⊗ₖ γ'.2.2.2.2.2.2 + γ'.2.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) *
          encodedState x.1 x.2.2.1 x.2.2.2.1) +
      (flagIsometry γ'.2.2.1)ᴴ * (decoder x.2.2.2.2.1 x.2.2.2.2.2 *
        encodedState x.1 x.2.2.1 x.2.2.2.1) =
      -pvmOutcomeGenerator x γ'.2 * pvmOverlapOn x + pvmOverlapOn x * pvmInputGenerator x γ'.2 := by
    rw [pvmOutcomeGenerator, neg_neg, pvmInputGenerator, ← hdiff, Matrix.mul_add]
    abel
  rw [hval, hD, hT, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, haskew, Matrix.conjTranspose_neg,
    show (pvmOutcomeGenerator x γ'.2)ᴴ = -pvmOutcomeGenerator x γ'.2 from
      (mem_diagSkew_iff.mp (Submodule.neg_mem _ hbL)).2]
  simp only [neg_neg, Matrix.neg_mul]
  abel

/-- **`prop:derivative-pvm`.** For a continuously differentiable family of
exact measurement strategies on an open set `J`, there are continuous maps
`a : J → Loc` and `b : J → 𝔲_diag` with `Ṁ = -a M + M b` on `J`. -/
theorem exists_continuous_pvm_generators (s : Fin 8 → ℕ) {J : Set ℝ} (hJ : IsOpen J)
    {γ : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s}
    (hγ : ContDiffOn ℝ 1 γ J) (hmem : ∀ t ∈ J, γ t ∈ pvmTargetWitnessSet d s) :
    ∃ a b : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      ContinuousOn a J ∧ ContinuousOn b J ∧
      ∀ t ∈ J, a t ∈ localSkew (Fin d) (Fin d) ∧ b t ∈ diagSkew (Fin d × Fin d) ∧
        HasDerivAt (fun τ => (γ τ).1) (-a t * (γ t).1 + (γ t).1 * b t) t := by
  have hd : ∀ t ∈ J, HasDerivAt γ (deriv γ t) t := fun t ht =>
    ((hγ.differentiableOn one_ne_zero t ht).differentiableAt (hJ.mem_nhds ht)).hasDerivAt
  have hγ0 : ContDiffOn ℝ 0 γ J := hγ.of_le (by norm_num)
  have hγ'0 : ContDiffOn ℝ 0 (deriv γ) J := hγ.deriv_of_isOpen hJ (by norm_num)
  have hgen := ContDiffOn.pvmGenerators (contDiff_snd.comp_contDiffOn hγ0)
    (contDiff_snd.comp_contDiffOn hγ'0)
  have hA := hgen.1
  have hB := hgen.2
  refine ⟨fun t => pvmInputGenerator (γ t).2 (deriv γ t).2,
    fun t => pvmOutcomeGenerator (γ t).2 (deriv γ t).2,
    hA, hB, fun t ht => ?_⟩
  have hev : ∀ᶠ τ in 𝓝 t, γ τ ∈ pvmTargetWitnessSet d s :=
    Filter.mem_of_superset (hJ.mem_nhds ht) fun τ hτ => hmem τ hτ
  obtain ⟨ha, hb, hval⟩ := pvm_target_velocity s (hd t ht) hev
  refine ⟨ha, hb, ?_⟩
  have h := HasDerivAt.prodFst' (hd t ht)
  rw [hval] at h
  exact h

end MeasurementDerivative

end NLQCLean

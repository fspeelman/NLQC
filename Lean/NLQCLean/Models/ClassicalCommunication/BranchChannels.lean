import NLQCLean.Models.ClassicalCommunication.FiniteProtocol
import NLQCLean.Models.ClassicalCommunication.TensorChannels

/-!
# Actual outcome channels and channel-slot linearity

The outcome channel inserts the given resource, applies the two local
operations, exchanges the quantum messages canonically, decodes, and traces
the final private environments. For finite instrument operations it agrees
with the actual Kraus-amplitude branch sum. Fixing one local operation gives
a real-linear map on the other operation, suitable for a separately proved
target-score functional.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

attribute [local implicit_reducible] Matrix

section LinearComposition

variable {V W X Y : Type*}
variable [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X] [AddCommMonoid Y]
variable [Module ℂ V] [Module ℂ W] [Module ℂ X] [Module ℂ Y]

/-- Fixed pre- and postcomposition are genuinely linear in the middle map. -/
def channelSandwichLinear (L : X →ₗ[ℂ] Y) (R : V →ₗ[ℂ] W) :
    (W →ₗ[ℂ] X) →ₗ[ℂ] (V →ₗ[ℂ] Y) where
  toFun Φ := L.comp (Φ.comp R)
  map_add' Φ Ψ := by simp only [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c Φ := by
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

@[simp] theorem channelSandwichLinear_apply
    (L : X →ₗ[ℂ] Y) (R : V →ₗ[ℂ] W) (Φ : W →ₗ[ℂ] X) :
    channelSandwichLinear L R Φ = L.comp (Φ.comp R) := rfl

end LinearComposition

section MatrixComposition

variable {α β γ δ α' : Type*} [Fintype β] [Fintype γ]

/-- Conjugation composition corresponds exactly to multiplying its matrices. -/
theorem adConj_mul_eq_comp (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    adConj (A * B) = (adConj A).comp (adConj B) := by
  apply LinearMap.ext
  intro Z
  simp only [adConj_apply, LinearMap.comp_apply, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

private theorem row_reindex_mul_mul
    (D : Matrix α β ℂ) (A : Matrix β γ ℂ) (R : Matrix γ δ ℂ) (e : α' → α) :
    (D * A * R).submatrix e id = D.submatrix e id * A * R := by
  rw [Matrix.submatrix_mul (D * A) R e id id Function.bijective_id,
    Matrix.submatrix_id_id, Matrix.submatrix_mul D A e id id Function.bijective_id,
    Matrix.submatrix_id_id]

end MatrixComposition

section BranchOperation

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

/-- The actual joint decoder after the canonical exchange, with outputs
regrouped only for tracing their private environments. -/
def exchangedDecoder
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    Matrix ((ιA' × ιB') × (εA × εB)) ((κA × μA) × (κB × μB)) ℂ :=
  ((DA ⊗ₖ DB) * exchangeMatrix κA μA κB μB).submatrix
    (outputRegroup ιA' ιB' εA εB) id

/-- The resource insertion and final physical operations form a fixed
linear sandwich around an arbitrary joint encoding operation. -/
def branchChannelSandwich (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    (Matrix ((ιA × ρA) × (ιB × ρB)) ((ιA × ρA) × (ιB × ρB)) ℂ →ₗ[ℂ]
      Matrix ((κA × μA) × (κB × μB)) ((κA × μA) × (κB × μB)) ℂ) →ₗ[ℂ]
    (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ) :=
  channelSandwichLinear
    ((ptraceB (ιA' × ιB') (εA × εB)).comp (adConj (exchangedDecoder DA DB)))
    (adConj (insertResource ιA ιB γ))

/-- Actual joint outcome channel from arbitrary local channel operations. -/
def branchChannel (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ :=
  branchChannelSandwich γ DA DB (tensorChannels Φ Ψ)

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
  [DecidableEq ρA] [DecidableEq ρB] in
/-- The Kraus amplitude factorization uses exactly the existing architecture. -/
theorem regrouped_globalIsometry_eq
    (γ : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    (NLQCLean.globalIsometry γ VA VB DA DB).submatrix
        (outputRegroup ιA' ιB' εA εB) id =
      exchangedDecoder DA DB * (VA ⊗ₖ VB) * insertResource ιA ιB γ := by
  have h : NLQCLean.globalIsometry γ VA VB DA DB =
      ((DA ⊗ₖ DB) * exchangeMatrix κA μA κB μB) * (VA ⊗ₖ VB) *
        insertResource ιA ιB γ := by
    simp only [NLQCLean.globalIsometry_eq, Matrix.mul_assoc]
  rw [h, row_reindex_mul_mul]
  rfl

omit [Fintype ιA'] [Fintype ιB'] in
/-- Actual matrix conjugations through the branch channel recover its
original unnormalized Stinespring amplitude. -/
theorem branchChannel_adConj
    (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ) :
    branchChannel γ DA DB (adConj VA) (adConj VB) =
      channelOf ((NLQCLean.globalIsometry γ VA VB DA DB).submatrix
        (outputRegroup ιA' ιB' εA εB) id) := by
  unfold branchChannel
  rw [tensorChannels_adConj]
  change ((ptraceB (ιA' × ιB') (εA × εB)).comp
      (adConj (exchangedDecoder DA DB))).comp
        ((adConj (VA ⊗ₖ VB)).comp (adConj (insertResource ιA ιB γ))) = _
  rw [LinearMap.comp_assoc, ← adConj_mul_eq_comp, ← adConj_mul_eq_comp,
    regrouped_globalIsometry_eq]
  apply LinearMap.ext
  intro Z
  simp only [LinearMap.comp_apply, channelOf_apply, adConj_apply, Matrix.mul_assoc]

/-- The first local operation enters the actual outcome channel linearly. -/
def branchChannelLeftLinear (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :
    (Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) →ₗ[ℂ]
      (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ) :=
  (branchChannelSandwich γ DA DB).comp (tensorChannelsLeftLinear Ψ)

/-- The second local operation enters the actual outcome channel linearly. -/
def branchChannelRightLinear (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) :
    (Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) →ₗ[ℂ]
      (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ) :=
  (branchChannelSandwich γ DA DB).comp (tensorChannelsRightLinear Φ)

/-- Real-linear first-slot map for composing an actual real target score. -/
noncomputable def branchChannelLeftRealLinear (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :
    (Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) →ₗ[ℝ]
      (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ) :=
  (branchChannelLeftLinear γ DA DB Ψ).restrictScalars ℝ

/-- Real-linear second-slot map for composing an actual real target score. -/
noncomputable def branchChannelRightRealLinear (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) :
    (Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) →ₗ[ℝ]
      (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ) :=
  (branchChannelRightLinear γ DA DB Φ).restrictScalars ℝ

omit [Fintype ιA'] [Fintype ιB'] in
@[simp] theorem branchChannelLeftRealLinear_apply
    (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) :
    branchChannelLeftRealLinear γ DA DB Ψ Φ = branchChannel γ DA DB Φ Ψ := rfl

omit [Fintype ιA'] [Fintype ιB'] in
@[simp] theorem branchChannelRightRealLinear_apply
    (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :
    branchChannelRightRealLinear γ DA DB Φ Ψ = branchChannel γ DA DB Φ Ψ := rfl

omit [Fintype ιA'] [Fintype ιB'] in
/-- The finite Kraus branch sum equals the composed channel. -/
theorem branchChannel_krausMap {ηA ηB : Type*} [Fintype ηA] [Fintype ηB]
    (γ : ρA × ρB → ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (A : ηA → Matrix (κA × μA) (ιA × ρA) ℂ)
    (B : ηB → Matrix (κB × μB) (ιB × ρB) ℂ) :
    branchChannel γ DA DB (krausMap A) (krausMap B) =
      ∑ e, ∑ f, channelOf ((NLQCLean.globalIsometry γ (A e) (B f) DA DB).submatrix
        (outputRegroup ιA' ιB' εA εB) id) := by
  unfold branchChannel
  rw [tensorChannels_krausMap]
  simp only [krausMap, map_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  have h := branchChannel_adConj γ DA DB (A e) (B f)
  simpa only [branchChannel, tensorChannels_adConj] using h

end BranchOperation

namespace FiniteClassicalProtocol

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)

/-- The actual outcome channel, with the resource and final channels fixed. -/
def outcomeChannel (x : σA) (y : σB)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :=
  branchChannel P.resource (P.decA x y) (P.decB x y) Φ Ψ

/-- Actual instrument operations reproduce all original unnormalized
Kraus-amplitude branches exactly at the channel level. -/
theorem outcomeChannel_instrument_branches (x : σA) (y : σB) :
    P.outcomeChannel x y (P.instrumentA.branch x) (P.instrumentB.branch y) =
      ∑ e, ∑ f, channelOf ((P.branchAmplitude x y e f).submatrix
        (outputRegroup ιA' ιB' εA εB) id) :=
  branchChannel_krausMap P.resource (P.decA x y) (P.decB x y)
    (P.instrumentA.operator x) (P.instrumentB.operator y)

/-- The defined operational channel is the sum of the actual outcome channels. -/
theorem operationalChannel_eq_sum_outcomeChannel :
    P.operationalChannel = ∑ x, ∑ y,
      P.outcomeChannel x y (P.instrumentA.branch x) (P.instrumentB.branch y) := by
  simp only [outcomeChannel_instrument_branches]
  rfl

/-- First local channel slot for a separately verified real score functional. -/
noncomputable def outcomeChannelLeftRealLinear (x : σA) (y : σB)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :
    (Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) →ₗ[ℝ]
      (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ) :=
  branchChannelLeftRealLinear P.resource (P.decA x y) (P.decB x y) Ψ

/-- Second local channel slot for a separately verified real score functional. -/
noncomputable def outcomeChannelRightRealLinear (x : σA) (y : σB)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) :
    (Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) →ₗ[ℝ]
      (Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℂ] Matrix (ιA' × ιB') (ιA' × ιB') ℂ) :=
  branchChannelRightRealLinear P.resource (P.decA x y) (P.decB x y) Φ

@[simp] theorem outcomeChannelLeftRealLinear_apply (x : σA) (y : σB)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ) :
    P.outcomeChannelLeftRealLinear x y Ψ Φ = P.outcomeChannel x y Φ Ψ := rfl

@[simp] theorem outcomeChannelRightRealLinear_apply (x : σA) (y : σB)
    (Φ : Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℂ] Matrix (κA × μA) (κA × μA) ℂ)
    (Ψ : Matrix (ιB × ρB) (ιB × ρB) ℂ →ₗ[ℂ] Matrix (κB × μB) (κB × μB) ℂ) :
    P.outcomeChannelRightRealLinear x y Φ Ψ = P.outcomeChannel x y Φ Ψ := rfl

end FiniteClassicalProtocol

end NLQCLean.ClassicalCommunication

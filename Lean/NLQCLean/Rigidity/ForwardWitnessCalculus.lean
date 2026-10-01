import NLQCLean.Models.ForwardWitness
import NLQCLean.Rigidity.ForwardExactDifferential

/-!
# Shared calculus for forward witnesses

These derivative rules apply to the ambient forward-witness formulas.  They
are shared by exact critical-value arguments and reverse-witness calculus.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

variable {ρA ρB κA κB μA μB εA εB ιA ιB ιA' ιB' : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']

/-- Differentiating a fixed reindexing. -/
theorem HasDerivAt.matrixSubmatrix {a b a' b' : Type*} [Fintype a] [Fintype b]
    [Fintype a'] [Fintype b'] [DecidableEq a] [DecidableEq b]
    {f : ℝ → Matrix a b ℂ} {f' : Matrix a b ℂ} {t : ℝ}
    (h : HasDerivAt f f' t) (r : a' → a) (c : b' → b) :
    HasDerivAt (fun s => (f s).submatrix r c) (f'.submatrix r c) t :=
  HasDerivAt.ofLinearMap
    ({ toFun := fun M => M.submatrix r c
       map_add' := by intros; ext i j; simp
       map_smul' := by intros; ext i j; simp } :
      Matrix a b ℂ →ₗ[ℝ] Matrix a' b' ℂ) h

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- Differentiating resource insertion. -/
theorem HasDerivAt.insertResource
    {f : ℝ → ρA × ρB → ℂ} {f' : ρA × ρB → ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => NLQCLean.insertResource ιA ιB (f s))
      (NLQCLean.insertResource ιA ιB f') t :=
  HasDerivAt.ofLinearMap ((insertResourceLM ιA ιB).restrictScalars ℝ) h

/-- Differentiating environment insertion. -/
theorem HasDerivAt.insertVector {κ ε : Type*} [Fintype κ] [Fintype ε] [DecidableEq κ]
    {f : ℝ → ε → ℂ} {f' : ε → ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => NLQCLean.insertVector κ (f s))
      (NLQCLean.insertVector κ f') t :=
  HasDerivAt.ofLinearMap ((insertVectorLM κ).restrictScalars ℝ) h

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- The derivative of the encoded state. -/
theorem hasDerivAt_encodedState
    {η : ℝ → ρA × ρB → ℂ} {η' : ρA × ρB → ℂ}
    {VA : ℝ → Matrix (κA × μA) (ιA × ρA) ℂ} {VA' : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : ℝ → Matrix (κB × μB) (ιB × ρB) ℂ} {VB' : Matrix (κB × μB) (ιB × ρB) ℂ}
    (hη : HasDerivAt η η' 0) (hVA : HasDerivAt VA VA' 0) (hVB : HasDerivAt VB VB' 0) :
    HasDerivAt (fun t => encodedState (ιA := ιA) (ιB := ιB) (η t) (VA t) (VB t))
      (encodedStateVelocity (ιA := ιA) (ιB := ιB) (η 0) η' (VA 0) VA' (VB 0) VB') 0 := by
  have hE := HasDerivAt.insertResource (ιA := ιA) (ιB := ιB) hη
  have hK := HasDerivAt.matrixKronecker hVA hVB
  have hM := HasDerivAt.matrixMul hK hE
  have hEx := HasDerivAt.matrixMul
    (hasDerivAt_const (0 : ℝ) (exchangeMatrix κA μA κB μB)) hM
  simp only [add_zero, Matrix.zero_mul] at hEx
  simp only [encodedState, encodedStateVelocity]
  convert hEx using 1
  simp only [Matrix.mul_add]
  abel

omit [Fintype εA] [Fintype εB] [Fintype ιA'] [Fintype ιB'] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq εA] [DecidableEq εB] [DecidableEq ιA'] [DecidableEq ιB'] in
/-- The regrouped global isometry factors as `W · Y`. -/
theorem globalIsometryRegrouped_eq (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    globalIsometryRegrouped η VA VB DA DB
      = (decoder DA DB).submatrix (outputRegroup ιA' ιB' εA εB) id
        * encodedState η VA VB := by
  rw [globalIsometryRegrouped, globalIsometry,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- The derivative of the forward overlap. -/
theorem hasDerivAt_forwardOverlap
    {η : ℝ → ρA × ρB → ℂ} {η' : ρA × ρB → ℂ}
    {g : ℝ → εA × εB → ℂ} {g' : εA × εB → ℂ}
    {VA : ℝ → Matrix (κA × μA) (ιA × ρA) ℂ} {VA' : Matrix (κA × μA) (ιA × ρA) ℂ}
    {VB : ℝ → Matrix (κB × μB) (ιB × ρB) ℂ} {VB' : Matrix (κB × μB) (ιB × ρB) ℂ}
    {DA : ℝ → Matrix (ιA' × εA) (κA × μB) ℂ} {DA' : Matrix (ιA' × εA) (κA × μB) ℂ}
    {DB : ℝ → Matrix (ιB' × εB) (κB × μA) ℂ} {DB' : Matrix (ιB' × εB) (κB × μA) ℂ}
    (hη : HasDerivAt η η' 0) (hg : HasDerivAt g g' 0)
    (hVA : HasDerivAt VA VA' 0) (hVB : HasDerivAt VB VB' 0)
    (hDA : HasDerivAt DA DA' 0) (hDB : HasDerivAt DB DB' 0) :
    HasDerivAt (fun t => forwardOverlap (η t) (g t) (VA t) (VB t) (DA t) (DB t))
      ((insertVector (ιA' × ιB') g')ᴴ
          * ((decoder (DA 0) (DB 0)).submatrix (outputRegroup ιA' ιB' εA εB) id
              * encodedState (η 0) (VA 0) (VB 0))
        + (insertVector (ιA' × ιB') (g 0))ᴴ
          * (((DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0).submatrix (outputRegroup ιA' ιB' εA εB) id)
              * encodedState (η 0) (VA 0) (VB 0))
        + (insertVector (ιA' × ιB') (g 0))ᴴ
          * ((decoder (DA 0) (DB 0)).submatrix (outputRegroup ιA' ιB' εA εB) id
              * encodedStateVelocity (η 0) η' (VA 0) VA' (VB 0) VB')) 0 := by
  have hY := hasDerivAt_encodedState (ιA := ιA) (ιB := ιB) hη hVA hVB
  have hW : HasDerivAt
      (fun t => (decoder (DA t) (DB t)).submatrix (outputRegroup ιA' ιB' εA εB) id)
      ((DA 0 ⊗ₖ DB' + DA' ⊗ₖ DB 0).submatrix (outputRegroup ιA' ιB' εA εB) id) 0 :=
    HasDerivAt.matrixSubmatrix (HasDerivAt.matrixKronecker hDA hDB) _ _
  have hEg := HasDerivAt.insertVector (κ := ιA' × ιB') hg
  have hEgH := HasDerivAt.matrixConjTranspose hEg
  have hWY := HasDerivAt.matrixMul hW hY
  have hfull := HasDerivAt.matrixMul hEgH hWY
  have hfun : (fun t => forwardOverlap (η t) (g t) (VA t) (VB t) (DA t) (DB t))
      = fun t => (insertVector (ιA' × ιB') (g t))ᴴ
          * ((decoder (DA t) (DB t)).submatrix (outputRegroup ιA' ιB' εA εB) id
              * encodedState (η t) (VA t) (VB t)) := by
    funext t
    rw [forwardOverlap, globalIsometryRegrouped_eq]
  rw [hfun]
  convert hfull using 1
  simp only [Matrix.mul_add]
  abel

end NLQCLean

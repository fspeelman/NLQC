/-
The six-block forward witness and its smoothness.
-/
import NLQCLean.LinearAlgebra.RealCoordinates
import NLQCLean.Models.OneRound
import NLQCLean.Models.Resource
import NLQCLean.Rigidity.FrozenDilation

/-!
# The six-block forward witness `H(x)` is smooth

The witness construction adds an
*independent* unit vector `g` in `E_A ⊗ E_B` to the five physical blocks
`(η, V_A, V_B, D_A, D_B)` and forms the raw matrix-valued map

  `H(x) = E_g† (D_A ⊗ D_B) Ex (V_A ⊗ V_B) E_η`,
  `x = (η, g, V_A, V_B, D_A, D_B)`.

`g` is a witness variable, not a function of the protocol. Accordingly
`NLQCLean.forwardOverlap` takes `g` as an ordinary sixth argument and
`NLQCLean.ForwardBlocks` is a plain product; no continuous choice of `g`
is assumed.

The module proves that `H` is `ContDiff ℝ ∞` in all six blocks jointly by
composition. Composing with the realignment-purity polynomial gives
`NLQCLean.contDiff_purityForwardOverlap`, the scalar-map regularity consumed
by `NLQCLean.scalarCriticalImage_volume_eq_zero`.

Nothing here asserts that `H` is unitary, that the blocks are isometries, or
that the constraint set is nonempty. The raw map is defined on the *full*
product of the complex matrix spaces viewed as a real vector space; the
sphere/isometry conditions cut out the constraint set `C` inside it; that
separation is preserved.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- The smoothness index `∞` of the `ContDiff` scope, pinned locally so that it
cannot be read as the `ENNReal` infinity. -/
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Insertion

variable {ρA ρB : Type*} [Fintype ρA] [Fintype ρB]
variable {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]

/-- `J_η` as a `ℂ`-linear map in the resource vector, from
`NLQCLean.insertResource_add` and `NLQCLean.insertResource_smul`. -/
def insertResourceLM (ιA ιB : Type*) [DecidableEq ιA] [DecidableEq ιB] :
    (ρA × ρB → ℂ) →ₗ[ℂ] Matrix ((ιA × ρA) × (ιB × ρB)) (ιA × ιB) ℂ where
  toFun := insertResource ιA ιB
  map_add' := insertResource_add
  map_smul' := insertResource_smul

omit [Fintype ρA] [Fintype ρB] in
@[simp] theorem insertResourceLM_apply (η : ρA × ρB → ℂ) :
    insertResourceLM (ρA := ρA) (ρB := ρB) ιA ιB η = insertResource ιA ιB η := rfl

end Insertion

section VectorInsertion

variable {κ ε : Type*} [DecidableEq κ]

/-- `J_γ` is additive in the environment vector. -/
theorem insertVector_add (γ θ : ε → ℂ) :
    insertVector κ (γ + θ) = insertVector κ γ + insertVector κ θ := by
  ext p k
  simp only [Matrix.add_apply, insertVector_apply, Pi.add_apply]
  ring

/-- `J_γ` is homogeneous in the environment vector. -/
theorem insertVector_smul (c : ℂ) (γ : ε → ℂ) :
    insertVector κ (c • γ) = c • insertVector κ γ := by
  ext p k
  simp only [Matrix.smul_apply, insertVector_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `J_γ` as a `ℂ`-linear map in the environment vector. -/
def insertVectorLM (κ : Type*) [DecidableEq κ] :
    (ε → ℂ) →ₗ[ℂ] Matrix (κ × ε) κ ℂ where
  toFun := insertVector κ
  map_add' := insertVector_add
  map_smul' := insertVector_smul

@[simp] theorem insertVectorLM_apply (γ : ε → ℂ) :
    insertVectorLM (ε := ε) κ γ = insertVector κ γ := rfl

end VectorInsertion

section SmoothnessRules

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {N : WithTop ℕ∞}

/-- Inserting a smooth family of resource vectors is smooth. -/
theorem ContDiff.insertResource {ρA ρB : Type*} [Fintype ρA] [Fintype ρB]
    {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    {f : E → ρA × ρB → ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => NLQCLean.insertResource ιA ιB (f x)) :=
  ContDiff.linearMapFD ((insertResourceLM ιA ιB).restrictScalars ℝ) hf

/-- Inserting a smooth family of environment vectors is smooth. -/
theorem ContDiff.insertVector {κ ε : Type*} [Fintype κ] [Fintype ε] [DecidableEq κ]
    {f : E → ε → ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => NLQCLean.insertVector κ (f x)) :=
  ContDiff.linearMapFD ((insertVectorLM κ).restrictScalars ℝ) hf

end SmoothnessRules

section ForwardWitness

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- The raw six-block forward overlap `H`:
`H = E_g† (D_A ⊗ D_B) Ex (V_A ⊗ V_B) E_η`, built on the regrouped global
isometry so that the retained output `H_{A'} ⊗ H_{B'}` and the environment
`E_A ⊗ E_B` are separated, which is what `E_g` acts on. -/
def forwardOverlap (η : ρA × ρB → ℂ) (g : εA × εB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    Matrix (ιA' × ιB') (ιA × ιB) ℂ :=
  (insertVector (ιA' × ιB') g)ᴴ * globalIsometryRegrouped η VA VB DA DB

/-- The ambient real parameter space: the full product of the six
complex block spaces, viewed as a real vector space.  Note that this product
carries Lean's sup norm rather than an `l²` norm; see the norm discussion in
`NLQCLean.LinearAlgebra.RealCoordinates`. -/
abbrev ForwardBlocks (ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*) :=
  (ρA × ρB → ℂ) × (εA × εB → ℂ) ×
    Matrix (κA × μA) (ιA × ρA) ℂ × Matrix (κB × μB) (ιB × ρB) ℂ ×
    Matrix (ιA' × εA) (κA × μB) ℂ × Matrix (ιB' × εB) (κB × μA) ℂ

/-- The forward overlap read off a point of the ambient parameter space. -/
def forwardOverlapOn
    (x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    Matrix (ιA' × ιB') (ιA × ιB) ℂ :=
  forwardOverlap x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

omit [DecidableEq ρA] [DecidableEq εA] [DecidableEq εB] in
/-- The six-block forward overlap is smooth by composition. The exchange
permutation is constant, and the vector insertions are linear maps on
finite-dimensional real spaces. -/
theorem contDiff_forwardOverlapOn :
    ContDiff ℝ ∞
      (forwardOverlapOn (ιA := ιA) (ιB := ιB) (ρA := ρA) (ρB := ρB)
        (κA := κA) (κB := κB) (μA := μA) (μB := μB)
        (ιA' := ιA') (ιB' := ιB') (εA := εA) (εB := εB)) := by
  have hη : ContDiff ℝ ∞
      (fun x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB => x.1) :=
    contDiff_fst
  have hg : ContDiff ℝ ∞
      (fun x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB => x.2.1) :=
    contDiff_fst.snd'
  have hVA : ContDiff ℝ ∞
      (fun x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB => x.2.2.1) :=
    contDiff_fst.snd'.snd'
  have hVB : ContDiff ℝ ∞
      (fun x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB => x.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'
  have hDA : ContDiff ℝ ∞
      (fun x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB => x.2.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'.snd'
  have hDB : ContDiff ℝ ∞
      (fun x : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB => x.2.2.2.2.2) :=
    contDiff_snd.snd'.snd'.snd'.snd'
  have hEeta := ContDiff.insertResource (ιA := ιA) (ιB := ιB) hη
  have hEg := ContDiff.insertVector (κ := ιA' × ιB') hg
  have hVV := ContDiff.matrixKronecker hVA hVB
  have hEx : ContDiff ℝ ∞
      (fun _ : ForwardBlocks ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB =>
        exchangeMatrix κA μA κB μB) := contDiff_const
  have hDD := ContDiff.matrixKronecker hDA hDB
  have hF := ContDiff.matrixMul hDD
    (ContDiff.matrixMul hEx (ContDiff.matrixMul hVV hEeta))
  have hFr := ContDiff.matrixSubmatrix hF (outputRegroup ιA' ιB' εA εB) id
  exact ContDiff.matrixMul (ContDiff.matrixConjTranspose hEg) hFr

end ForwardWitness

section BalancedComposite

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq ρA] [DecidableEq εA] [DecidableEq εB] in
/-- **The scalar map that the qualitative Sard argument differentiates.**

With balanced logical registers `H_A = H_B = H_{A'} = H_{B'} = C^d`, the
forward overlap is a square matrix on `C^d ⊗ C^d`, so the realignment-purity
polynomial applies to it.  This composite is `ContDiff ℝ ∞` on the full
real parameter space, which is precisely the hypothesis shape of
`NLQCLean.scalarCriticalImage_volume_eq_zero`.

Both the six-block forward overlap and the realignment-purity expression
are smooth by composition. -/
theorem contDiff_purityForwardOverlap (c : ℝ) :
    ContDiff ℝ ∞
      (fun x : ForwardBlocks (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB =>
        purity c (forwardOverlapOn x)) :=
  ContDiff.purity c contDiff_forwardOverlapOn

end BalancedComposite

end NLQCLean

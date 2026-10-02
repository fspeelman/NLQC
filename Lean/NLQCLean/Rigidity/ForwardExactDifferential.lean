/-
The skew-Hermitian lift of an isometry tangent.
-/
import NLQCLean.LinearAlgebra.Isometry
import NLQCLean.Geometry.CubicExtension
import NLQCLean.Rigidity.Compression
import NLQCLean.Models.OneRound

/-!
# An elementary skew-Hermitian lift of an isometry tangent

Let `V` be a rectangular complex matrix with `V†V = I` and let `Z` satisfy the
linearized isometry constraint `V†Z + Z†V = 0`. The companion proof uses

  `L(V,Z) = Z V† - V Z† - V (V† Z) V†`

and proves `L† = -L` and `L V = Z`.  Applied to the decoder velocities this
is what turns an arbitrary admissible block velocity into a *global*
skew-Hermitian generator acting on the left, which is the form used by the
forward differential.

## Linearized constraints

`NLQCLean.skewLift_conjTranspose` needs **only** the linearized constraint;
`V` is not assumed to be an isometry there. Isometry of `V` is used only
for `NLQCLean.skewLift_mul`. Keeping the two apart permits applications where
only the linearized constraint is available for the velocity.
-/

namespace NLQCLean

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The skew-Hermitian lift `L(V,Z) = Z V† - V Z† - V (V† Z) V†`. -/
def skewLift (V Z : Matrix m n ℂ) : Matrix m m ℂ :=
  Z * Vᴴ - V * Zᴴ - V * (Vᴴ * Z) * Vᴴ

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The linearized isometry constraint makes `V† Z` skew-Hermitian. -/
theorem conjTranspose_mul_skew {V Z : Matrix m n ℂ}
    (hZ : Vᴴ * Z + Zᴴ * V = 0) : (Vᴴ * Z)ᴴ = -(Vᴴ * Z) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hZ

omit [DecidableEq m] [DecidableEq n] in
/-- The lift is skew-Hermitian. Only the linearized
constraint is used; `V` need not be an isometry. -/
theorem skewLift_conjTranspose {V Z : Matrix m n ℂ}
    (hZ : Vᴴ * Z + Zᴴ * V = 0) :
    (skewLift V Z)ᴴ = -(skewLift V Z) := by
  have hskew : (Vᴴ * Z)ᴴ = -(Vᴴ * Z) := conjTranspose_mul_skew hZ
  have hterm : (V * (Vᴴ * Z) * Vᴴ)ᴴ = -(V * (Vᴴ * Z) * Vᴴ) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hskew, Matrix.neg_mul,
      Matrix.mul_neg, ← Matrix.mul_assoc]
  rw [skewLift, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, hterm,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  abel

omit [DecidableEq m] in
/-- The lift reproduces the tangent, `L V = Z`. -/
theorem skewLift_mul {V Z : Matrix m n ℂ} (hV : IsIsometry V)
    (hZ : Vᴴ * Z + Zᴴ * V = 0) :
    skewLift V Z * V = Z := by
  have hVV : Vᴴ * V = 1 := hV.conjTranspose_mul_self
  have hZV : Zᴴ * V = -(Vᴴ * Z) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hZ
  have e1 : skewLift V Z * V
      = Z * (Vᴴ * V) - V * (Zᴴ * V) - V * (Vᴴ * Z) * (Vᴴ * V) := by
    rw [skewLift, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc Z Vᴴ V,
      Matrix.mul_assoc V Zᴴ V, Matrix.mul_assoc (V * (Vᴴ * Z)) Vᴴ V]
  rw [e1, hVV, hZV, Matrix.mul_one, Matrix.mul_one, Matrix.mul_neg]
  abel

section ForwardDifferential

open scoped Kronecker

variable {ιA ιB ρA ρB κA κB μA μB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

/-!
## Input side: `a = Y† Ẏ` is a local generator

The input-side generator of the forward witness
lies in `Loc = NLQCLean.localSkew`. Two facts do the work: the
fixed exchange permutation cancels (`Ex† Ex = I`), and the shared-vector
compression identity carries local skew-Hermitian operators into `Loc` —
by `NLQCLean.compress_resource_mem_localSkew` and its
mirror.  The scalar `⟨η, η̇⟩ I` is purely imaginary by the sphere constraint,
which places it in the scalar direction of `Loc`.
-/

/-- A purely imaginary multiple of the identity is a local generator: this is
the scalar direction `iℝI ⊆ 𝔤_{A:B}`. -/
theorem smul_one_mem_localSkew_of_re_eq_zero {c : ℂ} (hc : c.re = 0) :
    c • (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ) ∈ localSkew ιA ιB := by
  have hcI : c = (c.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [hc]
  rw [hcI]
  exact smul_I_one_mem_localSkew _

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- **The Gram identity for resource insertion**: `E_η† E_θ = ⟨η,θ⟩ I`.
This turns the resource-velocity term into a scalar. -/
theorem insertResource_gram (η θ : ρA × ρB → ℂ) :
    (insertResource ιA ιB η)ᴴ * insertResource ιA ιB θ
      = vecInner η θ • (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ) := by
  ext q q'
  rw [insertResource_conjTranspose_mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  rcases Decidable.em (q = q') with h | h
  · subst h
    rw [ite_eq_left rfl, mul_one, vecInner, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [insertResource_apply]
    simp
  · rw [ite_eq_right h, mul_zero]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    rw [insertResource_apply]
    rcases Decidable.em (q.1 = q'.1) with h1 | h1
    · rcases Decidable.em (q.2 = q'.2) with h2 | h2
      · exact absurd (Prod.ext h1 h2) h
      · simp [h2]
    · simp [h1]

/-- The input generator is local: an Alice-local and a
Bob-local skew-Hermitian generator compressed through the resource, plus a
purely imaginary scalar, lie in `Loc`. -/
theorem compressed_pair_add_scalar_mem_localSkew (η : ρA × ρB → ℂ)
    {XA : Matrix (ιA × ρA) (ιA × ρA) ℂ} {XB : Matrix (ιB × ρB) (ιB × ρB) ℂ}
    (hXA : XAᴴ = -XA) (hXB : XBᴴ = -XB) {c : ℂ} (hc : c.re = 0) :
    (insertResource ιA ιB η)ᴴ
        * (ampLeft (ιA × ρA) (ιB × ρB) XA + ampRight (ιA × ρA) (ιB × ρB) XB)
        * insertResource ιA ιB η
      + c • (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ)
      ∈ localSkew ιA ιB := by
  have hsplit : (insertResource ιA ιB η)ᴴ
      * (ampLeft (ιA × ρA) (ιB × ρB) XA + ampRight (ιA × ρA) (ιB × ρB) XB)
      * insertResource ιA ιB η
      = (insertResource ιA ιB η)ᴴ * ampLeft (ιA × ρA) (ιB × ρB) XA
          * insertResource ιA ιB η
        + (insertResource ιA ιB η)ᴴ * ampRight (ιA × ρA) (ιB × ρB) XB
          * insertResource ιA ιB η := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [hsplit]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (compress_resource_mem_localSkew η hXA)
      (compress_resource_right_mem_localSkew η hXB))
    (smul_one_mem_localSkew_of_re_eq_zero hc)

/-- The product-rule velocity of `Y = Ex (V_A ⊗ V_B) E_η`,
defined algebraically for arbitrary block velocities. -/
noncomputable def encodedStateVelocity (η η' : ρA × ρB → ℂ)
    (VA VA' : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB VB' : Matrix (κB × μB) (ιB × ρB) ℂ) :
    Matrix ((κA × μB) × (κB × μA)) (ιA × ιB) ℂ :=
  exchangeMatrix κA μA κB μB *
    ((VA ⊗ₖ VB' + VA' ⊗ₖ VB) * insertResource ιA ιB η
      + (VA ⊗ₖ VB) * insertResource ιA ιB η')

/-- `Y† Ẏ = E_η†(V_A†V̇_A ⊗ I + I ⊗ V_B†V̇_B)E_η +
⟨η,η̇⟩ I`.  The fixed exchange permutation cancels. -/
theorem encodedState_conjTranspose_mul_velocity
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (η η' : ρA × ρB → ℂ)
    (VA' : Matrix (κA × μA) (ιA × ρA) ℂ) (VB' : Matrix (κB × μB) (ιB × ρB) ℂ) :
    (encodedState η VA VB)ᴴ * encodedStateVelocity η η' VA VA' VB VB'
      = (insertResource ιA ιB η)ᴴ
          * (ampLeft (ιA × ρA) (ιB × ρB) (VAᴴ * VA')
             + ampRight (ιA × ρA) (ιB × ρB) (VBᴴ * VB'))
          * insertResource ιA ιB η
        + vecInner η η' • (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ) := by
  have hA : VAᴴ * VA = 1 := hVA.conjTranspose_mul_self
  have hB : VBᴴ * VB = 1 := hVB.conjTranspose_mul_self
  have hEx : (exchangeMatrix κA μA κB μB)ᴴ * exchangeMatrix κA μA κB μB = 1 :=
    (isIsometry_exchangeMatrix κA μA κB μB).conjTranspose_mul_self
  have k1 : (VA ⊗ₖ VB)ᴴ * (VA ⊗ₖ VB')
      = ampRight (ιA × ρA) (ιB × ρB) (VBᴴ * VB') := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, ampRight_apply]
  have k2 : (VA ⊗ₖ VB)ᴴ * (VA' ⊗ₖ VB)
      = ampLeft (ιA × ρA) (ιB × ρB) (VAᴴ * VA') := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hB, ampLeft_apply]
  have k3 : (VA ⊗ₖ VB)ᴴ * (VA ⊗ₖ VB) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB,
      Matrix.one_kronecker_one]
  have hcancel : ∀ A B : Matrix ((κA × μA) × (κB × μB)) (ιA × ιB) ℂ,
      (exchangeMatrix κA μA κB μB * A)ᴴ * (exchangeMatrix κA μA κB μB * B)
        = Aᴴ * B := by
    intro A B
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (exchangeMatrix κA μA κB μB)ᴴ, hEx, Matrix.one_mul]
  rw [encodedState, encodedStateVelocity, hcancel, Matrix.conjTranspose_mul,
    Matrix.mul_add]
  congr 1
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((VA ⊗ₖ VB)ᴴ), Matrix.mul_add, k1, k2,
      add_comm, ← Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((VA ⊗ₖ VB)ᴴ), k3, Matrix.one_mul,
      insertResource_gram]

/-- For arbitrary block velocities satisfying
the linearized isometry constraints and a resource velocity satisfying the
linearized sphere constraint, the input generator `a = Y† Ẏ` lies in `Loc`.

The hypotheses are exactly the linearized constraints at the single point; no
curve is assumed to remain exact, and no differentiability beyond the given
velocities is used. -/
theorem encodedState_velocity_mem_localSkew
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (η η' : ρA × ρB → ℂ)
    {VA' : Matrix (κA × μA) (ιA × ρA) ℂ} {VB' : Matrix (κB × μB) (ιB × ρB) ℂ}
    (hVA' : VAᴴ * VA' + VA'ᴴ * VA = 0) (hVB' : VBᴴ * VB' + VB'ᴴ * VB = 0)
    (hη' : (vecInner η η').re = 0) :
    (encodedState η VA VB)ᴴ * encodedStateVelocity η η' VA VA' VB VB'
      ∈ localSkew ιA ιB := by
  rw [encodedState_conjTranspose_mul_velocity hVA hVB η η' VA' VB']
  exact compressed_pair_add_scalar_mem_localSkew η
    (conjTranspose_mul_skew hVA') (conjTranspose_mul_skew hVB') hη'

/-!
## Output side and register regrouping

The output generator uses environment insertion and the two decoder lifts.
The identity `Ḣ = bU + Ua` also uses the two groupings of the
output registers — `(ι_{A'} × ε_A) × (ι_{B'} × ε_B)` for the decoders against
`(ι_{A'} × ι_{B'}) × (ε_A × ε_B)` for `E_g`.
-/

/-- **The Gram identity for environment insertion**: `E_g† E_h = ⟨g,h⟩ I`. -/
theorem insertVector_gram {κ ε : Type*} [Fintype κ] [Fintype ε] [DecidableEq κ]
    (g h : ε → ℂ) :
    (insertVector κ g)ᴴ * insertVector κ h
      = vecInner g h • (1 : Matrix κ κ ℂ) := by
  ext k k'
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Fintype.sum_prod_type]
  rcases Decidable.em (k = k') with hk | hk
  · subst hk
    rw [ite_eq_left rfl, mul_one, vecInner]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Matrix.conjTranspose_apply, insertVector_apply, insertVector_apply]
      simp
    · intro k'' _ hk''
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [Matrix.conjTranspose_apply, insertVector_apply]
      simp [hk'']
  · rw [ite_eq_right hk, mul_zero]
    refine Finset.sum_eq_zero fun k'' _ => Finset.sum_eq_zero fun e _ => ?_
    rw [Matrix.conjTranspose_apply, insertVector_apply, insertVector_apply]
    rcases Decidable.em (k'' = k) with h1 | h1
    · subst h1
      simp [hk]
    · simp [h1]

/-- The two decoder lifts act on the joint decoder as a single
global skew-Hermitian generator, `(L_A ⊗ I + I ⊗ L_B) W = Ẇ`. -/
theorem skewLift_kronecker_mul {a b c d : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
    {DA DA' : Matrix a b ℂ} {DB DB' : Matrix c d ℂ}
    (hDA : IsIsometry DA) (hDA' : DAᴴ * DA' + DA'ᴴ * DA = 0)
    (hDB : IsIsometry DB) (hDB' : DBᴴ * DB' + DB'ᴴ * DB = 0) :
    (skewLift DA DA' ⊗ₖ (1 : Matrix c c ℂ)
        + (1 : Matrix a a ℂ) ⊗ₖ skewLift DB DB') * (DA ⊗ₖ DB)
      = DA' ⊗ₖ DB + DA ⊗ₖ DB' := by
  rw [Matrix.add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    skewLift_mul hDA hDA', skewLift_mul hDB hDB', Matrix.one_mul, Matrix.one_mul]

/-- The joint decoder generator is skew-Hermitian. -/
theorem skewLift_kronecker_conjTranspose {a b c d : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
    {DA DA' : Matrix a b ℂ} {DB DB' : Matrix c d ℂ}
    (hDA' : DAᴴ * DA' + DA'ᴴ * DA = 0) (hDB' : DBᴴ * DB' + DB'ᴴ * DB = 0) :
    (skewLift DA DA' ⊗ₖ (1 : Matrix c c ℂ)
        + (1 : Matrix a a ℂ) ⊗ₖ skewLift DB DB')ᴴ
      = -(skewLift DA DA' ⊗ₖ (1 : Matrix c c ℂ)
        + (1 : Matrix a a ℂ) ⊗ₖ skewLift DB DB') := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    skewLift_conjTranspose hDA', skewLift_conjTranspose hDB']
  ext p q
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_one]
  ring

/-- If `W Y = E_g U` with `W` an isometry
and `U` co-isometric, then `W† E_g = Y U†`.  This is what lets the middle term
of the product rule be rewritten without inverting anything. -/
theorem conjTranspose_mul_of_exact {P Q R S : Type*}
    [Fintype P] [Fintype Q] [Fintype R] [Fintype S]
    [DecidableEq P] [DecidableEq Q] [DecidableEq R] [DecidableEq S]
    {W : Matrix P Q ℂ} {Y : Matrix Q R ℂ} {Eg : Matrix P S ℂ} {U : Matrix S R ℂ}
    (hW : IsIsometry W) (hU : U * Uᴴ = 1) (hexact : W * Y = Eg * U) :
    Wᴴ * Eg = Y * Uᴴ := by
  have hY : Wᴴ * (Eg * U) = Y := by
    rw [← hexact, ← Matrix.mul_assoc, hW.conjTranspose_mul_self, Matrix.one_mul]
  calc Wᴴ * Eg
      = Wᴴ * Eg * (U * Uᴴ) := by rw [hU, Matrix.mul_one]
    _ = Wᴴ * (Eg * U) * Uᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Y * Uᴴ := by rw [hY]

/-- The mirror of `NLQCLean.conjTranspose_mul_of_exact`: `E_g† W = U Y†`. -/
theorem conjTranspose_mul_of_exact' {P Q R S : Type*}
    [Fintype P] [Fintype Q] [Fintype R] [Fintype S]
    [DecidableEq P] [DecidableEq Q] [DecidableEq R] [DecidableEq S]
    {W : Matrix P Q ℂ} {Y : Matrix Q R ℂ} {Eg : Matrix P S ℂ} {U : Matrix S R ℂ}
    (hW : IsIsometry W) (hU : U * Uᴴ = 1) (hexact : W * Y = Eg * U) :
    Egᴴ * W = U * Yᴴ := by
  have h := congrArg Matrix.conjTranspose (conjTranspose_mul_of_exact hW hU hexact)
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h

end ForwardDifferential

section OutputRegrouping

open scoped Kronecker

variable {ιA' ιB' εA εB : Type*}
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq εA] [DecidableEq εB] in
/-- **The output regrouping bridge.**  The decoders act on
`(ι_{A'} × ε_A) × (ι_{B'} × ε_B)` while `E_g` acts on
`(ι_{A'} × ι_{B'}) × (ε_A × ε_B)`.  Transporting the operator across
`NLQCLean.outputRegroup` turns compression through `E_g` into compression
through `E_g` read as a *resource* insertion in the by-laboratory grouping,
which is the form the shared-state compression lemmas are stated in. -/
theorem insertVector_compress_eq (g : εA × εB → ℂ)
    (G : Matrix ((ιA' × εA) × (ιB' × εB)) ((ιA' × εA) × (ιB' × εB)) ℂ) :
    (insertVector (ιA' × ιB') g)ᴴ
        * G.submatrix (outputRegroup ιA' ιB' εA εB) (outputRegroup ιA' ιB' εA εB)
        * insertVector (ιA' × ιB') g
      = (insertResource ιA' ιB' g)ᴴ * G * insertResource ιA' ιB' g := by
  have hbij : Function.Bijective (outputRegroup ιA' ιB' εA εB) :=
    (outputRegroup ιA' ιB' εA εB).bijective
  rw [insertVector_eq_insertResource_submatrix, Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ hbij, ← Matrix.submatrix_mul _ _ _ _ _ hbij,
    Matrix.submatrix_id_id]

/-- The output generator is local by resource compression after regrouping,
with `g` as the resource. -/
theorem outputGenerator_mem_localSkew (g gdot : εA × εB → ℂ)
    {XA : Matrix (ιA' × εA) (ιA' × εA) ℂ} {XB : Matrix (ιB' × εB) (ιB' × εB) ℂ}
    (hXA : XAᴴ = -XA) (hXB : XBᴴ = -XB) (hg : (vecInner gdot g).re = 0) :
    vecInner gdot g • (1 : Matrix (ιA' × ιB') (ιA' × ιB') ℂ)
      + (insertVector (ιA' × ιB') g)ᴴ
        * (ampLeft (ιA' × εA) (ιB' × εB) XA
           + ampRight (ιA' × εA) (ιB' × εB) XB).submatrix
            (outputRegroup ιA' ιB' εA εB) (outputRegroup ιA' ιB' εA εB)
        * insertVector (ιA' × ιB') g
      ∈ localSkew ιA' ιB' := by
  rw [add_comm, insertVector_compress_eq]
  exact compressed_pair_add_scalar_mem_localSkew g hXA hXB hg

end OutputRegrouping

section QP4Assembly

variable {ιA ιB ιA' ιB' ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [DecidableEq ρA] [DecidableEq ρB]
variable [Fintype ιA] [Fintype ιB] [Fintype ιA'] [Fintype ιB']
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ιA'] [DecidableEq ιB']
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]

/-- At an exact witness, the forward differential is `Ḣ = b U + U a`.

The three summands on the left are the three terms of the product rule for
`H = E_g† W Y`. The identity uses exactness at the single point and the
decoder velocity's skew generator; it does not require a varied witness to
stay exact or near-exact. -/
theorem forwardDifferential_eq
    {W Wdot : Matrix ((ιA' × ιB') × (εA × εB)) ((κA × μB) × (κB × μA)) ℂ}
    {G : Matrix ((ιA' × ιB') × (εA × εB)) ((ιA' × ιB') × (εA × εB)) ℂ}
    {Y Ydot : Matrix ((κA × μB) × (κB × μA)) (ιA × ιB) ℂ}
    {g gdot : εA × εB → ℂ} {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ}
    (hW : IsIsometry W) (hU : U * Uᴴ = 1)
    (hexact : W * Y = insertVector (ιA' × ιB') g * U)
    (hWdot : Wdot = G * W) :
    (insertVector (ιA' × ιB') gdot)ᴴ * (W * Y)
        + (insertVector (ιA' × ιB') g)ᴴ * (Wdot * Y)
        + (insertVector (ιA' × ιB') g)ᴴ * (W * Ydot)
      = (vecInner gdot g • (1 : Matrix (ιA' × ιB') (ιA' × ιB') ℂ)
          + (insertVector (ιA' × ιB') g)ᴴ * G * insertVector (ιA' × ιB') g) * U
        + U * (Yᴴ * Ydot) := by
  have hT1 : (insertVector (ιA' × ιB') gdot)ᴴ * (W * Y)
      = (vecInner gdot g • (1 : Matrix (ιA' × ιB') (ιA' × ιB') ℂ)) * U := by
    rw [hexact, ← Matrix.mul_assoc, insertVector_gram]
  have hT2 : (insertVector (ιA' × ιB') g)ᴴ * (Wdot * Y)
      = ((insertVector (ιA' × ιB') g)ᴴ * G * insertVector (ιA' × ιB') g) * U := by
    rw [hWdot]
    simp only [Matrix.mul_assoc]
    rw [hexact]
  have hT3 : (insertVector (ιA' × ιB') g)ᴴ * (W * Ydot) = U * (Yᴴ * Ydot) := by
    rw [← Matrix.mul_assoc (insertVector (ιA' × ιB') g)ᴴ W Ydot,
      conjTranspose_mul_of_exact' hW hU hexact, Matrix.mul_assoc]
  rw [hT1, hT2, hT3, Matrix.add_mul]

/-- **Exact-witness derivative constraints.**  At an exact witness, for
arbitrary block velocities satisfying the linearized constraints, the forward
differential is `b U + U a` with `a` and `b` local skew-Hermitian generators on
the input and output logical spaces respectively. -/
theorem forwardDifferential_local
    {W Wdot : Matrix ((ιA' × ιB') × (εA × εB)) ((κA × μB) × (κB × μA)) ℂ}
    {XA : Matrix (ιA' × εA) (ιA' × εA) ℂ} {XB : Matrix (ιB' × εB) (ιB' × εB) ℂ}
    {Y Ydot : Matrix ((κA × μB) × (κB × μA)) (ιA × ιB) ℂ}
    {g gdot : εA × εB → ℂ} {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ}
    (hW : IsIsometry W) (hU : U * Uᴴ = 1)
    (hexact : W * Y = insertVector (ιA' × ιB') g * U)
    (hWdot : Wdot =
      (ampLeft (ιA' × εA) (ιB' × εB) XA
        + ampRight (ιA' × εA) (ιB' × εB) XB).submatrix
          (outputRegroup ιA' ιB' εA εB) (outputRegroup ιA' ιB' εA εB) * W)
    (hXA : XAᴴ = -XA) (hXB : XBᴴ = -XB) (hg : (vecInner gdot g).re = 0) :
    ∃ b ∈ localSkew ιA' ιB',
      (insertVector (ιA' × ιB') gdot)ᴴ * (W * Y)
          + (insertVector (ιA' × ιB') g)ᴴ * (Wdot * Y)
          + (insertVector (ιA' × ιB') g)ᴴ * (W * Ydot)
        = b * U + U * (Yᴴ * Ydot) := by
  refine ⟨_, outputGenerator_mem_localSkew g gdot hXA hXB hg, ?_⟩
  exact forwardDifferential_eq hW hU hexact hWdot

/-- **Exact-witness derivative constraints in one statement.**

At an exact witness, and for *arbitrary* block velocities satisfying the six
linearized constraints — two sphere constraints for `η` and `g`, two isometry
constraints for the encoders, and the decoder velocity presented through the skew
lift — the forward differential is `Ḣ = b U + U a` with `a` and `b` local
skew-Hermitian generators on the input and output logical spaces.

This is algebraic and pointwise. No curve is assumed to remain exact, or even
near-exact, and the only differentiability used is that the supplied velocities
are the product-rule ones. -/
theorem forwardDifferential_local_full
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {VA' : Matrix (κA × μA) (ιA × ρA) ℂ} {VB' : Matrix (κB × μB) (ιB × ρB) ℂ}
    {W Wdot : Matrix ((ιA' × ιB') × (εA × εB)) ((κA × μB) × (κB × μA)) ℂ}
    {XA : Matrix (ιA' × εA) (ιA' × εA) ℂ} {XB : Matrix (ιB' × εB) (ιB' × εB) ℂ}
    {η η' : ρA × ρB → ℂ} {g gdot : εA × εB → ℂ}
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hVA' : VAᴴ * VA' + VA'ᴴ * VA = 0) (hVB' : VBᴴ * VB' + VB'ᴴ * VB = 0)
    (hη' : (vecInner η η').re = 0)
    (hW : IsIsometry W) (hU : U * Uᴴ = 1)
    (hexact : W * encodedState η VA VB = insertVector (ιA' × ιB') g * U)
    (hWdot : Wdot =
      (ampLeft (ιA' × εA) (ιB' × εB) XA
        + ampRight (ιA' × εA) (ιB' × εB) XB).submatrix
          (outputRegroup ιA' ιB' εA εB) (outputRegroup ιA' ιB' εA εB) * W)
    (hXA : XAᴴ = -XA) (hXB : XBᴴ = -XB) (hg : (vecInner gdot g).re = 0) :
    ∃ a ∈ localSkew ιA ιB, ∃ b ∈ localSkew ιA' ιB',
      (insertVector (ιA' × ιB') gdot)ᴴ * (W * encodedState η VA VB)
          + (insertVector (ιA' × ιB') g)ᴴ * (Wdot * encodedState η VA VB)
          + (insertVector (ιA' × ιB') g)ᴴ
              * (W * encodedStateVelocity η η' VA VA' VB VB')
        = b * U + U * a := by
  refine ⟨_, encodedState_velocity_mem_localSkew hVA hVB η η' hVA' hVB' hη',
    _, outputGenerator_mem_localSkew g gdot hXA hXB hg, ?_⟩
  exact forwardDifferential_eq hW hU hexact hWdot

end QP4Assembly

end NLQCLean

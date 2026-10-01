import NLQCLean.Rigidity.ForwardExactDifferential

/-!
# Forward differential at an exact PVM witness

At an exact frozen PVM witness `W Y = C_ω T`, where `C_ω` is the
flagged isometry, arbitrary tangent velocities of the flags, decoders and
encoders give a forward differential `b T + T a`. Here `a` is local
skew-Hermitian on the input and `b` is **diagonal** skew-Hermitian on the
outcome labels. The proof is pointwise algebra; no exact curve is assumed.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section FlagCalculus

variable {δ εA εB : Type*} [Fintype δ] [DecidableEq δ]
variable [Fintype εA] [DecidableEq εA] [Fintype εB] [DecidableEq εB]

omit [DecidableEq εA] [DecidableEq εB] in
/-- Cross-Grams of two flagged isometries are diagonal. -/
theorem flagIsometry_conjTranspose_mul_mem_diagonal (ω θ : δ → εA × εB → ℂ) :
    (flagIsometry ω)ᴴ * flagIsometry θ ∈ diagonalSubmodule δ := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases eq_or_ne p.1.1 j with hj | hj
  · have hne : ¬(p.1.1 = i) := by rw [hj]; exact fun h => hij h.symm
    simp [flagIsometry, hne]
  · simp [flagIsometry, hj]

omit [DecidableEq εA] [DecidableEq εB] in
/-- A diagonal entry of the flag cross-Gram is the inner product of the flags. -/
theorem flagIsometry_conjTranspose_mul_apply_self (ω θ : δ → εA × εB → ℂ) (i : δ) :
    ((flagIsometry ω)ᴴ * flagIsometry θ) i i = vecInner (ω i) (θ i) := by
  rw [Matrix.mul_apply, vecInner, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [flagIsometry, Fintype.sum_prod_type]

omit [DecidableEq εA] [DecidableEq εB] in
/-- Tangent flag velocities give a diagonal skew-Hermitian cross-Gram. -/
theorem flagIsometry_conjTranspose_mul_mem_diagSkew (ω θ : δ → εA × εB → ℂ)
    (h : ∀ i, (vecInner (ω i) (θ i)).re = 0) :
    (flagIsometry ω)ᴴ * flagIsometry θ ∈ diagSkew δ := by
  rw [mem_diagSkew_iff]
  refine ⟨flagIsometry_conjTranspose_mul_mem_diagonal ω θ, ?_⟩
  apply conjTranspose_mul_skew
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  by_cases hij : i = j
  · subst j
    rw [flagIsometry_conjTranspose_mul_apply_self, flagIsometry_conjTranspose_mul_apply_self]
    have hc : vecInner (θ i) (ω i) = star (vecInner (ω i) (θ i)) := by
      rw [vecInner, vecInner, star_sum]
      exact Finset.sum_congr rfl fun e _ => by rw [star_mul', star_star]; ring
    rw [hc]
    apply Complex.ext <;> simp [h i]
  · rw [flagIsometry_conjTranspose_mul_mem_diagonal ω θ i j hij,
      flagIsometry_conjTranspose_mul_mem_diagonal θ ω i j hij, add_zero]

/-- Local skew-Hermitian decoder generators compress through a flag to `diagSkew`. -/
theorem flag_local_compression_mem_diagSkew (ω : δ → εA × εB → ℂ)
    {XA : Matrix (δ × εA) (δ × εA) ℂ} {XB : Matrix (δ × εB) (δ × εB) ℂ}
    (hXA : XAᴴ = -XA) (hXB : XBᴴ = -XB) :
    (flagIsometry ω)ᴴ * (ampLeft (δ × εA) (δ × εB) XA + ampRight (δ × εA) (δ × εB) XB) *
        flagIsometry ω ∈ diagSkew δ := by
  rw [mem_diagSkew_iff]
  constructor
  · rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ (flag_compression_mem_diagonal ω XA)
      (flag_compression_right_mem_diagonal ω XB)
  · have hlocal : ampLeft (δ × εA) (δ × εB) XA + ampRight (δ × εA) (δ × εB) XB
        ∈ localSkew (δ × εA) (δ × εB) := mem_localSkew_iff.mpr ⟨XA, hXA, XB, hXB, rfl⟩
    have hskew := mem_skewHermitian_iff.mp (localSkew_le_skewHermitian hlocal)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end FlagCalculus

section ForwardDifferential

variable {δ εA εB ι K : Type*} [Fintype δ] [DecidableEq δ]
variable [Fintype εA] [DecidableEq εA] [Fintype εB] [DecidableEq εB]
variable [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]

/-- The three product-rule terms of `H = C_ω† W Y` at an exact PVM witness. -/
theorem pvmForwardDifferential_eq
    {W Wdot : Matrix ((δ × εA) × (δ × εB)) K ℂ}
    {G : Matrix ((δ × εA) × (δ × εB)) ((δ × εA) × (δ × εB)) ℂ}
    {Y Ydot : Matrix K ι ℂ} {ω ωdot : δ → εA × εB → ℂ} {T : Matrix δ ι ℂ}
    (hW : IsIsometry W) (hT : T * Tᴴ = 1)
    (hexact : W * Y = flagIsometry ω * T) (hWdot : Wdot = G * W) :
    (flagIsometry ωdot)ᴴ * (W * Y) + (flagIsometry ω)ᴴ * (Wdot * Y)
        + (flagIsometry ω)ᴴ * (W * Ydot)
      = ((flagIsometry ωdot)ᴴ * flagIsometry ω
          + (flagIsometry ω)ᴴ * G * flagIsometry ω) * T + T * (Yᴴ * Ydot) := by
  have hT1 : (flagIsometry ωdot)ᴴ * (W * Y) = ((flagIsometry ωdot)ᴴ * flagIsometry ω) * T := by
    rw [hexact, Matrix.mul_assoc]
  have hT2 : (flagIsometry ω)ᴴ * (Wdot * Y) = ((flagIsometry ω)ᴴ * G * flagIsometry ω) * T := by
    rw [hWdot]
    simp only [Matrix.mul_assoc]
    rw [hexact]
  have hT3 : (flagIsometry ω)ᴴ * (W * Ydot) = T * (Yᴴ * Ydot) := by
    rw [← Matrix.mul_assoc (flagIsometry ω)ᴴ W Ydot, conjTranspose_mul_of_exact' hW hT hexact,
      Matrix.mul_assoc]
  rw [hT1, hT2, hT3, Matrix.add_mul]

end ForwardDifferential

section LocalFull

variable {ιA ιB ρA ρB κA κB μA μB δ εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

/-- **PP7 exact-witness differential for PVMs.** At an exact frozen PVM witness,
arbitrary tangent velocities of the resource, encoders, decoders (through
their skew lifts) and flags give `b T + T a`. Here `a` is local skew-Hermitian on
the inputs and `b` is diagonal skew-Hermitian on the outcome labels. -/
theorem pvmForwardDifferential_local_full
    {VA : Matrix (κA × μA) (ιA × ρA) ℂ} {VB : Matrix (κB × μB) (ιB × ρB) ℂ}
    {VA' : Matrix (κA × μA) (ιA × ρA) ℂ} {VB' : Matrix (κB × μB) (ιB × ρB) ℂ}
    {W Wdot : Matrix ((δ × εA) × (δ × εB)) ((κA × μB) × (κB × μA)) ℂ}
    {XA : Matrix (δ × εA) (δ × εA) ℂ} {XB : Matrix (δ × εB) (δ × εB) ℂ}
    {η η' : ρA × ρB → ℂ} {ω ωdot : δ → εA × εB → ℂ}
    {T : Matrix δ (ιA × ιB) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hVA' : VAᴴ * VA' + VA'ᴴ * VA = 0) (hVB' : VBᴴ * VB' + VB'ᴴ * VB = 0)
    (hη' : (vecInner η η').re = 0)
    (hW : IsIsometry W) (hT : T * Tᴴ = 1)
    (hexact : W * encodedState η VA VB = flagIsometry ω * T)
    (hWdot : Wdot = (ampLeft (δ × εA) (δ × εB) XA + ampRight (δ × εA) (δ × εB) XB) * W)
    (hXA : XAᴴ = -XA) (hXB : XBᴴ = -XB) (hω : ∀ i, (vecInner (ωdot i) (ω i)).re = 0) :
    ∃ a ∈ localSkew ιA ιB, ∃ b ∈ diagSkew δ,
      (flagIsometry ωdot)ᴴ * (W * encodedState η VA VB)
          + (flagIsometry ω)ᴴ * (Wdot * encodedState η VA VB)
          + (flagIsometry ω)ᴴ * (W * encodedStateVelocity η η' VA VA' VB VB')
        = b * T + T * a := by
  refine ⟨_, encodedState_velocity_mem_localSkew hVA hVB η η' hVA' hVB' hη', _,
    Submodule.add_mem _ (flagIsometry_conjTranspose_mul_mem_diagSkew ωdot ω hω)
      (flag_local_compression_mem_diagSkew ω hXA hXB), ?_⟩
  exact pvmForwardDifferential_eq hW hT hexact hWdot

end LocalFull

end NLQCLean

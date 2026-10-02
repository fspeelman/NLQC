import NLQCLean.Exact.PVMBadDecomposition
import NLQCLean.Exact.ExactBadDecomposition
import NLQCLean.Exact.PolynomialWitnessMaps

/-!
# Rigidity statements of the exact paper

Source-shaped forms of the rigidity lemmas:

* `lem:rigidity`: an isometric dilation reproducing `U ρ U†` on pure input
  states is `E_γ U` for a fixed unit garbage vector `γ`;
* `cor:reformulation` and `lem:frozendilation`: exact implementation is
  equivalent to the frozen form `F = E_γ U`;
* `lem:rigidity-pvm`: exact two-sided rank-one PVM implementation is
  equivalent to `F = C_γ M†` with unit vectors `γ_i`;
* `lem:labels`: compressions of local operators by `C_γ` are diagonal and
  `C_γ` is an isometry;
* `lem:compression_state`: compressing a local operator through a shared state
  gives a local operator, preserves anti-Hermiticity, and has polynomial
  entries.
-/

noncomputable section

namespace NLQCLean

open Matrix
open scoped Kronecker

section PureStates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem vecMulVec_add_smul (x y : ι → ℂ) (c : ℂ) :
    Matrix.vecMulVec (x + c • y) (star (x + c • y)) = Matrix.vecMulVec x (star x) +
      star c • Matrix.vecMulVec x (star y) + c • Matrix.vecMulVec y (star x) +
      (c * star c) • Matrix.vecMulVec y (star y) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add,
    star_smul, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  ring

omit [Fintype ι] in
theorem single_eq_vecMulVec (i j : ι) :
    Matrix.single i j (1 : ℂ) = Matrix.vecMulVec (Pi.single i 1) (star (Pi.single j (1 : ℂ))) := by
  ext a b
  rw [Matrix.vecMulVec_apply, Matrix.single_apply]
  simp only [Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- Two linear maps on matrices agreeing on every pure state agree. -/
theorem linearMap_ext_of_pure {N : Type*} [AddCommGroup N] [Module ℂ N]
    (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] N)
    (h : ∀ ψ : ι → ℂ, IsUnitVector ψ → Φ (Matrix.vecMulVec ψ (star ψ)) =
      Ψ (Matrix.vecMulVec ψ (star ψ))) : Φ = Ψ := by
  have hall : ∀ ψ : ι → ℂ, Φ (Matrix.vecMulVec ψ (star ψ)) = Ψ (Matrix.vecMulVec ψ (star ψ)) := by
    intro ψ
    by_cases h0 : ψ = 0
    · subst h0
      simp
    · set c : ℝ := Real.sqrt (∑ e, Complex.normSq (ψ e))
      have hs : 0 < ∑ e, Complex.normSq (ψ e) := by
        obtain ⟨e, he⟩ := Function.ne_iff.mp h0
        exact lt_of_lt_of_le (Complex.normSq_pos.mpr he)
          (Finset.single_le_sum (fun e _ => Complex.normSq_nonneg (ψ e)) (Finset.mem_univ e))
      have hc : 0 < c := Real.sqrt_pos.mpr hs
      set u : ι → ℂ := (c⁻¹ : ℂ) • ψ
      have hu : IsUnitVector u := by
        unfold IsUnitVector
        simp only [u, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_inv,
          Complex.normSq_ofReal, ← Finset.mul_sum]
        rw [show c * c = ∑ e, Complex.normSq (ψ e) from Real.mul_self_sqrt hs.le]
        exact inv_mul_cancel₀ hs.ne'
      have hψ : ψ = (c : ℂ) • u := by
        simp only [u, smul_smul]
        rw [mul_inv_cancel₀ (by exact_mod_cast hc.ne'), one_smul]
      have hv : Matrix.vecMulVec ψ (star ψ) = ((c : ℂ) * c) • Matrix.vecMulVec u (star u) := by
        rw [hψ]
        ext a b
        simp [Matrix.vecMulVec_apply]
        ring
      rw [hv, map_smul, map_smul, h u hu]
  have hD : ∀ M, Φ M = Ψ M ↔ (Φ - Ψ) M = 0 := fun M => by
    rw [LinearMap.sub_apply, sub_eq_zero]
  have hdiag : ∀ ψ : ι → ℂ, (Φ - Ψ) (Matrix.vecMulVec ψ (star ψ)) = 0 :=
    fun ψ => (hD _).mp (hall ψ)
  have hoff : ∀ x y : ι → ℂ, (Φ - Ψ) (Matrix.vecMulVec x (star y)) = 0 := by
    intro x y
    have h1 := hdiag (x + (1 : ℂ) • y)
    have hI := hdiag (x + Complex.I • y)
    rw [vecMulVec_add_smul, map_add, map_add, map_add, map_smul, map_smul, map_smul,
      hdiag x, hdiag y] at h1 hI
    simp only [star_one, one_smul, smul_zero, add_zero, zero_add] at h1 hI
    have hIc : star Complex.I = -Complex.I := by simp
    rw [hIc, neg_smul] at hI
    set u := (Φ - Ψ) (Matrix.vecMulVec x (star y))
    set w := (Φ - Ψ) (Matrix.vecMulVec y (star x))
    have hw : w = -u := eq_neg_of_add_eq_zero_right h1
    rw [hw, smul_neg, ← neg_add, neg_eq_zero, ← two_smul ℂ (Complex.I • u), smul_smul] at hI
    have h2I : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    exact (smul_eq_zero.mp hI).resolve_left h2I
  refine LinearMap.ext fun ρ => (hD ρ).mpr ?_
  rw [Matrix.matrix_eq_sum_single ρ, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show Matrix.single i j (ρ i j) = ρ i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, single_eq_vecMulVec, hoff,
    smul_zero]

end PureStates

section Unitary

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

omit [DecidableEq ε] in
/-- **`lem:rigidity`.** If an isometry `F : H → H ⊗ G` reproduces `U ρ U†` after
tracing out `G` on every pure input state, then `F = E_γ U` for a unit vector
`γ ∈ G`. -/
theorem rigidity_of_pure_states [Nonempty ι] {F : Matrix (κ × ε) ι ℂ} {U : Matrix κ ι ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hF : ∀ ψ : ι → ℂ, IsUnitVector ψ →
      channelOf F (Matrix.vecMulVec ψ (star ψ)) = U * Matrix.vecMulVec ψ (star ψ) * Uᴴ) :
    ∃ γ : ε → ℂ, IsUnitVector γ ∧ F = insertVector κ γ * U :=
  exists_frozen_unitary hU hU' (linearMap_ext_of_pure _ _ hF)

end Unitary

section Protocols

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- **`cor:reformulation`.** A one-round protocol implements a unitary exactly if
and only if its global isometry is `E_γ U` for a unit garbage vector `γ` on
the discarded registers. -/
theorem PureProtocol.performsUnitary_iff_frozen [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    {U : Matrix (ιA' × ιB') (ιA × ιB) ℂ} (hU : UnitaryTarget U) :
    P.PerformsUnitary U ↔ ∃ γ : εA × εB → ℂ, IsUnitVector γ ∧
      globalIsometryRegrouped P.resource P.encA P.encB P.decA P.decB =
        insertVector (ιA' × ιB') γ * U := by
  constructor
  · intro h
    exact exists_frozen_unitary hU.conjTranspose_mul_self hU.self_mul_conjTranspose h
  · rintro ⟨γ, hγ, hF⟩
    change channelOf (globalIsometryRegrouped P.resource P.encA P.encB P.decA P.decB) = adConj U
    rw [hF]
    exact channelOf_insertVector_mul hγ U

omit [DecidableEq εA] [DecidableEq εB] in
/-- **`lem:rigidity-pvm`.** For a unitary basis matrix `M`, an isometry `F`
implements the ordered rank-one PVM exactly, with both parties obtaining the
outcome, if and only if `F = C_γ M†` for unit vectors `γ_i`. -/
theorem twoSidedExact_iff_flag {δ n : Type*} [Fintype δ] [DecidableEq δ] [Fintype n]
    [DecidableEq n] {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} {M : Matrix n δ ℂ}
    (hM : Mᴴ * M = 1) (hM' : M * Mᴴ = 1) :
    TwoSidedExact F M ↔ ∃ γ : δ → εA × εB → ℂ, (∀ i, IsUnitVector (γ i)) ∧
      F = flagIsometry γ * Mᴴ := by
  constructor
  · intro h
    obtain ⟨γ, hγ, hF, -⟩ := exists_frozen_pvm hM hM' h
    exact ⟨γ, hγ, hF⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact twoSidedExact_flag_mul_adjoint γ hγ M

/-- **`lem:labels`.** Compressing an operator on `A'E_A` or on `B'E_B` by the
duplicated-label map gives a diagonal matrix, and the duplicated-label map
with unit garbage vectors is an isometry. -/
theorem duplicated_labels {δ : Type*} [Fintype δ] [DecidableEq δ]
    (γ : δ → εA × εB → ℂ) (hγ : ∀ i, IsUnitVector (γ i))
    (ZA : Matrix (δ × εA) (δ × εA) ℂ) (ZB : Matrix (δ × εB) (δ × εB) ℂ) :
    (flagIsometry γ)ᴴ * (ZA ⊗ₖ (1 : Matrix (δ × εB) (δ × εB) ℂ)) * flagIsometry γ ∈
        diagonalSubmodule δ ∧
      (flagIsometry γ)ᴴ * ((1 : Matrix (δ × εA) (δ × εA) ℂ) ⊗ₖ ZB) * flagIsometry γ ∈
        diagonalSubmodule δ ∧
      IsIsometry (flagIsometry γ) :=
  ⟨flag_compression_mem_diagonal γ ZA, flag_compression_right_mem_diagonal γ ZB,
    isIsometry_flagIsometry γ hγ⟩

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] [DecidableEq ιA'] [DecidableEq ιB']
  [DecidableEq εA] [DecidableEq εB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
  [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] [DecidableEq ρA] in
/-- **`lem:compression_state`.** Compressing an Alice-local operator `c` on
`H_{A_l} ⊗ H_{A_s}` through a shared state `η ∈ H_{A_s} ⊗ H_{B_s}` gives
`ĉ ⊗ I` with `ĉ` acting on `H_{A_l}` only; `ĉ` is anti-Hermitian when `c` is,
and the real and imaginary parts of its entries are polynomials in those of
`c` and `η`. -/
theorem compression_state (η : ρA × ρB → ℂ) (c : Matrix (ιA × ρA) (ιA × ρA) ℂ) :
    (insertResource ιA ιB η)ᴴ * (c ⊗ₖ (1 : Matrix (ιB × ρB) (ιB × ρB) ℂ)) *
        insertResource ιA ιB η = compressResource η c ⊗ₖ (1 : Matrix ιB ιB ℂ) ∧
      (cᴴ = -c → (compressResource (ιA := ιA) η c)ᴴ = -compressResource η c) ∧
      IsPolyMatrix (fun p : (ρA × ρB → ℂ) × Matrix (ιA × ρA) (ιA × ρA) ℂ =>
        compressResource p.1 p.2) := by
  refine ⟨compress_resource_ampLeft η c, fun hc => ?_, ?_⟩
  · rw [← compressResource_conjTranspose, hc, compressResource_neg]
  · have hη : IsPolyVec (fun p : (ρA × ρB → ℂ) × Matrix (ιA × ρA) (ιA × ρA) ℂ => p.1) :=
      IsPolyVec.of_linear (LinearMap.fst ℝ (ρA × ρB → ℂ) (Matrix (ιA × ρA) (ιA × ρA) ℂ) :
        (ρA × ρB → ℂ) × Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℝ] (ρA × ρB → ℂ))
    have hc : IsPolyMatrix (fun p : (ρA × ρB → ℂ) × Matrix (ιA × ρA) (ιA × ρA) ℂ => p.2) :=
      IsPolyMatrix.linear (LinearMap.snd ℝ (ρA × ρB → ℂ) (Matrix (ιA × ρA) (ιA × ρA) ℂ) :
        (ρA × ρB → ℂ) × Matrix (ιA × ρA) (ιA × ρA) ℂ →ₗ[ℝ] Matrix (ιA × ρA) (ιA × ρA) ℂ)
    intro a a'
    simp only [compressResource, Matrix.of_apply, resourceMarginal]
    exact IsComplexPoly.sum _ fun r _ => IsComplexPoly.sum _ fun r' _ =>
      (IsComplexPoly.sum _ fun s _ => (hη (r, s)).mul (hη (r', s)).star).mul (hc _ _)

end Protocols

section Bad

variable {d : ℕ}

/-- **`lem:frozendilation`.** A unitary is exactly implementable if and only if
some finite strategy has global isometry `E_γ U` for a unit garbage vector. -/
theorem mem_exactUnitaryBad_iff_frozen [NeZero d] {U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} :
    U ∈ exactUnitaryBad d ↔ UnitaryTarget U ∧ ∃ s : ForwardShape,
      ∃ P : PureProtocol (Fin d) (Fin d) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
        (Fin (s 4)) (Fin (s 5)) (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7)),
        ∃ γ : Fin (s 6) × Fin (s 7) → ℂ, IsUnitVector γ ∧
          globalIsometryRegrouped P.resource P.encA P.encB P.decA P.decB =
            insertVector (Fin d × Fin d) γ * U := by
  constructor
  · rintro ⟨hU, s, P, hP⟩
    exact ⟨hU, s, P, (P.performsUnitary_iff_frozen hU).mp hP⟩
  · rintro ⟨hU, s, P, hγ⟩
    exact ⟨hU, s, P, (P.performsUnitary_iff_frozen hU).mpr hγ⟩

end Bad

end NLQCLean

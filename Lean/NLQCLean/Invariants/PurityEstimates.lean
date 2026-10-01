import NLQCLean.Invariants.OperatorSchmidtPurity
import NLQCLean.Geometry.MatrixPolynomialDegree
import NLQCLean.LinearAlgebra.FrobeniusInner
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative estimates for realignment purity

The estimates hold at every complex matrix, with the normalization retained
as an explicit scalar. In particular they apply to nonunitary overlap
matrices in the polynomial witness source.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exchange only the first subsystem of two copies of a bipartite register. -/
def swapFirstCopies (p : (ι × ι) × (ι × ι)) : (ι × ι) × (ι × ι) :=
  ((p.2.1, p.1.2), (p.1.1, p.2.2))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem swapFirstCopies_involutive (p : (ι × ι) × (ι × ι)) :
    swapFirstCopies (swapFirstCopies p) = p := by
  rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

/-- The matrix of the swap `S_A` in the operator-purity trace formula. -/
def firstCopiesSwapMatrix :
    Matrix ((ι × ι) × (ι × ι)) ((ι × ι) × (ι × ι)) ℂ :=
  fun p q => if swapFirstCopies p = q then 1 else 0

theorem mul_firstCopiesSwapMatrix
    (M : Matrix ((ι × ι) × (ι × ι)) ((ι × ι) × (ι × ι)) ℂ) :
    M * firstCopiesSwapMatrix = M.submatrix id swapFirstCopies := by
  ext p q
  have hi (u : (ι × ι) × (ι × ι)) :
      swapFirstCopies u = q ↔ u = swapFirstCopies q := by
    constructor
    · intro h
      simpa using congrArg swapFirstCopies h
    · rintro rfl
      simp
  change (∑ u, M p u * (if swapFirstCopies u = q then 1 else 0)) = M p (swapFirstCopies q)
  simp only [hi, mul_ite, mul_one, mul_zero]
  simp

/-- Reindex the four realignment indices as two doubled-register indices. -/
def puritySwapTraceEquiv :
    (((ι × ι) × (ι × ι)) × ((ι × ι) × (ι × ι))) ≃
      (((ι × ι) × (ι × ι)) × ((ι × ι) × (ι × ι))) where
  toFun x :=
    (((x.1.1.1, x.2.1.1), (x.1.2.1, x.2.2.1)),
      ((x.1.2.2, x.2.1.2), (x.1.1.2, x.2.2.2)))
  invFun x :=
    (((x.1.1.1, x.2.2.1), (x.1.2.1, x.2.1.1)),
      ((x.1.1.2, x.2.1.2), (x.1.2.2, x.2.2.2)))
  left_inv x := by rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨⟨e, f⟩, ⟨g, h⟩⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨⟨e, f⟩, ⟨g, h⟩⟩⟩; rfl

omit [DecidableEq ι] in
/-- Group four pair indices without recursively expanding their components. -/
theorem sum_four_pair_indices
    (f : (((ι × ι) × (ι × ι)) × ((ι × ι) × (ι × ι))) → ℂ) :
    ∑ x, f x = ∑ i : ι × ι, ∑ j : ι × ι, ∑ k : ι × ι, ∑ l : ι × ι, f ((i, j), (k, l)) := by
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type (f := fun p : (ι × ι) × (ι × ι) =>
    ∑ q : (ι × ι) × (ι × ι), f (p, q))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Fintype.sum_prod_type (f := fun q : (ι × ι) × (ι × ι) => f ((i, j), q))

/-- The realignment trace and the swap trace agree for every matrix. -/
theorem realign_trace_eq_swap_trace (X : Matrix (ι × ι) (ι × ι) ℂ) :
    Matrix.trace ((realign X * (realign X)ᴴ) * (realign X * (realign X)ᴴ)) =
      Matrix.trace (((X ⊗ₖ X) * firstCopiesSwapMatrix) *
        ((X ⊗ₖ X)ᴴ * firstCopiesSwapMatrix)) := by
  rw [mul_firstCopiesSwapMatrix, mul_firstCopiesSwapMatrix]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq, Finset.sum_mul, Finset.mul_sum]
  let f := fun x : (((ι × ι) × (ι × ι)) × ((ι × ι) × (ι × ι))) =>
    realign X x.1.1 x.2.1 * star (realign X x.1.2 x.2.1) *
      (realign X x.1.2 x.2.2 * star (realign X x.1.1 x.2.2))
  let g := fun x : (((ι × ι) × (ι × ι)) × ((ι × ι) × (ι × ι))) =>
    (X ⊗ₖ X) x.1 (swapFirstCopies x.2) * star ((X ⊗ₖ X) (swapFirstCopies x.1) x.2)
  have he : ∑ x, f x = ∑ x, g x :=
    Fintype.sum_equiv puritySwapTraceEquiv f g (fun x => by
      simp only [f, g, puritySwapTraceEquiv, Equiv.coe_fn_mk, realign_apply,
        swapFirstCopies, Matrix.kroneckerMap_apply, star_mul']
      ring)
  rw [sum_four_pair_indices] at he
  -- The second sum has only the two doubled-register indices.
  rw [Fintype.sum_prod_type (f := g)] at he
  calc
    _ = ∑ i : ι × ι, ∑ j : ι × ι, ∑ k : ι × ι, ∑ l : ι × ι, f ((i, j), (k, l)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact Finset.sum_comm
    _ = _ := he

/-- The normalization remains exactly the scalar in the original invariant. -/
theorem purity_eq_swap_trace (c : ℝ) (X : Matrix (ι × ι) (ι × ι) ℂ) :
    purity c X = c * (Matrix.trace (((X ⊗ₖ X) * firstCopiesSwapMatrix) *
      ((X ⊗ₖ X)ᴴ * firstCopiesSwapMatrix))).re := by
  rw [purity, realign_trace_eq_swap_trace]

/-- Realignment only permutes entries, so it preserves the Frobenius norm. -/
theorem realign_norm (X : Matrix (ι × ι) (ι × ι) ℂ) : ‖realign X‖ = ‖X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [frobNorm_sq, Fintype.sum_prod_type, realign_apply]
  congr 1
  funext i
  rw [Finset.sum_comm]

/-- A trace pairing obeys Frobenius Cauchy--Schwarz without a dimension factor. -/
theorem norm_trace_mul_le_frob {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : ‖Matrix.trace (A * B)‖ ≤ ‖A‖ * ‖B‖ := by
  have h := norm_frobInner_le Aᴴ B
  simpa only [frobInner_eq_trace, Matrix.conjTranspose_conjTranspose,
    Matrix.frobenius_norm_conjTranspose] using h

omit [DecidableEq ι] in
/-- The differential of the quartic invariant along an arbitrary straight line. -/
theorem hasDerivAt_purity_line (c : ℝ) (X V : Matrix (ι × ι) (ι × ι) ℂ) :
    HasDerivAt (fun t : ℝ => purity c (X + t • V))
      (c * (Matrix.trace
        ((realign X * (realign X)ᴴ) *
            (realign X * (realign V)ᴴ + realign V * (realign X)ᴴ) +
          (realign X * (realign V)ᴴ + realign V * (realign X)ᴴ) *
            (realign X * (realign X)ᴴ))).re) 0 := by
  have hl : HasDerivAt (fun t : ℝ => X + t • V) V 0 := hasDerivAt_line X V
  have hr : HasDerivAt (fun t : ℝ => realign (X + t • V)) (realign V) 0 :=
    HasDerivAt.ofLinearMap ((realignLM (ι := ι)).restrictScalars ℝ) hl
  have hs := HasDerivAt.matrixMul hr (HasDerivAt.matrixConjTranspose hr)
  have hss := HasDerivAt.matrixMul hs hs
  have htr := HasDerivAt.ofLinearMap
    ((Matrix.traceLinearMap (ι × ι) ℂ ℂ).restrictScalars ℝ) hss
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 htr
  simpa [purity, Function.comp_def] using hre.const_mul c

omit [DecidableEq ι] in
/-- The full Fréchet derivative agrees with the straight-line formula. -/
theorem fderiv_purity_apply (c : ℝ) (X V : Matrix (ι × ι) (ι × ι) ℂ) :
    fderiv ℝ (purity c) X V =
      c * (Matrix.trace
        ((realign X * (realign X)ᴴ) *
            (realign X * (realign V)ᴴ + realign V * (realign X)ᴴ) +
          (realign X * (realign V)ᴴ + realign V * (realign X)ᴴ) *
            (realign X * (realign X)ᴴ))).re := by
  have hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (purity (ι := ι) c) := ContDiff.purity c contDiff_id
  have hd : Differentiable ℝ (purity (ι := ι) c) := hc.differentiable (by simp)
  exact fderiv_apply_eq_of_hasDerivAt_line (hd X) (hasDerivAt_purity_line c X V)

/-- The normalized gradient estimate is valid at arbitrary matrices. -/
theorem norm_fderiv_purity_apply_le (c : ℝ) (X V : Matrix (ι × ι) (ι × ι) ℂ) :
    ‖fderiv ℝ (purity c) X V‖ ≤ 4 * |c| * ‖X‖ ^ 3 * ‖V‖ := by
  let R := realign X
  let W := realign V
  let S := R * Rᴴ
  let T := R * Wᴴ + W * Rᴴ
  have hS : ‖S‖ ≤ ‖X‖ ^ 2 := by
    simpa [S, R, Matrix.frobenius_norm_conjTranspose, realign_norm, pow_two]
      using Matrix.frobenius_norm_mul R Rᴴ
  have hT : ‖T‖ ≤ 2 * ‖X‖ * ‖V‖ := by
    have h := (norm_add_le (R * Wᴴ) (W * Rᴴ)).trans
      (add_le_add (Matrix.frobenius_norm_mul R Wᴴ) (Matrix.frobenius_norm_mul W Rᴴ))
    simp only [Matrix.frobenius_norm_conjTranspose, R, W, realign_norm] at h
    exact h.trans_eq (by ring)
  have htr : ‖Matrix.trace (S * T + T * S)‖ ≤ 4 * ‖X‖ ^ 3 * ‖V‖ := by
    rw [Matrix.trace_add]
    calc
      _ ≤ ‖Matrix.trace (S * T)‖ + ‖Matrix.trace (T * S)‖ := norm_add_le _ _
      _ ≤ ‖S‖ * ‖T‖ + ‖T‖ * ‖S‖ :=
        add_le_add (norm_trace_mul_le_frob S T) (norm_trace_mul_le_frob T S)
      _ ≤ ‖X‖ ^ 2 * (2 * ‖X‖ * ‖V‖) + (2 * ‖X‖ * ‖V‖) * ‖X‖ ^ 2 :=
        add_le_add (mul_le_mul hS hT (norm_nonneg _) (sq_nonneg _))
          (mul_le_mul hT hS (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [fderiv_purity_apply]
  simp only [norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ |c| * ‖Matrix.trace (S * T + T * S)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg c)
    _ ≤ |c| * (4 * ‖X‖ ^ 3 * ‖V‖) :=
      mul_le_mul_of_nonneg_left htr (abs_nonneg c)
    _ = _ := by ring

/-- Two-qubit normalization gives the factor two on the radius-two ball. -/
theorem norm_fderiv_qubit_purity_apply_le
    (X V : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hX : ‖X‖ ≤ 2) :
    ‖fderiv ℝ (purity (1 / 16)) X V‖ ≤ 2 * ‖V‖ := by
  have h := norm_fderiv_purity_apply_le (1 / 16) X V
  norm_num at h
  have hcube := pow_le_pow_left₀ (norm_nonneg X) hX 3
  norm_num at hcube
  rw [Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hcube (norm_nonneg V)]

/-- The invariant is two-Lipschitz on the convex Frobenius radius-two ball. -/
theorem qubit_purity_sub_le
    (X Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hX : ‖X‖ ≤ 2) (hY : ‖Y‖ ≤ 2) :
    |purity (1 / 16) Y - purity (1 / 16) X| ≤ 2 * ‖Y - X‖ := by
  have hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (purity (ι := Fin 2) (1 / 16)) :=
    ContDiff.purity (1 / 16) contDiff_id
  have hd : Differentiable ℝ (purity (ι := Fin 2) (1 / 16)) := hc.differentiable (by simp)
  let V := Y - X
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => X + t • V) V t := by
    have h := ((hasDerivAt_id t).smul_const V).const_add X
    simp only [one_smul, id_eq] at h
    exact h
  have hnorm {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖X + t • V‖ ≤ 2 := by
    have he : X + t • V = (1 - t) • X + t • Y := by
      dsimp only [V]
      module
    rw [he]
    calc
      _ ≤ ‖(1 - t) • X‖ + ‖t • Y‖ := norm_add_le _ _
      _ = (1 - t) * ‖X‖ + t * ‖Y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1 - t), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * 2 + t * 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hX (by linarith [ht.2]))
          (mul_le_mul_of_nonneg_left hY ht.1)
      _ = 2 := by ring
  have hD (t : ℝ) : HasDerivAt (fun t : ℝ => purity (1 / 16) (X + t • V))
      (fderiv ℝ (purity (1 / 16)) (X + t • V) V) t :=
    (hd _).hasFDerivAt.comp_hasDerivAt t (hline t)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hD t).hasDerivWithinAt)
    (fun t ht => norm_fderiv_qubit_purity_apply_le (X + t • V) V (hnorm ⟨ht.1, ht.2.le⟩))
  simpa [V, Real.norm_eq_abs] using h

/-- Local skew-Hermitian motion is killed by the full ambient derivative. -/
theorem fderiv_purity_local_eq_zero (c : ℝ) (X : Matrix (ι × ι) (ι × ι) ℂ)
    {aA aB bA bB : Matrix ι ι ℂ}
    (haA : aAᴴ = -aA) (haB : aBᴴ = -aB) (hbA : bAᴴ = -bA) (hbB : bBᴴ = -bB) :
    fderiv ℝ (purity c) X
      ((bA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ bB) * X +
        X * (aA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB)) = 0 := by
  have hc : ContDiff ℝ (⊤ : WithTop ℕ∞) (purity (ι := ι) c) := ContDiff.purity c contDiff_id
  have hd : Differentiable ℝ (purity (ι := ι) c) := hc.differentiable (by simp)
  exact fderiv_apply_eq_of_hasDerivAt_line (hd X)
    (hasDerivAt_purity_local c X haA haB hbA hbB)

/-- The local-algebra form matches the cross-Gram velocity split. -/
theorem fderiv_purity_localSkew_eq_zero (c : ℝ) (X : Matrix (ι × ι) (ι × ι) ℂ)
    {a b : Matrix (ι × ι) (ι × ι) ℂ}
    (ha : a ∈ localSkew ι ι) (hb : b ∈ localSkew ι ι) :
    fderiv ℝ (purity c) X (-b * X + X * a) = 0 := by
  obtain ⟨aA, haA, aB, haB, harep⟩ := mem_localSkew_iff.mp ha
  obtain ⟨bA, hbA, bB, hbB, hbrep⟩ :=
    mem_localSkew_iff.mp ((localSkew ι ι).neg_mem hb)
  rw [harep, hbrep]
  exact fderiv_purity_local_eq_zero c X haA haB hbA hbB

omit [DecidableEq ι] in
/-- Quartic composition multiplies the coordinate degree by four. -/
theorem polynomialDegree_purity {a D : ℕ}
    {f : RealEuclidean a → Matrix (ι × ι) (ι × ι) ℂ}
    (hf : MatrixPolynomialDegreeLE D f) (c : ℝ) :
    RealPolynomialDegreeLE (4 * D) (fun x => purity c (f x)) := by
  have hr : MatrixPolynomialDegreeLE D (fun x => realign (f x)) :=
    fun p q => hf (p.1, q.1) (p.2, q.2)
  have hs := hr.mul hr.conjTranspose
  have hss := hs.mul hs
  have htr := RealPolynomialDegreeLE.sum Finset.univ (fun i _ => (hss i i).1)
  exact ((htr.const_mul c).mono (by omega)).congr (fun x => by
    simp [purity, Matrix.trace, Matrix.diag, Complex.re_sum])

end NLQCLean

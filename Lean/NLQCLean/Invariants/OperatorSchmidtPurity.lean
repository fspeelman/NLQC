/-
The operator-Schmidt purity invariant and its differential.
-/
import NLQCLean.LinearAlgebra.RealCoordinates
import NLQCLean.LinearAlgebra.Bipartite

/-!
# The realignment invariant annihilates local motion

`NLQCLean.LinearAlgebra.RealCoordinates` defines
realignment `R` and the degree-four real polynomial

  `p(H) = c · Re Tr[(R(H) R(H)†)²]`

and proves it smooth.  This module proves the property that makes it useful:
its differential annihilates every local first-order motion `Ḣ = bH + Ha`
with `a, b` local skew-Hermitian, **for arbitrary `H`** — not only for unitary
`H`, and with no orbit integration.

## The mechanism

Realignment intertwines the four elementary local actions
(`NLQCLean.realign_kroneckerLeft_mul` and its three siblings), so for
`a = a_A ⊗ I + I ⊗ a_B` and `b = b_A ⊗ I + I ⊗ b_B`,

  `R(bH + Ha) = L R(H) + R(H) M`,
  `L = b_A ⊗ I + I ⊗ a_Aᵀ`,   `M = b_Bᵀ ⊗ I + I ⊗ a_B`,

with `L, M` again skew-Hermitian — the transpose of a skew-Hermitian matrix is
skew-Hermitian.  Writing `S = R R†` this gives `Ṡ = L S - S L`, a commutator,
so `d/dt Tr(S²) = Tr(L S² - S² L) = 0` by cyclicity of the trace.  No matrix
exponential and no local-unitary path is constructed.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section Intertwining

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Realignment intertwines a left action on the first output leg. -/
theorem realign_kroneckerLeft_mul (X : Matrix ι ι ℂ) (H : Matrix (ι × ι) (ι × ι) ℂ) :
    realign ((X ⊗ₖ (1 : Matrix ι ι ℂ)) * H)
      = (X ⊗ₖ (1 : Matrix ι ι ℂ)) * realign H := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, realign]
  rfl

/-- Realignment turns a left action on the second output leg into a right
action, transposed. -/
theorem realign_kroneckerRight_mul (Y : Matrix ι ι ℂ) (H : Matrix (ι × ι) (ι × ι) ℂ) :
    realign (((1 : Matrix ι ι ℂ) ⊗ₖ Y) * H)
      = realign H * (Yᵀ ⊗ₖ (1 : Matrix ι ι ℂ)) := by
  ext p q
  have hL : realign (((1 : Matrix ι ι ℂ) ⊗ₖ Y) * H) p q
      = ∑ u : ι, Y q.1 u * H (p.1, u) (p.2, q.2) := by
    rw [realign_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single_of_mem p.1 (Finset.mem_univ _)]
    · exact Finset.sum_congr rfl fun u _ => by
        rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq]; ring
    · intro u1 _ hu1
      exact Finset.sum_eq_zero fun u _ => by
        rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hu1)]; ring
  have hR : (realign H * (Yᵀ ⊗ₖ (1 : Matrix ι ι ℂ))) p q
      = ∑ u : ι, Y q.1 u * H (p.1, u) (p.2, q.2) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v1 _ => ?_
    rw [Finset.sum_eq_single_of_mem q.2 (Finset.mem_univ _)]
    · rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, realign_apply,
        Matrix.transpose_apply]
      ring
    · intro v2 _ hv2
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hv2]
      ring
  rw [hL, hR]

/-- Realignment turns a right action on the first input leg into a left action,
transposed. -/
theorem realign_mul_kroneckerLeft (X : Matrix ι ι ℂ) (H : Matrix (ι × ι) (ι × ι) ℂ) :
    realign (H * (X ⊗ₖ (1 : Matrix ι ι ℂ)))
      = ((1 : Matrix ι ι ℂ) ⊗ₖ Xᵀ) * realign H := by
  ext p q
  have hL : realign (H * (X ⊗ₖ (1 : Matrix ι ι ℂ))) p q
      = ∑ u : ι, H (p.1, q.1) (u, q.2) * X u p.2 := by
    rw [realign_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u1 _ => ?_
    rw [Finset.sum_eq_single_of_mem q.2 (Finset.mem_univ _)]
    · rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq]
      ring
    · intro u2 _ hu2
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hu2]
      ring
  have hR : (((1 : Matrix ι ι ℂ) ⊗ₖ Xᵀ) * realign H) p q
      = ∑ u : ι, H (p.1, q.1) (u, q.2) * X u p.2 := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single_of_mem p.1 (Finset.mem_univ _)]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, realign_apply,
        Matrix.transpose_apply]
      ring
    · intro v1 _ hv1
      exact Finset.sum_eq_zero fun u _ => by
        rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hv1)]; ring
  rw [hL, hR]

/-- Realignment intertwines a right action on the second input leg. -/
theorem realign_mul_kroneckerRight (Y : Matrix ι ι ℂ) (H : Matrix (ι × ι) (ι × ι) ℂ) :
    realign (H * ((1 : Matrix ι ι ℂ) ⊗ₖ Y))
      = realign H * ((1 : Matrix ι ι ℂ) ⊗ₖ Y) := by
  ext p q
  have hL : realign (H * ((1 : Matrix ι ι ℂ) ⊗ₖ Y)) p q
      = ∑ u : ι, H (p.1, q.1) (p.2, u) * Y u q.2 := by
    rw [realign_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single_of_mem p.2 (Finset.mem_univ _)]
    · exact Finset.sum_congr rfl fun u _ => by
        rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq]; ring
    · intro u1 _ hu1
      exact Finset.sum_eq_zero fun u _ => by
        rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hu1]; ring
  have hR : (realign H * ((1 : Matrix ι ι ℂ) ⊗ₖ Y)) p q
      = ∑ u : ι, H (p.1, q.1) (p.2, u) * Y u q.2 := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single_of_mem q.1 (Finset.mem_univ _)]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, realign_apply]
      ring
    · intro v1 _ hv1
      exact Finset.sum_eq_zero fun u _ => by
        rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hv1]; ring
  rw [hL, hR]

end Intertwining

section LocalDifferential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem realign_add (A B : Matrix (ι × ι) (ι × ι) ℂ) :
    realign (A + B) = realign A + realign B :=
  (realignLM (ι := ι)).map_add A B

omit [Fintype ι] [DecidableEq ι] in
/-- The transpose of a skew-Hermitian matrix is skew-Hermitian.  This is why
the transposed legs in `L` and `M` below are still admissible. -/
theorem conjTranspose_transpose_of_skew {X : Matrix ι ι ℂ} (hX : Xᴴ = -X) :
    (Xᵀ)ᴴ = -(Xᵀ) := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M j i) hX
  simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.neg_apply]
    using h

omit [Fintype ι] in
/-- A sum `X ⊗ I + I ⊗ Y` of skew-Hermitian legs is skew-Hermitian. -/
theorem kroneckerSum_skew {X Y : Matrix ι ι ℂ} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    (X ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ Y)ᴴ
      = -(X ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ Y) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hX, hY]
  ext p q
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.kroneckerMap_apply]
  ring

/-- Realignment carries a local first-order
motion `bH + Ha` to `L R + R M`. -/
theorem realign_local (H : Matrix (ι × ι) (ι × ι) ℂ) (aA aB bA bB : Matrix ι ι ℂ) :
    realign ((bA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ bB) * H
        + H * (aA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB))
      = (bA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aAᵀ) * realign H
        + realign H * (bBᵀ ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB) := by
  rw [Matrix.add_mul, Matrix.mul_add, realign_add, realign_add, realign_add,
    realign_kroneckerLeft_mul, realign_kroneckerRight_mul,
    realign_mul_kroneckerLeft, realign_mul_kroneckerRight,
    Matrix.add_mul, Matrix.mul_add]
  abel

/-- With `L, M` skew-Hermitian, the velocity of `S = R R†` is a commutator. -/
theorem velocity_eq_commutator {R L M : Matrix (ι × ι) (ι × ι) ℂ}
    (hL : Lᴴ = -L) (hM : Mᴴ = -M) :
    R * (L * R + R * M)ᴴ + (L * R + R * M) * Rᴴ
      = L * (R * Rᴴ) - (R * Rᴴ) * L := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hL, hM]
  noncomm_ring

/-- The trace of `S²` is annihilated by a commutator velocity. -/
theorem trace_commutator_velocity (S L : Matrix (ι × ι) (ι × ι) ℂ) :
    Matrix.trace (S * (L * S - S * L) + (L * S - S * L) * S) = 0 := by
  have hrw : S * (L * S - S * L) + (L * S - S * L) * S
      = L * (S * S) - (S * S) * L := by noncomm_ring
  rw [hrw, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The invariant's differential annihilates local motion.

For *arbitrary* `H` — not only unitary `H` — and any local skew-Hermitian
`a = a_A ⊗ I + I ⊗ a_B`, `b = b_A ⊗ I + I ⊗ b_B`, the derivative of the purity
polynomial along the straight line through `H` in the direction `bH + Ha`
vanishes.  No matrix exponential and no local-unitary path is constructed. -/
theorem hasDerivAt_purity_local (c : ℝ) (H : Matrix (ι × ι) (ι × ι) ℂ)
    {aA aB bA bB : Matrix ι ι ℂ}
    (haA : aAᴴ = -aA) (haB : aBᴴ = -aB) (hbA : bAᴴ = -bA) (hbB : bBᴴ = -bB) :
    HasDerivAt (fun t : ℝ => purity c (H + t •
        ((bA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ bB) * H
          + H * (aA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB)))) 0 0 := by
  set K := (bA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ bB) * H
      + H * (aA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB) with hK
  set L := bA ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aAᵀ with hLdef
  set M := bBᵀ ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ aB with hMdef
  have hLskew : Lᴴ = -L :=
    kroneckerSum_skew hbA (conjTranspose_transpose_of_skew haA)
  have hMskew : Mᴴ = -M :=
    kroneckerSum_skew (conjTranspose_transpose_of_skew hbB) haB
  have hRk : realign K = L * realign H + realign H * M := by
    rw [hK, hLdef, hMdef]; exact realign_local H aA aB bA bB
  have hline : HasDerivAt (fun t : ℝ => H + t • K) K 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const K).const_add H
    simp only [one_smul, id_eq] at h
    exact h
  have hR : HasDerivAt (fun t : ℝ => realign (H + t • K)) (realign K) 0 :=
    HasDerivAt.ofLinearMap ((realignLM (ι := ι)).restrictScalars ℝ) hline
  have h0 : (fun t : ℝ => H + t • K) 0 = H := by simp
  have hRH : HasDerivAt (fun t : ℝ => (realign (H + t • K))ᴴ) (realign K)ᴴ 0 :=
    HasDerivAt.matrixConjTranspose hR
  have hS : HasDerivAt (fun t : ℝ => realign (H + t • K) * (realign (H + t • K))ᴴ)
      (realign H * (realign K)ᴴ + realign K * (realign H)ᴴ) 0 := by
    have h := HasDerivAt.matrixMul hR hRH
    simpa [h0] using h
  set S := realign H * (realign H)ᴴ with hSdef
  have hSvel : realign H * (realign K)ᴴ + realign K * (realign H)ᴴ
      = L * S - S * L := by
    rw [hRk, hSdef]
    exact velocity_eq_commutator hLskew hMskew
  rw [hSvel] at hS
  have hSS : HasDerivAt
      (fun t : ℝ => (realign (H + t • K) * (realign (H + t • K))ᴴ)
        * (realign (H + t • K) * (realign (H + t • K))ᴴ))
      (S * (L * S - S * L) + (L * S - S * L) * S) 0 := by
    have h := HasDerivAt.matrixMul hS hS
    simpa [h0, hSdef] using h
  have htr : HasDerivAt
      (fun t : ℝ => Matrix.trace ((realign (H + t • K) * (realign (H + t • K))ᴴ)
        * (realign (H + t • K) * (realign (H + t • K))ᴴ)))
      (Matrix.trace (S * (L * S - S * L) + (L * S - S * L) * S)) 0 :=
    HasDerivAt.ofLinearMap
      ((Matrix.traceLinearMap (ι × ι) ℂ ℂ).restrictScalars ℝ) hSS
  rw [trace_commutator_velocity] at htr
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 htr
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.zero_re] at hre
  have hfin := hre.const_mul c
  simp only [mul_zero] at hfin
  exact hfin

end LocalDifferential

section PhaseFamily

/-!
## A one-parameter phase family of unitaries

`z(t) = t + i√(1-t²)` needs only the real square root — no transcendental
function and no choice of angle, which is what keeps the qualitative argument
free of transcendence infrastructure.
-/

variable {d : ℕ} [NeZero d]

/-- The phase `z(t) = t + i√(1-t²)`. -/
noncomputable def phaseZ (t : ℝ) : ℂ :=
  (t : ℂ) + (Real.sqrt (1 - t ^ 2) : ℝ) * Complex.I

@[simp] theorem phaseZ_re (t : ℝ) : (phaseZ t).re = t := by
  simp [phaseZ]

@[simp] theorem phaseZ_im (t : ℝ) : (phaseZ t).im = Real.sqrt (1 - t ^ 2) := by
  simp [phaseZ]

/-- `|z(t)| = 1` exactly on `[-1,1]`, which is where the family is unitary. -/
theorem normSq_phaseZ {t : ℝ} (ht : t ^ 2 ≤ 1) : Complex.normSq (phaseZ t) = 1 := by
  rw [Complex.normSq_apply, phaseZ_re, phaseZ_im, Real.mul_self_sqrt (by linarith)]
  ring

/-- The rank-one projector onto the first standard basis vector. -/
def basisProj (d : ℕ) [NeZero d] : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if i = 0 then (if j = 0 then 1 else 0) else 0

@[simp] theorem basisProj_apply (i j : Fin d) :
    basisProj d i j = if i = 0 then (if j = 0 then 1 else 0) else 0 := rfl

theorem basisProj_conjTranspose : (basisProj d)ᴴ = basisProj d := by
  ext i j
  rw [Matrix.conjTranspose_apply, basisProj_apply, basisProj_apply]
  split_ifs <;> simp_all

theorem basisProj_mul_self : basisProj d * basisProj d = basisProj d := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _)]
  · rw [basisProj_apply, basisProj_apply, basisProj_apply]
    split_ifs <;> simp_all
  · intro k _ hk
    rw [basisProj_apply, basisProj_apply, if_neg hk]
    simp

/-- The rank-one projector `Q = P ⊗ P` on `C^d ⊗ C^d`. -/
def cornerProj (d : ℕ) [NeZero d] :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  basisProj d ⊗ₖ basisProj d

theorem cornerProj_conjTranspose : (cornerProj d)ᴴ = cornerProj d := by
  rw [cornerProj, Matrix.conjTranspose_kronecker, basisProj_conjTranspose]

theorem cornerProj_mul_self : cornerProj d * cornerProj d = cornerProj d := by
  rw [cornerProj, ← Matrix.mul_kronecker_mul, basisProj_mul_self]

/-- The phase family `U_t = I + (z(t) - 1) P ⊗ P`. -/
noncomputable def phaseFamily (d : ℕ) [NeZero d] (t : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  1 + (phaseZ t - 1) • cornerProj d

/-- The scalar identity behind unitarity: for `|z| = 1`,
`(z-1) + conj(z-1) + |z-1|² = 0`. -/
theorem phase_scalar_identity {z : ℂ} (hz : Complex.normSq z = 1) :
    (z - 1) + star (z - 1) + star (z - 1) * (z - 1) = 0 := by
  have hre : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply]; exact hz
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im] <;> nlinarith [hre]

/-- A rank-one-projector phase perturbation of the identity is unitary exactly
when the scalar identity holds. -/
theorem one_add_smul_proj_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQh : Qᴴ = Q) (hQ2 : Q * Q = Q) {c : ℂ}
    (hc : c + star c + star c * c = 0) :
    ((1 : Matrix n n ℂ) + c • Q)ᴴ * (1 + c • Q) = 1
      ∧ ((1 : Matrix n n ℂ) + c • Q) * (1 + c • Q)ᴴ = 1 := by
  have hexp : ∀ a b : ℂ, ((1 : Matrix n n ℂ) + a • Q) * (1 + b • Q)
      = 1 + (a + b + a * b) • Q := by
    intro a b
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hQ2, add_smul]
    rw [smul_add, smul_smul, mul_comm b a]
    abel
  have hadj : ((1 : Matrix n n ℂ) + c • Q)ᴴ = 1 + star c • Q := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hQh]
  constructor
  · rw [hadj, hexp, show star c + c + star c * c = 0 by rw [← hc]; ring,
      zero_smul, add_zero]
  · rw [hadj, hexp, show c + star c + c * star c = 0 by rw [← hc]; ring,
      zero_smul, add_zero]

/-- **`U_t` is unitary on `[-1,1]`.**  Only the real square root is used. -/
theorem phaseFamily_unitary {t : ℝ} (ht : t ^ 2 ≤ 1) :
    (phaseFamily d t)ᴴ * phaseFamily d t = 1
      ∧ phaseFamily d t * (phaseFamily d t)ᴴ = 1 :=
  one_add_smul_proj_unitary cornerProj_conjTranspose cornerProj_mul_self
    (phase_scalar_identity (normSq_phaseZ ht))

/-!
### The explicit realignment of `U_t`

`R(U_t)` has nonzero rows only at `(i,i)` and columns only
at `(j,j)`, and on those indices it is the `d × d` matrix `B` all of whose
entries are one except `B₀₀ = z(t)`.
-/

/-- The matrix `B`: all entries one except the corner, which is `z(t)`. -/
noncomputable def diagBlock (d : ℕ) [NeZero d] (t : ℝ) (a b : Fin d) : ℂ :=
  if a = 0 ∧ b = 0 then phaseZ t else 1

/-- **The realignment of the phase family**, supported on the diagonal
indices. -/
theorem realign_phaseFamily_apply (t : ℝ) (p q : Fin d × Fin d) :
    realign (phaseFamily d t) p q
      = if p.1 = p.2 ∧ q.1 = q.2 then diagBlock d t p.1 q.1 else 0 := by
  rw [realign_apply, phaseFamily, Matrix.add_apply, Matrix.smul_apply,
    cornerProj, Matrix.kroneckerMap_apply, basisProj_apply, basisProj_apply,
    Matrix.one_apply, diagBlock, smul_eq_mul]
  by_cases h : p.1 = p.2 ∧ q.1 = q.2
  · rw [if_pos h, if_pos (by simp [h.1, h.2] : ((p.1, q.1) : Fin d × Fin d) = (p.2, q.2))]
    have hP : (if p.1 = 0 then (if p.2 = 0 then (1 : ℂ) else 0) else 0)
        = if p.1 = 0 then 1 else 0 := by rw [← h.1]; simp
    have hQ : (if q.1 = 0 then (if q.2 = 0 then (1 : ℂ) else 0) else 0)
        = if q.1 = 0 then 1 else 0 := by rw [← h.2]; simp
    rw [hP, hQ]
    by_cases hp : p.1 = 0 <;> by_cases hq : q.1 = 0 <;> simp [hp, hq]
  · rw [if_neg h, if_neg (by simpa [Prod.ext_iff] using h)]
    have hz : (if p.1 = 0 then (if p.2 = 0 then (1 : ℂ) else 0) else 0)
        * (if q.1 = 0 then (if q.2 = 0 then (1 : ℂ) else 0) else 0) = 0 := by
      by_cases hp1 : p.1 = 0
      · by_cases hp2 : p.2 = 0
        · by_cases hq1 : q.1 = 0
          · by_cases hq2 : q.2 = 0
            · exact absurd ⟨hp1.trans hp2.symm, hq1.trans hq2.symm⟩ h
            · simp [hq2]
          · simp [hq1]
        · simp [hp2]
      · simp [hp1]
    rw [hz, mul_zero, add_zero]

omit [NeZero d] in
/-- Collapsing a sum over `Fin d × Fin d` onto the diagonal. -/
theorem sum_prod_diag {M : Type*} [AddCommMonoid M] (f : Fin d → M) :
    ∑ q : Fin d × Fin d, (if q.1 = q.2 then f q.1 else 0) = ∑ c, f c := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c1 _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- The Gram matrix `B B†`. -/
noncomputable def gramBlock (d : ℕ) [NeZero d] (t : ℝ) (a b : Fin d) : ℂ :=
  ∑ c, diagBlock d t a c * star (diagBlock d t b c)

/-- `S = R R†` is supported on the diagonal indices, where it is `B B†`. -/
theorem realign_gram_apply (t : ℝ) (p p' : Fin d × Fin d) :
    (realign (phaseFamily d t) * (realign (phaseFamily d t))ᴴ) p p'
      = if p.1 = p.2 ∧ p'.1 = p'.2 then gramBlock d t p.1 p'.1 else 0 := by
  rw [Matrix.mul_apply]
  have hterm : ∀ q : Fin d × Fin d,
      realign (phaseFamily d t) p q * (realign (phaseFamily d t))ᴴ q p'
        = if p.1 = p.2 ∧ p'.1 = p'.2 then
            (if q.1 = q.2 then diagBlock d t p.1 q.1 * star (diagBlock d t p'.1 q.1)
              else 0)
          else 0 := by
    intro q
    rw [Matrix.conjTranspose_apply, realign_phaseFamily_apply,
      realign_phaseFamily_apply]
    by_cases h1 : p.1 = p.2 <;> by_cases h2 : p'.1 = p'.2 <;>
      by_cases h3 : q.1 = q.2 <;> simp_all
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  by_cases h : p.1 = p.2 ∧ p'.1 = p'.2
  · simp only [if_pos h]
    rw [sum_prod_diag (fun c => diagBlock d t p.1 c * star (diagBlock d t p'.1 c)),
      gramBlock]
  · simp only [if_neg h, Finset.sum_const_zero]

/-- **`Tr(S²)` collapses to a sum over the `d × d` block.** -/
theorem trace_gram_sq (t : ℝ) :
    Matrix.trace ((realign (phaseFamily d t) * (realign (phaseFamily d t))ᴴ)
        * (realign (phaseFamily d t) * (realign (phaseFamily d t))ᴴ))
      = ∑ a : Fin d, ∑ b : Fin d, gramBlock d t a b * gramBlock d t b a := by
  have hstep : ∀ p : Fin d × Fin d,
      ((realign (phaseFamily d t) * (realign (phaseFamily d t))ᴴ)
        * (realign (phaseFamily d t) * (realign (phaseFamily d t))ᴴ)) p p
        = if p.1 = p.2 then
            (∑ b : Fin d, gramBlock d t p.1 b * gramBlock d t b p.1) else 0 := by
    intro p
    rw [Matrix.mul_apply]
    have hterm : ∀ p' : Fin d × Fin d,
        (realign (phaseFamily d t) * (realign (phaseFamily d t))ᴴ) p p'
          * (realign (phaseFamily d t) * (realign (phaseFamily d t))ᴴ) p' p
        = if p.1 = p.2 then
            (if p'.1 = p'.2 then gramBlock d t p.1 p'.1 * gramBlock d t p'.1 p.1
              else 0) else 0 := by
      intro p'
      rw [realign_gram_apply, realign_gram_apply]
      by_cases h1 : p.1 = p.2 <;> by_cases h2 : p'.1 = p'.2 <;> simp_all
    rw [Finset.sum_congr rfl fun p' _ => hterm p']
    by_cases h1 : p.1 = p.2
    · simp only [if_pos h1]
      exact sum_prod_diag (fun b => gramBlock d t p.1 b * gramBlock d t b p.1)
    · simp only [if_neg h1, Finset.sum_const_zero]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl fun p _ => hstep p]
  exact sum_prod_diag (fun a => ∑ b : Fin d, gramBlock d t a b * gramBlock d t b a)

/-!
### Evaluating the double sum
-/

theorem sum_split_zero {M : Type*} [AddCommMonoid M] (f : Fin d → M) :
    ∑ i, f i = f 0 + ∑ i ∈ ({0}ᶜ : Finset (Fin d)), f i :=
  Fintype.sum_eq_add_sum_compl 0 f

theorem card_compl_zero : ({0}ᶜ : Finset (Fin d)).card = d - 1 := by
  rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]

theorem cast_card_compl_zero : (({0}ᶜ : Finset (Fin d)).card : ℂ) = (d : ℂ) - 1 := by
  rw [card_compl_zero, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))]
  norm_num

/-- The corner value of `B` at index `a`. -/
noncomputable def cornerVal (d : ℕ) [NeZero d] (t : ℝ) (a : Fin d) : ℂ :=
  if a = 0 then phaseZ t else 1

@[simp] theorem cornerVal_zero (t : ℝ) : cornerVal d t 0 = phaseZ t := by
  rw [cornerVal, if_pos rfl]

theorem cornerVal_of_ne (t : ℝ) {a : Fin d} (ha : a ≠ 0) : cornerVal d t a = 1 := by
  rw [cornerVal, if_neg ha]

/-- **`B B†` in closed form**: `G a b = e_a · conj(e_b) + (d-1)`. -/
theorem gramBlock_eq (t : ℝ) (a b : Fin d) :
    gramBlock d t a b
      = cornerVal d t a * star (cornerVal d t b) + ((d : ℂ) - 1) := by
  rw [gramBlock, sum_split_zero (fun c => diagBlock d t a c * star (diagBlock d t b c))]
  have h0 : diagBlock d t a 0 * star (diagBlock d t b 0)
      = cornerVal d t a * star (cornerVal d t b) := by
    rw [diagBlock, diagBlock, cornerVal, cornerVal]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
  have hrest : ∀ c ∈ ({0}ᶜ : Finset (Fin d)),
      diagBlock d t a c * star (diagBlock d t b c) = 1 := by
    intro c hc
    have hc0 : c ≠ 0 := by simpa using hc
    rw [diagBlock, diagBlock, if_neg (fun h => hc0 h.2), if_neg (fun h => hc0 h.2)]
    simp
  rw [h0, Finset.sum_congr rfl hrest, Finset.sum_const, nsmul_eq_mul,
    cast_card_compl_zero]
  ring

/-- `z · conj z = 1` on `[-1,1]`. -/
theorem phaseZ_mul_star {t : ℝ} (ht : t ^ 2 ≤ 1) :
    phaseZ t * star (phaseZ t) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, normSq_phaseZ ht]
  norm_num

/-- The double sum evaluating the squared Gram entries. -/
theorem sum_gram_sq (t : ℝ) (ht : t ^ 2 ≤ 1) :
    ∑ a : Fin d, ∑ b : Fin d, gramBlock d t a b * gramBlock d t b a
      = (1 + ((d : ℂ) - 1)) ^ 2 * (1 + ((d : ℂ) - 1) ^ 2)
        + 2 * ((d : ℂ) - 1)
          * ((phaseZ t + ((d : ℂ) - 1)) * (star (phaseZ t) + ((d : ℂ) - 1))) := by
  have hz : phaseZ t * star (phaseZ t) = 1 := phaseZ_mul_star ht
  have hterm : ∀ a b : Fin d, gramBlock d t a b * gramBlock d t b a
      = (cornerVal d t a * star (cornerVal d t b) + ((d : ℂ) - 1))
        * (cornerVal d t b * star (cornerVal d t a) + ((d : ℂ) - 1)) := by
    intro a b; rw [gramBlock_eq, gramBlock_eq]
  simp only [hterm]
  have hinner : ∀ a : Fin d, ∑ b : Fin d,
      (cornerVal d t a * star (cornerVal d t b) + ((d : ℂ) - 1))
        * (cornerVal d t b * star (cornerVal d t a) + ((d : ℂ) - 1))
      = (cornerVal d t a * star (phaseZ t) + ((d : ℂ) - 1))
          * (phaseZ t * star (cornerVal d t a) + ((d : ℂ) - 1))
        + ((d : ℂ) - 1) * ((cornerVal d t a + ((d : ℂ) - 1))
          * (star (cornerVal d t a) + ((d : ℂ) - 1))) := by
    intro a
    rw [sum_split_zero (fun b : Fin d =>
      (cornerVal d t a * star (cornerVal d t b) + ((d : ℂ) - 1))
        * (cornerVal d t b * star (cornerVal d t a) + ((d : ℂ) - 1)))]
    have hrest : ∀ b ∈ ({0}ᶜ : Finset (Fin d)),
        (cornerVal d t a * star (cornerVal d t b) + ((d : ℂ) - 1))
          * (cornerVal d t b * star (cornerVal d t a) + ((d : ℂ) - 1))
        = (cornerVal d t a + ((d : ℂ) - 1))
          * (star (cornerVal d t a) + ((d : ℂ) - 1)) := by
      intro b hb
      have hb0 : b ≠ 0 := by simpa using hb
      rw [cornerVal_of_ne (a := b) t hb0, star_one, mul_one, one_mul]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, nsmul_eq_mul,
      cast_card_compl_zero, cornerVal_zero]
  simp only [hinner]
  rw [sum_split_zero (fun a : Fin d =>
    (cornerVal d t a * star (phaseZ t) + ((d : ℂ) - 1))
        * (phaseZ t * star (cornerVal d t a) + ((d : ℂ) - 1))
      + ((d : ℂ) - 1) * ((cornerVal d t a + ((d : ℂ) - 1))
        * (star (cornerVal d t a) + ((d : ℂ) - 1))))]
  have hrest2 : ∀ a ∈ ({0}ᶜ : Finset (Fin d)),
      (cornerVal d t a * star (phaseZ t) + ((d : ℂ) - 1))
          * (phaseZ t * star (cornerVal d t a) + ((d : ℂ) - 1))
        + ((d : ℂ) - 1) * ((cornerVal d t a + ((d : ℂ) - 1))
          * (star (cornerVal d t a) + ((d : ℂ) - 1)))
      = (star (phaseZ t) + ((d : ℂ) - 1)) * (phaseZ t + ((d : ℂ) - 1))
        + ((d : ℂ) - 1) * (1 + ((d : ℂ) - 1)) ^ 2 := by
    intro a ha
    have ha0 : a ≠ 0 := by simpa using ha
    rw [cornerVal_of_ne (a := a) t ha0, star_one, one_mul, mul_one]
    ring
  rw [Finset.sum_congr rfl hrest2, Finset.sum_const, nsmul_eq_mul,
    cast_card_compl_zero, cornerVal_zero, hz]
  ring

/-!
### The purity formula and its interval
-/

/-- The double sum is a real affine expression in `t`. -/
theorem sum_gram_sq_real (t : ℝ) (ht : t ^ 2 ≤ 1) :
    ∑ a : Fin d, ∑ b : Fin d, gramBlock d t a b * gramBlock d t b a
      = (((d : ℝ) ^ 4 - 4 * ((d : ℝ) - 1) ^ 2 * (1 - t) : ℝ) : ℂ) := by
  have hW : (phaseZ t + ((d : ℂ) - 1)) * (star (phaseZ t) + ((d : ℂ) - 1))
      = (((t + ((d : ℝ) - 1)) ^ 2 + (1 - t ^ 2) : ℝ) : ℂ) := by
    have hre : (phaseZ t + ((d : ℂ) - 1)).re = t + ((d : ℝ) - 1) := by simp [phaseZ]
    have him : (phaseZ t + ((d : ℂ) - 1)).im = Real.sqrt (1 - t ^ 2) := by simp [phaseZ]
    have hsplit : star (phaseZ t) + ((d : ℂ) - 1) = star (phaseZ t + ((d : ℂ) - 1)) := by
      rw [star_add]
      congr 1
      rw [star_sub, star_one, Complex.star_def, Complex.conj_natCast]
    rw [hsplit, Complex.star_def, Complex.mul_conj, Complex.normSq_apply, hre, him,
      Real.mul_self_sqrt (by linarith)]
    congr 1
    ring
  rw [sum_gram_sq t ht, hW]
  push_cast
  ring

/-- `p(U_t) = 1 - 4(d-1)²/d⁴ · (1-t)`. -/
theorem purity_phaseFamily (t : ℝ) (ht : t ^ 2 ≤ 1) :
    purity (((d : ℝ) ^ 4)⁻¹) (phaseFamily d t)
      = 1 - 4 * ((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 4 * (1 - t) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [purity, trace_gram_sq, sum_gram_sq_real t ht, Complex.ofReal_re]
  field_simp

/-- **Exact interval realization.**  Every value of
`I_d = [1 - 8(d-1)²/d⁴, 1]` is attained by the phase family.  Solving the
affine formula is all that is needed; no intermediate value theorem. -/
theorem exists_purity_phaseFamily_eq (hd2 : 2 ≤ d) {s : ℝ}
    (hlo : 1 - 8 * ((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 4 ≤ s) (hhi : s ≤ 1) :
    ∃ t : ℝ, t ^ 2 ≤ 1 ∧ purity (((d : ℝ) ^ 4)⁻¹) (phaseFamily d t) = s := by
  have hd : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := lt_of_lt_of_le (by norm_num) hd2
    exact_mod_cast this
  have hD : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith
  set t : ℝ := 1 - (1 - s) * (d : ℝ) ^ 4 / (4 * ((d : ℝ) - 1) ^ 2) with htdef
  have hpos : (0 : ℝ) < 4 * ((d : ℝ) - 1) ^ 2 := by positivity
  have hd4 : (0 : ℝ) < (d : ℝ) ^ 4 := by positivity
  have hub : t ≤ 1 := by
    rw [htdef]
    have : 0 ≤ (1 - s) * (d : ℝ) ^ 4 / (4 * ((d : ℝ) - 1) ^ 2) := by
      apply div_nonneg _ (le_of_lt hpos)
      exact mul_nonneg (by linarith) (le_of_lt hd4)
    linarith
  have hlb : -1 ≤ t := by
    rw [htdef]
    have hs8 : (1 - s) ≤ 8 * ((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 4 := by linarith
    have hkey : (1 - s) * (d : ℝ) ^ 4 / (4 * ((d : ℝ) - 1) ^ 2) ≤ 2 := by
      rw [div_le_iff₀ hpos]
      have : (1 - s) * (d : ℝ) ^ 4 ≤ 8 * ((d : ℝ) - 1) ^ 2 := by
        have h1 : (1 - s) * (d : ℝ) ^ 4
            ≤ (8 * ((d : ℝ) - 1) ^ 2 / (d : ℝ) ^ 4) * (d : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hs8 (le_of_lt hd4)
        rwa [div_mul_cancel₀ _ (ne_of_gt hd4)] at h1
      linarith
    linarith
  refine ⟨t, ?_, ?_⟩
  · nlinarith [hub, hlb]
  · rw [purity_phaseFamily t (by nlinarith [hub, hlb]), htdef]
    field_simp
    ring

end PhaseFamily

end NLQCLean

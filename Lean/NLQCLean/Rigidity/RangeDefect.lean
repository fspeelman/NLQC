/-
The principal-angle defect and its symmetry.
-/
import NLQCLean.LinearAlgebra.Isometry
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The principal-angle defect

For isometries `A, B : ℂ^D → 𝒦` with the same domain, `lem:cross-gram-rigidity`
uses the *largest principal-angle defect*

  `α = ‖(I - B B†) A‖_op`

and asserts the symmetry eq:principal-angle-symmetry (snapshot L751-757)

  `‖(I - A A†) B‖_op = ‖(I - B B†) A‖_op = α`.

The paper's justification is that the squares are `‖I - H H†‖_op` and
`‖I - H† H‖_op` with `H = B†A`, and that both equal `1 - σ_min(H)²`.  The
argument needs `H` to be **square**, which holds exactly because `A` and `B`
share the domain `ℂ^D`; for isometries with domains of different dimensions
the two defects genuinely differ.

The route taken here avoids singular values.  `H†H` and `HH†` are Hermitian
with the same characteristic polynomial (`Matrix.charpoly_mul_comm`, valid for
square factors), hence the same eigenvalues; the spectral theorem then writes
`I - H†H` and `I - HH†` as unitary conjugates of one and the same diagonal
matrix, and conjugation by a unitary is a star algebra automorphism of the
C*-algebra `Matrix n n ℂ`, hence isometric.

Everything here is over `ℂ`, as in the paper: `StarAlgEquiv.norm_map` is
stated for C*-algebras over `ℂ`.
-/

namespace NLQCLean

open Matrix

section OperatorNorm

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation by a unitary preserves the operator norm: it is a star algebra
automorphism of the C*-algebra `Matrix n n ℂ`. -/
theorem opNorm_conjStarAlgAut (u : unitary (Matrix n n ℂ)) (M : Matrix n n ℂ) :
    opNorm (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u M) = opNorm M := by
  simpa only [opNorm_eq_l2_opNorm] using
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u) M

/-- `‖I - H†H‖_op = ‖I - HH†‖_op` for a **square** matrix `H`.

This is the analytic content of eq:principal-angle-symmetry (L751-757).
Squareness is essential and enters through `Matrix.charpoly_mul_comm`. -/
theorem opNorm_one_sub_conjTranspose_mul_comm (H : Matrix n n ℂ) :
    opNorm (1 - Hᴴ * H) = opNorm (1 - H * Hᴴ) := by
  have hA : (Hᴴ * H).IsHermitian := isHermitian_conjTranspose_mul_self H
  have hB : (H * Hᴴ).IsHermitian := isHermitian_mul_conjTranspose_self H
  have heig : hA.eigenvalues = hB.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hA hB).mpr (charpoly_mul_comm _ _)
  have hEA : (1 : Matrix n n ℂ) - Hᴴ * H
      = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
          (1 - diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
    rw [map_sub, map_one, ← hA.spectral_theorem]
  have hEB : (1 : Matrix n n ℂ) - H * Hᴴ
      = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary
          (1 - diagonal (RCLike.ofReal ∘ hB.eigenvalues)) := by
    rw [map_sub, map_one, ← hB.spectral_theorem]
  rw [hEA, hEB, opNorm_conjStarAlgAut, opNorm_conjStarAlgAut, heig]

end OperatorNorm

section Symmetry

open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- `I - A A†` is idempotent when `A` is an isometry. -/
theorem IsIsometry.complProj_idem {A : Matrix κ ι ℂ} (h : IsIsometry A) :
    ((1 : Matrix κ κ ℂ) - A * Aᴴ) * (1 - A * Aᴴ) = 1 - A * Aᴴ := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, h.rangeProj_idem]
  abel

omit [Fintype κ] [DecidableEq ι] in
/-- `I - A A†` is self-adjoint. -/
theorem complProj_conjTranspose (A : Matrix κ ι ℂ) :
    ((1 : Matrix κ κ ℂ) - A * Aᴴ)ᴴ = 1 - A * Aᴴ := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, rangeProj_conjTranspose]

/-- The Gram matrix of the residual `(I - BB†)A` is `I - H†H` with `H = B†A`. -/
theorem gram_complProj_mul {A B : Matrix κ ι ℂ} (hA : IsIsometry A) (hB : IsIsometry B) :
    ((((1 : Matrix κ κ ℂ) - B * Bᴴ) * A)ᴴ * (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A))
      = 1 - (Bᴴ * A)ᴴ * (Bᴴ * A) := by
  rw [Matrix.conjTranspose_mul, complProj_conjTranspose, ← Matrix.mul_assoc,
    Matrix.mul_assoc Aᴴ, hB.complProj_idem, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul, hA.conjTranspose_mul_self, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp [Matrix.mul_assoc]

/-- **eq:principal-angle-symmetry** (snapshot L751-757).  For isometries with a
common domain the two range defects agree, so the paper's single symbol `α` is
well defined. -/
theorem principal_angle_symm {A B : Matrix κ ι ℂ} (hA : IsIsometry A) (hB : IsIsometry B) :
    opNorm (((1 : Matrix κ κ ℂ) - A * Aᴴ) * B) = opNorm (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A) := by
  have key : ∀ {X Y : Matrix κ ι ℂ}, IsIsometry X → IsIsometry Y →
      opNorm (((1 : Matrix κ κ ℂ) - Y * Yᴴ) * X) * opNorm (((1 : Matrix κ κ ℂ) - Y * Yᴴ) * X)
        = opNorm (1 - (Yᴴ * X)ᴴ * (Yᴴ * X)) := by
    intro X Y hX hY
    rw [opNorm_eq_l2_opNorm, opNorm_eq_l2_opNorm, ← Matrix.l2_opNorm_conjTranspose_mul_self,
      gram_complProj_mul hX hY]
  have h1 := key hB hA
  have h2 := key hA hB
  have hHH : (Aᴴ * B)ᴴ * (Aᴴ * B) = (Bᴴ * A) * (Bᴴ * A)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hHH] at h1
  have hsym : opNorm (1 - (Bᴴ * A) * (Bᴴ * A)ᴴ) = opNorm (1 - (Bᴴ * A)ᴴ * (Bᴴ * A)) :=
    (opNorm_one_sub_conjTranspose_mul_comm (Bᴴ * A)).symm
  rw [hsym] at h1
  have hnn₁ : 0 ≤ opNorm (((1 : Matrix κ κ ℂ) - A * Aᴴ) * B) := opNorm_nonneg _
  have hnn₂ : 0 ≤ opNorm (((1 : Matrix κ κ ℂ) - B * Bᴴ) * A) := opNorm_nonneg _
  nlinarith [h1, h2, hnn₁, hnn₂]

end Symmetry

end NLQCLean

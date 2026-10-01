import NLQCLean.Models.ClassicalCommunication.FiniteInstruments
import NLQCLean.Models.ForwardReindex

/-!
# Coherent finite classical labels

Actual instrument outcomes are copied to a retained label and a message
label. Controlled final isometries retain the labels in their environment.
These matrices are physical isometries, including on unused label sectors.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix

section Controlled

variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq σ]

/-- A block-controlled matrix that retains the controlling label. -/
def controlledMatrix (A : σ → Matrix κ ι ℂ) : Matrix (κ × σ) (ι × σ) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then A q.2 p.1 q.1 else 0

omit [Fintype ι] [DecidableEq κ] in
/-- Every label sector has its own isometry; different sectors stay orthogonal. -/
theorem controlledMatrix_isometry (A : σ → Matrix κ ι ℂ)
    (hA : ∀ x, IsIsometry (A x)) : IsIsometry (controlledMatrix A) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases hxy : x = y
  · subst y
    have h := congrArg (fun M : Matrix ι ι ℂ => M i j)
      (hA x).conjTranspose_mul_self
    simpa [controlledMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, Matrix.one_apply] using h
  · simp [controlledMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, hxy, Ne.symm hxy]

end Controlled

namespace FiniteKrausInstrument

variable {ι κ μ σ ε : Type*}
variable [Fintype ι] [Fintype κ] [Fintype μ] [Fintype σ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]
variable [DecidableEq σ] [DecidableEq ε]

/-- The outcome label is retained locally and coherently copied into the
outgoing message. The Kraus label stays in the uncharged private workspace. -/
def coherentEncoder (I : FiniteKrausInstrument ι (κ × μ) σ ε) :
    Matrix ((κ × (σ × ε)) × (μ × σ)) ι ℂ :=
  Matrix.of fun p i => if p.1.2.1 = p.2.2 then
    I.operator p.1.2.1 p.1.2.2 (p.1.1, p.2.1) i else 0

omit [DecidableEq κ] [DecidableEq μ] [DecidableEq ε] in
/-- The copied labels do not alter the actual instrument normalization. -/
theorem coherentEncoder_isometry (I : FiniteKrausInstrument ι (κ × μ) σ ε) :
    IsIsometry I.coherentEncoder := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) I.normalized
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type] at h
  simp only [coherentEncoder, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  simp [apply_ite, ite_mul]
  calc
    _ = ∑ x, ∑ e, ∑ k, ∑ q,
        star (I.operator x e (k, q) i) * I.operator x e (k, q) j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      rfl
    _ = _ := h

end FiniteKrausInstrument

end NLQCLean.ClassicalCommunication

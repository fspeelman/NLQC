import NLQCLean.Models.ClassicalCommunication.FiniteInstruments
import NLQCLean.Models.ForwardReindex

/-! # Relabeling finite Kraus instruments -/

namespace NLQCLean.ClassicalCommunication.FiniteKrausInstrument

open Matrix

attribute [local implicit_reducible] Matrix

variable {ι κ σ η ι₂ κ₂ σ₂ η₂ : Type*}
variable [Fintype ι] [Fintype κ] [Fintype σ] [Fintype η]
variable [Fintype ι₂] [Fintype κ₂] [Fintype σ₂] [Fintype η₂]
variable [DecidableEq ι] [DecidableEq ι₂]

/-- Transport input, output, outcome and private Kraus labels by bijections,
preserving the total operator normalization. -/
def reindex (I : FiniteKrausInstrument ι κ σ η)
    (a : ι₂ ≃ ι) (b : κ₂ ≃ κ) (s : σ₂ ≃ σ) (t : η₂ ≃ η) :
    FiniteKrausInstrument ι₂ κ₂ σ₂ η₂ where
  operator x e := (I.operator (s x) (t e)).submatrix b a
  normalized := by
    calc
      (∑ x, ∑ e, ((I.operator (s x) (t e)).submatrix b a)ᴴ *
          (I.operator (s x) (t e)).submatrix b a) =
          ∑ x, ∑ e, ((I.operator (s x) (t e))ᴴ *
            I.operator (s x) (t e)).submatrix a a := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro e _
        rw [Matrix.conjTranspose_submatrix]
        exact Matrix.submatrix_mul_equiv _ _ a b a
      _ = (∑ x, ∑ e, (I.operator x e)ᴴ * I.operator x e).submatrix a a := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.sum_apply]
        calc
          _ = ∑ x : σ₂, ∑ e : η,
              ((I.operator (s x) e)ᴴ * I.operator (s x) e) (a i) (a j) := by
            apply Finset.sum_congr rfl
            intro x _
            exact t.sum_comp (fun e =>
              ((I.operator (s x) e)ᴴ * I.operator (s x) e) (a i) (a j))
          _ = _ := s.sum_comp (fun x => ∑ e : η,
            ((I.operator x e)ᴴ * I.operator x e) (a i) (a j))
      _ = 1 := by rw [I.normalized]; exact Matrix.submatrix_one_equiv a

@[simp] theorem reindex_operator (I : FiniteKrausInstrument ι κ σ η)
    (a : ι₂ ≃ ι) (b : κ₂ ≃ κ) (s : σ₂ ≃ σ) (t : η₂ ≃ η)
    (x : σ₂) (e : η₂) :
    (I.reindex a b s t).operator x e = (I.operator (s x) (t e)).submatrix b a := rfl

end NLQCLean.ClassicalCommunication.FiniteKrausInstrument

import NLQCLean.Models.ClassicalCommunication.FiniteInstruments
import NLQCLean.Models.ChoiMetrics
import Mathlib.Analysis.Matrix.Order

/-!
# Finite completely positive maps and Kraus representations

Finite-ancilla complete positivity makes the existing normalized Choi matrix
positive. A positive Choi matrix has a Gram factor, whose columns reshape to
actual Kraus operators on the original input and output systems. The Kraus
alphabet is the finite product of those systems. Trace-preserving finite
families therefore give actual normalized finite Kraus instruments.

These are finite-dimensional, finite-outcome equivalences; they do not assert
a representation theorem for standard-Borel instruments.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- Fin-card ancillary positivity transports to every original finite ancilla. -/
theorem CompletelyPositive.amplify_posSemidef
    {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} (hΦ : CompletelyPositive Φ)
    {α : Type*} [Fintype α] [DecidableEq α]
    {X : Matrix (ι × α) (ι × α) ℂ} (hX : X.PosSemidef) :
    (amplify Φ α X).PosSemidef := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  apply (Matrix.posSemidef_submatrix_equiv ((Equiv.refl κ).prodCongr e)).mp
  rw [← amplify_submatrix_ancilla Φ e X]
  exact hΦ _ _ (hX.submatrix ((Equiv.refl ι).prodCongr e))

omit [Fintype κ] [DecidableEq κ] in
/-- Complete positivity proves positivity of the actual normalized Choi matrix. -/
theorem CompletelyPositive.choiMatrix_posSemidef
    {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} (hΦ : CompletelyPositive Φ) :
    (choiMatrix Φ).PosSemidef := by
  rw [← amplify_maximallyEntangledInput]
  apply hΦ.amplify_posSemidef
  exact posSemidef_choiMatrix_adConj (1 : Matrix ι ι ℂ)

/-- The unnormalized Choi coefficient matrix, in the same output-input order. -/
def unnormalizedChoiMatrix (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    Matrix (κ × ι) (κ × ι) ℂ :=
  fun p q => Φ (Matrix.single p.2 q.2 1) p.1 q.1

omit [Fintype κ] [DecidableEq κ] in
theorem unnormalizedChoiMatrix_eq_smul [Nonempty ι]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    unnormalizedChoiMatrix Φ = (Fintype.card ι : ℂ) • choiMatrix Φ := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := ι)
  ext p q
  simp only [unnormalizedChoiMatrix, Matrix.smul_apply, choiMatrix_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem exists_gram_factor {ν : Type*} [Fintype ν] [DecidableEq ν]
    {C : Matrix ν ν ℂ} (hC : C.PosSemidef) :
    ∃ B : Matrix ν ν ℂ, B * Bᴴ = C := by
  obtain ⟨B, hB, _, hBB⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hC.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hC.nonneg)
  refine ⟨B, ?_⟩
  change B * star B = C
  rw [hB.star_eq]
  exact hBB

omit [Fintype κ] [DecidableEq κ] in
/-- Matrix-unit coefficients of a finite Kraus operation. -/
theorem krausMap_single_apply {ε : Type*} [Fintype ε]
    (A : ε → Matrix κ ι ℂ) (i j : ι) (k l : κ) :
    krausMap A (Matrix.single i j 1) k l = ∑ e, A e k i * star (A e l j) := by
  simp [krausMap_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and]

/-- Choi positivity reconstructs a finite Kraus family. -/
theorem exists_kraus_of_choiMatrix_posSemidef [Nonempty ι]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (hΦ : (choiMatrix Φ).PosSemidef) :
    ∃ A : (κ × ι) → Matrix κ ι ℂ, Φ = krausMap A := by
  have hC : (unnormalizedChoiMatrix Φ).PosSemidef := by
    rw [unnormalizedChoiMatrix_eq_smul]
    exact hΦ.smul (by positivity)
  obtain ⟨B, hB⟩ := exists_gram_factor hC
  let A : (κ × ι) → Matrix κ ι ℂ := fun e k i => B (k, i) e
  have hcoeff (i j : ι) (k l : κ) :
      Φ (Matrix.single i j 1) k l = ∑ e, A e k i * star (A e l j) := by
    have h := congrArg (fun C : Matrix (κ × ι) (κ × ι) ℂ => C (k, i) (l, j)) hB
    exact h.symm
  refine ⟨A, ?_⟩
  apply LinearMap.ext
  intro X
  ext k l
  rw [linearMap_matrix_apply Φ X k l, linearMap_matrix_apply (krausMap A) X k l]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hcoeff, krausMap_single_apply]

/-- A completely positive map has at most card(output)*card(input) Kraus slots. -/
theorem exists_kraus_of_completelyPositive [Nonempty ι]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (hΦ : CompletelyPositive Φ) :
    ∃ A : (κ × ι) → Matrix κ ι ℂ, Φ = krausMap A :=
  exists_kraus_of_choiMatrix_posSemidef Φ hΦ.choiMatrix_posSemidef

/-- Finite ancillary complete positivity is equivalent to finite Kraus form. -/
theorem completelyPositive_iff_exists_kraus [Nonempty ι]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    CompletelyPositive Φ ↔ ∃ A : (κ × ι) → Matrix κ ι ℂ, Φ = krausMap A := by
  constructor
  · exact exists_kraus_of_completelyPositive Φ
  · rintro ⟨A, rfl⟩
    exact completelyPositive_krausMap A

/-- The normalized Choi positivity criterion uses the existing CP definition. -/
theorem completelyPositive_iff_choiMatrix_posSemidef [Nonempty ι]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    CompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  constructor
  · exact CompletelyPositive.choiMatrix_posSemidef
  · intro hΦ
    obtain ⟨A, rfl⟩ := exists_kraus_of_choiMatrix_posSemidef Φ hΦ
    exact completelyPositive_krausMap A

section FiniteInstrument

variable {σ : Type*} [Fintype σ] [Nonempty ι]

/-- Trace-preserving finite CP branches admit a genuine normalized Kraus
instrument with the original outcome and quantum systems. -/
theorem exists_instrument_of_completelyPositive_branches
    (Φ : σ → (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ))
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTP : ∀ X : Matrix ι ι ℂ, (∑ x, Φ x X).trace = X.trace) :
    ∃ I : FiniteKrausInstrument ι κ σ (κ × ι), ∀ x, I.branch x = Φ x := by
  classical
  choose A hA using fun x => exists_kraus_of_completelyPositive (Φ x) (hCP x)
  have hnorm : (∑ x, ∑ e, (A x e)ᴴ * A x e) = (1 : Matrix ι ι ℂ) := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.one_mul]
    calc
      _ = ∑ x, ∑ e, (A x e * X * (A x e)ᴴ).trace := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro e _
        exact (Matrix.trace_mul_cycle (A x e) X (A x e)ᴴ).symm
      _ = ∑ x, (Φ x X).trace := by
        simp only [hA, krausMap_apply, Matrix.trace_sum]
      _ = X.trace := by simpa only [Matrix.trace_sum] using hTP X
  let I : FiniteKrausInstrument ι κ σ (κ × ι) := ⟨A, hnorm⟩
  exact ⟨I, fun x => (hA x).symm⟩

/-- Finite CP maps with trace-preserving sum are exactly finite Kraus instruments. -/
theorem exists_instrument_iff_completelyPositive_trace_preserving
    (Φ : σ → (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)) :
    (∃ I : FiniteKrausInstrument ι κ σ (κ × ι), ∀ x, I.branch x = Φ x) ↔
      (∀ x, CompletelyPositive (Φ x)) ∧
        (∀ X : Matrix ι ι ℂ, (∑ x, Φ x X).trace = X.trace) := by
  constructor
  · rintro ⟨I, hI⟩
    constructor
    · intro x
      rw [← hI x]
      exact I.branch_completelyPositive x
    · intro X
      have h := I.trace_channel X
      simpa only [FiniteKrausInstrument.channel, LinearMap.sum_apply, hI] using h
  · rintro ⟨hCP, hTP⟩
    exact exists_instrument_of_completelyPositive_branches Φ hCP hTP

end FiniteInstrument

end

end NLQCLean.ClassicalCommunication

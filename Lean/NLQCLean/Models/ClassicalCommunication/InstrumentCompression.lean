import NLQCLean.Models.ClassicalCommunication.FiniteInstruments
import NLQCLean.Models.ClassicalCommunication.HermitianMomentSupport

/-!
# Score-preserving finite Kraus instrument compression

Actual positive-trace outcomes supply the normalized Hermitian marginal and
real score moments. Their trace probabilities prove the convex-hull premise;
the selected moments are realized by rescaling the original Kraus matrices.
The input, output and within-branch Kraus systems are unchanged.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped ComplexOrder

noncomputable section

private def hermitianMatrixCoe (ι : Type*) [Fintype ι] [DecidableEq ι] :
    selfAdjoint (Matrix ι ι ℂ) →ₗ[ℝ] Matrix ι ι ℂ where
  toFun A := A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem hermitianMatrixCoe_apply
    (ι : Type*) [Fintype ι] [DecidableEq ι] (A : selfAdjoint (Matrix ι ι ℂ)) :
    hermitianMatrixCoe ι A = (A : Matrix ι ι ℂ) := rfl

namespace FiniteKrausInstrument

variable {ι κ σ ε : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [Fintype ε]
variable [DecidableEq ι]

/-- The input effect of one actual instrument outcome. -/
def inputMarginal (I : FiniteKrausInstrument ι κ σ ε) (x : σ) :
    selfAdjoint (Matrix ι ι ℂ) :=
  ⟨∑ e, (I.operator x e)ᴴ * I.operator x e,
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      (Matrix.posSemidef_sum _ (fun e _ =>
        Matrix.posSemidef_conjTranspose_mul_self (I.operator x e))).isHermitian⟩

theorem inputMarginal_posSemidef (I : FiniteKrausInstrument ι κ σ ε) (x : σ) :
    (I.inputMarginal x : Matrix ι ι ℂ).PosSemidef :=
  Matrix.posSemidef_sum _ (fun e _ =>
    Matrix.posSemidef_conjTranspose_mul_self (I.operator x e))

theorem sum_inputMarginal (I : FiniteKrausInstrument ι κ σ ε) :
    (∑ x, I.inputMarginal x) = 1 := by
  apply Subtype.ext
  change hermitianMatrixCoe ι (∑ x, I.inputMarginal x) =
    hermitianMatrixCoe ι 1
  rw [map_sum]
  exact I.normalized

/-- The unnormalized input trace mass of an outcome. -/
def traceMass (I : FiniteKrausInstrument ι κ σ ε) (x : σ) : ℝ :=
  (I.inputMarginal x : Matrix ι ι ℂ).trace.re

theorem traceMass_eq_sum_frobNormSq (I : FiniteKrausInstrument ι κ σ ε) (x : σ) :
    I.traceMass x = ∑ e, frobNormSq (I.operator x e) := by
  simp only [traceMass, inputMarginal, Matrix.trace_sum, Complex.re_sum,
    ← frobInner_eq_trace, frobNormSq]

theorem traceMass_nonneg (I : FiniteKrausInstrument ι κ σ ε) (x : σ) :
    0 ≤ I.traceMass x := by
  rw [traceMass_eq_sum_frobNormSq]
  exact Finset.sum_nonneg (fun e _ => frobNormSq_nonneg _)

theorem operator_eq_zero_of_traceMass_eq_zero
    (I : FiniteKrausInstrument ι κ σ ε) {x : σ} (hx : I.traceMass x = 0) :
    ∀ e, I.operator x e = 0 := by
  rw [traceMass_eq_sum_frobNormSq] at hx
  intro e
  apply (frobNormSq_eq_zero_iff (I.operator x e)).mp
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => frobNormSq_nonneg (I.operator x e))).mp hx e (Finset.mem_univ e)

theorem inputMarginal_eq_zero_of_traceMass_eq_zero
    (I : FiniteKrausInstrument ι κ σ ε) {x : σ} (hx : I.traceMass x = 0) :
    I.inputMarginal x = 0 := by
  apply Subtype.ext
  simp [inputMarginal, I.operator_eq_zero_of_traceMass_eq_zero hx]

theorem branch_eq_zero_of_traceMass_eq_zero
    (I : FiniteKrausInstrument ι κ σ ε) {x : σ} (hx : I.traceMass x = 0) :
    I.branch x = 0 := by
  ext X k l
  simp [branch, krausMap_apply, I.operator_eq_zero_of_traceMass_eq_zero hx]

theorem sum_traceMass (I : FiniteKrausInstrument ι κ σ ε) :
    (∑ x, I.traceMass x) = Fintype.card ι := by
  have h := congrArg (hermitianRealTrace ι) I.sum_inputMarginal
  simpa [map_sum, hermitianRealTrace, traceMass, Matrix.trace_one] using h

/-- The probability of an outcome on the maximally mixed input. -/
def traceProbability (I : FiniteKrausInstrument ι κ σ ε) (x : σ) : ℝ :=
  I.traceMass x / Fintype.card ι

theorem traceProbability_nonneg (I : FiniteKrausInstrument ι κ σ ε) (x : σ) :
    0 ≤ I.traceProbability x :=
  div_nonneg (I.traceMass_nonneg x) (Nat.cast_nonneg _)

section NonemptyInput

variable [Nonempty ι]

theorem sum_traceProbability (I : FiniteKrausInstrument ι κ σ ε) :
    (∑ x, I.traceProbability x) = 1 := by
  simp only [traceProbability, ← Finset.sum_div, I.sum_traceMass]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Only original outcomes with strictly positive input trace mass. -/
abbrev PositiveOutcome (I : FiniteKrausInstrument ι κ σ ε) :=
  {x : σ // 0 < I.traceMass x}

instance fintypePositiveOutcome (I : FiniteKrausInstrument ι κ σ ε) :
    Fintype I.PositiveOutcome := by
  classical
  exact inferInstanceAs (Fintype {x : σ // 0 < I.traceMass x})

theorem traceProbability_pos (I : FiniteKrausInstrument ι κ σ ε)
    (a : I.PositiveOutcome) : 0 < I.traceProbability a.val :=
  div_pos a.property (Nat.cast_pos.mpr Fintype.card_pos)

omit [Nonempty ι] in
/-- Zero-trace outcomes contribute zero to every moment that vanishes there. -/
theorem sum_positiveOutcome_eq_sum (I : FiniteKrausInstrument ι κ σ ε)
    {V : Type*} [AddCommMonoid V] (f : σ → V)
    (hzero : ∀ x, I.traceMass x = 0 → f x = 0) :
    (∑ a : I.PositiveOutcome, f a.val) = ∑ x, f x := by
  classical
  have hz : (∑ a : {x : σ // ¬0 < I.traceMass x}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hzero a.val (le_antisymm (le_of_not_gt a.property) (I.traceMass_nonneg _))
  have h := Fintype.sum_subtype_add_sum_subtype (fun x => 0 < I.traceMass x) f
  simpa only [hz, add_zero, PositiveOutcome] using h

/-- Each positive outcome is normalized to the input identity's real trace. -/
def normalizedMarginal (I : FiniteKrausInstrument ι κ σ ε) (a : I.PositiveOutcome) :
    selfAdjoint (Matrix ι ι ℂ) :=
  (I.traceProbability a.val)⁻¹ • I.inputMarginal a.val

theorem trace_normalizedMarginal (I : FiniteKrausInstrument ι κ σ ε)
    (a : I.PositiveOutcome) :
    (I.normalizedMarginal a : Matrix ι ι ℂ).trace.re = Fintype.card ι := by
  change hermitianRealTrace ι ((I.traceProbability a.val)⁻¹ • I.inputMarginal a.val) = _
  rw [map_smul, smul_eq_mul]
  change (I.traceProbability a.val)⁻¹ * I.traceMass a.val = _
  have ht : I.traceMass a.val = I.traceProbability a.val * (Fintype.card ι : ℝ) := by
    rw [traceProbability, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  rw [ht, ← mul_assoc, inv_mul_cancel₀ (I.traceProbability_pos a).ne', one_mul]

/-- The moment barycenter of a finite instrument belongs to the convex hull
of its positive outcomes. -/
theorem normalized_marginal_score_mem_convexHull
    (I : FiniteKrausInstrument ι κ σ ε)
    (L : σ → ((Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ)) :
    ((1 : selfAdjoint (Matrix ι ι ℂ)), ∑ x, L x (I.branch x)) ∈
      convexHull ℝ (Set.range fun a : I.PositiveOutcome =>
        (I.normalizedMarginal a,
          (I.traceProbability a.val)⁻¹ * L a.val (I.branch a.val))) := by
  classical
  let p : I.PositiveOutcome → ℝ := fun a => I.traceProbability a.val
  let f : I.PositiveOutcome → selfAdjoint (Matrix ι ι ℂ) × ℝ := fun a =>
    (I.normalizedMarginal a, (p a)⁻¹ * L a.val (I.branch a.val))
  have hsum : (∑ a : I.PositiveOutcome, p a) = 1 := by
    rw [I.sum_positiveOutcome_eq_sum I.traceProbability ?_]
    · exact I.sum_traceProbability
    · intro x hx
      simp [traceProbability, hx]
  have hm : (∑ a : I.PositiveOutcome, p a • f a) =
      ((1 : selfAdjoint (Matrix ι ι ℂ)), ∑ x, L x (I.branch x)) := by
    calc
      _ = ∑ a : I.PositiveOutcome, (I.inputMarginal a.val, L a.val (I.branch a.val)) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Prod.ext
        · change p a • ((p a)⁻¹ • I.inputMarginal a.val) = _
          rw [smul_smul, mul_inv_cancel₀ (I.traceProbability_pos a).ne', one_smul]
        · change p a * ((p a)⁻¹ * L a.val (I.branch a.val)) = _
          rw [← mul_assoc, mul_inv_cancel₀ (I.traceProbability_pos a).ne', one_mul]
      _ = ∑ x, (I.inputMarginal x, L x (I.branch x)) := by
        apply I.sum_positiveOutcome_eq_sum
          (fun x => (I.inputMarginal x, L x (I.branch x)))
        intro x hx
        simp [I.inputMarginal_eq_zero_of_traceMass_eq_zero hx,
          I.branch_eq_zero_of_traceMass_eq_zero hx]
      _ = _ := by
        apply Prod.ext
        · simpa only [Prod.fst_sum] using I.sum_inputMarginal
        · simp only [Prod.snd_sum]
  have hconv := (convex_convexHull ℝ (Set.range f)).sum_mem
    (t := Finset.univ) (w := p) (z := f)
    (fun a _ => (I.traceProbability_pos a).le) hsum
    (fun a _ => subset_convexHull ℝ (Set.range f) ⟨a, rfl⟩)
  have hconv' : (∑ a : I.PositiveOutcome, p a • f a) ∈
      convexHull ℝ (Set.range f) := hconv
  rw [hm] at hconv'
  exact hconv'

end NonemptyInput

omit [Fintype ι] [DecidableEq ι] in
/-- Square-root Kraus scaling scales the input effect by the nonnegative
real coefficient. -/
theorem sqrt_smul_gram (c : ℝ) (hc : 0 ≤ c) (A : Matrix κ ι ℂ) :
    ((Real.sqrt c : ℂ) • A)ᴴ * ((Real.sqrt c : ℂ) • A) = c • (Aᴴ * A) := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show star (Real.sqrt c : ℂ) = (Real.sqrt c : ℂ) from by simp,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rfl

omit [Fintype κ] [DecidableEq ι] in
/-- Square-root Kraus scaling scales the complete branch operation. -/
theorem krausMap_sqrt_smul (c : ℝ) (hc : 0 ≤ c) (A : ε → Matrix κ ι ℂ) :
    krausMap (fun e => (Real.sqrt c : ℂ) • A e) = c • krausMap A := by
  apply LinearMap.ext
  intro X
  simp only [krausMap_apply, LinearMap.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show star (Real.sqrt c : ℂ) = (Real.sqrt c : ℂ) from by simp,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rfl

/-- Selected outcomes with normalized rescaled input effects are an actual
finite Kraus instrument on the unchanged quantum and Kraus systems. -/
def rescaleSelected (I : FiniteKrausInstrument ι κ σ ε) {n : ℕ}
    (select : Fin n → σ) (scale : Fin n → ℝ) (hscale : ∀ j, 0 ≤ scale j)
    (hnormalized : (∑ j, scale j • I.inputMarginal (select j)) = 1) :
    FiniteKrausInstrument ι κ (Fin n) ε where
  operator j e := (Real.sqrt (scale j) : ℂ) • I.operator (select j) e
  normalized := by
    have h := congrArg (hermitianMatrixCoe ι) hnormalized
    simp only [map_sum, map_smul, hermitianMatrixCoe_apply] at h
    calc
      _ = ∑ j, scale j • (I.inputMarginal (select j) : Matrix ι ι ℂ) := by
        simp only [sqrt_smul_gram _ (hscale _), inputMarginal, Finset.smul_sum]
      _ = 1 := h

theorem branch_rescaleSelected (I : FiniteKrausInstrument ι κ σ ε) {n : ℕ}
    (select : Fin n → σ) (scale : Fin n → ℝ) (hscale : ∀ j, 0 ≤ scale j)
    (hnormalized : (∑ j, scale j • I.inputMarginal (select j)) = 1) (j : Fin n) :
    (I.rescaleSelected select scale hscale hnormalized).branch j =
      scale j • I.branch (select j) :=
  krausMap_sqrt_smul _ (hscale j) _

/-- At most s²+1 selected actual outcomes, realized by square-root rescaling,
preserve any outcome-dependent real-linear target score exactly. -/
theorem exists_score_preserving_compression [Nonempty ι]
    (I : FiniteKrausInstrument ι κ σ ε)
    (L : σ → ((Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ)) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 + 1 ∧
      ∃ (select : Fin n → σ) (scale : Fin n → ℝ)
        (J : FiniteKrausInstrument ι κ (Fin n) ε),
        (∀ j, 0 ≤ scale j) ∧
        (∀ j e, J.operator j e = (Real.sqrt (scale j) : ℂ) • I.operator (select j) e) ∧
        (∀ j, J.branch j = scale j • I.branch (select j)) ∧
        (∑ j, L (select j) (J.branch j)) = ∑ x, L x (I.branch x) := by
  classical
  obtain ⟨n, hn, chooseOutcome, weight, hweight, hsum, hm, hq⟩ :=
    exists_normalized_hermitian_marginal_score_support
      I.normalizedMarginal
      (fun a => (I.traceProbability a.val)⁻¹ * L a.val (I.branch a.val))
      (∑ x, L x (I.branch x)) I.trace_normalizedMarginal
      (I.normalized_marginal_score_mem_convexHull L)
  let select : Fin n → σ := fun j => (chooseOutcome j).val
  let scale : Fin n → ℝ := fun j =>
    weight j * (I.traceProbability (select j))⁻¹
  have hscale : ∀ j, 0 ≤ scale j := fun j =>
    mul_nonneg (hweight j) (inv_nonneg.mpr (I.traceProbability_nonneg _))
  have hnormalized : (∑ j, scale j • I.inputMarginal (select j)) = 1 := by
    simpa only [normalizedMarginal, select, scale, smul_smul] using hm
  let J := I.rescaleSelected select scale hscale hnormalized
  refine ⟨n, hn, select, scale, J, hscale, (fun _ _ => rfl), ?_, ?_⟩
  · exact I.branch_rescaleSelected select scale hscale hnormalized
  · calc
      _ = ∑ j, scale j * L (select j) (I.branch (select j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [I.branch_rescaleSelected select scale hscale hnormalized, map_smul,
          smul_eq_mul]
      _ = _ := by
        simpa only [scale, select, mul_assoc] using hq

end FiniteKrausInstrument

end

end NLQCLean.ClassicalCommunication

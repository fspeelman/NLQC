import NLQCLean.LinearAlgebra.CrossedSinglet
import NLQCLean.Models.ClassicalCommunication.CoherentConversion
import NLQCLean.Models.ClassicalCommunication.CoherentLabels
import NLQCLean.Approx.GeneralizedBellBasis
import NLQCLean.Approx.PVMSharpFreezing
import NLQCLean.Approx.NearBellFreezing

/-!
# Reference entanglement and messages for near-Bell measurements

Bob's local input/reference pair and his label-controlled reference correction
give an actual finite isometric probe of a PVM protocol. Its crossed amplitude
is bounded directly by the communicated message dimension. The physical PVM
reference comparison is separate from the unitary near-SWAP message theorem.
The source is `lem:bell-compression` in the revised robust companion.
-/

namespace NLQCLean

open Matrix ClassicalCommunication
open scoped Matrix.Norms.Frobenius Kronecker

/-- Swap the reference index and message index in a kept-register tuple. -/
def nearBellProbeRegisterEquiv (κ μ : Type*) (d : ℕ) :
    (κ × Fin d) × μ ≃ (κ × μ) × Fin d where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A local Bob input/reference pair, with no cross-laboratory resource cost. -/
noncomputable def nearBellLocalReferencePair (d : ℕ) : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt (d : ℝ))⁻¹ : ℂ) else 0

theorem nearBellLocalReferencePair_isUnitVector {d : ℕ} (hd : 0 < d) :
    IsUnitVector (nearBellLocalReferencePair d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnorm : Complex.normSq ((Real.sqrt (d : ℝ))⁻¹ : ℂ) = (d : ℝ)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      inv_pow, sq_abs, Real.sq_sqrt hdR.le]
  change (∑ p : Fin d × Fin d, Complex.normSq (nearBellLocalReferencePair d p)) = 1
  rw [Fintype.sum_prod_type]
  simp only [nearBellLocalReferencePair, apply_ite, Complex.normSq_zero, hnorm,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hdR.ne'

/-- The probe's decoder is the actual decoder tensored with the retained
reference, followed by a correction controlled by Bob's output label. -/
noncomputable def nearBellCorrectedReferenceDecoder
    {d : ℕ} {δ κ μ ε : Type*} [Fintype δ] [Fintype κ] [Fintype μ] [Fintype ε]
    [DecidableEq δ] [DecidableEq κ] [DecidableEq μ] [DecidableEq ε]
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (D : Matrix (δ × ε) (κ × μ) ℂ) :
    Matrix (Fin d × (δ × ε)) ((κ × Fin d) × μ) ℂ :=
  let correction : Matrix (Fin d × (δ × ε)) (Fin d × (δ × ε)) ℂ :=
    controlledMatrix (ι := Fin d) (κ := Fin d) (σ := δ × ε) (fun y => C y.1)
  let decoder : Matrix (Fin d × (δ × ε)) ((κ × Fin d) × μ) ℂ :=
    (D ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
      (Equiv.prodComm (Fin d) (δ × ε)) (nearBellProbeRegisterEquiv κ μ d)
  correction * decoder

theorem nearBellCorrectedReferenceDecoder_isometry
    {d : ℕ} {δ κ μ ε : Type*} [Fintype δ] [Fintype κ] [Fintype μ] [Fintype ε]
    [DecidableEq δ] [DecidableEq κ] [DecidableEq μ] [DecidableEq ε]
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (D : Matrix (δ × ε) (κ × μ) ℂ)
    (hC : ∀ i, IsIsometry (C i)) (hD : IsIsometry D) :
    IsIsometry (nearBellCorrectedReferenceDecoder C D) := by
  unfold nearBellCorrectedReferenceDecoder
  have hc : IsIsometry
      (controlledMatrix (ι := Fin d) (κ := Fin d) (σ := δ × ε)
        (fun y : δ × ε => C y.1)) :=
    controlledMatrix_isometry (ι := Fin d) (κ := Fin d) (σ := δ × ε)
      (fun y : δ × ε => C y.1) (fun y => hC y.1)
  have hd : IsIsometry
      ((D ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
        (Equiv.prodComm (Fin d) (δ × ε)) (nearBellProbeRegisterEquiv κ μ d)) :=
    (hD.kronecker isIsometry_one).submatrix_equiv
      (Equiv.prodComm (Fin d) (δ × ε)) (nearBellProbeRegisterEquiv κ μ d)
  exact hc.mul hd

/-- The seed input separates Bob's original resource and his two local
reference-pair indices. -/
def nearBellProbeInputEquiv (ρ : Type*) (d : ℕ) :
    Unit × (ρ × (Fin d × Fin d)) ≃ (Fin d × ρ) × Fin d where
  toFun p := ((p.2.2.1, p.2.1), p.2.2.2)
  invFun p := ((), (p.1.2, (p.1.1, p.2)))
  left_inv := by rintro ⟨⟨⟩, p⟩; rfl
  right_inv _ := rfl

/-- Bob encodes his local input half while retaining the reference half. -/
noncomputable def nearBellReferenceEncoder
    {d : ℕ} {ρ κ μ : Type*} [Fintype ρ] [Fintype κ] [Fintype μ]
    [DecidableEq ρ] [DecidableEq κ] [DecidableEq μ]
    (V : Matrix (κ × μ) (Fin d × ρ) ℂ) :
    Matrix ((κ × Fin d) × μ) (Unit × (ρ × (Fin d × Fin d))) ℂ :=
  (V ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
    (nearBellProbeRegisterEquiv κ μ d) (nearBellProbeInputEquiv ρ d)

theorem nearBellReferenceEncoder_isometry
    {d : ℕ} {ρ κ μ : Type*} [Fintype ρ] [Fintype κ] [Fintype μ]
    [DecidableEq ρ] [DecidableEq κ] [DecidableEq μ]
    (V : Matrix (κ × μ) (Fin d × ρ) ℂ) (hV : IsIsometry V) :
    IsIsometry (nearBellReferenceEncoder V) := by
  unfold nearBellReferenceEncoder
  exact (hV.kronecker isIsometry_one).submatrix_equiv
    (nearBellProbeRegisterEquiv κ μ d) (nearBellProbeInputEquiv ρ d)

/-- Append Bob's normalized local pair to the original shared resource. -/
noncomputable def nearBellReferenceResource {ρA ρB : Type*} (d : ℕ)
    (η : ρA × ρB → ℂ) : ρA × (ρB × (Fin d × Fin d)) → ℂ :=
  fun p => η (p.1, p.2.1) * nearBellLocalReferencePair d p.2.2

theorem nearBellReferenceResource_isUnitVector
    {d : ℕ} (hd : 0 < d) {ρA ρB : Type*} [Fintype ρA] [Fintype ρB]
    (η : ρA × ρB → ℂ) (hη : IsUnitVector η) :
    IsUnitVector (nearBellReferenceResource d η) := by
  have hp : ∑ a, ∑ b, Complex.normSq (nearBellLocalReferencePair d (a, b)) = 1 := by
    simpa only [IsUnitVector, Fintype.sum_prod_type] using
      nearBellLocalReferencePair_isUnitVector hd
  have hη' : ∑ a, ∑ b, Complex.normSq (η (a, b)) = 1 := by
    simpa only [IsUnitVector, Fintype.sum_prod_type] using hη
  change (∑ p, Complex.normSq (nearBellReferenceResource d η p)) = 1
  simp only [nearBellReferenceResource, Complex.normSq_mul, Fintype.sum_prod_type,
    ← Finset.mul_sum, hp, mul_one]
  exact hη'

/-- The retained reference is the unchanged second half of Bob's local pair. -/
theorem nearBellReferenceEncoder_apply
    {d : ℕ} {ρ κ μ : Type*} [Fintype ρ] [Fintype κ] [Fintype μ]
    [DecidableEq ρ] [DecidableEq κ] [DecidableEq μ]
    (V : Matrix (κ × μ) (Fin d × ρ) ℂ)
    (k : κ) (a : Fin d) (m : μ) (p : ρ) (b c : Fin d) :
    nearBellReferenceEncoder V ((k, a), m) ((), (p, (b, c))) =
      if a = c then V (k, m) (b, p) else 0 := by
  change V (k, m) (b, p) * (1 : Matrix (Fin d) (Fin d) ℂ) a c = _
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The actual decoder correction acts on the retained reference only. -/
theorem nearBellCorrectedReferenceDecoder_apply
    {d : ℕ} {δ κ μ ε : Type*} [Fintype δ] [Fintype κ] [Fintype μ] [Fintype ε]
    [DecidableEq δ] [DecidableEq κ] [DecidableEq μ] [DecidableEq ε]
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (D : Matrix (δ × ε) (κ × μ) ℂ)
    (r b : Fin d) (i : δ) (e : ε) (k : κ) (m : μ) :
    nearBellCorrectedReferenceDecoder C D (r, (i, e)) ((k, b), m) =
      C i r b * D (i, e) (k, m) := by
  simp [nearBellCorrectedReferenceDecoder, controlledMatrix,
    Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, nearBellProbeRegisterEquiv, Prod.swap, Prod.ext_iff,
    ite_mul, ite_and]

/-- Bob's encoded coefficient with the locally retained reference equals
the original Choi-input coefficient with its exact normalization. -/
theorem nearBellReference_crossedPhi
    {d : ℕ} {ρA ρB κB μB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κB] [Fintype μB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κB] [DecidableEq μB]
    (V : Matrix (κB × μB) (Fin d × ρB) ℂ) (η : ρA × ρB → ℂ)
    (k : κB) (b : Fin d) (m : μB) (p : ρA) :
    crossedPhi (nearBellReferenceEncoder V) (nearBellReferenceResource d η)
        ((k, b), m) () p =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * crossedPhi V η (k, m) b p := by
  simp only [crossedPhi, Fintype.sum_prod_type, nearBellReferenceEncoder_apply,
    nearBellReferenceResource, nearBellLocalReferencePair,
    mul_ite, ite_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pB _
  ring

/-- The probe's conditional Bob amplitude applies the actual label
correction to Bob's Choi reference index. -/
theorem nearBellReference_crossedChi
    {d : ℕ} {δ ρA ρB κB μA μB εB : Type*}
    [Fintype δ] [Fintype ρA] [Fintype ρB] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εB]
    [DecidableEq δ] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εB]
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (D : Matrix (δ × εB) (κB × μA) ℂ)
    (V : Matrix (κB × μB) (Fin d × ρB) ℂ) (η : ρA × ρB → ℂ)
    (a : μA) (y : δ × εB) (mB : μB) (q : Fin d × ρA) :
    crossedChi (nearBellCorrectedReferenceDecoder C D) (nearBellReferenceEncoder V)
        (nearBellReferenceResource d η) a () y mB q =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * ∑ kB, ∑ b,
        C y.1 q.1 b * D y (kB, a) * crossedPhi V η (kB, mB) b q.2 := by
  obtain ⟨i, e⟩ := y
  simp only [crossedChi, Fintype.sum_prod_type, nearBellCorrectedReferenceDecoder_apply,
    nearBellReference_crossedPhi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kB _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Full amplitude of the physical probe, with both input references and
the exact local-pair normalization retained in the coefficient formula. -/
theorem nearBellReference_crossedAmplitude
    {d : ℕ} {δ ρA ρB κA κB μA μB εA εB : Type*}
    [Fintype δ] [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq δ] [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (DA : Matrix (δ × εA) (κA × μB) ℂ) (DB : Matrix (δ × εB) (κB × μA) ℂ)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ) (η : ρA × ρB → ℂ)
    (x : δ × εA) (y : δ × εB) :
    crossedAmplitude DA (nearBellCorrectedReferenceDecoder C DB) VA
        (nearBellReferenceEncoder VB) (nearBellReferenceResource d η) () x y =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
        ∑ a, ∑ kA, ∑ mB, ∑ r, ∑ pA, ∑ kB, ∑ b, ∑ pB,
          C y.1 r b * DA x (kA, mB) * DB y (kB, a) *
            VA (kA, a) (r, pA) * VB (kB, mB) (b, pB) * η (pA, pB) := by
  simp only [crossedAmplitude, crossedXi, Fintype.sum_prod_type,
    nearBellReference_crossedChi, crossedPhi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun kA _ =>
    Finset.sum_congr rfl fun mB _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun pA _ => Finset.sum_congr rfl fun kB _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun pB _ => ?_
  ring

/-- Rearrange the finite encoder, message and Choi-reference sums without
any assumption on the original register cardinalities. -/
theorem nearBellReferenceSum_reorder
    {α₁ α₂ α₃ α₄ α₅ α₆ α₇ α₈ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype α₃] [Fintype α₄]
    [Fintype α₅] [Fintype α₆] [Fintype α₇] [Fintype α₈]
    (f : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → α₈ → ℂ) :
    ∑ a, ∑ kA, ∑ mB, ∑ r, ∑ pA, ∑ kB, ∑ b, ∑ pB, f a kA mB r pA kB b pB =
      ∑ r, ∑ b, ∑ kA, ∑ mB, ∑ kB, ∑ a, ∑ pA, ∑ pB, f a kA mB r pA kB b pB := by
  let E : (α₁ × α₂ × α₃ × α₄ × α₅ × α₆ × α₇ × α₈) ≃
      (α₄ × α₇ × α₂ × α₃ × α₆ × α₁ × α₅ × α₈) :=
    ⟨fun p => (p.2.2.2.1, p.2.2.2.2.2.2.1, p.2.1, p.2.2.1,
        p.2.2.2.2.2.1, p.1, p.2.2.2.2.1, p.2.2.2.2.2.2.2),
      fun p => (p.2.2.2.2.2.1, p.2.2.1, p.2.2.2.1, p.1,
        p.2.2.2.2.2.2.1, p.2.2.2.2.1, p.2.1, p.2.2.2.2.2.2.2),
      fun _ => rfl, fun _ => rfl⟩
  have h := Fintype.sum_equiv E
    (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)
    (fun p => f p.2.2.2.2.2.1 p.2.2.1 p.2.2.2.1 p.1 p.2.2.2.2.2.2.1
      p.2.2.2.2.1 p.2.1 p.2.2.2.2.2.2.2) (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using h

lemma nearBellReferenceProjection_globalIsometry_apply
    {d : ℕ} {δ εA εB ρA ρB κA μA κB μB : Type*}
    [Fintype δ] [Fintype εA] [Fintype εB] [Fintype ρA] [Fintype ρB]
    [Fintype κA] [Fintype μA] [Fintype κB] [Fintype μB]
    [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq μA]
    [DecidableEq κB] [DecidableEq μB]
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (δ × εA) (κA × μB) ℂ)
    (DB : Matrix (δ × εB) (κB × μA) ℂ)
    (x : δ × εA) (y : δ × εB) :
    nearBellReferenceProjection C (globalIsometry η VA VB DA DB) x y =
      ∑ r, ∑ b, ∑ kA, ∑ mB, ∑ kB, ∑ a, ∑ pA, ∑ pB,
        C y.1 r b * DA x (kA, mB) * DB y (kB, a) *
          VA (kA, a) (r, pA) * VB (kB, mB) (b, pB) * η (pA, pB) := by
  unfold nearBellReferenceProjection
  simp_rw [globalIsometry_entry, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro kA _
  apply Finset.sum_congr rfl
  intro mB _
  apply Finset.sum_congr rfl
  intro kB _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro pA _
  apply Finset.sum_congr rfl
  intro pB _
  ring

/-- The crossed local-reference experiment is exactly the corrected PVM projection. -/
theorem nearBellReference_crossedAmplitude_eq_projection
    {d : ℕ} {δ εA εB ρA ρB κA μA κB μB : Type*}
    [Fintype δ] [Fintype εA] [Fintype εB] [Fintype ρA] [Fintype ρB]
    [Fintype κA] [Fintype μA] [Fintype κB] [Fintype μB]
    [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq μA]
    [DecidableEq κB] [DecidableEq μB]
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (δ × εA) (κA × μB) ℂ)
    (DB : Matrix (δ × εB) (κB × μA) ℂ)
    (x : δ × εA) (y : δ × εB) :
    crossedAmplitude DA (nearBellCorrectedReferenceDecoder C DB) VA
      (nearBellReferenceEncoder VB) (nearBellReferenceResource d η) () x y =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
        nearBellReferenceProjection C (globalIsometry η VA VB DA DB) x y := by
  rw [nearBellReference_crossedAmplitude, nearBellReferenceProjection_globalIsometry_apply]
  congr 1
  exact nearBellReferenceSum_reorder _

/-- A physical label-controlled correction bounds the reference projection by
the square of Alice's message dimension, independently of the shared resource. -/
theorem nearBellReferenceProjection_messageA_upper
    {d : ℕ} (hd : 0 < d) {δ εA εB ρA ρB κA μA κB μB : Type*}
    [Fintype δ] [Fintype εA] [Fintype εB] [Fintype ρA] [Fintype ρB]
    [Fintype κA] [Fintype μA] [Fintype κB] [Fintype μB]
    [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq μA]
    [DecidableEq κB] [DecidableEq μB]
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (δ × εA) (κA × μB) ℂ)
    (DB : Matrix (δ × εB) (κB × μA) ℂ)
    (hC : ∀ i, IsIsometry (C i)) (hη : IsUnitVector η)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB) :
    ‖nearBellReferenceProjection C (globalIsometry η VA VB DA DB)‖ ^ 2 ≤
      (d : ℝ) * (Fintype.card μA : ℝ) ^ 2 := by
  have h := sum_normSq_crossedAmplitude_le hDA
    (nearBellCorrectedReferenceDecoder_isometry C DB hC hDB) hVA
    (nearBellReferenceEncoder_isometry VB hVB)
    (nearBellReferenceResource_isUnitVector hd η hη)
  have hbound : ∑ x, ∑ y, Complex.normSq
      (crossedAmplitude DA (nearBellCorrectedReferenceDecoder C DB) VA
        (nearBellReferenceEncoder VB) (nearBellReferenceResource d η) () x y) ≤
      (Fintype.card μA : ℝ) ^ 2 := by
    simpa using h
  have hnorm : Complex.normSq (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) = (d : ℝ)⁻¹ := by
    simp only [Complex.normSq_eq_norm_sq, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, inv_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp_rw [nearBellReference_crossedAmplitude_eq_projection, Complex.normSq_mul,
    hnorm, ← Finset.mul_sum] at hbound
  have hF : (∑ x, ∑ y, Complex.normSq
      (nearBellReferenceProjection C (globalIsometry η VA VB DA DB) x y)) =
      ‖nearBellReferenceProjection C (globalIsometry η VA VB DA DB)‖ ^ 2 := by
    simp only [← frobNormSq_eq_norm_sq, frobNormSq_eq_sum_normSq, Fintype.sum_prod_type]
  rw [hF] at hbound
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  calc
    _ = (d : ℝ) * ((d : ℝ)⁻¹ *
        ‖nearBellReferenceProjection C (globalIsometry η VA VB DA DB)‖ ^ 2) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hdR), one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hdR.le

end NLQCLean

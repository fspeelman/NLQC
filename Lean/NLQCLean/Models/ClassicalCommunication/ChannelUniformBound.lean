import NLQCLean.Models.ClassicalCommunication.ChoiChannelEquivalence

/-!
# Uniform norms of actual completely positive trace-preserving channels

The induced operator norm uses the elementwise supremum norm on the fixed
finite input and output matrix spaces. The actual normalized Kraus
representation bounds every Kraus entry by one, hence every matrix-unit
channel coefficient by the fixed Kraus alphabet size. Matrix-unit expansion
then gives a uniform operator-norm bound.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance uniformChannelMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance uniformChannelMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (uniformChannelMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
/-- The genuine instrument normalization bounds each of its actual Kraus
entries. Outcome and Kraus alphabets may be any finite types. -/
theorem FiniteKrausInstrument.operator_norm_le_one
    {σ ε : Type*} [Fintype σ] [Fintype ε]
    (I : FiniteKrausInstrument ι κ σ ε) (x : σ) (e : ε) (k : κ) (i : ι) :
    ‖I.operator x e k i‖ ≤ 1 := by
  classical
  have hrow := I.dilation_isometry.row_norm_sq_le_one (k, (x, e))
  have hsquare : ‖I.dilation (k, (x, e)) i‖ ^ 2 ≤ 1 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (‖I.dilation (k, (x, e)) j‖))
      (Finset.mem_univ i)).trans hrow
  change ‖I.operator x e k i‖ ^ 2 ≤ 1 at hsquare
  nlinarith [norm_nonneg (I.operator x e k i)]

omit [DecidableEq κ] in
/-- A coefficient bound on the actual matrix-unit images bounds the induced
elementwise operator norm of a continuous complex-linear operation. -/
theorem norm_le_of_matrixUnit_entry_bound
    (Φ : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hentry : ∀ (i j : ι) (k l : κ), ‖Φ (Matrix.single i j 1) k l‖ ≤ M) :
    ‖Φ‖ ≤ (Fintype.card ι : ℝ) ^ 2 * M := by
  classical
  apply Φ.opNorm_le_bound (by positivity)
  intro X
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro k l
  change ‖Φ.toLinearMap X k l‖ ≤ _
  rw [linearMap_matrix_apply]
  calc
    ‖∑ i, ∑ j, Φ.toLinearMap (Matrix.single i j 1) k l * X i j‖ ≤
        ∑ i, ∑ j, ‖Φ.toLinearMap (Matrix.single i j 1) k l * X i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : ι, ∑ _j : ι, M * ‖X‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hentry i j k l) (Matrix.norm_entry_le_entrywise_sup_norm X)
        (norm_nonneg _) hM
    _ = ((Fintype.card ι : ℝ) ^ 2 * M) * ‖X‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Actual finite-ancilla complete positivity and trace preservation give
a uniform matrix-unit coefficient bound through the checked Kraus theorem. -/
theorem completelyPositive_tracePreserving_matrixUnit_entry_bound [Nonempty ι]
    (Φ : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ)
    (hCP : CompletelyPositive Φ.toLinearMap)
    (hTP : ∀ X : Matrix ι ι ℂ, (Φ X).trace = X.trace)
    (i j : ι) (k l : κ) :
    ‖Φ (Matrix.single i j 1) k l‖ ≤ (Fintype.card (κ × ι) : ℝ) := by
  classical
  obtain ⟨I, hI⟩ := exists_instrument_of_completelyPositive_branches
    (fun _ : Unit => Φ.toLinearMap) (fun _ => hCP) (fun X => by simpa using hTP X)
  change ‖Φ.toLinearMap (Matrix.single i j 1) k l‖ ≤ _
  rw [← hI (), FiniteKrausInstrument.branch, krausMap_single_apply]
  calc
    ‖∑ e, I.operator () e k i * star (I.operator () e l j)‖ ≤
        ∑ e, ‖I.operator () e k i * star (I.operator () e l j)‖ := norm_sum_le _ _
    _ ≤ ∑ _e : κ × ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [one_mul, norm_mul, norm_star] using
        mul_le_mul (I.operator_norm_le_one () e k i) (I.operator_norm_le_one () e l j)
          (norm_nonneg (I.operator () e l j)) (by norm_num : (0 : ℝ) ≤ 1)
    _ = (Fintype.card (κ × ι) : ℝ) := by simp

/-- A concrete coarse bound depends only on the fixed input and output
dimensions, not on the channel, its Kraus operators or any classical outcome. -/
theorem completelyPositive_tracePreserving_norm_le [Nonempty ι]
    (Φ : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ)
    (hCP : CompletelyPositive Φ.toLinearMap)
    (hTP : ∀ X : Matrix ι ι ℂ, (Φ X).trace = X.trace) :
    ‖Φ‖ ≤ (Fintype.card ι : ℝ) ^ 2 * (Fintype.card (κ × ι) : ℝ) :=
  norm_le_of_matrixUnit_entry_bound Φ (Nat.cast_nonneg _)
    (completelyPositive_tracePreserving_matrixUnit_entry_bound Φ hCP hTP)

/-- All actual CP+TP continuous channel operations on the fixed finite
systems share a nonnegative elementwise operator-norm bound. -/
theorem exists_completelyPositive_tracePreserving_norm_bound
    (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Φ : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ,
      CompletelyPositive Φ.toLinearMap →
      (∀ X : Matrix ι ι ℂ, (Φ X).trace = X.trace) → ‖Φ‖ ≤ B := by
  refine ⟨(Fintype.card ι : ℝ) ^ 2 * (Fintype.card (κ × ι) : ℝ), by positivity, ?_⟩
  intro Φ hCP hTP
  exact completelyPositive_tracePreserving_norm_le Φ hCP hTP

end

end NLQCLean.ClassicalCommunication

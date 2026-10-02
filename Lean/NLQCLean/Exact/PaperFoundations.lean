import NLQCLean.Geometry.UnitaryHaar
import NLQCLean.Models.ClassicalCommunication.KrausRepresentation
import NLQCLean.Semialgebraic.Fibers
import NLQCLean.Semialgebraic.ProjectionTheorem

/-!
# Background facts stated in the exact paper

* The Haar measure: `unitaryHaar` is a left- and right-invariant probability
  measure on the unitary group, and the unique such measure.
* `fact:stinespring`: every completely positive trace-preserving map between
  finite matrix algebras is `ρ ↦ Tr_G[T ρ T†]` for a finite isometry `T`.
* `fact:TS`: projections of semialgebraic sets are semialgebraic, and the
  coordinate functions of a semialgebraic map are semialgebraic.
-/

noncomputable section

namespace NLQCLean

open MeasureTheory Matrix

section Haar

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Right translates of the unitary Haar measure are left-invariant
probability measures, hence equal to it. -/
instance isMulRightInvariant_unitaryHaar : (unitaryHaar n).IsMulRightInvariant := by
  constructor
  intro g
  let ν := Measure.map (· * g) (unitaryHaar n)
  have hmg : Measurable fun x : Matrix.unitaryGroup n ℂ => x * g := measurable_mul_const g
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have : ν.IsMulLeftInvariant := by
    constructor
    intro h
    change Measure.map (h * ·) (Measure.map (· * g) (unitaryHaar n)) =
      Measure.map (· * g) (unitaryHaar n)
    rw [Measure.map_map (measurable_const_mul h) hmg]
    have hcomm : (h * ·) ∘ (· * g) = (· * g) ∘ (h * ·) := by
      funext x
      simp [mul_assoc]
    rw [hcomm, ← Measure.map_map hmg (measurable_const_mul h), map_mul_left_eq_self]
  have hν := unitary_invariant_measure_eq_smul n ν
  have huniv : ν Set.univ = 1 := by
    rw [Measure.map_apply hmg MeasurableSet.univ, Set.preimage_univ, unitaryHaar_univ]
  rw [huniv, one_smul] at hν
  exact hν

/-- **Haar measure.** `unitaryHaar` is a probability measure that is both left
and right invariant, and every left- and right-invariant probability measure
on the unitary group equals it. -/
theorem unitaryHaar_isHaar_characterization :
    IsProbabilityMeasure (unitaryHaar n) ∧ (unitaryHaar n).IsMulLeftInvariant ∧
      (unitaryHaar n).IsMulRightInvariant ∧
      ∀ ν : Measure (Matrix.unitaryGroup n ℂ), IsProbabilityMeasure ν →
        ν.IsMulLeftInvariant → ν.IsMulRightInvariant → ν = unitaryHaar n := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun ν hν _ _ => ?_⟩
  have h := unitary_invariant_measure_eq_smul n ν
  rw [measure_univ, one_smul] at h
  exact h

end Haar

section Stinespring

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem trace_mul_single (B : Matrix ι ι ℂ) (i j : ι) :
    trace (B * Matrix.single j i (1 : ℂ)) = B i j := by
  rw [Matrix.trace, Finset.sum_eq_single i]
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · intro k _ hk
    simp [Matrix.mul_apply, Ne.symm hk]
  · simp

omit [DecidableEq κ] in
theorem eq_one_of_trace_mul_eq_trace {B : Matrix ι ι ℂ}
    (h : ∀ X : Matrix ι ι ℂ, trace (B * X) = trace X) : B = 1 := by
  ext i j
  have hX := h (Matrix.single j i 1)
  rw [trace_mul_single] at hX
  rw [hX, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.trace]
  · rw [ite_eq_right hij, Matrix.trace]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [Matrix.diag_apply, Matrix.single_apply]
    rw [ite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

/-- **`fact:stinespring`.** Every completely positive trace-preserving map
`Φ` from operators on `H` to operators on `K` has a finite isometric dilation
`T : H → K ⊗ G` with `Φ(ρ) = Tr_G[T ρ T†]` for every `ρ`; here
`G = Unit × (K × H)` indexes a Kraus family. -/
theorem exists_stinespring [Nonempty ι] (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hCP : ClassicalCommunication.CompletelyPositive Φ)
    (hTP : ∀ X, trace (Φ X) = trace X) :
    ∃ T : Matrix (κ × (Unit × (κ × ι))) ι ℂ, IsIsometry T ∧ Φ = channelOf T := by
  obtain ⟨A, hA⟩ := ClassicalCommunication.exists_kraus_of_completelyPositive Φ hCP
  have hnorm : ∑ e, (A e)ᴴ * A e = 1 := by
    apply eq_one_of_trace_mul_eq_trace
    intro X
    rw [← hTP X, hA, ClassicalCommunication.krausMap_apply, Matrix.trace_sum, Matrix.sum_mul,
      Matrix.trace_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.trace_mul_cycle (A e) X (A e)ᴴ]
  let I : ClassicalCommunication.FiniteKrausInstrument ι κ Unit (κ × ι) :=
    ⟨fun _ e => A e, by simpa using hnorm⟩
  refine ⟨I.dilation, I.dilation_isometry, ?_⟩
  rw [← I.channel_eq_channelOf_dilation, hA]
  ext X a b
  simp [I, ClassicalCommunication.FiniteKrausInstrument.channel_apply,
    ClassicalCommunication.krausMap_apply]

end Stinespring

section TarskiSeidenberg

/-- **`fact:TS`, projection.** The image of a semialgebraic subset of
`ℝ^{n+1}` under the projection to the first `n` coordinates is
semialgebraic. -/
theorem fact_TS_projection : SemialgebraicProjectionTheorem := semialgebraicProjectionTheorem

/-- **`fact:TS`, coordinates.** Each coordinate function of a semialgebraic map
is semialgebraic. -/
theorem SemialgebraicMapOn.coordinate {n m : ℕ} {S : Set (RealEuclidean n)}
    {c : RealEuclidean n → RealEuclidean m} (hc : SemialgebraicMapOn S c) (i : Fin m) :
    SemialgebraicMapOn S (fun x => (WithLp.toLp 2 (fun _ : Fin 1 => c x i) : RealEuclidean 1)) := by
  let J : Fin (n + 1) → Fin (n + m) := Fin.append (Fin.castAdd m) (fun _ : Fin 1 => Fin.natAdd n i)
  have h := SemialgebraicMapOn.image semialgebraicProjectionTheorem (hc.coordinate_graph J)
  unfold SemialgebraicMapOn
  convert h using 1
  rw [Set.image_image]
  refine Set.image_congr fun x _ => ?_
  ext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [J, coordinateProjection, Fin.append_left]
  · simp [J, coordinateProjection, Fin.append_right, Subsingleton.elim j 0]

end TarskiSeidenberg

end NLQCLean

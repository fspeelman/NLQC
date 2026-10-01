import NLQCLean.Geometry.UnitaryNormalVolume
import NLQCLean.Approx.WitnessEuclideanCoordinates

/-!
# The unitary tube in the witness output coordinates

The witness tube uses the same Frobenius metric and volume as the normal chart. The only change is
the fixed ordering of the real matrix-entry coordinates.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal

noncomputable def witnessOutputReindex (d : ℕ) :
    EuclideanSpace ℝ (((Fin d × Fin d) × (Fin d × Fin d)) × Fin 2) ≃ₗᵢ[ℝ]
      RealEuclidean (2 * d ^ 4) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (overlapOutputIndex d)

theorem witnessOutputReindex_apply (d : ℕ)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    witnessOutputReindex d (matrixFrobeniusCoordinates _ _ H) =
      overlapOutputCoordinates d H := rfl

def unitaryWitnessTube (d : ℕ) (r : ℝ)
    (S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)) : Set (RealEuclidean (2 * d ^ 4)) :=
  {y | ∃ U ∈ S, dist y (overlapOutputCoordinates d (U : Matrix _ _ ℂ)) < r}

theorem unitaryWitnessTube_eq_image (d : ℕ) (r : ℝ)
    (S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)) :
    unitaryWitnessTube d r S =
      witnessOutputReindex d '' unitaryFrobeniusTube (Fin d × Fin d) r S := by
  ext y
  constructor
  · rintro ⟨U, hU, hy⟩
    refine ⟨(witnessOutputReindex d).symm y, ⟨U, hU, ?_⟩,
      (witnessOutputReindex d).apply_symm_apply y⟩
    rwa [← (witnessOutputReindex d).dist_map, LinearIsometryEquiv.apply_symm_apply,
      witnessOutputReindex_apply]
  · rintro ⟨z, ⟨U, hU, hz⟩, rfl⟩
    refine ⟨U, hU, ?_⟩
    rwa [← witnessOutputReindex_apply, (witnessOutputReindex d).dist_map]

theorem volume_unitaryWitnessTube (d : ℕ) (r : ℝ)
    (S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)) :
    volume (unitaryWitnessTube d r S) =
      volume (unitaryFrobeniusTube (Fin d × Fin d) r S) := by
  rw [unitaryWitnessTube_eq_image]
  have h := (witnessOutputReindex d).symm.measurePreserving.measure_preimage_equiv
    (f := (witnessOutputReindex d).symm.toMeasurableEquiv)
    (unitaryFrobeniusTube (Fin d × Fin d) r S)
  convert h using 2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨(witnessOutputReindex d).symm x, hx, (witnessOutputReindex d).apply_symm_apply x⟩

/-- The normal-tube/Haar comparison in the coordinates of the polynomial witness. -/
theorem unitaryHaar_witnessTube_volume_lower (d : ℕ) {r : ℝ}
    (hr : 0 < r) (hr' : r ≤ 1 / 2)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S) :
    ENNReal.ofReal ((1 / 16 : ℝ) ^ (d ^ 4)) * euclideanUnitBallVolume (d ^ 4) ^ 2 *
      ENNReal.ofReal r ^ (d ^ 4) * unitaryHaar (Fin d × Fin d) S ≤
        volume (unitaryWitnessTube d r S) := by
  rw [volume_unitaryWitnessTube]
  have hd : Fintype.card (Fin d × Fin d) ^ 2 = d ^ 4 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  simpa only [hd] using unitaryHaar_tube_volume_lower_explicit (Fin d × Fin d) hr hr' hS

/-- A triangle inequality for nearby witnesses, with no distance-attainment premise. -/
theorem unitaryWitnessTube_subset_imageTube {d a : ℕ}
    {f : RealEuclidean a → RealEuclidean (2 * d ^ 4)} {X : Set (RealEuclidean a)}
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} {ρ r : ℝ} (hρ : ρ ≤ r)
    (hS : ∀ U ∈ S, ∃ x ∈ X, dist (overlapOutputCoordinates d (U : Matrix _ _ ℂ)) (f x) ≤ ρ) :
    unitaryWitnessTube d r S ⊆ {y | ∃ x ∈ X, dist y (f x) < 2 * r} := by
  rintro y ⟨U, hU, hy⟩
  obtain ⟨x, hx, hdist⟩ := hS U hU
  refine ⟨x, hx, ?_⟩
  have htri := dist_triangle y (overlapOutputCoordinates d (U : Matrix _ _ ℂ)) (f x)
  linarith

end NLQCLean

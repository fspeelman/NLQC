import NLQCLean.Exact.ScalarCriticalValues
import NLQCLean.Models.CompactForward

/-!
# Exact witnesses with an explicit target block

The target is a separate matrix variable, subject to the actual coisometry
and frozen-dilation equations. Normalization of the auxiliary environment
vector makes this target equal to the existing forward overlap. These
constraints therefore describe exactly the original exact-witness locus.
-/

namespace NLQCLean

open Matrix

/-- Seven blocks satisfying physicality, witness normalization, target
coisometry and the exact frozen-dilation equation. -/
def targetExactWitnessSet (d : ℕ) (s : ForwardShape) :
    Set (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s) :=
  {z | (z.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2) ∈ physicalSet d s ∧
    IsUnitVector z.2.2.1 ∧ z.1 * z.1ᴴ = 1 ∧
    globalIsometryRegrouped z.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 =
      insertVector (Fin d × Fin d) z.2.2.1 * z.1}

/-- No new exactness model is introduced by the independent target variable. -/
theorem mem_targetExactWitnessSet_iff (d : ℕ) (s : ForwardShape)
    (z : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × ShapeBlocks d s) :
    z ∈ targetExactWitnessSet d s ↔ IsExactWitness z.2 ∧ forwardOverlapOn z.2 = z.1 := by
  constructor
  · rintro ⟨hphys, hg, hU, hfreeze⟩
    rcases hphys with ⟨hη, hVA, hVB, hDA, hDB⟩
    have hH : forwardOverlapOn z.2 = z.1 := by
      change (insertVector (Fin d × Fin d) z.2.2.1)ᴴ *
        globalIsometryRegrouped z.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2 = _
      rw [hfreeze, ← Matrix.mul_assoc,
        (isIsometry_insertVector _ hg).conjTranspose_mul_self, Matrix.one_mul]
    refine ⟨⟨hη, hg, hVA, hVB, hDA, hDB, ?_, ?_, ?_⟩, hH⟩
    · exact (isIsometry_decoder hDA hDB).submatrix_equiv
        (outputRegroup (Fin d) (Fin d) (Fin (s 6)) (Fin (s 7))) (Equiv.refl _)
    · rw [hH]
      exact hU
    · rw [← globalIsometryRegrouped_eq, hH]
      exact hfreeze
  · rintro ⟨hx, hH⟩
    refine ⟨⟨hx.resource_unit, hx.encA_isometry, hx.encB_isometry,
      hx.decA_isometry, hx.decB_isometry⟩, hx.witness_unit, ?_, ?_⟩
    · rw [← hH]
      exact hx.overlap_coisometry
    · rw [globalIsometryRegrouped_eq, ← hH]
      exact hx.exact

/-- The target-purity image is exactly the original scalar critical image,
for every real normalization, including degenerate dimensions. -/
theorem purity_image_targetExactWitnessSet (d : ℕ) (s : ForwardShape) (c : ℝ) :
    (fun z => purity c z.1) '' targetExactWitnessSet d s =
      scalarPhi c '' {x : ShapeBlocks d s | IsExactWitness x} := by
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hx, hH⟩ := (mem_targetExactWitnessSet_iff d s z).mp hz
    refine ⟨z.2, hx, ?_⟩
    rw [scalarPhi, cubicBlocks_of_isExactWitness hx, hH]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(forwardOverlapOn x, x), ?_, ?_⟩
    · exact (mem_targetExactWitnessSet_iff d s _).mpr ⟨hx, rfl⟩
    · rw [scalarPhi, cubicBlocks_of_isExactWitness hx]

end NLQCLean

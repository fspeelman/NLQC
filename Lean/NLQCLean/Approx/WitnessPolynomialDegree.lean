import NLQCLean.Geometry.MatrixPolynomialDegree
import NLQCLean.Approx.WitnessNormalization

/-!
# Explicit polynomial degrees of the common-coordinate witness maps

The raw overlap has degree at most six, its cubic extension at most
eighteen, and the raw leakage polynomial at most twelve. The bounds are
real `MvPolynomial` certificates for the coordinate maps.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

theorem polynomialDegree_overlapOutputCoordinates {a d D : ℕ}
    {f : RealEuclidean a → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hf : MatrixPolynomialDegreeLE D f) (j : Fin (2 * d ^ 4)) :
    RealPolynomialDegreeLE D (fun x => overlapOutputCoordinates d (f x) j) := by
  let p := (overlapOutputIndex d).symm j
  change RealPolynomialDegreeLE D (fun x => ![(f x p.1.1 p.1.2).re, (f x p.1.1 p.1.2).im] p.2)
  rcases p with ⟨⟨i, k⟩, b⟩
  fin_cases b
  · exact (hf i k).1
  · exact (hf i k).2

namespace ReverseBlocks

variable {a d K D : ℕ} {s : ReverseShape d K}

/-- One degree bound for each coordinate of the six independent complex blocks. -/
def PolynomialDegreeLE (D : ℕ) (f : RealEuclidean a → ReverseBlocks s) : Prop :=
  (∀ i, ComplexPolynomialDegreeLE D (fun x => (f x).1 i)) ∧
  (∀ i, ComplexPolynomialDegreeLE D (fun x => (f x).2.1 i)) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x => (f x).2.2.2.2.2)

namespace PolynomialDegreeLE

variable {f : RealEuclidean a → ReverseBlocks s}

theorem linear (L : RealEuclidean a →ₗ[ℝ] ReverseBlocks s) : PolynomialDegreeLE 1 (fun x => L x) := by
  let Lη := (LinearMap.fst ℝ _ _).comp L
  let L1 := (LinearMap.snd ℝ _ _).comp L
  let Lg := (LinearMap.fst ℝ _ _).comp L1
  let L2 := (LinearMap.snd ℝ _ _).comp L1
  let LA := (LinearMap.fst ℝ _ _).comp L2
  let L3 := (LinearMap.snd ℝ _ _).comp L2
  let LB := (LinearMap.fst ℝ _ _).comp L3
  let L4 := (LinearMap.snd ℝ _ _).comp L3
  let LTA := (LinearMap.fst ℝ _ _).comp L4
  let LTB := (LinearMap.snd ℝ _ _).comp L4
  exact ⟨fun i => ComplexPolynomialDegreeLE.linear ((LinearMap.proj i).comp Lη),
    fun i => ComplexPolynomialDegreeLE.linear ((LinearMap.proj i).comp Lg),
    MatrixPolynomialDegreeLE.linear LA, MatrixPolynomialDegreeLE.linear LB,
    MatrixPolynomialDegreeLE.linear LTA, MatrixPolynomialDegreeLE.linear LTB⟩

theorem rescale (hf : PolynomialDegreeLE D f) : PolynomialDegreeLE D (fun x => rescaleBlocks (f x)) :=
  ⟨hf.1, hf.2.1, hf.2.2.1.real_smul _, hf.2.2.2.1.real_smul _,
    hf.2.2.2.2.1.real_smul _, hf.2.2.2.2.2.real_smul _⟩

theorem cubic (hf : PolynomialDegreeLE D f) :
    PolynomialDegreeLE (3 * D) (fun x => normalizedCubicBlocks (f x)) :=
  ⟨polynomialDegree_cubicSphere hf.1, polynomialDegree_cubicSphere hf.2.1,
    hf.2.2.1.rescaledCubicStiefel _, hf.2.2.2.1.rescaledCubicStiefel _,
    hf.2.2.2.2.1.rescaledCubicStiefel _, hf.2.2.2.2.2.rescaledCubicStiefel _⟩

theorem forward (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (3 * D) (fun x => ReverseBlocks.forward (f x)) := by
  have hJ := polynomialDegree_insertResource (ιA := Fin d) (ιB := Fin d) hf.1
  have h := (MatrixPolynomialDegreeLE.const (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)).mul
    ((MatrixPolynomialDegreeLE.const
      (exchangeMatrix (Fin (d * s.r * s.mA)) (Fin s.mA) (Fin (d * s.r * s.mB)) (Fin s.mB))).mul
        ((hf.2.2.1.kronecker hf.2.2.2.1).mul hJ))
  exact h.mono (by omega)

theorem reverse (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (3 * D) (fun x => ReverseBlocks.reverse (f x)) := by
  have hJ := polynomialDegree_insertResource (ιA := Fin d) (ιB := Fin d) hf.2.1
  exact ((hf.2.2.2.2.1.kronecker hf.2.2.2.2.2).mul hJ).mono (by omega)

theorem overlap (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (6 * D) (fun x => ReverseBlocks.overlap (f x)) :=
  (hf.reverse.conjTranspose.mul hf.forward).mono (by omega)

end PolynomialDegreeLE

variable (s : ReverseShape d K) (hd : 0 < d)

theorem polynomialDegree_rawOverlap :
    MatrixPolynomialDegreeLE 6 (fun x => overlap (rescaleBlocks (decodeCoordinates s hd x))) := by
  have h := (PolynomialDegreeLE.linear (decodeCoordinates s hd)).rescale.overlap
  simpa only [mul_one] using h

theorem polynomialDegree_extendedOverlap :
    MatrixPolynomialDegreeLE 18 (fun x => extendedOverlap (decodeCoordinates s hd x)) := by
  have h := (PolynomialDegreeLE.linear (decodeCoordinates s hd)).cubic.rescale.overlap
  exact h

theorem polynomialDegree_coordinateRawOverlap (j : Fin (2 * d ^ 4)) :
    RealPolynomialDegreeLE 6 (fun x => coordinateRawOverlap s hd x j) :=
  polynomialDegree_overlapOutputCoordinates (polynomialDegree_rawOverlap s hd) j

theorem polynomialDegree_coordinateOverlap (j : Fin (2 * d ^ 4)) :
    RealPolynomialDegreeLE 18 (fun x => coordinateOverlap s hd x j) :=
  polynomialDegree_overlapOutputCoordinates (polynomialDegree_extendedOverlap s hd) j

theorem polynomialDegree_rawLeakage : RealPolynomialDegreeLE 12
    (fun x => (d : ℝ) ^ 2 - ‖overlap (rescaleBlocks (decodeCoordinates s hd x))‖ ^ 2) := by
  have h := (RealPolynomialDegreeLE.const ((d : ℝ) ^ 2)).sub
    (polynomialDegree_rawOverlap s hd).frobNorm_sq
  exact h

/-- The common-coordinate raw overlap, packaged for the fixed polynomial contract. -/
noncomputable def coordinateRawOverlapPolynomial :
    BoundedPolynomialMap (witnessCoordinateBudget d K) (2 * d ^ 4) where
  coordinates j := Classical.choose (polynomialDegree_coordinateRawOverlap s hd j)
  degree_le j := (Classical.choose_spec (polynomialDegree_coordinateRawOverlap s hd j)).1.trans (by decide)

theorem coordinateRawOverlapPolynomial_eval (x : RealEuclidean (witnessCoordinateBudget d K)) :
    (coordinateRawOverlapPolynomial s hd).eval x = coordinateRawOverlap s hd x := by
  ext j
  exact (Classical.choose_spec (polynomialDegree_coordinateRawOverlap s hd j)).2 x

/-- The cubic overlap extension, packaged for the fixed polynomial contract. -/
noncomputable def coordinateOverlapPolynomial :
    BoundedPolynomialMap (witnessCoordinateBudget d K) (2 * d ^ 4) where
  coordinates j := Classical.choose (polynomialDegree_coordinateOverlap s hd j)
  degree_le j := (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd j)).1.trans (by decide)

theorem coordinateOverlapPolynomial_eval (x : RealEuclidean (witnessCoordinateBudget d K)) :
    (coordinateOverlapPolynomial s hd).eval x = coordinateOverlap s hd x := by
  ext j
  exact (Classical.choose_spec (polynomialDegree_coordinateOverlap s hd j)).2 x

end ReverseBlocks
end NLQCLean

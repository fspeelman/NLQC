import NLQCLean.Geometry.PolynomialStrictDeriv
import NLQCLean.Geometry.PolynomialGraphFormat
import NLQCLean.Exact.RationalPolynomialSmoothness

/-!
# Direct image-volume route: polynomial evaluation in Euclidean coordinates

Smoothness of every order and strict derivatives of `x ↦ P(x)` on
`RealEuclidean a`, transported from `Fin a → ℝ` along the identity equivalence.
Part of roadmap step B1 for the direct proof of `PolynomialImageVolumeBound`
(see `docs/assumption-removal-2026-10-01/D0-PROOF.md`).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial
open scoped ContDiff

variable {a n : ℕ}

/-- Evaluation of a polynomial at a Euclidean point. -/
noncomputable def evalE (P : MvPolynomial (Fin a) ℝ) (x : RealEuclidean a) : ℝ :=
  eval (fun i => x i) P

theorem contDiff_eval_top (P : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ∞ (fun q : Fin n → ℝ => eval q P) :=
  contDiff_mvPolynomial_eval_comp (f := fun q => q) (fun i => contDiff_apply ℝ ℝ i) P

theorem contDiff_evalE (P : MvPolynomial (Fin a) ℝ) : ContDiff ℝ ∞ (evalE P) :=
  contDiff_mvPolynomial_eval_comp (f := fun x : RealEuclidean a => fun i => x i)
    (fun _ => contDiff_piLp_apply 2) P

theorem BoundedPolynomialMap.contDiff_eval_top {m : ℕ} (p : BoundedPolynomialMap a m) :
    ContDiff ℝ ∞ p.eval :=
  (contDiff_piLp 2).2 fun j => contDiff_evalE (p.coordinates j)

/-- A coordinatewise real polynomial map of total degree at most `D`. -/
structure PolyMap (a m D : ℕ) where
  coordinates : Fin m → MvPolynomial (Fin a) ℝ
  degree_le : ∀ j, (coordinates j).totalDegree ≤ D

/-- Evaluate the polynomial coordinates in the Euclidean source and target spaces. -/
noncomputable def PolyMap.eval {m D : ℕ} (p : PolyMap a m D) (x : RealEuclidean a) :
    RealEuclidean m :=
  WithLp.toLp 2 (fun j ↦ MvPolynomial.eval (fun i ↦ x i) (p.coordinates j))

theorem PolyMap.contDiff_eval_top {m D : ℕ} (p : PolyMap a m D) : ContDiff ℝ ∞ p.eval :=
  (contDiff_piLp 2).2 fun j => contDiff_evalE (p.coordinates j)

theorem PolyMap.contDiff_eval {m D : ℕ} (p : PolyMap a m D) : ContDiff ℝ 1 p.eval :=
  contDiff_polynomialMap p.coordinates

/-- The bounded maps of the image-volume contract have degree at most `100`. -/
def _root_.NLQCLean.BoundedPolynomialMap.toPolyMap {m : ℕ} (p : BoundedPolynomialMap a m) :
    PolyMap a m 100 :=
  ⟨p.coordinates, p.degree_le⟩

@[simp] theorem _root_.NLQCLean.BoundedPolynomialMap.toPolyMap_eval {m : ℕ}
    (p : BoundedPolynomialMap a m) : p.toPolyMap.eval = p.eval := rfl

/-- The derivative of `evalE P` at `x`. -/
noncomputable def gradE (P : MvPolynomial (Fin a) ℝ) (x : RealEuclidean a) :
    RealEuclidean a →L[ℝ] ℝ :=
  (PolynomialCalculus.gradL P (fun i => x i)).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ) : RealEuclidean a →L[ℝ] (Fin a → ℝ))

theorem gradE_apply (P : MvPolynomial (Fin a) ℝ) (x v : RealEuclidean a) :
    gradE P x v = ∑ k, evalE (pderiv k P) x * v k := by
  simp [gradE, PolynomialCalculus.gradL_apply, evalE, PiLp.coe_continuousLinearEquiv]

theorem hasStrictFDerivAt_evalE (P : MvPolynomial (Fin a) ℝ) (x : RealEuclidean a) :
    HasStrictFDerivAt (evalE P) (gradE P x) x := by
  have h := (PolynomialCalculus.hasStrictFDerivAt_eval P (fun i => x i)).comp x
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin a => ℝ)).hasStrictFDerivAt
  exact h

theorem fderiv_evalE_apply (P : MvPolynomial (Fin a) ℝ) (x v : RealEuclidean a) :
    fderiv ℝ (evalE P) x v = ∑ k, evalE (pderiv k P) x * v k := by
  rw [(hasStrictFDerivAt_evalE P x).hasFDerivAt.fderiv, gradE_apply]

end NLQCLean.DirectVolume

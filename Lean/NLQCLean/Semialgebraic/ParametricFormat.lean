/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.PolynomialSubstitution
import NLQCLean.Semialgebraic.FormatParameters

/-!
# Uniform image formats by retaining coefficient parameters

Each fixed template is encoded by one polynomial family with all
coefficients free. The projection theorem is applied before these parameters are fixed.
Specialization preserves the resulting one format bound. Finitely many
templates are then combined. No elimination complexity enters a volume base.
-/

section

open scoped BigOperators

namespace NLQCLean

theorem Semialgebraic.iUnion {n : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (RealEuclidean n)) (hS : ∀ i, Semialgebraic (S i)) :
    Semialgebraic (⋃ i, S i) := by
  simpa using (Semialgebraic.iInter (fun i => (S i)ᶜ) (fun i => (hS i).compl)).compl

theorem Semialgebraic.setOf_forall {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → RealEuclidean n → Prop) (hP : ∀ i, Semialgebraic {x | P i x}) :
    Semialgebraic {x | ∀ i, P i x} := by
  convert Semialgebraic.iInter (fun i => {x | P i x}) hP using 1
  ext x
  simp

theorem Semialgebraic.setOf_exists {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → RealEuclidean n → Prop) (hP : ∀ i, Semialgebraic {x | P i x}) :
    Semialgebraic {x | ∃ i, P i x} := by
  convert Semialgebraic.iUnion (fun i => {x | P i x}) hP using 1
  ext x
  simp

theorem Semialgebraic.setOf_const {n : ℕ} (P : Prop) :
    Semialgebraic {_x : RealEuclidean n | P} := by
  by_cases h : P
  · simpa [h] using (Semialgebraic.univ (n := n))
  · simpa [h] using (Semialgebraic.empty (n := n))

theorem Semialgebraic.setOf_const_imp {n : ℕ} (P : Prop) {Q : RealEuclidean n → Prop}
    (hQ : Semialgebraic {x | Q x}) : Semialgebraic {x | P → Q x} := by
  by_cases h : P
  · simpa [h] using hQ
  · simpa [h] using (Semialgebraic.univ (n := n))

/-- A fixed finite template whose slots are polynomials. -/
def polynomialTemplateSource {k r b : ℕ} (T : PolynomialFormatTemplate r b)
    (P : Fin r → Fin b → MvPolynomial (Fin k) ℝ) : Set (RealEuclidean k) :=
  {z | ∃ i A, T i = some A ∧ ∀ j s, A j = some s →
    s.Holds (MvPolynomial.eval (fun l => z l) (P i j))}

theorem semialgebraic_polynomialTemplateSource {k r b : ℕ} (T : PolynomialFormatTemplate r b)
    (P : Fin r → Fin b → MvPolynomial (Fin k) ℝ) :
    Semialgebraic (polynomialTemplateSource T P) := by
  unfold polynomialTemplateSource
  apply Semialgebraic.setOf_exists
  intro i
  apply Semialgebraic.setOf_exists
  intro A
  have hall : Semialgebraic {z : RealEuclidean k | ∀ j s, A j = some s →
      s.Holds (MvPolynomial.eval (fun l => z l) (P i j))} := by
    apply Semialgebraic.setOf_forall
    intro j
    apply Semialgebraic.setOf_forall
    intro s
    apply Semialgebraic.setOf_const_imp
    exact ⟨PolynomialSignDNF.atom ⟨P i j, s⟩, by simp [PolynomialSignAtom.Holds]⟩
  exact (Semialgebraic.setOf_const (T i = some A)).inter hall

/-- One coordinate for every coefficient slot of a fixed template. -/
abbrev FormatCoefficientIndex (n D r b : ℕ) := Fin r × Fin b × DegreeMonomial n D

noncomputable abbrev FormatParameterDimension (n D r b : ℕ) := Fintype.card (FormatCoefficientIndex n D r b)

noncomputable def formatCoefficientCoordinates {n D r b : ℕ}
    (a : PolynomialFormatCoefficients n D r b) : RealEuclidean (FormatParameterDimension n D r b) :=
  WithLp.toLp 2 (fun k =>
    let ijd := (Fintype.equivFin (FormatCoefficientIndex n D r b)).symm k
    a ijd.1 ijd.2.1 ijd.2.2)

noncomputable def formatCoefficientsOfCoordinates {n D r b : ℕ}
    (θ : RealEuclidean (FormatParameterDimension n D r b)) : PolynomialFormatCoefficients n D r b :=
  fun i j => WithLp.toLp 2 (fun d => θ (Fintype.equivFin _ (i, j, d)))

@[simp] theorem formatCoefficientsOfCoordinates_coordinates {n D r b : ℕ}
    (a : PolynomialFormatCoefficients n D r b) :
    formatCoefficientsOfCoordinates (formatCoefficientCoordinates a) = a := by
  funext i j
  ext d
  simp [formatCoefficientsOfCoordinates, formatCoefficientCoordinates]

/-- The coefficient variables and source variables occur in a single polynomial. -/
noncomputable def universalSlotPolynomial (n D r b : ℕ) (i : Fin r) (j : Fin b) :
    MvPolynomial (Fin (FormatParameterDimension n D r b + n)) ℝ :=
  ∑ d : DegreeMonomial n D,
    MvPolynomial.X (Fin.castAdd n (Fintype.equivFin (FormatCoefficientIndex n D r b) (i, j, d))) *
      MvPolynomial.rename (Fin.natAdd (FormatParameterDimension n D r b))
        (MvPolynomial.monomial d.val 1)

theorem eval_universalSlotPolynomial {n D r b : ℕ}
    (θ : RealEuclidean (FormatParameterDimension n D r b)) (x : RealEuclidean n)
    (i : Fin r) (j : Fin b) :
    MvPolynomial.eval (fun l => euclideanPair θ x l) (universalSlotPolynomial n D r b i j) =
      (formatCoefficientsOfCoordinates θ i j).evaluate x := by
  classical
  simp only [universalSlotPolynomial, map_sum, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, Function.comp_def, euclideanPair_left, euclideanPair_right,
    MvPolynomial.eval_monomial, one_mul, PolynomialCoefficients.evaluate_eq,
    formatCoefficientsOfCoordinates]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

noncomputable def universalTemplateSource {n D r b : ℕ} (T : PolynomialFormatTemplate r b) :
    Set (RealEuclidean (FormatParameterDimension n D r b + n)) :=
  polynomialTemplateSource T (universalSlotPolynomial n D r b)

theorem semialgebraic_universalTemplateSource {n D r b : ℕ} (T : PolynomialFormatTemplate r b) :
    Semialgebraic (universalTemplateSource (n := n) (D := D) T) :=
  semialgebraic_polynomialTemplateSource T _

@[simp] theorem mem_universalTemplateSource_pair {n D r b : ℕ} (T : PolynomialFormatTemplate r b)
    (θ : RealEuclidean (FormatParameterDimension n D r b)) (x : RealEuclidean n) :
    euclideanPair θ x ∈ universalTemplateSource (D := D) T ↔
      x ∈ T.source (formatCoefficientsOfCoordinates θ) := by
  simp only [universalTemplateSource, polynomialTemplateSource, PolynomialFormatTemplate.source,
    Set.mem_ofPred_eq, eval_universalSlotPolynomial]

theorem euclideanPair_projections {h n : ℕ} (z : RealEuclidean (h + n)) :
    euclideanPair (coordinateProjection (Fin.castAdd n) z)
      (coordinateProjection (Fin.natAdd h) z) = z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Retain every parameter coordinate and apply a polynomial map to the source. -/
noncomputable def parameterRetainingPolynomialMap {h n m : ℕ}
    (q : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (h + m) → MvPolynomial (Fin (h + n)) ℝ :=
  Fin.append (fun i => MvPolynomial.X (Fin.castAdd n i))
    (fun j => MvPolynomial.rename (Fin.natAdd h) (q j))

@[simp] theorem polynomialMap_parameterRetaining_pair {h n m : ℕ}
    (q : Fin m → MvPolynomial (Fin n) ℝ) (θ : RealEuclidean h) (x : RealEuclidean n) :
    PolynomialSignDNF.polynomialMap (parameterRetainingPolynomialMap q) (euclideanPair θ x) =
      euclideanPair θ (PolynomialSignDNF.polynomialMap q x) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [parameterRetainingPolynomialMap, PolynomialSignDNF.polynomialMap,
      MvPolynomial.eval_rename, Function.comp_def]

/-- Specializing the retained parameters gives exactly the image of that
source fiber, rather than a union over different parameter values. -/
theorem parameterRetaining_image_fiber {h n m : ℕ}
    (q : Fin m → MvPolynomial (Fin n) ℝ) (S : Set (RealEuclidean (h + n)))
    (θ : RealEuclidean h) :
    {y | euclideanPair θ y ∈ PolynomialSignDNF.polynomialMap (parameterRetainingPolynomialMap q) '' S} =
      PolynomialSignDNF.polynomialMap q '' {x | euclideanPair θ x ∈ S} := by
  ext y
  constructor
  · rintro ⟨z, hz, hout⟩
    let θz := coordinateProjection (Fin.castAdd n) z
    let xz := coordinateProjection (Fin.natAdd h) z
    have hzpair : euclideanPair θz xz = z := euclideanPair_projections z
    have hout' : euclideanPair θz (PolynomialSignDNF.polynomialMap q xz) = euclideanPair θ y := by
      rw [← polynomialMap_parameterRetaining_pair, hzpair]
      exact hout
    have hθ : θz = θ := by
      simpa using congrArg (coordinateProjection (Fin.castAdd m)) hout'
    have hy : PolynomialSignDNF.polynomialMap q xz = y := by
      simpa using congrArg (coordinateProjection (Fin.natAdd h)) hout'
    refine ⟨xz, ?_, hy⟩
    change euclideanPair θ xz ∈ S
    rw [← hθ, hzpair]
    exact hz
  · rintro ⟨x, hx, rfl⟩
    exact ⟨euclideanPair θ x, hx, polynomialMap_parameterRetaining_pair q θ x⟩

/-- One format bound for the images of all coefficient choices of one template.
The description is selected before any coefficient vector is fixed. -/
theorem exists_uniform_template_image_format (hProjection : SemialgebraicProjectionTheorem)
    {n m D r b : ℕ} (T : PolynomialFormatTemplate r b) (q : Fin m → MvPolynomial (Fin n) ℝ) :
    ∃ c' D' : ℕ, ∀ a : PolynomialFormatCoefficients n D r b,
      HasSemialgebraicFormat (PolynomialSignDNF.polynomialMap q '' T.source a) c' D' := by
  have h := (semialgebraic_universalTemplateSource (n := n) (D := D) T).polynomial_image
    hProjection (parameterRetainingPolynomialMap q)
  obtain ⟨c', D', hf⟩ := h.exists_format
  refine ⟨c', D', ?_⟩
  intro a
  have hs := hf.specialize_parameters (formatCoefficientCoordinates a)
  rw [parameterRetaining_image_fiber] at hs
  have hsource : {x | euclideanPair (formatCoefficientCoordinates a) x ∈
      universalTemplateSource (D := D) T} = T.source a := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_universalTemplateSource_pair,
      formatCoefficientsOfCoordinates_coordinates]
  rwa [hsource] at hs

/-- For fixed input format and polynomial map, one output format works
for every represented source set, with arbitrary real coefficients.
The projection theorem is the only supplied premise. This bound is for convergence, not the exponential
constant in the image-volume inequality. -/
theorem exists_uniform_image_format (hProjection : SemialgebraicProjectionTheorem)
    {n m : ℕ} (c D : ℕ) (q : Fin m → MvPolynomial (Fin n) ℝ) :
    ∃ c' D' : ℕ, ∀ S : Set (RealEuclidean n), HasSemialgebraicFormat S c D →
      HasSemialgebraicFormat (PolynomialSignDNF.polynomialMap q '' S) c' D' := by
  classical
  choose C E hCE using fun T : PolynomialFormatTemplate (c + 1) (c + 1) =>
    exists_uniform_template_image_format (D := D) hProjection T q
  refine ⟨Finset.univ.sup C, Finset.univ.sup E, ?_⟩
  intro S hS
  obtain ⟨T, a, _, rfl⟩ := hS.exists_normalized_parameters
  exact (hCE T a).mono (Finset.le_sup (Finset.mem_univ T)) (Finset.le_sup (Finset.mem_univ T))

end NLQCLean
end

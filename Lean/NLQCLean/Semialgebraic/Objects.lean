/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.DimensionDef
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Connected.Clopen

/-!
# Concrete objects used by the external semialgebraic contracts

These definitions describe sets, graphs and
embedded C1 cubes. They contain no volume, fiber-count or Jacobian estimate.
-/

section

namespace NLQCLean

/-- Existence of a sign description with the two prescribed caps. -/
def HasSemialgebraicFormat {n : ℕ} (S : Set (RealEuclidean n)) (c D : ℕ) : Prop :=
  ∃ F : PolynomialSignDNF n, F.source = S ∧ F.HasFormat c D

theorem HasSemialgebraicFormat.semialgebraic {n c D : ℕ} {S : Set (RealEuclidean n)}
    (h : HasSemialgebraicFormat S c D) : Semialgebraic S := by
  obtain ⟨F, hF, _⟩ := h
  exact ⟨F, hF⟩

theorem HasSemialgebraicFormat.mono {n c D c' D' : ℕ} {S : Set (RealEuclidean n)}
    (h : HasSemialgebraicFormat S c D) (hc : c ≤ c') (hD : D ≤ D') :
    HasSemialgebraicFormat S c' D' := by
  obtain ⟨F, hF, hf⟩ := h
  exact ⟨F, hF, hf.mono hc hD⟩

/-- Concatenation in Euclidean coordinates, used to encode graphs. -/
noncomputable def euclideanPair {n k : ℕ} (x : RealEuclidean n) (y : RealEuclidean k) :
    RealEuclidean (n + k) := WithLp.toLp 2 (Fin.append (fun i => x i) (fun j => y j))

@[simp] theorem euclideanPair_left {n k : ℕ} (x : RealEuclidean n) (y : RealEuclidean k)
    (i : Fin n) : euclideanPair x y (Fin.castAdd k i) = x i := by
  exact Fin.append_left _ _ _

@[simp] theorem euclideanPair_right {n k : ℕ} (x : RealEuclidean n) (y : RealEuclidean k)
    (j : Fin k) : euclideanPair x y (Fin.natAdd n j) = y j := by
  exact Fin.append_right _ _ _

/-- Semialgebraicity of a map on A is semialgebraicity of its graph.
There is no requirement on the map off A and no continuity field. -/
def SemialgebraicMapOn {n k : ℕ} (A : Set (RealEuclidean n))
    (f : RealEuclidean n → RealEuclidean k) : Prop :=
  Semialgebraic ((fun x => euclideanPair x (f x)) '' A)

/-- The open unit cube, also in dimension zero. -/
def openUnitCube (d : ℕ) : Set (RealEuclidean d) :=
  {x | ∀ i, 0 < x i ∧ x i < 1}

/-- A nonempty semialgebraic embedded C1 cube of dimension d. The derivative
is injective on the open parameter cube, and the restricted parametrization
is a topological embedding. No global inverse extension is asserted. -/
def SemialgebraicSmoothCube {n : ℕ} (C : Set (RealEuclidean n)) (d : ℕ) : Prop :=
  d ≤ n ∧ C.Nonempty ∧ Semialgebraic C ∧
  ∃ φ : RealEuclidean d → RealEuclidean n,
    φ '' openUnitCube d = C ∧
    SemialgebraicMapOn (openUnitCube d) φ ∧
    ContDiffOn ℝ 1 φ (openUnitCube d) ∧
    (∀ x ∈ openUnitCube d, Function.Injective (fderiv ℝ φ x)) ∧
    Topology.IsEmbedding (fun x : openUnitCube d => φ x)

/-- A finite disjoint cover by ordinary smooth cubes. Dimensions are chart
dimensions; their agreement with coordinate-interior dimension is proved in
`NLQCLean.Semialgebraic.Dimension`. -/
structure SmoothCubeDecomposition {n : ℕ} (S : Set (RealEuclidean n)) where
  count : ℕ
  piece : Fin count → Set (RealEuclidean n)
  dimension : Fin count → ℕ
  smoothCube : ∀ i, SemialgebraicSmoothCube (piece i) (dimension i)
  disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  covers : (⋃ i, piece i) = S

/-- The polynomial-system relations in Coste Proposition 4.13. Negative
inequalities are obtained by negating the polynomial, and disequalities by
splitting into strict sign cases. -/
inductive PolynomialSystemRelation where
  | zero | positive | nonnegative

def PolynomialSystemRelation.Holds : PolynomialSystemRelation → ℝ → Prop
  | .zero, t => t = 0
  | .positive, t => 0 < t
  | .nonnegative, t => 0 ≤ t

structure PolynomialSystemAtom (n : ℕ) where
  polynomial : MvPolynomial (Fin n) ℝ
  relation : PolynomialSystemRelation

def polynomialSystemSource {n : ℕ} (L : List (PolynomialSystemAtom n)) :
    Set (RealEuclidean n) :=
  {x | ∀ A ∈ L, A.relation.Holds (MvPolynomial.eval (fun i => x i) A.polynomial)}

end NLQCLean
end

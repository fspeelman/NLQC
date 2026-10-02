import NLQCLean.Semialgebraic.Projection
import NLQCLean.Semialgebraic.ProjectionTheorem
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Complex.Basic

/-!
# Polynomial functions on finite-dimensional real spaces

A real function on a finite-dimensional real vector space is polynomial if
it is a real polynomial in the coordinates of one fixed basis; linear
functionals are polynomial and polynomial functions form a subalgebra.
Complex matrix-valued maps are polynomial if the real and imaginary parts of
all entries are. Sums, products, Kronecker products, reindexing and adjoints
preserve this. Scalar images of polynomial zero sets under polynomial
functions are semialgebraic, by the proved projection theorem.
-/

noncomputable section

namespace NLQCLean

open Module MvPolynomial Matrix
open scoped Kronecker

section Scalar

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Coordinates in the standard finite basis. -/
def polyCoords (E : Type*) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] :
    E ≃ₗ[ℝ] (Fin (finrank ℝ E) → ℝ) :=
  (Module.finBasis ℝ E).equivFun

/-- A real polynomial in linear coordinates. -/
def IsRealPoly (f : E → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin (finrank ℝ E)) ℝ, ∀ x, f x = eval (polyCoords E x) p

namespace IsRealPoly

theorem const (c : ℝ) : IsRealPoly (fun _ : E => c) := ⟨C c, fun _ => by simp⟩

theorem add {f g : E → ℝ} (hf : IsRealPoly f) (hg : IsRealPoly g) :
    IsRealPoly (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

theorem mul {f g : E → ℝ} (hf : IsRealPoly f) (hg : IsRealPoly g) :
    IsRealPoly (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

theorem neg {f : E → ℝ} (hf : IsRealPoly f) : IsRealPoly (fun x => -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x => by simp [hp]⟩

theorem sub {f g : E → ℝ} (hf : IsRealPoly f) (hg : IsRealPoly g) :
    IsRealPoly (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, IsRealPoly (f i)) :
    IsRealPoly (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (E := E) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem fintype_sum {ι : Type*} [Fintype ι] {f : ι → E → ℝ} (hf : ∀ i, IsRealPoly (f i)) :
    IsRealPoly (fun x => ∑ i, f i x) :=
  sum Finset.univ fun i _ => hf i

theorem pow {f : E → ℝ} (hf : IsRealPoly f) (n : ℕ) : IsRealPoly (fun x => f x ^ n) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun x => by simp [hp]⟩

theorem congr {f g : E → ℝ} (hf : IsRealPoly f) (h : ∀ x, f x = g x) : IsRealPoly g := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, fun x => by rw [← h, hp]⟩

/-- Linear functionals are polynomial. -/
theorem linear (ℓ : E →ₗ[ℝ] ℝ) : IsRealPoly ℓ := by
  let b := Module.finBasis ℝ E
  refine ⟨∑ i, C (ℓ (b i)) * X i, fun x => ?_⟩
  have hx : ℓ x = ∑ i, b.equivFun x i * ℓ (b i) := by
    conv_lhs => rw [← b.sum_equivFun x]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hx]
  simp [polyCoords, b, mul_comm]

end IsRealPoly

/-- The zero set of a polynomial function. -/
def IsPolyZeroSet (S : Set E) : Prop := ∃ P : E → ℝ, IsRealPoly P ∧ S = {x | P x = 0}

theorem IsPolyZeroSet.inter {S T : Set E} (hS : IsPolyZeroSet S) (hT : IsPolyZeroSet T) :
    IsPolyZeroSet (S ∩ T) := by
  obtain ⟨P, hP, rfl⟩ := hS
  obtain ⟨Q, hQ, rfl⟩ := hT
  refine ⟨fun x => P x ^ 2 + Q x ^ 2, (hP.pow 2).add (hQ.pow 2), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    simp [h1, h2]
  · intro h
    have h1 : P x ^ 2 = 0 := by nlinarith [sq_nonneg (P x), sq_nonneg (Q x)]
    have h2 : Q x ^ 2 = 0 := by nlinarith [sq_nonneg (P x), sq_nonneg (Q x)]
    exact ⟨pow_eq_zero_iff (two_ne_zero) |>.mp h1, pow_eq_zero_iff (two_ne_zero) |>.mp h2⟩

theorem IsPolyZeroSet.of_eq {f g : E → ℝ} (hf : IsRealPoly f) (hg : IsRealPoly g) :
    IsPolyZeroSet {x | f x = g x} :=
  ⟨fun x => f x - g x, hf.sub hg, by ext x; simp [sub_eq_zero]⟩

theorem IsPolyZeroSet.univ : IsPolyZeroSet (Set.univ : Set E) :=
  ⟨fun _ => 0, IsRealPoly.const 0, by simp⟩

theorem IsPolyZeroSet.iInter {ι : Type*} [Finite ι] {S : ι → Set E}
    (hS : ∀ i, IsPolyZeroSet (S i)) : IsPolyZeroSet (⋂ i, S i) := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, IsPolyZeroSet (⋂ i ∈ s, S i) by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using IsPolyZeroSet.univ (E := E)
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact (hS a).inter ih

/-- **Semialgebraic scalar images.** The image of a polynomial zero set under a
polynomial function is semialgebraic (in its one-coordinate Euclidean copy). -/
theorem IsPolyZeroSet.semialgebraic_image {S : Set E} (hS : IsPolyZeroSet S) {g : E → ℝ}
    (hg : IsRealPoly g) : Semialgebraic {y : RealEuclidean 1 | y 0 ∈ g '' S} := by
  obtain ⟨P, ⟨p, hp⟩, rfl⟩ := hS
  obtain ⟨q, hq⟩ := hg
  let n := finrank ℝ E
  let S' : Set (RealEuclidean n) := {z | MvPolynomial.eval (fun i => z i) p = 0}
  have hS' : Semialgebraic S' :=
    ⟨PolynomialSignDNF.atom ⟨p, .zero⟩, by
      ext z
      simp [S', PolynomialSignAtom.Holds, PolynomialSign.Holds]⟩
  have h := hS'.polynomial_image semialgebraicProjectionTheorem (fun _ : Fin 1 => q)
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨WithLp.toLp 2 (polyCoords E x), ?_, ?_⟩
    · change MvPolynomial.eval (polyCoords E x) p = 0
      rw [← hp]
      exact hx
    · ext i
      rw [show i = (0 : Fin 1) from Subsingleton.elim _ _, ← hxy, hq]
      rfl
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(polyCoords E).symm (fun i => z i), ?_, ?_⟩
    · change P _ = 0
      rw [hp, LinearEquiv.apply_symm_apply]
      exact hz
    · rw [hq, LinearEquiv.apply_symm_apply]
      rfl

end Scalar

section MatrixValued

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- A complex-valued function whose real and imaginary parts are polynomial. -/
def IsComplexPoly (f : E → ℂ) : Prop :=
  IsRealPoly (fun x => (f x).re) ∧ IsRealPoly (fun x => (f x).im)

namespace IsComplexPoly

theorem const (c : ℂ) : IsComplexPoly (fun _ : E => c) :=
  ⟨IsRealPoly.const _, IsRealPoly.const _⟩

theorem add {f g : E → ℂ} (hf : IsComplexPoly f) (hg : IsComplexPoly g) :
    IsComplexPoly (fun x => f x + g x) :=
  ⟨(hf.1.add hg.1).congr fun x => by simp, (hf.2.add hg.2).congr fun x => by simp⟩

theorem neg {f : E → ℂ} (hf : IsComplexPoly f) : IsComplexPoly (fun x => -f x) :=
  ⟨hf.1.neg.congr fun x => by simp, hf.2.neg.congr fun x => by simp⟩

theorem sub {f g : E → ℂ} (hf : IsComplexPoly f) (hg : IsComplexPoly g) :
    IsComplexPoly (fun x => f x - g x) :=
  ⟨(hf.1.sub hg.1).congr fun x => by simp, (hf.2.sub hg.2).congr fun x => by simp⟩

theorem mul {f g : E → ℂ} (hf : IsComplexPoly f) (hg : IsComplexPoly g) :
    IsComplexPoly (fun x => f x * g x) :=
  ⟨((hf.1.mul hg.1).sub (hf.2.mul hg.2)).congr fun x => by simp [Complex.mul_re],
    ((hf.1.mul hg.2).add (hf.2.mul hg.1)).congr fun x => by simp [Complex.mul_im]⟩

theorem star {f : E → ℂ} (hf : IsComplexPoly f) : IsComplexPoly (fun x => star (f x)) :=
  ⟨hf.1.congr fun x => by simp, hf.2.neg.congr fun x => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} (hf : ∀ i ∈ s, IsComplexPoly (f i)) :
    IsComplexPoly (fun x => ∑ i ∈ s, f i x) :=
  ⟨(IsRealPoly.sum s fun i hi => (hf i hi).1).congr fun x => by simp [Complex.re_sum],
    (IsRealPoly.sum s fun i hi => (hf i hi).2).congr fun x => by simp [Complex.im_sum]⟩

theorem linear (ℓ : E →ₗ[ℝ] ℂ) : IsComplexPoly ℓ :=
  ⟨IsRealPoly.linear (Complex.reLm.comp ℓ), IsRealPoly.linear (Complex.imLm.comp ℓ)⟩

theorem ite {f g : E → ℂ} (P : Prop) [Decidable P] (hf : IsComplexPoly f)
    (hg : IsComplexPoly g) : IsComplexPoly (fun x => if P then f x else g x) := by
  by_cases h : P
  · simpa [h] using hf
  · simpa [h] using hg

/-- `|f|²` is a real polynomial. -/
theorem normSq {f : E → ℂ} (hf : IsComplexPoly f) :
    IsRealPoly (fun x => Complex.normSq (f x)) :=
  ((hf.1.mul hf.1).add (hf.2.mul hf.2)).congr fun x => by simp [Complex.normSq_apply]

end IsComplexPoly

/-- A matrix-valued function with polynomial entries. -/
def IsPolyMatrix {m n : Type*} (F : E → Matrix m n ℂ) : Prop :=
  ∀ i j, IsComplexPoly (fun x => F x i j)

/-- A vector-valued function with polynomial entries. -/
def IsPolyVec {ι : Type*} (v : E → ι → ℂ) : Prop :=
  ∀ i, IsComplexPoly (fun x => v x i)

namespace IsPolyMatrix

variable {l m n p : Type*}

theorem const (A : Matrix m n ℂ) : IsPolyMatrix (fun _ : E => A) :=
  fun _ _ => IsComplexPoly.const _

theorem linear (L : E →ₗ[ℝ] Matrix m n ℂ) : IsPolyMatrix L := fun i j =>
  IsComplexPoly.linear ((LinearMap.proj j).comp ((LinearMap.proj i).comp L) :
    E →ₗ[ℝ] ℂ)

theorem add {F G : E → Matrix m n ℂ} (hF : IsPolyMatrix F) (hG : IsPolyMatrix G) :
    IsPolyMatrix (fun x => F x + G x) := fun i j => (hF i j).add (hG i j)

theorem sub {F G : E → Matrix m n ℂ} (hF : IsPolyMatrix F) (hG : IsPolyMatrix G) :
    IsPolyMatrix (fun x => F x - G x) := fun i j => (hF i j).sub (hG i j)

theorem mul [Fintype m] {F : E → Matrix l m ℂ} {G : E → Matrix m n ℂ}
    (hF : IsPolyMatrix F) (hG : IsPolyMatrix G) : IsPolyMatrix (fun x => F x * G x) :=
  fun i j => IsComplexPoly.sum Finset.univ fun k _ => (hF i k).mul (hG k j)

theorem kronecker {F : E → Matrix l m ℂ} {G : E → Matrix n p ℂ}
    (hF : IsPolyMatrix F) (hG : IsPolyMatrix G) : IsPolyMatrix (fun x => F x ⊗ₖ G x) :=
  fun i j => (hF i.1 j.1).mul (hG i.2 j.2)

theorem submatrix {l' n' : Type*} {F : E → Matrix m n ℂ} (hF : IsPolyMatrix F)
    (r : l' → m) (c : n' → n) : IsPolyMatrix (fun x => (F x).submatrix r c) :=
  fun i j => hF (r i) (c j)

theorem conjTranspose {F : E → Matrix m n ℂ} (hF : IsPolyMatrix F) :
    IsPolyMatrix (fun x => (F x)ᴴ) := fun i j => (hF j i).star

/-- Entrywise equality of two polynomial matrices is a polynomial zero set. -/
theorem isPolyZeroSet_eq [Fintype m] [Fintype n] {F G : E → Matrix m n ℂ}
    (hF : IsPolyMatrix F) (hG : IsPolyMatrix G) : IsPolyZeroSet {x | F x = G x} := by
  have h := (IsPolyZeroSet.iInter (ι := m × n) fun ij =>
      IsPolyZeroSet.of_eq (hF ij.1 ij.2).1 (hG ij.1 ij.2).1).inter
    (IsPolyZeroSet.iInter (ι := m × n) fun ij =>
      IsPolyZeroSet.of_eq (hF ij.1 ij.2).2 (hG ij.1 ij.2).2)
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    exact ⟨fun ij => by rw [h], fun ij => by rw [h]⟩
  · rintro ⟨hre, him⟩
    ext i j
    exact Complex.ext (hre (i, j)) (him (i, j))

end IsPolyMatrix

/-- The unit-vector condition is a polynomial zero set. -/
theorem isPolyZeroSet_isUnitVector {ι : Type*} [Fintype ι] {v : E → ι → ℂ} (hv : IsPolyVec v) :
    IsPolyZeroSet {x | ∑ i, Complex.normSq (v x i) = 1} :=
  IsPolyZeroSet.of_eq (IsRealPoly.sum Finset.univ fun i _ => (hv i).normSq) (IsRealPoly.const 1)

end MatrixValued

section Continuity

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

theorem IsRealPoly.continuous {f : E → ℝ} (hf : IsRealPoly f) : Continuous f := by
  obtain ⟨p, hp⟩ := hf
  rw [show f = fun x => MvPolynomial.eval (polyCoords E x) p from funext hp]
  exact (MvPolynomial.continuous_eval p).comp
    (LinearMap.continuous_of_finiteDimensional (polyCoords E).toLinearMap)

theorem IsComplexPoly.continuous {f : E → ℂ} (hf : IsComplexPoly f) : Continuous f := by
  have h : f = fun x => ((f x).re : ℂ) + ((f x).im : ℂ) * Complex.I := by
    funext x
    exact (Complex.re_add_im (f x)).symm
  rw [h]
  exact (Complex.continuous_ofReal.comp hf.1.continuous).add
    ((Complex.continuous_ofReal.comp hf.2.continuous).mul continuous_const)

theorem IsPolyMatrix.continuous {m n : Type*} {F : E → Matrix m n ℂ} (hF : IsPolyMatrix F) :
    Continuous F :=
  continuous_pi fun i => continuous_pi fun j => (hF i j).continuous

end Continuity

end NLQCLean

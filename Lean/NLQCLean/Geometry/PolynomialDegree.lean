import NLQCLean.Geometry.PolynomialImageVolumeHypothesis
import NLQCLean.LinearAlgebra.RealCoordinates
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Explicit polynomial-function degree certificates

Every certificate contains a real `MvPolynomial`, its total
degree bound, and equality of evaluation at every real Euclidean point.
Complex functions have separate real and imaginary certificates.
-/

namespace NLQCLean

open MvPolynomial

/-- An explicit real polynomial representing a function on Euclidean coordinates. -/
def RealPolynomialDegreeLE {a : ℕ} (D : ℕ) (f : RealEuclidean a → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin a) ℝ, p.totalDegree ≤ D ∧
    ∀ x, MvPolynomial.eval (fun i => x i) p = f x

namespace RealPolynomialDegreeLE

variable {a D E : ℕ} {f g : RealEuclidean a → ℝ}

theorem congr (hf : RealPolynomialDegreeLE D f) (h : ∀ x, f x = g x) :
    RealPolynomialDegreeLE D g := by
  obtain ⟨p, hp, he⟩ := hf
  exact ⟨p, hp, fun x => (he x).trans (h x)⟩

theorem mono (hf : RealPolynomialDegreeLE D f) (h : D ≤ E) : RealPolynomialDegreeLE E f := by
  obtain ⟨p, hp, he⟩ := hf
  exact ⟨p, hp.trans h, he⟩

theorem const (c : ℝ) : RealPolynomialDegreeLE 0 (fun _ : RealEuclidean a => c) :=
  ⟨C c, by simp, by intro x; simp⟩

theorem coord (i : Fin a) : RealPolynomialDegreeLE 1 (fun x : RealEuclidean a => x i) :=
  ⟨X i, by simp, by intro x; simp⟩

theorem add (hf : RealPolynomialDegreeLE D f) (hg : RealPolynomialDegreeLE E g) :
    RealPolynomialDegreeLE (max D E) (fun x => f x + g x) := by
  obtain ⟨p, hp, he⟩ := hf
  obtain ⟨q, hq, hqv⟩ := hg
  exact ⟨p + q, (totalDegree_add p q).trans (max_le_max hp hq), by intro x; simp [he, hqv]⟩

theorem neg (hf : RealPolynomialDegreeLE D f) : RealPolynomialDegreeLE D (fun x => -f x) := by
  obtain ⟨p, hp, he⟩ := hf
  exact ⟨-p, by simpa using hp, by intro x; simp [he]⟩

theorem sub (hf : RealPolynomialDegreeLE D f) (hg : RealPolynomialDegreeLE E g) :
    RealPolynomialDegreeLE (max D E) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : RealPolynomialDegreeLE D f) (hg : RealPolynomialDegreeLE E g) :
    RealPolynomialDegreeLE (D + E) (fun x => f x * g x) := by
  obtain ⟨p, hp, he⟩ := hf
  obtain ⟨q, hq, hqv⟩ := hg
  exact ⟨p * q, (totalDegree_mul p q).trans (add_le_add hp hq), by intro x; simp [he, hqv]⟩

theorem const_mul (hf : RealPolynomialDegreeLE D f) (c : ℝ) :
    RealPolynomialDegreeLE D (fun x => c * f x) := by
  simpa only [zero_add] using (const c).mul hf

theorem sq (hf : RealPolynomialDegreeLE D f) : RealPolynomialDegreeLE (2 * D) (fun x => f x ^ 2) := by
  simpa only [two_mul, pow_two] using hf.mul hf

theorem sum {ι : Type*} (t : Finset ι) {f : ι → RealEuclidean a → ℝ}
    (hf : ∀ i ∈ t, RealPolynomialDegreeLE D (f i)) :
    RealPolynomialDegreeLE D (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (const 0).mono (Nat.zero_le D)
  | @insert i t hi ih =>
    have h1 := hf i (Finset.mem_insert_self _ _)
    have ht := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi, max_self] using h1.add ht

/-- Every real linear functional is represented by its coordinate linear polynomial. -/
theorem linear (L : RealEuclidean a →ₗ[ℝ] ℝ) : RealPolynomialDegreeLE 1 (fun x => L x) := by
  let b := EuclideanSpace.basisFun (Fin a) ℝ
  have h := sum Finset.univ (fun i _ => (coord i).const_mul (L (b i)))
  apply h.congr
  intro x
  have he := congrArg L (b.sum_repr x)
  simpa only [b, map_sum, map_smul, EuclideanSpace.basisFun_repr, smul_eq_mul, mul_comm] using he

end RealPolynomialDegreeLE

/-- Real polynomial degree of a complex-valued function. -/
def ComplexPolynomialDegreeLE {a : ℕ} (D : ℕ) (f : RealEuclidean a → ℂ) : Prop :=
  RealPolynomialDegreeLE D (fun x => (f x).re) ∧ RealPolynomialDegreeLE D (fun x => (f x).im)

namespace ComplexPolynomialDegreeLE

variable {a D E : ℕ} {f g : RealEuclidean a → ℂ}

theorem congr (hf : ComplexPolynomialDegreeLE D f) (h : ∀ x, f x = g x) :
    ComplexPolynomialDegreeLE D g :=
  ⟨hf.1.congr (fun x => congrArg Complex.re (h x)), hf.2.congr (fun x => congrArg Complex.im (h x))⟩

theorem mono (hf : ComplexPolynomialDegreeLE D f) (h : D ≤ E) : ComplexPolynomialDegreeLE E f :=
  ⟨hf.1.mono h, hf.2.mono h⟩

theorem const (c : ℂ) : ComplexPolynomialDegreeLE 0 (fun _ : RealEuclidean a => c) :=
  ⟨RealPolynomialDegreeLE.const c.re, RealPolynomialDegreeLE.const c.im⟩

theorem add (hf : ComplexPolynomialDegreeLE D f) (hg : ComplexPolynomialDegreeLE E g) :
    ComplexPolynomialDegreeLE (max D E) (fun x => f x + g x) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem neg (hf : ComplexPolynomialDegreeLE D f) : ComplexPolynomialDegreeLE D (fun x => -f x) :=
  ⟨hf.1.neg, hf.2.neg⟩

theorem sub (hf : ComplexPolynomialDegreeLE D f) (hg : ComplexPolynomialDegreeLE E g) :
    ComplexPolynomialDegreeLE (max D E) (fun x => f x - g x) := ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem mul (hf : ComplexPolynomialDegreeLE D f) (hg : ComplexPolynomialDegreeLE E g) :
    ComplexPolynomialDegreeLE (D + E) (fun x => f x * g x) := by
  constructor
  · simpa only [Complex.mul_re, max_self] using (hf.1.mul hg.1).sub (hf.2.mul hg.2)
  · simpa only [Complex.mul_im, max_self] using (hf.1.mul hg.2).add (hf.2.mul hg.1)

theorem const_mul (hf : ComplexPolynomialDegreeLE D f) (c : ℂ) :
    ComplexPolynomialDegreeLE D (fun x => c * f x) := by
  simpa only [zero_add] using (const c).mul hf

theorem star (hf : ComplexPolynomialDegreeLE D f) : ComplexPolynomialDegreeLE D (fun x => star (f x)) :=
  ⟨hf.1, hf.2.neg⟩

theorem ofReal {f : RealEuclidean a → ℝ} (hf : RealPolynomialDegreeLE D f) :
    ComplexPolynomialDegreeLE D (fun x => (f x : ℂ)) :=
  ⟨hf, (RealPolynomialDegreeLE.const 0).mono (Nat.zero_le D)⟩

theorem real_smul (hf : ComplexPolynomialDegreeLE D f) (c : ℝ) :
    ComplexPolynomialDegreeLE D (fun x => c • f x) := by
  simpa only [Complex.real_smul] using hf.const_mul (c : ℂ)

theorem normSq (hf : ComplexPolynomialDegreeLE D f) :
    RealPolynomialDegreeLE (2 * D) (fun x => Complex.normSq (f x)) := by
  simpa only [Complex.normSq_apply, ← pow_two, max_self] using hf.1.sq.add hf.2.sq

theorem sum {ι : Type*} (t : Finset ι) {f : ι → RealEuclidean a → ℂ}
    (hf : ∀ i ∈ t, ComplexPolynomialDegreeLE D (f i)) :
    ComplexPolynomialDegreeLE D (fun x => ∑ i ∈ t, f i x) := by
  constructor
  · simpa only [Complex.re_sum] using RealPolynomialDegreeLE.sum t (fun i hi => (hf i hi).1)
  · simpa only [Complex.im_sum] using RealPolynomialDegreeLE.sum t (fun i hi => (hf i hi).2)

theorem linear (L : RealEuclidean a →ₗ[ℝ] ℂ) : ComplexPolynomialDegreeLE 1 (fun x => L x) :=
  ⟨RealPolynomialDegreeLE.linear (Complex.reCLM.toLinearMap.comp L),
    RealPolynomialDegreeLE.linear (Complex.imCLM.toLinearMap.comp L)⟩

end ComplexPolynomialDegreeLE

end NLQCLean

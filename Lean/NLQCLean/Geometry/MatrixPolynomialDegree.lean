import NLQCLean.Geometry.PolynomialDegree
import NLQCLean.Geometry.RescaledCubicProjection
import NLQCLean.Rigidity.Compression

/-!
# Polynomial degree certificates for the witness's matrix operations

Matrix multiplication, tensor products, adjoints, Frobenius squared
norms, resource insertion, and the two cubic maps preserve explicit real
polynomial representations with the stated degree bounds.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

def MatrixPolynomialDegreeLE {a : ℕ} {m n : Type*} (D : ℕ)
    (f : RealEuclidean a → Matrix m n ℂ) : Prop :=
  ∀ i j, ComplexPolynomialDegreeLE D (fun x => f x i j)

namespace MatrixPolynomialDegreeLE

variable {a D E : ℕ} {m n k l : Type*}
variable {f g : RealEuclidean a → Matrix m n ℂ}

theorem congr (hf : MatrixPolynomialDegreeLE D f) (h : ∀ x, f x = g x) :
    MatrixPolynomialDegreeLE D g := fun i j =>
  (hf i j).congr (fun x => congrArg (fun M => M i j) (h x))

theorem mono (hf : MatrixPolynomialDegreeLE D f) (h : D ≤ E) : MatrixPolynomialDegreeLE E f :=
  fun i j => (hf i j).mono h

theorem const (M : Matrix m n ℂ) : MatrixPolynomialDegreeLE 0 (fun _ : RealEuclidean a => M) :=
  fun i j => ComplexPolynomialDegreeLE.const (M i j)

theorem add (hf : MatrixPolynomialDegreeLE D f) (hg : MatrixPolynomialDegreeLE E g) :
    MatrixPolynomialDegreeLE (max D E) (fun x => f x + g x) := fun i j => (hf i j).add (hg i j)

theorem sub (hf : MatrixPolynomialDegreeLE D f) (hg : MatrixPolynomialDegreeLE E g) :
    MatrixPolynomialDegreeLE (max D E) (fun x => f x - g x) := fun i j => (hf i j).sub (hg i j)

theorem real_smul (hf : MatrixPolynomialDegreeLE D f) (c : ℝ) :
    MatrixPolynomialDegreeLE D (fun x => c • f x) := fun i j => (hf i j).real_smul c

theorem conjTranspose (hf : MatrixPolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE D (fun x => (f x)ᴴ) := fun i j => (hf j i).star

theorem mul [Fintype n] {f : RealEuclidean a → Matrix m n ℂ} {g : RealEuclidean a → Matrix n k ℂ}
    (hf : MatrixPolynomialDegreeLE D f) (hg : MatrixPolynomialDegreeLE E g) :
    MatrixPolynomialDegreeLE (D + E) (fun x => f x * g x) := by
  intro i j
  exact ComplexPolynomialDegreeLE.sum Finset.univ (fun q _ => (hf i q).mul (hg q j))

theorem kronecker {g : RealEuclidean a → Matrix k l ℂ}
    (hf : MatrixPolynomialDegreeLE D f) (hg : MatrixPolynomialDegreeLE E g) :
    MatrixPolynomialDegreeLE (D + E) (fun x => f x ⊗ₖ g x) :=
  fun i j => (hf i.1 j.1).mul (hg i.2 j.2)

theorem linear (L : RealEuclidean a →ₗ[ℝ] Matrix m n ℂ) :
    MatrixPolynomialDegreeLE 1 (fun x => L x) := by
  intro i j
  let e : Matrix m n ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact ComplexPolynomialDegreeLE.linear (e.comp L)

theorem frobNorm_sq [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (hf : MatrixPolynomialDegreeLE D f) :
    RealPolynomialDegreeLE (2 * D) (fun x => ‖f x‖ ^ 2) := by
  have h := RealPolynomialDegreeLE.sum Finset.univ (fun i _ =>
    RealPolynomialDegreeLE.sum Finset.univ (fun j _ => (hf i j).normSq))
  simpa only [NLQCLean.frobNorm_sq, Complex.normSq_eq_norm_sq] using h

/-- The normalized Stiefel cubic multiplies coordinate degree by at most three. -/
theorem rescaledCubicStiefel [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (hf : MatrixPolynomialDegreeLE D f) (c : ℝ) :
    MatrixPolynomialDegreeLE (3 * D) (fun x => NLQCLean.rescaledCubicStiefel c (f x)) := by
  have h := (hf.real_smul (3 / 2)).sub (((hf.mul hf.conjTranspose).mul hf).real_smul (c / 2))
  exact h.mono (by omega)

end MatrixPolynomialDegreeLE

theorem polynomialDegree_sqNorm {a D : ℕ} {ι : Type*} [Fintype ι]
    {f : RealEuclidean a → ι → ℂ} (hf : ∀ i, ComplexPolynomialDegreeLE D (fun x => f x i)) :
    RealPolynomialDegreeLE (2 * D) (fun x => sqNorm (f x)) :=
  RealPolynomialDegreeLE.sum Finset.univ (fun i _ => (hf i).normSq)

theorem polynomialDegree_insertResource {a D : ℕ} {ιA ιB ρA ρB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] {f : RealEuclidean a → ρA × ρB → ℂ}
    (hf : ∀ i, ComplexPolynomialDegreeLE D (fun x => f x i)) :
    MatrixPolynomialDegreeLE D (fun x => insertResource ιA ιB (f x)) := by
  intro p q
  exact (hf (p.1.2, p.2.2)).const_mul
    ((if p.1.1 = q.1 then 1 else 0) * (if p.2.1 = q.2 then 1 else 0))

theorem polynomialDegree_cubicSphere {a D : ℕ} {ι : Type*} [Fintype ι]
    {f : RealEuclidean a → ι → ℂ} (hf : ∀ i, ComplexPolynomialDegreeLE D (fun x => f x i)) :
    ∀ i, ComplexPolynomialDegreeLE (3 * D) (fun x => cubicSphere (f x) i) := by
  intro i
  have hn := polynomialDegree_sqNorm hf
  have hs : RealPolynomialDegreeLE (2 * D) (fun x => (3 - sqNorm (f x)) / 2) := by
    have h := ((RealPolynomialDegreeLE.const 3).sub hn).const_mul (1 / 2)
    simpa only [Nat.zero_max, div_eq_mul_inv, one_div, one_mul, mul_comm] using h
  have h := (ComplexPolynomialDegreeLE.ofReal hs).mul (hf i)
  apply (h.mono (by omega)).congr
  intro x
  simp only [cubicSphere, Complex.real_smul]

end NLQCLean

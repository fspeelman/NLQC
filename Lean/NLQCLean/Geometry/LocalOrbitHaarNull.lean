import NLQCLean.Invariants.LocalOrbitSeparation
import NLQCLean.Geometry.HaarPolynomialZero
import NLQCLean.Invariants.PVMRotationFamily

/-!
# Local orbits are Haar-null

A finite separating family of polynomial invariants writes each orbit as the
zero set of one real polynomial, a sum of squares. That polynomial is nonzero
at every unitary outside the orbit, so its zero set is Haar-null as soon as
some unitary lies outside the orbit. Two explicit unitaries in different
orbits supply such a witness:

* for double local-unitary orbits, the identity and a single corner phase
  `-1`, for any two local dimensions at least two;
* for measurement orbits, the identity and a basis with one entangled
  column, for balanced local dimension at least two.
-/

noncomputable section

namespace NLQCLean

open Matrix MeasureTheory MvPolynomial
open scoped Kronecker

section Coordinates

theorem matrixFrobeniusCoordinates_eq_matrixRealCoords {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) :
    (fun k => matrixFrobeniusCoordinates m n M k) = matrixRealCoords m n M := by
  funext ⟨⟨i, j⟩, b⟩
  fin_cases b <;> rfl

end Coordinates

section SumOfSquares

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sum of squared invariant differences from the values at `U`. -/
def orbitDefect (S : Finset (MvPolynomial ((n × n) × Fin 2) ℝ)) (U : Matrix n n ℂ) :
    MvPolynomial ((n × n) × Fin 2) ℝ :=
  ∑ p ∈ S, (p - C (matrixPolyEval p U)) ^ 2

omit [Fintype n] [DecidableEq n] in
theorem matrixPolyEval_orbitDefect (S : Finset (MvPolynomial ((n × n) × Fin 2) ℝ))
    (U V : Matrix n n ℂ) :
    matrixPolyEval (orbitDefect S U) V = ∑ p ∈ S, (matrixPolyEval p V - matrixPolyEval p U) ^ 2 := by
  simp [orbitDefect, matrixPolyEval]

/-- **Haar nullity of a polynomially separated orbit.** If finitely many
polynomial invariants separate the orbits of a relation and some unitary lies
outside the orbit of `U`, then that orbit is Haar-null. -/
theorem unitaryHaar_orbit_eq_zero_of_separating
    (O : Matrix n n ℂ → Set (Matrix n n ℂ))
    (S : Finset (MvPolynomial ((n × n) × Fin 2) ℝ))
    (hinv : ∀ p ∈ S, ∀ U V, V ∈ O U → matrixPolyEval p V = matrixPolyEval p U)
    (hsep : ∀ U V, (∀ p ∈ S, matrixPolyEval p U = matrixPolyEval p V) → V ∈ O U)
    (U : Matrix n n ℂ) (W : Matrix.unitaryGroup n ℂ) (hW : (W : Matrix n n ℂ) ∉ O U) :
    unitaryHaar n {V : Matrix.unitaryGroup n ℂ | (V : Matrix n n ℂ) ∈ O U} = 0 := by
  have hWq : MvPolynomial.eval (fun k => matrixFrobeniusCoordinates n n (W : Matrix n n ℂ) k)
      (orbitDefect S U) ≠ 0 := by
    rw [matrixFrobeniusCoordinates_eq_matrixRealCoords]
    change matrixPolyEval (orbitDefect S U) (W : Matrix n n ℂ) ≠ 0
    rw [matrixPolyEval_orbitDefect]
    intro h0
    apply hW
    apply hsep
    intro p hp
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg _)).mp h0 p hp
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
    linarith
  refine measure_mono_null ?_ (unitaryHaar_polynomial_zeroSet_eq_zero _ W hWq)
  intro V hV
  simp only [Set.mem_ofPred_eq] at hV ⊢
  rw [matrixFrobeniusCoordinates_eq_matrixRealCoords]
  change matrixPolyEval (orbitDefect S U) (V : Matrix n n ℂ) = 0
  rw [matrixPolyEval_orbitDefect]
  exact Finset.sum_eq_zero fun p hp => by rw [hinv p hp U _ hV, sub_self]; ring

end SumOfSquares

section DoubleOrbit

variable {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- One corner phase `-1` at the basis vector `(a, b)`. -/
def cornerSign (a : ιA) (b : ιB) : Matrix (ιA × ιB) (ιA × ιB) ℂ :=
  Matrix.diagonal fun i => if i = (a, b) then -1 else 1

theorem cornerSign_mem_unitaryGroup (a : ιA) (b : ιB) :
    cornerSign a b ∈ Matrix.unitaryGroup (ιA × ιB) ℂ :=
  phaseUnitaries_subset_unitary ⟨_, fun i => by split_ifs <;> simp, rfl⟩

omit [Fintype ιA] [Fintype ιB] in
/-- A corner sign is not a tensor product of two matrices. -/
theorem cornerSign_ne_kronecker {a a' : ιA} {b b' : ιB} (ha : a ≠ a') (hb : b ≠ b')
    (X : Matrix ιA ιA ℂ) (Y : Matrix ιB ιB ℂ) : cornerSign a b ≠ X ⊗ₖ Y := by
  intro h
  have e : ∀ x y, cornerSign a b (x, y) (x, y) = X x x * Y y y := fun x y => by
    rw [h, Matrix.kroneckerMap_apply]
  have h1 := e a b
  have h2 := e a b'
  have h3 := e a' b
  have h4 := e a' b'
  simp only [cornerSign, Matrix.diagonal_apply_eq, Prod.mk.injEq, ha.symm, hb.symm, and_true,
    and_false, ite_true, ite_false] at h1 h2 h3 h4
  have : (-1 : ℂ) * 1 = 1 * 1 := by
    calc (-1 : ℂ) * 1 = (X a a * Y b b) * (X a' a' * Y b' b') := by rw [← h1, ← h4]
      _ = (X a a * Y b' b') * (X a' a' * Y b b) := by ring
      _ = 1 * 1 := by rw [← h2, ← h3]
  norm_num at this

/-- If two matrices lie in one double orbit, one is a product-type
transform of the other. -/
theorem exists_kronecker_of_mem_unitaryDoubleOrbit_one {U V : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (h1 : (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ) ∈ unitaryDoubleOrbit ιA ιB U)
    (hV : V ∈ unitaryDoubleOrbit ιA ιB U) :
    ∃ X : Matrix ιA ιA ℂ, ∃ Y : Matrix ιB ιB ℂ, V = X ⊗ₖ Y := by
  rcases h1 with ⟨_, ⟨LA, hLA, LB, hLB, rfl⟩, _, ⟨SA, hSA, SB, hSB, rfl⟩, h1⟩
  rcases hV with ⟨_, ⟨MA, hMA, MB, hMB, rfl⟩, _, ⟨TA, hTA, TB, hTB, rfl⟩, rfl⟩
  have hL := Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary hLA hLB)
  have hS := Matrix.mem_unitaryGroup_iff.mp (Matrix.kronecker_mem_unitary hSA hSB)
  have hU : U = (LA ⊗ₖ LB)ᴴ * (SA ⊗ₖ SB)ᴴ := by
    have : (LA ⊗ₖ LB)ᴴ * ((LA ⊗ₖ LB) * U * (SA ⊗ₖ SB)) * (SA ⊗ₖ SB)ᴴ = U := by
      rw [show (LA ⊗ₖ LB)ᴴ * ((LA ⊗ₖ LB) * U * (SA ⊗ₖ SB)) * (SA ⊗ₖ SB)ᴴ =
          ((LA ⊗ₖ LB)ᴴ * (LA ⊗ₖ LB)) * U * ((SA ⊗ₖ SB) * (SA ⊗ₖ SB)ᴴ) by
        simp only [Matrix.mul_assoc]]
      rw [show (LA ⊗ₖ LB)ᴴ * (LA ⊗ₖ LB) = 1 from hL,
        show (SA ⊗ₖ SB) * (SA ⊗ₖ SB)ᴴ = 1 from hS, Matrix.one_mul, Matrix.mul_one]
    rw [← this, ← h1, Matrix.mul_one]
  refine ⟨MA * LAᴴ * SAᴴ * TA, MB * LBᴴ * SBᴴ * TB, ?_⟩
  rw [hU, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker]
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_assoc]

/-- **Each double local-unitary orbit is Haar-null** (`lem:orbitHaarNull`,
and its unequal-dimension version), for local dimensions at least two. -/
theorem unitaryHaar_unitaryDoubleOrbit_eq_zero [Nontrivial ιA] [Nontrivial ιB]
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    unitaryHaar (ιA × ιB)
      {V : Matrix.unitaryGroup (ιA × ιB) ℂ | (V : Matrix (ιA × ιB) (ιA × ιB) ℂ) ∈
        unitaryDoubleOrbit ιA ιB U} = 0 := by
  obtain ⟨S, hinv, hsep⟩ := exists_finite_unitaryDoubleOrbit_separating (ιA := ιA) (ιB := ιB)
  obtain ⟨a, a', ha⟩ := exists_pair_ne ιA
  obtain ⟨b, b', hb⟩ := exists_pair_ne ιB
  by_cases h1 : (1 : Matrix (ιA × ιB) (ιA × ιB) ℂ) ∈ unitaryDoubleOrbit ιA ιB U
  · refine unitaryHaar_orbit_eq_zero_of_separating _ S hinv hsep U
      ⟨cornerSign a b, cornerSign_mem_unitaryGroup a b⟩ ?_
    intro hZ
    obtain ⟨X, Y, hXY⟩ := exists_kronecker_of_mem_unitaryDoubleOrbit_one h1 hZ
    exact cornerSign_ne_kronecker ha hb X Y hXY
  · exact unitaryHaar_orbit_eq_zero_of_separating _ S hinv hsep U 1 h1

end DoubleOrbit

section Measurement

variable {d : ℕ}

/-- If the identity and `N` lie in one measurement orbit, every column of `N`
is a phase times a product vector. -/
theorem exists_product_columns_of_mem_pvmBasisOrbit_one
    {M N : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (h1 : (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ pvmBasisOrbit (Fin d) (Fin d) M)
    (hN : N ∈ pvmBasisOrbit (Fin d) (Fin d) M) :
    ∃ A B : Matrix (Fin d) (Fin d) ℂ, ∃ δ : Fin d × Fin d → ℂ,
      ∀ a b c, N (a, b) c = A a c.1 * B b c.2 * δ c := by
  rcases h1 with ⟨_, ⟨LA, hLA, LB, hLB, rfl⟩, _, ⟨φ, hφ, rfl⟩, h1⟩
  rcases hN with ⟨_, ⟨MA, hMA, MB, hMB, rfl⟩, _, ⟨ψ, hψ, rfl⟩, rfl⟩
  have hL := Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary hLA hLB)
  have hΔ := Matrix.mem_unitaryGroup_iff.mp
    (phaseUnitaries_subset_unitary (n := Fin d × Fin d) ⟨φ, hφ, rfl⟩)
  have hM : M = (LA ⊗ₖ LB)ᴴ * (Matrix.diagonal φ)ᴴ := by
    have : (LA ⊗ₖ LB)ᴴ * ((LA ⊗ₖ LB) * M * Matrix.diagonal φ) * (Matrix.diagonal φ)ᴴ = M := by
      rw [show (LA ⊗ₖ LB)ᴴ * ((LA ⊗ₖ LB) * M * Matrix.diagonal φ) * (Matrix.diagonal φ)ᴴ =
          ((LA ⊗ₖ LB)ᴴ * (LA ⊗ₖ LB)) * M * (Matrix.diagonal φ * (Matrix.diagonal φ)ᴴ) by
        simp only [Matrix.mul_assoc]]
      rw [show (LA ⊗ₖ LB)ᴴ * (LA ⊗ₖ LB) = 1 from hL,
        show Matrix.diagonal φ * (Matrix.diagonal φ)ᴴ = 1 from hΔ, Matrix.one_mul, Matrix.mul_one]
    rw [← this, ← h1, Matrix.mul_one]
  refine ⟨MA * LAᴴ, MB * LBᴴ, fun c => star (φ c) * ψ c, fun a b c => ?_⟩
  rw [hM, Matrix.conjTranspose_kronecker, Matrix.diagonal_conjTranspose,
    show (MA ⊗ₖ MB) * ((LAᴴ ⊗ₖ LBᴴ) * Matrix.diagonal (star φ)) * Matrix.diagonal ψ =
      ((MA * LAᴴ) ⊗ₖ (MB * LBᴴ)) * Matrix.diagonal (fun c => star (φ c) * ψ c) by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, ← Matrix.mul_assoc,
        Matrix.mul_kronecker_mul]
      rfl]
  rw [Matrix.mul_diagonal, Matrix.kroneckerMap_apply]

/-- The rotated basis at `s = 1/2` has an entangled column. -/
theorem pvmRotationBasis_half_not_product (hd : 2 ≤ d)
    (A B : Matrix (Fin d) (Fin d) ℂ) (δ : Fin d × Fin d → ℂ)
    (h : ∀ a b c, pvmRotationBasis hd (1 / 2) (a, b) c = A a c.1 * B b c.2 * δ c) : False := by
  set c := rotO hd
  set x := rotLabel0 hd
  set y := rotLabel1 hd
  have hxy : x ≠ y := rotLabel0_ne_rotLabel1 hd
  have entry : ∀ a b, pvmRotationBasis hd (1 / 2) (a, b) c =
      (if (a, b) = rotO hd then ((Real.sqrt (1 - 1 / 2) : ℝ) : ℂ) else 0) +
        (if (a, b) = rotE hd then ((Real.sqrt (1 / 2) : ℝ) : ℂ) else 0) := by
    intro a b
    simp only [pvmRotationBasis, Matrix.of_apply, c, pvmRotationColumn_O, rotVector]
  have h00 := (entry x x).symm.trans (h x x c)
  have h11 := (entry y y).symm.trans (h y y c)
  have h01 := (entry x y).symm.trans (h x y c)
  have h10 := (entry y x).symm.trans (h y x c)
  simp only [rotO, rotE, x, y, Prod.mk.injEq, hxy, hxy.symm, and_self, and_false, false_and,
    ite_true, ite_false, add_zero, zero_add] at h00 h11 h01 h10
  have hs : ((Real.sqrt (1 - 1 / 2) : ℝ) : ℂ) * ((Real.sqrt (1 / 2) : ℝ) : ℂ) = 0 := by
    calc ((Real.sqrt (1 - 1 / 2) : ℝ) : ℂ) * ((Real.sqrt (1 / 2) : ℝ) : ℂ)
        = (A x c.1 * B x c.2 * δ c) * (A y c.1 * B y c.2 * δ c) := by rw [h00, h11]
      _ = (A x c.1 * B y c.2 * δ c) * (A y c.1 * B x c.2 * δ c) := by ring
      _ = 0 := by rw [← h01, ← h10, zero_mul]
  have hpos : (0 : ℝ) < Real.sqrt (1 - 1 / 2) * Real.sqrt (1 / 2) :=
    mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  have := congrArg Complex.re hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.zero_re] at this
  linarith

/-- **Each measurement orbit is Haar-null** (`lem:orbitHaarNull-pvm`), for
balanced local dimension `d ≥ 2`. -/
theorem unitaryHaar_pvmBasisOrbit_eq_zero (hd : 2 ≤ d)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    unitaryHaar (Fin d × Fin d)
      {V : Matrix.unitaryGroup (Fin d × Fin d) ℂ | (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈
        pvmBasisOrbit (Fin d) (Fin d) M} = 0 := by
  obtain ⟨S, hinv, hsep⟩ := exists_finite_pvmBasisOrbit_separating (ιA := Fin d) (ιB := Fin d)
  by_cases h1 : (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∈ pvmBasisOrbit (Fin d) (Fin d) M
  · refine unitaryHaar_orbit_eq_zero_of_separating _ S hinv hsep M
      ⟨pvmRotationBasis hd (1 / 2), pvmRotationBasis_mem_unitaryGroup hd (by norm_num)
        (by norm_num)⟩ ?_
    intro hW
    obtain ⟨A, B, δ, hprod⟩ := exists_product_columns_of_mem_pvmBasisOrbit_one h1 hW
    exact pvmRotationBasis_half_not_product hd A B δ hprod
  · exact unitaryHaar_orbit_eq_zero_of_separating _ S hinv hsep M 1 h1

end Measurement

end NLQCLean

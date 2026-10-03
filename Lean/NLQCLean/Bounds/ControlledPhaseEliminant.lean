import NLQCLean.Arithmetic.DeformationBounds
import NLQCLean.Arithmetic.ControlledPhaseLeastDeficit
import NLQCLean.External.EffectiveArithmetic
import NLQCLean.Arithmetic.TranscriptPolynomial

/-!
# Controlled-phase eliminants without external input

Physical and transcript feasible points have all real coordinates in `[−1, 1]`: every
coordinate is a real or imaginary part of an entry of a unit vector, an isometry, or a
family `V_x` with `Σ_x V_xᴴ V_x = 1`. With this, the deformation eliminant applies to the
controlled-phase certificate. It gives the eliminant of `(g_K(θ), cos θ)` with degree at most
`12^{4(|B|+1)}` and bit size `(56 + 14K) · 12^{4(|B|+1)}` (`B = BoundIndex t`), the size that
the separation argument needs.
-/

namespace NLQCLean

namespace ExplicitGate

/-- The bound variables of the epigraph of `g_K(θ)`: the sine coordinate and the raw physical
coordinates. -/
abbrev BoundIndex (t : Fin 8 → ℕ) := Unit ⊕ PhysicalPolynomial.PhysicalCoordinateIndex 2 t

end ExplicitGate

open MvPolynomial PhysicalPolynomial Matrix

/-! ### Coordinate bounds -/

theorem normSq_le_one_of_isUnitVector {ε : Type*} [Fintype ε] {v : ε → ℂ}
    (h : IsUnitVector v) (e : ε) : Complex.normSq (v e) ≤ 1 := by
  unfold IsUnitVector at h
  rw [← h]
  exact Finset.single_le_sum (f := fun e => Complex.normSq (v e))
    (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ e)

theorem re_conjTranspose_mul_self_apply {m n : Type*} [Fintype m] (V : Matrix m n ℂ) (j : n) :
    ((Vᴴ * V) j j).re = ∑ i, Complex.normSq (V i j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]

theorem normSq_le_one_of_sum {ι m n : Type*} [Fintype ι] [Fintype m] [DecidableEq n]
    (V : ι → Matrix m n ℂ) (h : ∑ x, (V x)ᴴ * V x = 1) (x : ι) (i : m) (j : n) :
    Complex.normSq (V x i j) ≤ 1 := by
  have h1 : ((∑ x, (V x)ᴴ * V x) j j).re = 1 := by rw [h]; simp
  rw [Matrix.sum_apply, Complex.re_sum] at h1
  simp only [re_conjTranspose_mul_self_apply] at h1
  rw [← h1]
  calc Complex.normSq (V x i j) ≤ ∑ i', Complex.normSq (V x i' j) :=
        Finset.single_le_sum (f := fun i' => Complex.normSq (V x i' j))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ x', ∑ i', Complex.normSq (V x' i' j) :=
        Finset.single_le_sum (f := fun x' => ∑ i', Complex.normSq (V x' i' j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ x)

theorem normSq_le_one_of_isIsometry {m n : Type*} [Fintype m] [DecidableEq n]
    {V : Matrix m n ℂ} (h : IsIsometry V) (i : m) (j : n) : Complex.normSq (V i j) ≤ 1 :=
  normSq_le_one_of_sum (fun _ : Unit => V) (by simpa [IsIsometry] using h) () i j

theorem abs_complexRealCoordEquiv_le_one {ι : Type*} (z : ι → ℂ)
    (hz : ∀ q, Complex.normSq (z q) ≤ 1) (p : ι × Fin 2) :
    |complexRealCoordEquiv ι z p| ≤ 1 := by
  rcases p with ⟨q, b⟩
  have h := hz q
  rw [Complex.normSq_apply] at h
  fin_cases b
  · show |(z q).re| ≤ 1
    rw [abs_le]; constructor <;> nlinarith [mul_self_nonneg (z q).im]
  · show |(z q).im| ≤ 1
    rw [abs_le]; constructor <;> nlinarith [mul_self_nonneg (z q).re]

theorem abs_physicalCoordinates_le_one {s : Fin 8 → ℕ} {y : PhysicalBlocks 2 s}
    (hy : y ∈ physicalSet 2 s) (i : PhysicalCoordinateIndex 2 s) :
    |physicalCoordinatesEquiv 2 s y i| ≤ 1 := by
  refine abs_complexRealCoordEquiv_le_one (physicalComplexEntriesEquiv 2 s y) (fun q => ?_) i
  rcases q with q | q | q | q | q
  · exact normSq_le_one_of_isUnitVector hy.1 q
  · exact normSq_le_one_of_isIsometry hy.2.1 q.1 q.2
  · exact normSq_le_one_of_isIsometry hy.2.2.1 q.1 q.2
  · exact normSq_le_one_of_isIsometry hy.2.2.2.1 q.1 q.2
  · exact normSq_le_one_of_isIsometry hy.2.2.2.2 q.1 q.2

theorem abs_tCoords_le_one {s : Fin 8 → ℕ} {nA nB : ℕ}
    {z : TranscriptPolynomial.TBlocks s nA nB} (hz : z ∈ TranscriptPolynomial.transcriptSet s nA nB)
    (i : TranscriptPolynomial.TCoordIndex s nA nB) :
    |TranscriptPolynomial.tCoordsEquiv s nA nB z i| ≤ 1 := by
  refine abs_complexRealCoordEquiv_le_one (TranscriptPolynomial.tEntriesEquiv s nA nB z)
    (fun q => ?_) i
  obtain ⟨h0, h1, h2, h3, h4⟩ := hz
  rcases q with q | q | q | q | q
  · exact normSq_le_one_of_isUnitVector h0 q
  · exact normSq_le_one_of_sum _ h1 q.1 q.2.1 q.2.2
  · exact normSq_le_one_of_sum _ h2 q.1 q.2.1 q.2.2
  · exact normSq_le_one_of_isIsometry (h3 q.1.1 q.1.2) q.2.1 q.2.2
  · exact normSq_le_one_of_isIsometry (h4 q.1.1 q.1.2) q.2.1 q.2.2

/-! ### The controlled-phase eliminant -/

theorem thirty_two_add_lt_two_pow (K : ℕ) :
    32 + 2 ^ 51 * K ^ 14 < 2 ^ (56 + 14 * K) := by
  have hK2 : K ^ 14 ≤ 2 ^ (14 * K) := by
    calc K ^ 14 ≤ (2 ^ K) ^ 14 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 14
      _ = 2 ^ (14 * K) := by rw [← pow_mul, mul_comm]
  have h1 : 1 ≤ 2 ^ (14 * K) := Nat.one_le_two_pow
  calc 32 + 2 ^ 51 * K ^ 14 ≤ 32 + 2 ^ 51 * 2 ^ (14 * K) := by gcongr
    _ < 2 ^ 5 * (2 ^ 51 * 2 ^ (14 * K)) := by
        have : 1 ≤ 2 ^ 51 * 2 ^ (14 * K) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
    _ = 2 ^ (56 + 14 * K) := by rw [← pow_add, ← pow_add]; congr 1; ring

/-- **Controlled-phase eliminant without external input.** -/
theorem exists_controlledPhase_certificate_eliminant {K : ℕ} (hK : 1 ≤ K) (θ g : ℝ)
    (t : Fin 8 → ℕ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hCdeg : (physicalConstraintSumSquares 2 t).totalDegree ≤ 4)
    (hSdeg : (controlledPhaseScoreNumeratorPolynomial t).totalDegree ≤ 12)
    (hCm : CoefficientMassLE (physicalConstraintSumSquares 2 t) (34406400 * K ^ 8))
    (hSm : CoefficientMassLE (controlledPhaseScoreNumeratorPolynomial t) (2 ^ 51 * K ^ 14))
    (hupper : ∀ x : PhysicalBlocks 2 t,
      eval (physicalCoordinatesEquiv 2 t x) (physicalConstraintSumSquares 2 t) = 0 →
        eval (phaseScoreCoordinates t (Real.cos θ) (Real.sin θ) x)
          (controlledPhaseScoreNumeratorPolynomial t) ≤ 16 * (1 - g))
    (hattain : ∃ x : PhysicalBlocks 2 t,
      eval (physicalCoordinatesEquiv 2 t x) (physicalConstraintSumSquares 2 t) = 0 ∧
        eval (phaseScoreCoordinates t (Real.cos θ) (Real.sin θ) x)
          (controlledPhaseScoreNumeratorPolynomial t) = 16 * (1 - g)) :
    ∃ A : MvPolynomial (Fin 2) ℤ, A ≠ 0 ∧
      A.totalDegree ≤ 12 ^ (4 * (Fintype.card (ExplicitGate.BoundIndex t) + 1)) ∧
      IntPolynomialBitsizeLE A
        ((56 + 14 * K) * 12 ^ (4 * (Fintype.card (ExplicitGate.BoundIndex t) + 1))) ∧
      MvPolynomial.eval₂ (Int.castRingHom ℝ) ![g, Real.cos θ] A = 0 := by
  classical
  have hcard : Fintype.card (ExplicitGate.BoundIndex t) + 1 =
      Fintype.card (PhysicalCoordinateIndex 2 t) + 2 := by
    simp only [ExplicitGate.BoundIndex, Fintype.card_sum, Fintype.card_unit]
    omega
  have hCm' : CoefficientMassLE (physicalConstraintSumSquares 2 t) (2 ^ 51 * K ^ 14) :=
    hCm.mono (by
      have : K ^ 8 ≤ K ^ 14 := Nat.pow_le_pow_right hK (by norm_num)
      calc 34406400 * K ^ 8 ≤ 2 ^ 51 * K ^ 14 := Nat.mul_le_mul (by norm_num) this)
  obtain ⟨A, hA0, hdeg, hbits, hz⟩ := Deformation.exists_eliminant_explicit
    (PhysicalCoordinateIndex 2 t) (physicalConstraintSumSquares 2 t)
    (controlledPhaseScoreNumeratorPolynomial t) (2 ^ 51 * K ^ 14) (56 + 14 * K) θ g (by omega)
    (hCdeg.trans (by norm_num)) hSdeg hCm' hSm (thirty_two_add_lt_two_pow K) hg0 hg1
    (fun w hw => by
      have h := hupper ((physicalCoordinatesEquiv 2 t).symm w) (by
        rw [LinearEquiv.apply_symm_apply]; exact hw)
      have hphase : phaseScoreCoordinates t (Real.cos θ) (Real.sin θ)
          ((physicalCoordinatesEquiv 2 t).symm w) = Sum.elim ![Real.cos θ, Real.sin θ] w := by
        show Sum.elim ![Real.cos θ, Real.sin θ] _ = _
        rw [LinearEquiv.apply_symm_apply]
      rwa [hphase] at h)
    (by
      obtain ⟨x, hx, hxv⟩ := hattain
      have hxP : x ∈ physicalSet 2 t :=
        (physicalConstraintSumSquares_eval_coordinates_eq_zero_iff 2 t x).mp hx
      exact ⟨physicalCoordinatesEquiv 2 t x, hx, hxv, abs_physicalCoordinates_le_one hxP⟩)
  rw [hcard]
  exact ⟨A, hA0, hdeg, hbits, hz⟩

end NLQCLean

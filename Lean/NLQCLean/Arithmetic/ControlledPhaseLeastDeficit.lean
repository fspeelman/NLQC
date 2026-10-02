import NLQCLean.Arithmetic.ChargedPhysicalCoordinates
import NLQCLean.Arithmetic.PhysicalPolynomialHeight
import NLQCLean.Exact.ControlledPhaseExclusion
import NLQCLean.Bounds.ControlledPhaseLength
import NLQCLean.Bounds.BorelClassicalRates

/-!
# The least deficit of a controlled phase as a polynomial optimization

Step 1 of the proof of `thm:explicit` (Appendix C of the robust companion),
for two qubits and charged footprint `K ≥ 1`:

* `g_K(θ)` is the least score deficit `unitaryScoreDeficit (controlledPhase θ) K`;
  it lies in `[0, 1]`, is nonincreasing in `K`, and bounds the score deficit
  (Choi infidelity) of every pure or common-map mixed protocol of footprint at
  most `K`, and through Borel compression every free-classical protocol of
  quantum footprint `Kq` at footprint `16 Kq⁵`;
* for `θ = 1`, and every nonzero real algebraic angle, `g_K(θ) > 0`, by the
  exact exclusion of the named gate;
* one attaining architecture has all eight dimensions at most `4K` and at most
  `82 K²` raw real coordinates; on its physical algebraic set, cut out by one
  integer sum of squares, the integer score polynomial at `(cos θ, sin θ)` is
  at most `16 (1 - g_K(θ))` and attains it. The coefficient bounds of the
  four-times-`K` box therefore apply to the attaining architecture.

No elimination, height-of-elimination or transcendence-measure statement is
made here.
-/

namespace NLQCLean

open Matrix MvPolynomial PhysicalPolynomial ClassicalCommunication

/-- A nonempty qubit finite protocol has a positive resource dimension and
positive message dimensions. -/
theorem FinProtocol.qubit_shape_pos {s : Fin 8 → ℕ} (Q : FinProtocol 2 s) :
    0 < s 0 ∧ 0 < s 4 ∧ 0 < s 5 := by
  have hr : 0 < s 0 := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hA : 2 * s 0 ≤ s 2 * s 4 := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encA_isometry.card_le
  have hB : 2 * s 1 ≤ s 3 * s 5 := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encB_isometry.card_le
  have hr1 : 0 < s 1 := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_left h
  exact ⟨hr, Nat.pos_of_mul_pos_left ((Nat.mul_pos (by omega) hr).trans_le hA),
    Nat.pos_of_mul_pos_left ((Nat.mul_pos (by omega) hr1).trans_le hB)⟩

/-- The sharp compressed qubit shape lies in the four-times-`K` box used by
the coefficient-height bounds. -/
theorem sharp_qubit_shape_le_four_mul
    {K r kA kB mA mB eA eB : ℕ} (hr : 0 < r) (hmA : 0 < mA) (hmB : 0 < mB)
    (hcharge : r * mA * mB ≤ K)
    (hkA : kA ≤ 2 * r * mA) (hkB : kB ≤ 2 * r * mB)
    (heA : eA ≤ 2 * kA * mB) (heB : eB ≤ 2 * kB * mA) :
    ∀ i, (![r, r, kA, kB, mA, mB, eA, eB] : Fin 8 → ℕ) i ≤ 4 * K := by
  have hrmA : r * mA ≤ K := (Nat.le_mul_of_pos_right _ hmB).trans hcharge
  have hrmB : r * mB ≤ K := by
    apply (Nat.le_mul_of_pos_right _ hmA).trans
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcharge
  have hr' : r ≤ K := (Nat.le_mul_of_pos_right _ hmA).trans hrmA
  have hmA' : mA ≤ K := (Nat.le_mul_of_pos_left _ hr).trans hrmA
  have hmB' : mB ≤ K := (Nat.le_mul_of_pos_left _ hr).trans hrmB
  have hkA' : kA ≤ 2 * K := hkA.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 hrmA)
  have hkB' : kB ≤ 2 * K := hkB.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 hrmB)
  obtain ⟨-, -, hea, heb⟩ := sharp_qubit_decoder_dimensions hcharge hkA hkB heA heB
  intro i
  fin_cases i <;> simp <;> omega

section LeastDeficit

/-- `g_K(θ)`: the least score deficit of the controlled phase at footprint `K`. -/
noncomputable def controlledPhaseLeastDeficit (K : ℕ) (θ : ℝ) : ℝ :=
  unitaryScoreDeficit (controlledPhase θ) K

theorem controlledPhase_isIsometry (θ : ℝ) : IsIsometry (controlledPhase θ) :=
  Matrix.mem_unitaryGroup_iff'.mp (controlledPhase_unitary θ)

theorem controlledPhaseLeastDeficit_mem_Icc {K : ℕ} (hK : 1 ≤ K) (θ : ℝ) :
    controlledPhaseLeastDeficit K θ ∈ Set.Icc 0 1 :=
  unitaryScoreDeficit_mem_Icc (by decide) hK _ (controlledPhase_isIsometry θ)

/-- The least deficit is nonincreasing in the footprint. -/
theorem controlledPhaseLeastDeficit_antitone {K K' : ℕ} (hK : 1 ≤ K) (hKK' : K ≤ K')
    (θ : ℝ) : controlledPhaseLeastDeficit K' θ ≤ controlledPhaseLeastDeficit K θ := by
  obtain ⟨s, P, hP, hscore⟩ := exists_unitaryScoreMaximum_protocol (by decide) hK
    (controlledPhase θ)
  have hle := P.score_le_unitaryScoreMaximum (by decide) (hK.trans hKK')
    (HasFootprint.mono hP hKK') (controlledPhase θ)
  unfold controlledPhaseLeastDeficit unitaryScoreDeficit
  linarith

/-- Every pure protocol of footprint at most `K` has score deficit at least `g_K`. -/
theorem PureProtocol.controlledPhaseLeastDeficit_le
    {ρA ρB κA κB μA μB εA εB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
    {K : ℕ} (hK : 1 ≤ K) (hP : P.HasFootprint K) {θ ε : ℝ}
    (hs : 1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel) :
    controlledPhaseLeastDeficit K θ ≤ ε := by
  have h := P.score_le_unitaryScoreMaximum (by decide) hK hP (controlledPhase θ)
  unfold controlledPhaseLeastDeficit unitaryScoreDeficit
  linarith

/-- The same lower bound for common-map mixed resources of Schmidt number `R`. -/
theorem MixedResource.controlledPhaseLeastDeficit_le
    {ρA ρB κA κB μA μB εA εB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
    [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin 2 × ρA) ℂ) (VB : Matrix (κB × μB) (Fin 2 × ρB) ℂ)
    (DA : Matrix (Fin 2 × εA) (κA × μB) ℂ) (DB : Matrix (Fin 2 × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {R K : ℕ} (hK : 1 ≤ K) (hR : m.schmidtNumberLE R)
    (hcharge : R * Fintype.card μA * Fintype.card μB ≤ K) {θ ε : ℝ}
    (hs : 1 - ε ≤ scoreU (controlledPhase θ) (m.mixedChannel VA VB DA DB)) :
    controlledPhaseLeastDeficit K θ ≤ ε := by
  have h := m.score_le_unitaryScoreMaximum VA VB DA DB hVA hVB hDA hDB (by decide) hK hR
    hcharge (controlledPhase θ)
  unfold controlledPhaseLeastDeficit unitaryScoreDeficit
  linarith

/-- Charged reachability is exactly a bound on the least deficit. -/
theorem controlledPhaseLeastDeficit_le_iff {K : ℕ} (hK : 1 ≤ K) (θ ε : ℝ) :
    controlledPhaseLeastDeficit K θ ≤ ε ↔ controlledPhaseTarget θ ∈ pureReachable 2 K ε := by
  rw [mem_pureReachable_iff_le_unitaryScoreMaximum (by decide) hK]
  unfold controlledPhaseLeastDeficit unitaryScoreDeficit
  change _ ↔ 1 - ε ≤ unitaryScoreMaximum (controlledPhase θ) K
  constructor <;> intro h <;> linarith

/-- **Positivity.** For every nonzero real algebraic angle, in particular
`θ = 1`, the least deficit is positive at every footprint. -/
theorem controlledPhaseLeastDeficit_pos {K : ℕ} (hK : 1 ≤ K) {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : IsAlgebraic ℚ θ) : 0 < controlledPhaseLeastDeficit K θ := by
  have hnn := (controlledPhaseLeastDeficit_mem_Icc hK θ).1
  refine lt_of_le_of_ne hnn fun hzero => ?_
  obtain ⟨s, P, -, hexact⟩ := (unitaryScoreDeficit_eq_zero_iff (by decide) hK _
    (controlledPhase_isIsometry θ)).mp hzero.symm
  exact (controlledPhase_no_finite_exact_implementation.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    hθ0 hθ).1 _ _ _ _ _ _ _ _ P hexact

theorem controlledPhaseLeastDeficit_one_pos {K : ℕ} (hK : 1 ≤ K) :
    0 < controlledPhaseLeastDeficit K 1 :=
  controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one

/-- Free standard-Borel classical messages: a pure or common-map mixed Borel
protocol of quantum footprint `Kq` and score deficit `ε` has
`g_{16 Kq⁵}(θ) ≤ ε`. -/
theorem StandardBorelClassicalProtocol.controlledPhaseLeastDeficit_le
    {ρA ρB κA κB μA μB σA σB : Type*}
    [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
    [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
    [DecidableEq μA] [DecidableEq μB]
    [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
    (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
      (Fin 2) (Fin 2)) {Kq : ℕ} (hKq : 1 ≤ Kq) {θ ε : ℝ} :
    (P.HasQuantumFootprint Kq →
      1 - ε ≤ scoreU (controlledPhase θ) P.operationalChannel.toLinearMap →
        controlledPhaseLeastDeficit (16 * Kq ^ 5) θ ≤ ε) ∧
    (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
      1 - ε ≤ scoreU (controlledPhase θ) (P.mixedOperationalChannel m) →
        controlledPhaseLeastDeficit (16 * Kq ^ 5) θ ≤ ε) := by
  have h64 : 1 ≤ 16 * Kq ^ 5 := by
    have := Nat.one_le_pow 5 Kq hKq
    omega
  have hcast : 2 ^ 4 * Kq ^ 5 = 16 * Kq ^ 5 := by norm_num
  refine ⟨fun hK hs => ?_, fun n m hK hs => ?_⟩
  · rw [controlledPhaseLeastDeficit_le_iff h64, ← hcast]
    exact P.mem_pureReachable_of_quantumFootprint (controlledPhaseTarget θ) (by decide) hK hs
  · rw [controlledPhaseLeastDeficit_le_iff h64, ← hcast]
    exact P.mem_pureReachable_of_mixedQuantumFootprint m (controlledPhaseTarget θ)
      (by decide) hK hs

end LeastDeficit

/-- **Polynomial model of the least deficit.** One attaining architecture `t`
has all dimensions at most `4K` and at most `82 K²` raw real coordinates. On
its physical set, cut out by the integer sum of squares
`physicalConstraintSumSquares 2 t`, the integer score polynomial at
`(cos θ, sin θ)` is at most `16 (1 - g_K(θ))`, with equality at some point.
The constraint and score polynomials have total degree at most `4` and `12`
and coefficient mass at most `34406400 K⁸` and `2⁵¹ K¹⁴`. -/
theorem exists_controlledPhaseLeastDeficit_polynomial_certificate {K : ℕ} (hK : 1 ≤ K)
    (θ : ℝ) :
    ∃ t : Fin 8 → ℕ, (∀ i, t i ≤ 4 * K) ∧ physicalRawRealCoordinateCount 2 t ≤ 82 * K ^ 2 ∧
      (physicalConstraintSumSquares 2 t).totalDegree ≤ 4 ∧
      (controlledPhaseScoreNumeratorPolynomial t).totalDegree ≤ 12 ∧
      CoefficientMassLE (physicalConstraintSumSquares 2 t) (34406400 * K ^ 8) ∧
      CoefficientMassLE (controlledPhaseScoreNumeratorPolynomial t) (2 ^ 51 * K ^ 14) ∧
      (∀ x : PhysicalBlocks 2 t,
        eval (physicalCoordinatesEquiv 2 t x) (physicalConstraintSumSquares 2 t) = 0 →
        eval (phaseScoreCoordinates t (Real.cos θ) (Real.sin θ) x)
            (controlledPhaseScoreNumeratorPolynomial t) ≤
          16 * (1 - controlledPhaseLeastDeficit K θ)) ∧
      ∃ x : PhysicalBlocks 2 t,
        eval (physicalCoordinatesEquiv 2 t x) (physicalConstraintSumSquares 2 t) = 0 ∧
        eval (phaseScoreCoordinates t (Real.cos θ) (Real.sin θ) x)
            (controlledPhaseScoreNumeratorPolynomial t) =
          16 * (1 - controlledPhaseLeastDeficit K θ) := by
  obtain ⟨s, P, hP, hscore⟩ := exists_unitaryScoreMaximum_protocol (by decide) hK
    (controlledPhase θ)
  obtain ⟨r, kA, kB, eA, eB, -, hcharge, hkA, hkB, heA, heB, Q, -, hchan, hcoords⟩ :=
    P.exists_qubit_compressed_coordinate_certificate hP
  obtain ⟨hr, hmA, hmB⟩ := Q.qubit_shape_pos
  have hbox := sharp_qubit_shape_le_four_mul hr hmA hmB hcharge hkA hkB heA heB
  have hsupport : r * Fintype.card (Fin (s 4)) * Fintype.card (Fin (s 5)) ≤ K := hcharge
  refine ⟨_, hbox, ?_, physicalConstraintSumSquares_degree_le 2 _,
    controlledPhaseScoreNumeratorPolynomial_degree_le _,
    physicalConstraintSumSquares_massLE_of_four_mul_box hK _ hbox,
    controlledPhaseScoreNumeratorPolynomial_massLE_of_four_mul_box _ hbox, ?_, ?_⟩
  · rw [← finrank_physicalBlocks_eq_rawRealCoordinateCount]
    exact hcoords
  · intro x hx
    have hxs : x ∈ physicalSet 2 _ :=
      (physicalConstraintSumSquares_eval_coordinates_eq_zero_iff 2 _ x).mp hx
    let R := x.toProtocol hxs
    have hle := R.score_le_unitaryScoreMaximum (by decide) hK
      (R.hasFootprint_of_support_charge hsupport) (controlledPhase θ)
    rw [controlledPhaseScoreNumeratorPolynomial_evaluate_angle]
    unfold controlledPhaseLeastDeficit unitaryScoreDeficit
    change 16 * scoreU (controlledPhase θ) R.operationalChannel ≤ _
    linarith
  · refine ⟨(Q.resource, Q.encA, Q.encB, Q.decA, Q.decB), ?_, ?_⟩
    · exact (physicalConstraintSumSquares_eval_coordinates_eq_zero_iff 2 _ _).mpr
        ⟨Q.resource_unit, Q.encA_isometry, Q.encB_isometry, Q.decA_isometry, Q.decB_isometry⟩
    · rw [controlledPhaseScoreNumeratorPolynomial_evaluate_angle]
      unfold controlledPhaseLeastDeficit unitaryScoreDeficit
      change 16 * scoreU (controlledPhase θ) Q.operationalChannel = _
      rw [← hchan, hscore]
      ring

end NLQCLean

import NLQCLean.Arithmetic.TranscriptHeight
import NLQCLean.Bounds.ControlledPhaseEliminant
import NLQCLean.Bounds.ExplicitControlledPhaseGelfond
import NLQCLean.Bounds.SharedRandomLOSCC

/-!
# The explicit bound for `C₁` with free classical messages (`eq:explicit-quantum-tradeoff`)

For a transcript shape the score of the transcript family is maximized on a compact real
algebraic set; at `C₁` the maximum is below one by exact impossibility, and the boundary
eliminant of the epigraph (`Deformation.exists_eliminant_of_family`) with the proved
Gelfond measure
for `e^i` gives a least deficit at least `exp(-exp(C r⁴ q²))`, `q = rab`, uniformly in the
shape. The transcript representative then bounds every free-classical protocol.
-/

namespace NLQCLean

open Matrix MvPolynomial PhysicalPolynomial TranscriptPolynomial ClassicalCommunication

/-! ### Entry bounds and compactness -/

theorem norm_entry_le_one_of_sum_gram {ξ m n : Type*} [Fintype ξ] [Fintype m] [DecidableEq n]
    (V : ξ → Matrix m n ℂ) (h : ∑ x, (V x)ᴴ * V x = 1) (x : ξ) (k : m) (i : n) :
    ‖V x k i‖ ≤ 1 := by
  have hterm : ∀ (x : ξ) (k : m), (star (V x k i) * V x k i).re = ‖V x k i‖ ^ 2 := by
    intro x k
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  have hii := congrArg (fun M : Matrix n n ℂ => (M i i).re) h
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.one_re, Complex.re_sum] at hii
  have hle : ‖V x k i‖ ^ 2 ≤ 1 := by
    rw [← hii, ← hterm x k]
    calc (star (V x k i) * V x k i).re ≤ ∑ k', (star (V x k' i) * V x k' i).re :=
          Finset.single_le_sum (f := fun k' => (star (V x k' i) * V x k' i).re)
            (fun k' _ => by rw [hterm]; positivity) (Finset.mem_univ k)
      _ ≤ ∑ x', ∑ k', (star (V x' k' i) * V x' k' i).re :=
          Finset.single_le_sum (f := fun x' => ∑ k', (star (V x' k' i) * V x' k' i).re)
            (fun x' _ => Finset.sum_nonneg fun k' _ => by rw [hterm]; positivity)
            (Finset.mem_univ x)
  nlinarith [norm_nonneg (V x k i)]

variable {s : Fin 8 → ℕ} {nA nB : ℕ}

theorem norm_tEntries_le_one {z : TBlocks s nA nB} (hz : z ∈ transcriptSet s nA nB)
    (q : TComplexEntryIndex s nA nB) : ‖tEntriesEquiv s nA nB z q‖ ≤ 1 := by
  obtain ⟨hR, hA, hB, hDA, hDB⟩ := hz
  rcases q with q | ⟨x, i, j⟩ | ⟨y, i, j⟩ | ⟨⟨x, y⟩, i, j⟩ | ⟨⟨x, y⟩, i, j⟩
  · change ‖z.1 q‖ ≤ 1
    have hsum : Complex.normSq (z.1 q) ≤ 1 := by
      rw [← hR]
      exact Finset.single_le_sum (f := fun q' => Complex.normSq (z.1 q'))
        (fun q' _ => Complex.normSq_nonneg _) (Finset.mem_univ q)
    rw [← Complex.sq_norm] at hsum
    nlinarith [norm_nonneg (z.1 q)]
  · exact norm_entry_le_one_of_sum_gram z.2.1 hA x i j
  · exact norm_entry_le_one_of_sum_gram z.2.2.1 hB y i j
  · exact norm_entry_le_one_of_sum_gram (fun _ : Unit => z.2.2.2.1 x y)
      (by simpa using (hDA x y).conjTranspose_mul_self) () i j
  · exact norm_entry_le_one_of_sum_gram (fun _ : Unit => z.2.2.2.2 x y)
      (by simpa using (hDB x y).conjTranspose_mul_self) () i j

variable (s nA nB)

/-- Physical points of the transcript family, in real coordinates. -/
def tPhys : Set (TCoordIndex s nA nB → ℝ) :=
  {w | PhysicalPolynomial.eval w (transcriptConstraintSumSquares s nA nB) = 0}

variable {s nA nB}

theorem mem_tPhys_iff (w : TCoordIndex s nA nB → ℝ) :
    w ∈ tPhys s nA nB ↔ (tCoordsEquiv s nA nB).symm w ∈ transcriptSet s nA nB := by
  rw [← transcriptConstraintSumSquares_eval_eq_zero_iff, LinearEquiv.apply_symm_apply]
  rfl

theorem continuous_intEval {σ : Type*} (p : MvPolynomial σ ℤ) :
    Continuous fun w : σ → ℝ => PhysicalPolynomial.eval w p := by
  have := MvPolynomial.continuous_eval (p.map (Int.castRingHom ℝ))
  simpa [MvPolynomial.eval_map, PhysicalPolynomial.eval] using this

theorem isCompact_tPhys : IsCompact (tPhys s nA nB) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (continuous_intEval _) continuous_const
  · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun w hw => ?_
    rw [mem_tPhys_iff] at hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro ⟨q, c⟩
    have hq := norm_tEntries_le_one hw q
    have hw' : w = tCoordsEquiv s nA nB ((tCoordsEquiv s nA nB).symm w) := by simp
    rw [hw']
    change ‖(![(tEntriesEquiv s nA nB _ q).re, (tEntriesEquiv s nA nB _ q).im] : Fin 2 → ℝ) c‖ ≤ 1
    fin_cases c
    · exact (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans hq
    · exact (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm _).trans hq

/-! ### The least deficit of a transcript shape -/

variable (s nA nB)

/-- Sixteen times the largest family score at the phase angle `θ`. -/
noncomputable def tScoreMax (θ : ℝ) : ℝ :=
  sSup ((fun w => PhysicalPolynomial.eval (Sum.elim ![Real.cos θ, Real.sin θ] w)
    (transcriptScorePolynomial s nA nB)) '' tPhys s nA nB)

variable {s nA nB}

theorem continuous_transcriptScore (θ : ℝ) :
    Continuous fun w : TCoordIndex s nA nB → ℝ => PhysicalPolynomial.eval
      (Sum.elim ![Real.cos θ, Real.sin θ] w) (transcriptScorePolynomial s nA nB) := by
  refine (continuous_intEval _).comp (continuous_pi fun u => ?_)
  rcases u with u | u
  · exact continuous_const
  · exact continuous_apply u

theorem isGreatest_tScoreMax (hne : (tPhys s nA nB).Nonempty) (θ : ℝ) :
    IsGreatest ((fun w => PhysicalPolynomial.eval (Sum.elim ![Real.cos θ, Real.sin θ] w)
      (transcriptScorePolynomial s nA nB)) '' tPhys s nA nB) (tScoreMax s nA nB θ) := by
  have hc := isCompact_tPhys.image (continuous_transcriptScore (s := s) (nA := nA) (nB := nB) θ)
  exact ⟨hc.sSup_mem (hne.image _), fun v hv => le_csSup hc.bddAbove hv⟩

theorem qubitCornerPhase_cos_sin (θ : ℝ) :
    qubitCornerPhase ⟨Real.cos θ, Real.sin θ⟩ = controlledPhase θ := by
  change qubitCornerPhase ⟨Real.cos θ, Real.sin θ⟩ =
    qubitCornerPhase (Complex.exp ((θ : ℂ) * Complex.I))
  congr 1
  rw [Complex.exp_mul_I]
  apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The family polynomial at a physical point is sixteen times the actual score. -/
theorem transcriptScore_eq (θ : ℝ) (z : TBlocks s nA nB) (hz : z ∈ transcriptSet s nA nB) :
    PhysicalPolynomial.eval (Sum.elim ![Real.cos θ, Real.sin θ] (tCoordsEquiv s nA nB z))
        (transcriptScorePolynomial s nA nB) =
      16 * scoreU (controlledPhase θ) (toProtocol z hz).operationalChannel := by
  rw [transcriptScorePolynomial_evaluate, scoreU_toProtocol, qubitCornerPhase_cos_sin,
    Finset.mul_sum]
  simp only [Finset.mul_sum]

/-- Every protocol of the family shape scores at most `tScoreMax / 16`. -/
theorem score_le_tScoreMax (θ : ℝ)
    (Q : FiniteClassicalProtocol (Fin 2) (Fin 2) (Fin (s 0)) (Fin (s 1)) (Fin (s 2)) (Fin (s 3))
      (Fin (s 4)) (Fin (s 5)) (Fin nA) (Fin nB) Unit Unit (Fin 2) (Fin 2) (Fin (s 6))
      (Fin (s 7))) :
    16 * scoreU (controlledPhase θ) Q.operationalChannel ≤ tScoreMax s nA nB θ := by
  have hmem : tCoordsEquiv s nA nB (ofProtocol Q) ∈ tPhys s nA nB := by
    rw [mem_tPhys_iff, LinearEquiv.symm_apply_apply]
    exact ofProtocol_mem Q
  have hne : (tPhys s nA nB).Nonempty := ⟨_, hmem⟩
  have h := (isGreatest_tScoreMax hne θ).2 ⟨_, hmem, rfl⟩
  beta_reduce at h
  rw [transcriptScore_eq θ _ (ofProtocol_mem Q), toProtocol_ofProtocol] at h
  exact h

/-- **Exact impossibility.** Every physical point scores strictly below one at `C₁`. -/
theorem score_lt_one_controlledPhase_one (z : TBlocks s nA nB) (hz : z ∈ transcriptSet s nA nB) :
    scoreU (controlledPhase 1) (toProtocol z hz).operationalChannel < 1 := by
  classical
  set R := toProtocol z hz
  set P := R.coherentProtocol
  set K₀ := max (schmidtRank P.resource * Fintype.card (Fin (s 4) × Fin nA) *
    Fintype.card (Fin (s 5) × Fin nB)) 1
  have hK : 1 ≤ K₀ := le_max_right _ _
  have hP : P.HasFootprint K₀ := (hasFootprint_iff K₀ P.resource).mpr (le_max_left _ _)
  have hpos := controlledPhaseLeastDeficit_pos hK one_ne_zero isAlgebraic_one
  have hle := P.controlledPhaseLeastDeficit_le hK hP (θ := 1)
    (ε := 1 - scoreU (controlledPhase 1) R.operationalChannel)
    (by rw [R.coherentProtocol_operationalChannel]; linarith)
  linarith

theorem tScoreMax_lt (hne : (tPhys s nA nB).Nonempty) : tScoreMax s nA nB 1 < 16 := by
  obtain ⟨⟨w, hw, hwv⟩, -⟩ := isGreatest_tScoreMax hne 1
  rw [← hwv]
  beta_reduce
  have hz := (mem_tPhys_iff w).mp hw
  have h := transcriptScore_eq 1 _ hz
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h]
  have := score_lt_one_controlledPhase_one _ hz
  linarith

theorem tScoreMax_nonneg (hne : (tPhys s nA nB).Nonempty) (θ : ℝ) : 0 ≤ tScoreMax s nA nB θ := by
  obtain ⟨⟨w, hw, hwv⟩, -⟩ := isGreatest_tScoreMax hne θ
  rw [← hwv]
  beta_reduce
  have hz := (mem_tPhys_iff w).mp hw
  have h := transcriptScore_eq θ _ hz
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, scoreU_toProtocol]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    scoreU_channelOf_nonneg _ _)

/-! ### The uniform family bound -/

/-- `202 (6M + τM + 128)^{33} ≤ exp((108108 α + 237) P)` for `M = 12^{α(N+2)}`,
`τ = 56 + 18q`, `N + 2 ≤ 1092 P` and `q ≤ P`. -/
theorem transcript_exponent_le {α N q : ℕ} {P : ℝ} (hq : 1 ≤ q) (hP1 : 1 ≤ P) (hqP : (q : ℝ) ≤ P)
    (hN : (N : ℝ) + 2 ≤ 1092 * P) :
    202 * (((6 * 12 ^ (α * (N + 2)) + (56 + 18 * q) * 12 ^ (α * (N + 2)) + 128 : ℕ) : ℝ)) ^ 33 ≤
      Real.exp ((108108 * α + 237) * P) := by
  set M : ℕ := 12 ^ (α * (N + 2)) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ (by norm_num)
  have hbase : 6 * M + (56 + 18 * q) * M + 128 ≤ 208 * q * M := by nlinarith
  have hMexp : (M : ℝ) ≤ Real.exp (3276 * α * P) := by
    have h := twelve_pow_le_exp (α * (N + 2))
    have hcast : (M : ℝ) = (12 : ℝ) ^ (α * (N + 2)) := by rw [hMdef]; push_cast; ring
    rw [hcast]
    refine h.trans (Real.exp_le_exp.mpr ?_)
    push_cast
    have hα : (0 : ℝ) ≤ α := Nat.cast_nonneg α
    nlinarith
  have h208 : (208 : ℝ) ≤ Real.exp 6 := by
    have := pow_2718_le_exp 6; norm_num at this ⊢; linarith
  have h202 : (202 : ℝ) ≤ Real.exp 6 := by
    have := pow_2718_le_exp 6; norm_num at this ⊢; linarith
  have hqe : (q : ℝ) ≤ Real.exp P := by
    have := Real.add_one_le_exp P
    linarith
  have hb : (((6 * M + (56 + 18 * q) * M + 128 : ℕ) : ℝ)) ≤ Real.exp ((7 + 3276 * α) * P) := by
    calc (((6 * M + (56 + 18 * q) * M + 128 : ℕ) : ℝ)) ≤ ((208 * q * M : ℕ) : ℝ) := by
          exact_mod_cast hbase
      _ = 208 * (q : ℝ) * M := by push_cast; ring
      _ ≤ Real.exp 6 * Real.exp P * Real.exp (3276 * α * P) := by gcongr
      _ = Real.exp (6 + P + 3276 * α * P) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((7 + 3276 * α) * P) := Real.exp_le_exp.mpr (by nlinarith)
  calc 202 * (((6 * M + (56 + 18 * q) * M + 128 : ℕ) : ℝ)) ^ 33
      ≤ Real.exp 6 * Real.exp ((7 + 3276 * α) * P) ^ 33 := by gcongr
    _ = Real.exp (6 + 33 * ((7 + 3276 * α) * P)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp ((108108 * α + 237) * P) := Real.exp_le_exp.mpr (by nlinarith)

/-- **Uniform bound for transcript shapes.** There is `C > 0` such that for every
shape produced by the transcript representative, `g ≥ exp(-exp(C r⁴ q²))`, `q = rab`. -/
theorem exists_transcript_deficit_bound :
    ∃ CE : ℝ, 0 < CE ∧ ∀ (r a b kA kB eA eB nA nB : ℕ), 1 ≤ r → 1 ≤ a → 1 ≤ b →
      kA ≤ 2 * r * a → kB ≤ 2 * r * b → eA ≤ 2 * kA * b → eB ≤ 2 * kB * a →
      nA ≤ 4 * r ^ 2 → nB ≤ 4 * r ^ 2 →
      (tPhys ![r, r, kA, kB, a, b, eA, eB] nA nB).Nonempty →
      Real.exp (-Real.exp (CE * ((r : ℝ) ^ 4 * ((r * a * b : ℕ) : ℝ) ^ 2))) ≤
        1 - tScoreMax ![r, r, kA, kB, a, b, eA, eB] nA nB 1 / 16 := by
  obtain ⟨α, helim⟩ := Deformation.exists_eliminant_of_family
  refine ⟨108108 * α + 237, by positivity, ?_⟩
  intro r a b kA kB eA eB nA nB hr ha hb hkA hkB heA heB hnA hnB hne
  set s : Fin 8 → ℕ := ![r, r, kA, kB, a, b, eA, eB] with hsdef
  set q := r * a * b with hqdef
  have hra : r ≤ q := by
    calc r = r * 1 * 1 := by ring
      _ ≤ r * a * b := Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) hb
  have haq : a ≤ q := by
    calc a = 1 * a * 1 := by ring
      _ ≤ r * a * b := Nat.mul_le_mul (Nat.mul_le_mul_right _ hr) hb
  have hbq : b ≤ q := by
    calc b = 1 * 1 * b := by ring
      _ ≤ r * a * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul hr ha)
  have hq1 : 1 ≤ q := hr.trans hra
  have hkAq : kA ≤ 2 * q := hkA.trans (by
    calc 2 * r * a = 2 * (r * a * 1) := by ring
      _ ≤ 2 * (r * a * b) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb))
  have hkBq : kB ≤ 2 * q := hkB.trans (by
    calc 2 * r * b = 2 * (r * 1 * b) := by ring
      _ ≤ 2 * (r * a * b) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha)))
  have heAq : eA ≤ 4 * q := heA.trans (by
    calc 2 * kA * b ≤ 2 * (2 * r * a) * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkA)
      _ = 4 * q := by rw [hqdef]; ring)
  have heBq : eB ≤ 4 * q := heB.trans (by
    calc 2 * kB * a ≤ 2 * (2 * r * b) * a := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkB)
      _ = 4 * q := by rw [hqdef]; ring)
  have hs : ∀ i, s i ≤ 4 * q := by
    intro i
    fin_cases i <;> simp [s] <;> omega
  have hr2 : r ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hra 2
  have hnA' : nA ≤ 4 * q ^ 2 := hnA.trans (Nat.mul_le_mul_left _ hr2)
  have hnB' : nB ≤ 4 * q ^ 2 := hnB.trans (Nat.mul_le_mul_left _ hr2)
  set g := 1 - tScoreMax s nA nB 1 / 16 with hgdef
  have hlt := tScoreMax_lt hne
  have hg0 : 0 < g := by rw [hgdef]; linarith
  have hg1 : g ≤ 1 := by have := tScoreMax_nonneg hne 1; rw [hgdef]; linarith
  have hG := isGreatest_tScoreMax hne 1
  have hval : tScoreMax s nA nB 1 = 16 * (1 - g) := by rw [hgdef]; ring
  have hupper : ∀ w : TCoordIndex s nA nB → ℝ,
      PhysicalPolynomial.eval w (transcriptConstraintSumSquares s nA nB) = 0 →
      PhysicalPolynomial.eval (Sum.elim ![Real.cos 1, Real.sin 1] w)
        (transcriptScorePolynomial s nA nB) ≤ 16 * (1 - g) := fun w hw =>
    hval ▸ hG.2 ⟨w, hw, rfl⟩
  have hattain : ∃ w : TCoordIndex s nA nB → ℝ,
      PhysicalPolynomial.eval w (transcriptConstraintSumSquares s nA nB) = 0 ∧
      PhysicalPolynomial.eval (Sum.elim ![Real.cos 1, Real.sin 1] w)
        (transcriptScorePolynomial s nA nB) = 16 * (1 - g) ∧ ∀ i, |w i| ≤ 1 := by
    obtain ⟨w, hw, hwv⟩ := hG.1
    refine ⟨w, hw, hwv.trans hval, fun i => ?_⟩
    have hz := (mem_tPhys_iff w).mp hw
    simpa using abs_tCoords_le_one hz i
  obtain ⟨A, hA0, hdeg, hbits, hzero⟩ := helim (TCoordIndex s nA nB)
    (transcriptConstraintSumSquares s nA nB) (transcriptScorePolynomial s nA nB)
    (2 ^ 55 * q ^ 18) (56 + 18 * q) 1 g (by omega)
    ((transcriptConstraintSumSquares_degree_le s nA nB).trans (by norm_num))
    (transcriptScorePolynomial_degree_le s nA nB)
    (transcriptConstraintSumSquares_massLE hq1 hs hnA' hnB')
    (transcriptScorePolynomial_massLE hs hnA' hnB') (two_pow_transcript_bit_bound q)
    hg0 hg1 hupper hattain
  set N := Fintype.card (TCoordIndex s nA nB) with hNdef
  have hM : 1 ≤ 12 ^ (α * (N + 2)) := Nat.one_le_pow _ _ (by norm_num)
  have hgap := gap_ge_of_cos_one_eliminant_gelfond hg0 hg1 hA0 hM hdeg
    (τ' := (56 + 18 * q) * 12 ^ (α * (N + 2))) hbits (by simpa using hzero)
  refine le_trans (Real.exp_le_exp.mpr ?_) hgap
  rw [neg_le_neg_iff]
  have hcard := card_tCoordIndex_le hr ha hb hkA hkB heA heB hnA hnB
  set P : ℝ := (r : ℝ) ^ 4 * ((q : ℕ) : ℝ) ^ 2 with hPdef
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr1) (one_le_pow₀ hq1')
  have hqP : (q : ℝ) ≤ P := by
    calc (q : ℝ) = 1 * q := by ring
      _ ≤ (r : ℝ) ^ 4 * ((q : ℝ) ^ 2) :=
          mul_le_mul (one_le_pow₀ hr1) (by nlinarith) (by positivity) (by positivity)
  have hN : (N : ℝ) + 2 ≤ 1092 * P := by
    have : (N : ℝ) ≤ 1090 * P := by
      rw [hPdef]
      have h' : ((N : ℕ) : ℝ) ≤ ((1090 * r ^ 4 * q ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
      push_cast at h'
      linarith
    linarith
  have := transcript_exponent_le (α := α) (N := N) hq1 hP1 hqP hN
  refine this.trans (le_of_eq ?_)
  rw [hPdef]

/-! ### Protocols -/

/-- **Core transfer.** A finite free-classical protocol on rank-sized resource registers with
at most `(2r)²` outcomes per party has deficit at least `exp(-exp(C r⁴ q²))` at `C₁`. -/
theorem exists_transcript_core_bound :
    ∃ CE : ℝ, 0 < CE ∧ ∀ {κA κB μA μB ηA ηB εA εB : Type*}
      [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB] [Fintype ηA] [Fintype ηB]
      [Fintype εA] [Fintype εB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
      [DecidableEq μB] [DecidableEq ηA] [DecidableEq ηB] [DecidableEq εA] [DecidableEq εB]
      {r nA nB : ℕ}
      (Q : FiniteClassicalProtocol (Fin 2) (Fin 2) (Fin r) (Fin r) κA κB μA μB (Fin nA) (Fin nB)
        ηA ηB (Fin 2) (Fin 2) εA εB),
      nA ≤ (2 * r) ^ 2 → nB ≤ (2 * r) ^ 2 →
      Real.exp (-Real.exp (CE * ((r : ℝ) ^ 4 *
          ((r * Fintype.card μA * Fintype.card μB : ℕ) : ℝ) ^ 2))) ≤
        1 - scoreU (controlledPhase 1) Q.operationalChannel := by
  obtain ⟨CE, hCE, hfam⟩ := exists_transcript_deficit_bound
  refine ⟨CE, hCE, fun {κA κB μA μB ηA ηB εA εB} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ {r nA nB} Q
    hnA hnB => ?_⟩
  classical
  have hr : 1 ≤ r := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hencA := Q.instrumentA.dilation_isometry.card_le
  have hencB := Q.instrumentB.dilation_isometry.card_le
  simp only [Fintype.card_prod, Fintype.card_fin] at hencA hencB
  have ha : 1 ≤ Fintype.card μA := by
    by_contra h0
    have : Fintype.card μA = 0 := by omega
    rw [this] at hencA
    simp at hencA
    omega
  have hb : 1 ≤ Fintype.card μB := by
    by_contra h0
    have : Fintype.card μB = 0 := by omega
    rw [this] at hencB
    simp at hencB
    omega
  obtain ⟨kA, kB, eA, eB, hkA, hkB, heA, heB, Q', -, hchan⟩ := exists_transcript_representative Q
  have h4 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
  have hle := score_le_tScoreMax (s := ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB])
    (nA := nA) (nB := nB) 1 Q'
  have hne : (tPhys ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB] nA nB).Nonempty := by
    refine ⟨tCoordsEquiv _ _ _
      (ofProtocol (s := ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB]) Q'), ?_⟩
    rw [mem_tPhys_iff, LinearEquiv.symm_apply_apply]
    exact ofProtocol_mem (s := ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB]) Q'
  have hfb := hfam r _ _ kA kB eA eB nA nB hr ha hb hkA hkB heA heB (h4 ▸ hnA) (h4 ▸ hnB) hne
  have hle' : 16 * scoreU (controlledPhase 1) Q.operationalChannel ≤
      tScoreMax ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB] nA nB 1 := by
    rw [← hchan]
    exact hle
  linarith

/-- Monotonicity of the double exponential in `R⁴ Kq²`. -/
theorem exp_neg_exp_mono {C x y : ℝ} (hC : 0 < C) (hxy : x ≤ y) :
    Real.exp (-Real.exp (C * y)) ≤ Real.exp (-Real.exp (C * x)) :=
  Real.exp_le_exp.mpr (neg_le_neg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hC.le)))

theorem rank_quantum_le {r a b R Kq : ℕ} (hrR : r ≤ R) (hK : r * a * b ≤ Kq) :
    (r : ℝ) ^ 4 * ((r * a * b : ℕ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 4 * (Kq : ℝ) ^ 2 := by
  have h1 : (r : ℝ) ≤ R := by exact_mod_cast hrR
  have h2 : ((r * a * b : ℕ) : ℝ) ≤ Kq := by exact_mod_cast hK
  gcongr

/-- **`eq:explicit-quantum-tradeoff`, finite free-classical protocols.** Unconditionally, there
is `C > 0` such that every finite
free-classical protocol for `C₁` with resource Schmidt number at most `R`, quantum footprint at
most `Kq` and score deficit at most `ε` has `ε ≥ exp(-exp(C R⁴ Kq²))`. -/
theorem exists_explicit_controlledPhase_one_quantum_tradeoff :
    ∃ CE : ℝ, 0 < CE ∧ ∀ {ρA ρB κA κB μA μB σA σB ηA ηB εA εB : Type*}
      [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
      [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
      [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB] [DecidableEq μA]
      [DecidableEq μB] [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
      [DecidableEq εA] [DecidableEq εB]
      (P : FiniteClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB ηA ηB (Fin 2) (Fin 2)
        εA εB) {R Kq : ℕ} {ε : ℝ},
      schmidtRank P.resource ≤ R → P.HasQuantumFootprint Kq →
      1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel →
      Real.exp (-Real.exp (CE * ((R : ℝ) ^ 4 * (Kq : ℝ) ^ 2))) ≤ ε := by
  obtain ⟨CE, hCE, hcore⟩ := exists_transcript_core_bound
  refine ⟨CE, hCE, fun {ρA ρB κA κB μA μB σA σB ηA ηB εA εB} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ P {R Kq ε} hR hK hs => ?_⟩
  classical
  obtain ⟨nA, hnA, nB, hnB, Q, -, hscore, -, -⟩ :=
    P.exists_bounded_outcomes_charged_linearScore (unitaryScoreRealLinear (controlledPhase 1))
      (by decide) hK
  have hcore' := hcore Q hnA hnB
  have hfoot := (hasFootprint_iff Kq P.resource).mp hK
  change scoreU (controlledPhase 1) P.operationalChannel ≤
    scoreU (controlledPhase 1) Q.operationalChannel at hscore
  have hmono := exp_neg_exp_mono hCE (rank_quantum_le hR hfoot)
  linarith

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **`eq:explicit-quantum-tradeoff`, standard-Borel free-classical protocols**, pure and
common-map mixed resources (Schmidt number at most `R`). -/
theorem exists_explicit_controlledPhase_one_borel_quantum_tradeoff :
    ∃ CE : ℝ, 0 < CE ∧ ∀ {ρA ρB κA κB μA μB σA σB : Type*}
      [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
      [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
      [DecidableEq μA] [DecidableEq μB]
      [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
      (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
        (Fin 2) (Fin 2)) {R Kq : ℕ} {ε : ℝ},
      (schmidtRank P.resource ≤ R → P.HasQuantumFootprint Kq →
        1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
        Real.exp (-Real.exp (CE * ((R : ℝ) ^ 4 * (Kq : ℝ) ^ 2))) ≤ ε) ∧
      (∀ (n : ℕ) (m : MixedResource ρA ρB n), m.schmidtNumberLE R →
        P.HasMixedQuantumFootprint m Kq →
        1 - ε ≤ scoreU (controlledPhase 1) (P.mixedOperationalChannel m) →
        Real.exp (-Real.exp (CE * ((R : ℝ) ^ 4 * (Kq : ℝ) ^ 2))) ≤ ε) := by
  obtain ⟨CE, hCE, hcore⟩ := exists_transcript_core_bound
  refine ⟨CE, hCE, fun {ρA ρB κA κB μA μB σA σB} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P {R Kq ε} =>
    ⟨fun hR hK hs => ?_, fun n m hm hK hs => ?_⟩⟩
  · obtain ⟨nA, hnA, nB, hnB, Q, -, hscore, -, -⟩ :=
      P.exists_bounded_outcomes_charged_linearScore (unitaryScoreRealLinear (controlledPhase 1))
        (by decide) hK
    have hcore' := hcore Q hnA hnB
    have hfoot := (hasFootprint_iff Kq P.resource).mp hK
    change scoreU (controlledPhase 1) P.operationalChannel.toLinearMap ≤
      scoreU (controlledPhase 1) Q.operationalChannel at hscore
    have hmono := exp_neg_exp_mono hCE (rank_quantum_le hR hfoot)
    linarith
  · obtain ⟨k, nA, hnA, nB, hnB, Q, -, -, hscore⟩ :=
      P.exists_component_bounded_outcomes_charged_linearScore m
        (unitaryScoreRealLinear (controlledPhase 1)) (by decide) hK
    have hcore' := hcore Q hnA hnB
    obtain ⟨R', hR', hfoot'⟩ := hK
    have hrk : schmidtRank (m.component k) * Fintype.card μA * Fintype.card μB ≤ Kq := by
      have : schmidtRank (m.component k) ≤ R' := hR' k
      exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)).trans hfoot'
    have hscore' : scoreU (controlledPhase 1) (P.mixedOperationalChannel m) ≤
        scoreU (controlledPhase 1) Q.operationalChannel := by
      have h := hscore
      rw [Q.coherentProtocol_operationalChannel] at h
      exact h
    have hmono := exp_neg_exp_mono hCE (rank_quantum_le (hm k) hrk)
    linarith

/-- **The sixth-power bound.** Every finite or standard-Borel free-classical protocol for `C₁`
of quantum footprint at most `Kq` has `ε ≥ exp(-exp(C Kq⁶))`. -/
theorem exists_explicit_controlledPhase_one_sixth_power :
    ∃ CE : ℝ, 0 < CE ∧ ∀ {ρA ρB κA κB μA μB σA σB : Type*}
      [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
      [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
      [DecidableEq μA] [DecidableEq μB]
      [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
      (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
        (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ},
      P.HasQuantumFootprint Kq →
      1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
      Real.exp (-Real.exp (CE * (Kq : ℝ) ^ 6)) ≤ ε := by
  obtain ⟨CE, hCE, hB⟩ := exists_explicit_controlledPhase_one_borel_quantum_tradeoff
  refine ⟨CE, hCE, fun {ρA ρB κA κB μA μB σA σB} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P {Kq ε}
    hK hs => ?_⟩
  have hfoot := (hasFootprint_iff Kq P.resource).mp hK
  obtain ⟨nA, -, nB, -, Q, -, -, -, -⟩ :=
    P.exists_bounded_outcomes_charged_linearScore (unitaryScoreRealLinear (controlledPhase 1))
      (by decide) hK
  have hencA := Q.instrumentA.dilation_isometry.card_le
  have hencB := Q.instrumentB.dilation_isometry.card_le
  simp only [Fintype.card_prod, Fintype.card_fin] at hencA hencB
  have hr : 1 ≤ schmidtRank P.resource := P.resource_unit.schmidtRank_pos
  have ha : 1 ≤ Fintype.card μA := by
    by_contra h0
    have : Fintype.card μA = 0 := by omega
    rw [this] at hencA
    simp at hencA
    omega
  have hb : 1 ≤ Fintype.card μB := by
    by_contra h0
    have : Fintype.card μB = 0 := by omega
    rw [this] at hencB
    simp at hencB
    omega
  have hrK : schmidtRank P.resource ≤ Kq := by
    calc schmidtRank P.resource = schmidtRank P.resource * 1 * 1 := by ring
      _ ≤ schmidtRank P.resource * Fintype.card μA * Fintype.card μB :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) hb
      _ ≤ Kq := hfoot
  have h := (hB P (R := Kq) (Kq := Kq) (ε := ε)).1 hrK hK hs
  have hpow : ((Kq : ℝ) ^ 4 * (Kq : ℝ) ^ 2) = (Kq : ℝ) ^ 6 := by ring
  rwa [hpow] at h

/-- **Iterated-logarithm form.** For `0 < ε < 1/e`, a standard-Borel free-classical protocol
for `C₁` of quantum footprint `Kq` with score deficit at most `ε` has
`log₂ Kq ≥ (1/6) log₂ ln ln(1/ε) - O(1)`. -/
theorem exists_explicit_controlledPhase_one_sixth_log_bound :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ {ρA ρB κA κB μA μB σA σB : Type*}
      [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
      [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
      [DecidableEq μA] [DecidableEq μB]
      [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
      (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
        (Fin 2) (Fin 2)) {Kq : ℕ} {ε : ℝ}, 1 ≤ Kq → 0 < ε → ε < Real.exp (-1) →
      P.HasQuantumFootprint Kq →
      1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
      (1 / 6 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ Real.logb 2 Kq := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhase_one_sixth_power
  refine ⟨max 0 ((1 / 6 : ℝ) * Real.logb 2 CE), le_max_left _ _, ?_⟩
  intro ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P Kq ε hKq hε hεe hK hs
  have hKr : (0 : ℝ) < Kq := by exact_mod_cast hKq
  have h := logb_iterated_log_le_of_double_exp (p := 6) hCE hKr (by norm_num) hε hεe
    (hbound P hK hs)
  push_cast at h
  linarith [le_max_right 0 ((1 / 6 : ℝ) * Real.logb 2 CE)]

/-- **Resource qubits in LOSCC.** For `0 < ε < 1/e`, an LOSCC protocol for `C₁` (classical
messages only) with at most `q` initial resource qubits and score deficit at most `ε` has
`q ≥ (1/3) log₂ ln ln(1/ε) - O(1)`. -/
theorem exists_explicit_controlledPhase_one_loscc_qubit_bound :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ {ρA ρB κA κB μA μB σA σB : Type*}
      [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
      [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
      [DecidableEq μA] [DecidableEq μB]
      [MeasurableSpace σA] [MeasurableSpace σB] [StandardBorelSpace σA] [StandardBorelSpace σB]
      (P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB
        (Fin 2) (Fin 2)) {q : ℕ} {ε : ℝ}, 0 < ε → ε < Real.exp (-1) →
      Fintype.card ρA * Fintype.card ρB ≤ 2 ^ q → Fintype.card μA = 1 → Fintype.card μB = 1 →
      1 - ε ≤ scoreU (controlledPhase 1) P.operationalChannel.toLinearMap →
      (1 / 3 : ℝ) * Real.logb 2 (Real.log (Real.log (1 / ε))) - b ≤ q := by
  obtain ⟨CE, hCE, hbound⟩ := exists_explicit_controlledPhase_one_sixth_power
  refine ⟨max 0 ((1 / 3 : ℝ) * Real.logb 2 CE), le_max_left _ _, ?_⟩
  intro ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P q ε hε hεe hcard hμA hμB hs
  have hK := P.hasQuantumFootprint_of_loscc hcard hμA hμB
  set Kq := Nat.sqrt (2 ^ q) with hKqdef
  have hKq1 : 1 ≤ Kq := Nat.le_sqrt.mpr (by simpa using Nat.one_le_two_pow)
  have hKr : (0 : ℝ) < Kq := by exact_mod_cast hKq1
  have h := logb_iterated_log_le_of_double_exp (p := 6) hCE hKr (by norm_num) hε hεe
    (hbound P hK hs)
  have hsq : ((Kq : ℝ)) ^ 2 ≤ (2 : ℝ) ^ q := by exact_mod_cast sqrt_two_pow_sq_le q
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hsq
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  push_cast at h hlog
  linarith [le_max_right 0 ((1 / 3 : ℝ) * Real.logb 2 CE)]

end NLQCLean

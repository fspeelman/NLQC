import NLQCLean.Models.NearBellResourceFloors
import NLQCLean.Bounds.SwapNeighborhoodMessages

/-!
# Both message floors near a maximally entangled basis

For a PVM protocol whose basis matrix lies within normalized distance `1/4` of
the generalized Bell basis and whose score is at least `1 - ε` with
`ε ≤ 1/256`, both message dimensions satisfy `d² ≤ 2 m²`. Bob's (respectively
Alice's) label-controlled correction of his reference produces, for the frozen
dilation, a reference projection of norm about `d^{3/2}`, while for the actual
protocol it is bounded by `√d` times the dimension of the message crossing to
him. Alice's bound is the mirror image, obtained from the party-swap symmetry
of the global isometry. The source is `lem:bell-compression` in the revised
robust companion.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

theorem sum4_swap {α β γ δ' : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ']
    (f : α → β → γ → δ' → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ a, ∑ c, ∑ b, ∑ e, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, f a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := Finset.sum_congr rfl fun c _ => Finset.sum_comm

section Swap

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- Exchanging the two parties exchanges both input and output pairs. -/
theorem globalIsometry_swap (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ) (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (p : (ιA' × εA) × (ιB' × εB)) (i : ιA × ιB) :
    globalIsometry (fun q : ρB × ρA => η (q.2, q.1)) VB VA DB DA (p.2, p.1) (i.2, i.1) =
      globalIsometry η VA VB DA DB p i := by
  rw [ClassicalCommunication.globalIsometry_entry, ClassicalCommunication.globalIsometry_entry,
    sum4_swap]
  refine Finset.sum_congr rfl fun kA _ => Finset.sum_congr rfl fun qB _ =>
    Finset.sum_congr rfl fun kB _ => Finset.sum_congr rfl fun qA _ => ?_
  rw [mul_comm (DB _ _), Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun rA _ => Finset.sum_congr rfl fun rB _ => ?_
  ring

end Swap

/-- A label-controlled contraction of the two Choi-input indices. -/
def labelContraction {X Y Q : Type*} [Fintype Q] (c : X → Y → Q → ℂ)
    (F : Matrix (X × Y) Q ℂ) : Matrix X Y ℂ :=
  fun x y => ∑ q, c x y q * F (x, y) q

theorem labelContraction_sub {X Y Q : Type*} [Fintype Q] (c : X → Y → Q → ℂ)
    (F G : Matrix (X × Y) Q ℂ) :
    labelContraction c (F - G) = labelContraction c F - labelContraction c G := by
  ext x y
  simp only [labelContraction, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem labelContraction_norm_sq_le {X Y Q : Type*} [Fintype X] [Fintype Y] [Fintype Q]
    (c : X → Y → Q → ℂ) {s : ℝ} (hc : ∀ x y, ∑ q, ‖c x y q‖ ^ 2 ≤ s)
    (F : Matrix (X × Y) Q ℂ) :
    ‖labelContraction c F‖ ^ 2 ≤ s * ‖F‖ ^ 2 := by
  have hrow (x : X) (y : Y) :
      ‖labelContraction c F x y‖ ^ 2 ≤ s * ∑ q, ‖F (x, y) q‖ ^ 2 := by
    have h1 : ‖∑ q, c x y q * F (x, y) q‖ ≤ ∑ q, ‖c x y q‖ * ‖F (x, y) q‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun q => ‖c x y q‖)
      (fun q => ‖F (x, y) q‖)
    calc ‖labelContraction c F x y‖ ^ 2 ≤ (∑ q, ‖c x y q‖ * ‖F (x, y) q‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ q, ‖c x y q‖ ^ 2) * ∑ q, ‖F (x, y) q‖ ^ 2 := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (hc x y) (Finset.sum_nonneg fun q _ => sq_nonneg _)
  rw [frobNorm_sq, frobNorm_sq, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => (Finset.sum_le_sum fun y _ => hrow x y).trans
    (le_of_eq (by rw [Finset.mul_sum]))

section Frozen

variable {δ εA εB Q : Type*} [Fintype δ] [Fintype εA] [Fintype εB] [Fintype Q]
variable [DecidableEq δ]

/-- On a flagged frozen dilation, a label-diagonal contraction only sees the
overlaps of the correction with the conjugated target columns. -/
theorem labelContraction_flag_norm_sq (c : δ → Q → ℂ) (u : δ → εA × εB → ℂ)
    (hu : ∀ i, IsUnitVector (u i)) (M : Matrix Q δ ℂ) :
    ‖labelContraction (fun (x : δ × εA) (_ : δ × εB) q => c x.1 q)
        (flagIsometry u * Mᴴ)‖ ^ 2 =
      ∑ i, ‖∑ q, c i q * star (M q i)‖ ^ 2 := by
  classical
  have hentry (x : δ × εA) (y : δ × εB) :
      labelContraction (fun (x : δ × εA) (y : δ × εB) q => c x.1 q) (flagIsometry u * Mᴴ) x y =
        if x.1 = y.1 then u x.1 (x.2, y.2) * ∑ q, c x.1 q * star (M q x.1) else 0 := by
    simp only [labelContraction, Matrix.mul_apply, flagIsometry_apply, Matrix.conjTranspose_apply]
    split_ifs with h
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_eq_single x.1]
      · simp [h]
        ring
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    · refine Finset.sum_eq_zero fun q _ => ?_
      rw [Finset.sum_eq_zero]
      · simp
      · intro j _
        by_cases h1 : x.1 = j
        · subst h1
          simp [Ne.symm h]
        · simp [h1]
  rw [frobNorm_sq]
  simp only [Fintype.sum_prod_type, hentry]
  have hui (i : δ) : ∑ a, ∑ b, ‖u i (a, b)‖ ^ 2 = 1 := by
    have := hu i
    simp only [IsUnitVector, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq] at this
    exact this
  calc (∑ i, ∑ a, ∑ j, ∑ b,
        ‖if i = j then u i (a, b) * ∑ q, c i q * star (M q i) else 0‖ ^ 2)
      = ∑ i, ∑ a, ∑ b, ‖u i (a, b) * ∑ q, c i q * star (M q i)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
    _ = ∑ i, ∑ a, ∑ b, ‖∑ q, c i q * star (M q i)‖ ^ 2 * ‖u i (a, b)‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => by rw [norm_mul, mul_pow, mul_comm]
    _ = ∑ i, ‖∑ q, c i q * star (M q i)‖ ^ 2 * ∑ a, ∑ b, ‖u i (a, b)‖ ^ 2 := by
        simp only [Finset.mul_sum]
    _ = _ := by simp [hui]

end Frozen

section Bell

variable {d : ℕ}

/-- Bob's correction for label `i`: `√d` times the coefficient matrix of the
`i`-th generalized Bell column. -/
noncomputable def bellCorrection (d : ℕ) [NeZero d] (i : Fin d × Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => (Real.sqrt (d : ℝ) : ℂ) * generalizedBellFinMatrix d (a, b) i

theorem norm_sq_bellCorrection_entry_sum (d : ℕ) [NeZero d] (i : Fin d × Fin d) :
    ∑ q : Fin d × Fin d, ‖bellCorrection d i q.1 q.2‖ ^ 2 = d := by
  have hcol := congrFun (congrFun (isIsometry_generalizedBellFinMatrix d) i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hcol
  have hsum : ∑ q : Fin d × Fin d, ‖generalizedBellFinMatrix d q i‖ ^ 2 = 1 := by
    have h := congrArg Complex.re hcol
    simp only [Complex.re_sum, Complex.one_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
  simp only [bellCorrection, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg d), ← Finset.mul_sum]
  rw [show (fun q : Fin d × Fin d => ‖generalizedBellFinMatrix d (q.1, q.2) i‖ ^ 2) =
    fun q => ‖generalizedBellFinMatrix d q i‖ ^ 2 from rfl, hsum, mul_one]

theorem bellCorrection_mul_conjTranspose (d : ℕ) [NeZero d] (i : Fin d × Fin d) :
    bellCorrection d i * (bellCorrection d i)ᴴ = 1 := by
  have hg := pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram d i
  ext a a'
  have h := congrFun (congrFun hg a) a'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pvmConjugateColumnMatrix,
    Matrix.of_apply, Matrix.diagonal_apply, star_star, Fintype.card_fin] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, bellCorrection, Matrix.one_apply,
    star_mul', Complex.star_def, Complex.conj_ofReal]
  have hsq : (Real.sqrt (d : ℝ) : ℂ) * (Real.sqrt (d : ℝ) : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    norm_cast
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hconj := congrArg (starRingEnd ℂ) h
  simp only [map_sum, map_mul, Complex.conj_conj, apply_ite (starRingEnd ℂ), map_zero,
    map_inv₀, Complex.conj_ofReal, Complex.star_def] at hconj
  have hfac : ∑ b, (Real.sqrt (d : ℝ) : ℂ) * generalizedBellFinMatrix d (a, b) i *
        ((Real.sqrt (d : ℝ) : ℂ) * (starRingEnd ℂ) (generalizedBellFinMatrix d (a', b) i)) =
      ((Real.sqrt (d : ℝ) : ℂ) * (Real.sqrt (d : ℝ) : ℂ)) *
        ∑ b, generalizedBellFinMatrix d (a, b) i *
          (starRingEnd ℂ) (generalizedBellFinMatrix d (a', b) i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hfac, hsq, hconj]
  split_ifs
  · push_cast
    field_simp
  · simp

theorem isIsometry_bellCorrection (d : ℕ) [NeZero d] (i : Fin d × Fin d) :
    IsIsometry (bellCorrection d i) :=
  mul_eq_one_comm.mp (bellCorrection_mul_conjTranspose d i)

theorem isIsometry_bellCorrection_transpose (d : ℕ) [NeZero d] (i : Fin d × Fin d) :
    IsIsometry (bellCorrection d i)ᵀ := by
  rw [IsIsometry]
  change ((bellCorrection d i)ᴴ)ᵀ * (bellCorrection d i)ᵀ = 1
  rw [← Matrix.transpose_mul, bellCorrection_mul_conjTranspose, Matrix.transpose_one]

end Bell

section Protocol

variable {d : ℕ} {δ εA εB ρA ρB κA κB μA μB : Type*}
variable [Fintype δ] [Fintype εA] [Fintype εB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

omit [Fintype δ] [Fintype εA] [Fintype εB] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
theorem nearBellReferenceProjection_eq_labelContraction
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (F : Matrix ((δ × εA) × (δ × εB)) (Fin d × Fin d) ℂ) :
    nearBellReferenceProjection C F =
      labelContraction (fun (_ : δ × εA) (y : δ × εB) q => C y.1 q.1 q.2) F := by
  ext x y
  simp [nearBellReferenceProjection, labelContraction, Fintype.sum_prod_type]

omit [Fintype δ] [Fintype εA] [Fintype εB] [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
  [Fintype μA] [Fintype μB] [DecidableEq εA] [DecidableEq εB] [DecidableEq ρA] [DecidableEq ρB]
  [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB] in
/-- On a flagged dilation only label-diagonal entries survive, so a
contraction controlled by Bob's label equals the one controlled by Alice's. -/
theorem labelContraction_flag_right_eq_left [Fintype δ] {Q : Type*} [Fintype Q]
    (c : δ → Q → ℂ) (u : δ → εA × εB → ℂ) (M : Matrix Q δ ℂ) :
    labelContraction (fun (_ : δ × εA) (y : δ × εB) q => c y.1 q) (flagIsometry u * Mᴴ) =
      labelContraction (fun (x : δ × εA) (_ : δ × εB) q => c x.1 q) (flagIsometry u * Mᴴ) := by
  ext x y
  by_cases h : x.1 = y.1
  · simp [labelContraction, h]
  · have hz : ∀ q, (flagIsometry u * Mᴴ) (x, y) q = 0 := by
      intro q
      simp only [Matrix.mul_apply, flagIsometry_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h1 : x.1 = j
      · subst h1
        simp [Ne.symm h]
      · simp [h1]
    simp [labelContraction, hz]

set_option linter.unusedSectionVars false in
/-- The mirrored contraction, controlled by Alice's label, is a
contraction controlled by Bob's label for the party-swapped protocol. -/
theorem norm_mirrorContraction_globalIsometry
    (C : δ → Matrix (Fin d) (Fin d) ℂ) (η : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ) (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix (δ × εA) (κA × μB) ℂ) (DB : Matrix (δ × εB) (κB × μA) ℂ) :
    ‖labelContraction (fun (x : δ × εA) (_ : δ × εB) q => C x.1 q.2 q.1)
        (globalIsometry η VA VB DA DB)‖ =
      ‖nearBellReferenceProjection C
        (globalIsometry (fun q : ρB × ρA => η (q.2, q.1)) VB VA DB DA)‖ := by
  have h : labelContraction (fun (x : δ × εA) (_ : δ × εB) q => C x.1 q.2 q.1)
      (globalIsometry η VA VB DA DB) =
      (nearBellReferenceProjection C
        (globalIsometry (fun q : ρB × ρA => η (q.2, q.1)) VB VA DB DA))ᵀ := by
    ext x y
    simp only [Matrix.transpose_apply, nearBellReferenceProjection, labelContraction,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have := globalIsometry_swap η VA VB DA DB (x, y) (b, a)
    simp only at this
    rw [this]
  rw [h, Matrix.frobenius_norm_transpose]

set_option maxHeartbeats 1000000 in
/-- **Message floors near a maximally entangled basis.** If the basis matrix
lies within Frobenius distance `d/4` of the generalized Bell basis and the PVM
score is at least `1 - ε` with `0 ≤ ε ≤ 1/256`, then both message dimensions
satisfy `d² ≤ 2 m²`. Original registers are arbitrary finite types. -/
theorem PureProtocol.sq_le_two_mul_message_sq_of_near_bell [NeZero d]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hM : IsIsometry M)
    (hnear : ‖M - generalizedBellFinMatrix d‖ ≤ (d : ℝ) / 4) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 256) (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    (d : ℝ) ^ 2 ≤ 2 * (Fintype.card μA : ℝ) ^ 2 ∧
      (d : ℝ) ^ 2 ≤ 2 * (Fintype.card μB : ℝ) ^ 2 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set B := generalizedBellFinMatrix d
  have hB : IsIsometry B := isIsometry_generalizedBellFinMatrix d
  -- frozen dilation
  obtain ⟨u, hu, -, hclose⟩ := P.exists_pvm_frozen hM
    ((hasFootprint_iff _ P.resource).mpr le_rfl) ⟨hε0, by linarith⟩ hscore
  have hsqrt : Real.sqrt (Fintype.card (Fin d × Fin d) : ℝ) = d := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact Real.sqrt_mul_self hdR.le
  rw [hsqrt, div_le_iff₀ hdR] at hclose
  set F := P.globalIsometry
  set F₀ := flagIsometry u * Mᴴ
  -- overlaps with the Bell columns
  let t : Fin d × Fin d → ℂ := fun i => ∑ q, B q i * star (M q i)
  have hsumt : (∑ i, (t i).re) = (frobInner M B).re := by
    simp only [t, frobInner, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have hcard : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by
    simp [Fintype.card_prod, sq]
  have hMn := norm_sq_of_isIsometry hM
  have hBn := norm_sq_of_isIsometry hB
  rw [hcard] at hMn hBn
  have hdist := frobNorm_sub_sq M B
  have hconj : (frobInner B M).re = (frobInner M B).re := by
    have := congrArg Complex.re (frobInner_conj M B)
    simpa [Complex.star_def, Complex.conj_re] using this.symm
  have hnear2 : ‖M - B‖ ^ 2 ≤ (d : ℝ) ^ 2 / 16 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hnear 2
    nlinarith
  have hRe : (31 / 32 : ℝ) * (d : ℝ) ^ 2 ≤ ∑ i, (t i).re := by
    rw [hsumt, ← hconj]
    nlinarith
  -- the frozen contraction mass
  let c : Fin d × Fin d → Fin d × Fin d → ℂ := fun i q => bellCorrection d i q.1 q.2
  have hS : ‖labelContraction (fun (x : (Fin d × Fin d) × εA) (_ : (Fin d × Fin d) × εB) q =>
      c x.1 q) F₀‖ ^ 2 = d * ∑ i, ‖t i‖ ^ 2 := by
    rw [labelContraction_flag_norm_sq c u hu M, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (∑ q, c i q * star (M q i)) = (Real.sqrt (d : ℝ) : ℂ) * t i := by
      simp only [c, t, bellCorrection, Finset.mul_sum, mul_assoc]
      rfl
    rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt hdR.le]
  have hCS : (∑ i, (t i).re) ^ 2 ≤ (d : ℝ) ^ 2 * ∑ i, ‖t i‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d × Fin d => (1 : ℝ))
      (fun i => (t i).re)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    have hle : ∀ i, (t i).re ^ 2 ≤ ‖t i‖ ^ 2 := fun i => by
      have := Complex.abs_re_le_norm (t i)
      nlinarith [abs_nonneg (t i).re, sq_abs (t i).re]
    calc (∑ i, (t i).re) ^ 2 ≤ ((d * d : ℕ) : ℝ) * ∑ i, (t i).re ^ 2 := h
      _ ≤ (d : ℝ) ^ 2 * ∑ i, ‖t i‖ ^ 2 := by
        push_cast
        rw [← sq]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hle i) (by positivity)
  have hS0 : (31 / 32 : ℝ) ^ 2 * (d : ℝ) ^ 3 ≤
      ‖labelContraction (fun (x : (Fin d × Fin d) × εA) (_ : (Fin d × Fin d) × εB) q =>
        c x.1 q) F₀‖ ^ 2 := by
    rw [hS]
    have h1 : ((31 / 32 : ℝ) * (d : ℝ) ^ 2) ^ 2 ≤ (∑ i, (t i).re) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hRe 2
    have h2 : (31 / 32 : ℝ) ^ 2 * (d : ℝ) ^ 2 ≤ ∑ i, ‖t i‖ ^ 2 := by
      have := h1.trans hCS
      have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
      nlinarith
    nlinarith
  -- a generic estimate for both labels
  have hcorr : ∀ (G : Matrix (((Fin d × Fin d) × εA) × ((Fin d × Fin d) × εB)) (Fin d × Fin d) ℂ)
      (g : ((Fin d × Fin d) × εA) → ((Fin d × Fin d) × εB) → (Fin d × Fin d) → ℂ),
      (∀ x y, ∑ q, ‖g x y q‖ ^ 2 ≤ d) →
      labelContraction g F₀ = labelContraction
        (fun (x : (Fin d × Fin d) × εA) (_ : (Fin d × Fin d) × εB) q => c x.1 q) F₀ →
      (31 / 32 : ℝ) ^ 2 * (d : ℝ) ^ 3 ≤ ‖labelContraction g F₀‖ ^ 2 ∧
        ‖labelContraction g F - labelContraction g F₀‖ ^ 2 ≤ (d : ℝ) ^ 3 / 64 := by
    intro G g hg heq
    refine ⟨heq ▸ hS0, ?_⟩
    rw [← labelContraction_sub]
    have h1 := labelContraction_norm_sq_le g hg (F - F₀)
    have h2 : ‖F - F₀‖ ^ 2 ≤ (d : ℝ) ^ 2 / 64 := by
      have hs : Real.sqrt ε ≤ 1 / 16 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
      have h3 : ‖F - F₀‖ ≤ (d : ℝ) / 8 := by nlinarith [Real.sqrt_nonneg ε]
      have := pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith
    nlinarith
  have hfinal : ∀ X Y Z m : ℝ, 0 ≤ X → 0 ≤ Y → 0 ≤ Z → 0 ≤ m →
      (31 / 32 : ℝ) ^ 2 * (d : ℝ) ^ 3 ≤ Y ^ 2 → Z ^ 2 ≤ (d : ℝ) ^ 3 / 64 → Y - Z ≤ X →
      X ^ 2 ≤ (d : ℝ) * m ^ 2 → (d : ℝ) ^ 2 ≤ 2 * m ^ 2 := by
    intro X Y Z m hX hY hZ hm hY2 hZ2 hXYZ hX2
    set w := Real.sqrt ((d : ℝ) ^ 3)
    have hw : w ^ 2 = (d : ℝ) ^ 3 := Real.sq_sqrt (by positivity)
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hYw : 31 / 32 * w ≤ Y := by
      refine (pow_le_pow_iff_left₀ (by positivity) hY (by decide : 2 ≠ 0)).mp ?_
      rw [mul_pow, hw]
      exact hY2
    have hZw : Z ≤ w / 8 := by
      refine (pow_le_pow_iff_left₀ hZ (by positivity) (by decide : 2 ≠ 0)).mp ?_
      rw [div_pow, hw]
      linarith only [hZ2]
    have hXw : 27 / 32 * w ≤ X := by linarith only [hYw, hZw, hXYZ]
    have hX2' : (27 / 32 * w) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hXw 2
    rw [mul_pow, hw] at hX2'
    have h3 : (d : ℝ) * ((729 / 1024) * (d : ℝ) ^ 2) ≤ d * m ^ 2 := by
      have : (27 / 32 : ℝ) ^ 2 * (d : ℝ) ^ 3 = (d : ℝ) * ((729 / 1024) * (d : ℝ) ^ 2) := by ring
      linarith only [this, hX2', hX2]
    have h4 := le_of_mul_le_mul_left h3 hdR
    linarith only [h4, sq_nonneg (d : ℝ)]
  have hcA : ∀ x y, ∑ q, ‖(fun (_ : (Fin d × Fin d) × εA) (y : (Fin d × Fin d) × εB) (q : Fin d × Fin d) =>
      bellCorrection d y.1 q.1 q.2) x y q‖ ^ 2 ≤ d := fun x y =>
    (norm_sq_bellCorrection_entry_sum d y.1).le
  have hcB : ∀ x y, ∑ q, ‖(fun (x : (Fin d × Fin d) × εA) (_ : (Fin d × Fin d) × εB) (q : Fin d × Fin d) =>
      (bellCorrection d x.1)ᵀ q.2 q.1) x y q‖ ^ 2 ≤ d := fun x y =>
    (norm_sq_bellCorrection_entry_sum d x.1).le
  constructor
  · -- Alice's message, through Bob's correction
    obtain ⟨hY, hZ⟩ := hcorr F _ hcA (labelContraction_flag_right_eq_left c u M)
    have hX := nearBellReferenceProjection_messageA_upper hd (bellCorrection d) P.resource
      P.encA P.encB P.decA P.decB (isIsometry_bellCorrection d) P.resource_unit
      P.encA_isometry P.encB_isometry P.decA_isometry P.decB_isometry
    rw [nearBellReferenceProjection_eq_labelContraction] at hX
    refine hfinal _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (by positivity)
      hY hZ ?_ hX
    have := norm_sub_norm_le (labelContraction (fun (_ : (Fin d × Fin d) × εA)
      (y : (Fin d × Fin d) × εB) q => bellCorrection d y.1 q.1 q.2) F₀)
      (labelContraction (fun (_ : (Fin d × Fin d) × εA)
      (y : (Fin d × Fin d) × εB) q => bellCorrection d y.1 q.1 q.2) F)
    rw [norm_sub_rev] at this
    exact sub_le_comm.mp this
  · -- Bob's message, through Alice's correction
    obtain ⟨hY, hZ⟩ := hcorr F _ hcB (by
      ext x y
      simp only [labelContraction, c, Matrix.transpose_apply])
    have hη : IsUnitVector (fun q : ρB × ρA => P.resource (q.2, q.1)) :=
      (Fintype.sum_equiv (Equiv.prodComm ρB ρA) _ _ (fun _ => rfl)).trans P.resource_unit
    have hX := nearBellReferenceProjection_messageA_upper hd (fun i => (bellCorrection d i)ᵀ)
      (fun q : ρB × ρA => P.resource (q.2, q.1)) P.encB P.encA P.decB P.decA
      (isIsometry_bellCorrection_transpose d) hη
      P.encB_isometry P.encA_isometry P.decB_isometry P.decA_isometry
    rw [← norm_mirrorContraction_globalIsometry] at hX
    refine hfinal _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (by positivity)
      hY hZ ?_ hX
    have := norm_sub_norm_le (labelContraction (fun (x : (Fin d × Fin d) × εA)
      (_ : (Fin d × Fin d) × εB) (q : Fin d × Fin d) => (bellCorrection d x.1)ᵀ q.2 q.1) F₀)
      (labelContraction (fun (x : (Fin d × Fin d) × εA)
      (_ : (Fin d × Fin d) × εB) (q : Fin d × Fin d) => (bellCorrection d x.1)ᵀ q.2 q.1) F)
    rw [norm_sub_rev] at this
    exact sub_le_comm.mp this

end Protocol

end NLQCLean

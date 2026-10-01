/-
The unitary score: bounds, exactness and mixed-resource affinity.
-/
import NLQCLean.LinearAlgebra.RealCoordinates
import NLQCLean.Models.Channels
import NLQCLean.Models.Resource
import NLQCLean.Models.OneRound
import NLQCLean.Rigidity.FrozenDilation

/-!
# The unitary score `f(Φ, U)`, its bounds, and exact freezing

`NLQCLean.Models.Channels` defines the score `q_U` of
`rem:scalar-approximation-input` and proves the slice identity
`NLQCLean.scoreU_channelOf`. Grouping the factors of the normalized Choi
vector `|F⟩⟩` as logical output, logical reference and discarded environment
reads that identity as a statement about one explicit vector:

  `z = (⟨⟨U| ⊗ I)|F⟩⟩`,   `z_e = D⁻¹ Tr(U† F_e)`,   `f(Φ,U) = ‖z‖²`.

`NLQCLean.scoreVector` is that `z`.

## The one identity everything follows from

Write `R_e = F_e - z_e U` for the component of each environment slice
orthogonal to the target.  Because `⟨U, R_e⟩ = ⟨U,F_e⟩ - z_e‖U‖² = 0`
identically, Pythagoras applies slice by slice, and summing gives

  `Σ_e ‖R_e‖² = D (1 - f(Φ,U))`   (`NLQCLean.sum_frobNormSq_scoreResidual`).

This single equation yields the main score properties:

* `f ≤ 1`, because the left side is a sum of squares;
* `f = 1 ↔ every R_e = 0 ↔ F = E_z U`;
* and hence `f = 1 → channelOf F = adConj U`.

The reverse implication follows from `NLQCLean.scoreU_adConj_self`.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section Slices

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
/-- The Frobenius inner product decomposes over environment slices. -/
theorem sum_frobInner_sliceAt (F G : Matrix (κ × ε) ι ℂ) :
    ∑ e, frobInner (sliceAt F e) (sliceAt G e) = frobInner F G := by
  simp only [frobInner, sliceAt_apply]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
/-- The squared Frobenius norm decomposes over environment slices. -/
theorem sum_frobNormSq_sliceAt (F : Matrix (κ × ε) ι ℂ) :
    ∑ e, frobNormSq (sliceAt F e) = frobNormSq F := by
  rw [frobNormSq, ← sum_frobInner_sliceAt F F, Complex.re_sum]
  rfl

end Slices

section ScoreVector

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

/-- The environment vector `z = (⟨⟨U| ⊗ I)|F⟩⟩`, in slice form
`z_e = D⁻¹ Tr(U† F_e)`. -/
noncomputable def scoreVector (U : Matrix κ ι ℂ) (F : Matrix (κ × ε) ι ℂ) (e : ε) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * frobInner U (sliceAt F e)

omit [DecidableEq κ] [DecidableEq ε] in
/-- The score is the squared norm of the environment vector. -/
theorem scoreU_eq_sum_normSq_scoreVector (U : Matrix κ ι ℂ) (F : Matrix (κ × ε) ι ℂ) :
    scoreU U (channelOf F) = ∑ e, Complex.normSq (scoreVector U F e) :=
  scoreU_channelOf U F

/-- The component of the environment slice `F_e` orthogonal to the target. -/
noncomputable def scoreResidual (U : Matrix κ ι ℂ) (F : Matrix (κ × ε) ι ℂ) (e : ε) :
    Matrix κ ι ℂ :=
  sliceAt F e - scoreVector U F e • U

omit [Fintype ε] [DecidableEq ε] in
omit [DecidableEq κ] in
/-- The residual is orthogonal to the target: `⟨U, R_e⟩ = 0`, for every `F`. -/
theorem frobInner_scoreResidual [Nonempty ι] {U : Matrix κ ι ℂ} (hU : IsIsometry U)
    (F : Matrix (κ × ε) ι ℂ) (e : ε) :
    frobInner U (scoreResidual U F e) = 0 := by
  have hD : (Fintype.card ι : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  rw [scoreResidual, frobInner_sub_right, frobInner_smul_right,
    frobInner_self_of_isometry hU, scoreVector]
  field_simp
  ring

omit [DecidableEq ι] [DecidableEq κ] in
/-- Expanding a self inner product against a scalar multiple. -/
theorem frobInner_self_sub_smul (z : ℂ) (A U : Matrix κ ι ℂ) :
    frobInner (A - z • U) (A - z • U)
      = frobInner A A - star z * frobInner U A - z * frobInner A U
        + star z * z * frobInner U U := by
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right,
    frobInner_smul_left, frobInner_smul_right, frobInner_smul_right,
    frobInner_smul_left]
  ring

omit [DecidableEq κ] [DecidableEq ε] in
/-- The Pythagorean identity: the total squared norm of the
orthogonal residuals measures exactly the score defect. -/
theorem sum_frobNormSq_scoreResidual [Nonempty ι] {U : Matrix κ ι ℂ}
    {F : Matrix (κ × ε) ι ℂ} (hU : IsIsometry U) (hF : IsIsometry F) :
    ∑ e, frobNormSq (scoreResidual U F e)
      = (Fintype.card ι : ℝ) * (1 - scoreU U (channelOf F)) := by
  have hDc : (Fintype.card ι : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hslice : ∀ e : ε, frobInner (scoreResidual U F e) (scoreResidual U F e)
      = frobInner (sliceAt F e) (sliceAt F e)
        - (Fintype.card ι : ℂ) * ((Complex.normSq (scoreVector U F e) : ℝ) : ℂ) := by
    intro e
    have hUA : frobInner U (sliceAt F e)
        = (Fintype.card ι : ℂ) * scoreVector U F e := by
      rw [scoreVector]; field_simp
    have hAU : frobInner (sliceAt F e) U
        = (Fintype.card ι : ℂ) * star (scoreVector U F e) := by
      rw [← frobInner_conj, hUA]
      simp [mul_comm]
    show frobInner (sliceAt F e - scoreVector U F e • U)
        (sliceAt F e - scoreVector U F e • U) = _
    rw [frobInner_self_sub_smul, hUA, hAU, frobInner_self_of_isometry hU,
      Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply]
    ring
  have hcast : ∑ e, frobNormSq (scoreResidual U F e)
      = (∑ e, frobInner (scoreResidual U F e) (scoreResidual U F e)).re := by
    rw [Complex.re_sum]; rfl
  have hsum : ∑ e, frobInner (scoreResidual U F e) (scoreResidual U F e)
      = (Fintype.card ι : ℂ)
          - (Fintype.card ι : ℂ) * ((scoreU U (channelOf F) : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun e _ => hslice e), Finset.sum_sub_distrib,
      sum_frobInner_sliceAt, frobInner_self_of_isometry hF, ← Finset.mul_sum,
      scoreU_eq_sum_normSq_scoreVector]
    push_cast
    ring
  rw [hcast, hsum]
  simp
  ring

end ScoreVector

section Bounds

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

omit [DecidableEq κ] [DecidableEq ε] in
/-- **The score of a physical protocol is at most one.**  Immediate from the
Pythagorean identity: the residuals contribute a nonnegative amount. -/
theorem scoreU_le_one [Nonempty ι] {U : Matrix κ ι ℂ} {F : Matrix (κ × ε) ι ℂ}
    (hU : IsIsometry U) (hF : IsIsometry F) :
    scoreU U (channelOf F) ≤ 1 := by
  have hid := sum_frobNormSq_scoreResidual hU hF
  have hnn : (0:ℝ) ≤ ∑ e, frobNormSq (scoreResidual U F e) :=
    Finset.sum_nonneg fun e _ => frobNormSq_nonneg _
  rw [hid] at hnn
  have hD : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith

omit [DecidableEq κ] [DecidableEq ε] in
/-- **`0 ≤ f ≤ 1`** for a physical protocol. -/
theorem scoreU_mem_Icc [Nonempty ι] {U : Matrix κ ι ℂ} {F : Matrix (κ × ε) ι ℂ}
    (hU : IsIsometry U) (hF : IsIsometry F) :
    scoreU U (channelOf F) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨scoreU_channelOf_nonneg U F, scoreU_le_one hU hF⟩

end Bounds

section Exactness

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

omit [Fintype ε] [DecidableEq ι] [DecidableEq ε] in
omit [Fintype ι] in
/-- The entries of a frozen dilation `E_z U`. -/
theorem insertVector_mul_apply (z : ε → ℂ) (U : Matrix κ ι ℂ) (p : κ × ε) (i : ι) :
    (insertVector κ z * U) p i = z p.2 * U p.1 i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p.1]
  · rw [insertVector_apply]; simp
  · intro k' _ hk'
    rw [insertVector_apply]
    simp [Ne.symm hk']
  · intro h
    exact absurd (Finset.mem_univ p.1) h

omit [Fintype ε] [DecidableEq ι] [DecidableEq ε] in
omit [Fintype ι] in
/-- `F = E_z U` says exactly that every environment slice is the corresponding
multiple of the target. -/
theorem eq_insertVector_mul_iff (z : ε → ℂ) (U : Matrix κ ι ℂ)
    (F : Matrix (κ × ε) ι ℂ) :
    F = insertVector κ z * U ↔ ∀ e, sliceAt F e = z e • U := by
  constructor
  · rintro rfl e
    ext k i
    rw [sliceAt_apply, insertVector_mul_apply]
    simp
  · intro h
    ext p i
    have hp := congrArg (fun M => M p.1 i) (h p.2)
    simp only [sliceAt_apply, Matrix.smul_apply, smul_eq_mul] at hp
    rw [insertVector_mul_apply]
    exact hp

omit [DecidableEq ε] in
/-- Score one is equivalent to exact freezing, `F = E_z U`. -/
theorem scoreU_eq_one_iff [Nonempty ι] {U : Matrix κ ι ℂ} {F : Matrix (κ × ε) ι ℂ}
    (hU : IsIsometry U) (hF : IsIsometry F) :
    scoreU U (channelOf F) = 1 ↔ F = insertVector κ (scoreVector U F) * U := by
  have hD : ((Fintype.card ι : ℝ)) ≠ 0 := by
    have : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt this
  have hid := sum_frobNormSq_scoreResidual hU hF
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at hid
    have hzero : ∀ e, frobNormSq (scoreResidual U F e) = 0 := fun e =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun e' _ => frobNormSq_nonneg _)).mp hid e (Finset.mem_univ e)
    rw [eq_insertVector_mul_iff]
    intro e
    have := (frobNormSq_eq_zero_iff _).mp (hzero e)
    rwa [scoreResidual, sub_eq_zero] at this
  · intro h
    have hzero : ∑ e, frobNormSq (scoreResidual U F e) = 0 := by
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [frobNormSq_eq_zero_iff, scoreResidual,
        (eq_insertVector_mul_iff _ _ _).mp h e, sub_self]
    rw [hzero] at hid
    have := (mul_eq_zero.mp hid.symm).resolve_left hD
    linarith [this]

omit [DecidableEq κ] [DecidableEq ε] in
/-- At score one the environment vector is a unit vector.  This is a
restatement of the slice identity, so it needs no isometry hypothesis. -/
theorem isUnitVector_scoreVector_iff (U : Matrix κ ι ℂ) (F : Matrix (κ × ε) ι ℂ) :
    IsUnitVector (scoreVector U F) ↔ scoreU U (channelOf F) = 1 := by
  rw [IsUnitVector, ← scoreU_eq_sum_normSq_scoreVector]

omit [DecidableEq ι] [DecidableEq ε] in
/-- A frozen dilation implements `Ad_U` exactly. -/
theorem channelOf_insertVector_mul {z : ε → ℂ} (hz : IsUnitVector z)
    (U : Matrix κ ι ℂ) :
    channelOf (insertVector κ z * U) = adConj U := by
  have hzsum : ∑ e, z e * star (z e) = 1 := (isUnitVector_iff_sum z).mp hz
  refine LinearMap.ext fun ρ => ?_
  ext k k'
  have hGrho : ∀ (e : ε) (j : ι), ((insertVector κ z * U) * ρ) (k, e) j
      = z e * (U * ρ) k j := by
    intro e j
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [insertVector_mul_apply]; ring
  have hUUH : (U * ρ * Uᴴ) k k' = ∑ j, (U * ρ) k j * star (U k' j) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.conjTranspose_apply]
  have hentry : ∀ (e e' : ε),
      ((insertVector κ z * U) * ρ * (insertVector κ z * U)ᴴ) (k, e) (k', e')
        = z e * star (z e') * (U * ρ * Uᴴ) k k' := by
    intro e e'
    rw [Matrix.mul_apply, hUUH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hGrho, Matrix.conjTranspose_apply, insertVector_mul_apply, star_mul']
    ring
  show ptraceB κ ε _ k k' = _
  show ∑ e, ((insertVector κ z * U) * ρ * (insertVector κ z * U)ᴴ) (k, e) (k', e) = _
  rw [Finset.sum_congr rfl (fun e _ => hentry e e), ← Finset.sum_mul, hzsum, one_mul]
  rfl

omit [DecidableEq ε] in
/-- For a physical protocol the score is one exactly when its operational
channel is `Ad_U`. -/
theorem scoreU_eq_one_iff_channelOf_eq [Nonempty ι] {U : Matrix κ ι ℂ}
    {F : Matrix (κ × ε) ι ℂ} (hU : IsIsometry U) (hF : IsIsometry F) :
    scoreU U (channelOf F) = 1 ↔ channelOf F = adConj U := by
  constructor
  · intro h
    have hfact := (scoreU_eq_one_iff hU hF).mp h
    have hunit : IsUnitVector (scoreVector U F) :=
      (isUnitVector_scoreVector_iff U F).mpr h
    rw [hfact, channelOf_insertVector_mul hunit]
  · intro h
    rw [h]
    exact scoreU_adConj_self hU

end Exactness

section Smoothness

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {N : WithTop ℕ∞}

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
/-- The environment vector is a fixed linear combination of the entries of the
dilation, hence smooth in it. -/
theorem ContDiff.scoreVector (U : Matrix κ ι ℂ) (e : ε)
    {f : E → Matrix (κ × ε) ι ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => NLQCLean.scoreVector U (f x) e) := by
  have h : (fun x => NLQCLean.scoreVector U (f x) e)
      = fun x => (Fintype.card ι : ℂ)⁻¹
          * ∑ p : κ × ι, star (U p.1 p.2) * (f x) (p.1, e) p.2 := by
    funext x
    rw [NLQCLean.scoreVector, frobInner_eq_sum_prod]
    rfl
  rw [h]
  exact contDiff_const.mul (_root_.ContDiff.sum fun p _ =>
    contDiff_const.mul (NLQCLean.ContDiff.matrixEntry hf (p.1, e) p.2))

omit [DecidableEq κ] [DecidableEq ε] in
/-- **The score is smooth in the forward blocks.**  It is a finite sum of
squared moduli of linear functions of the dilation, so smoothness follows from finite-sum and polynomial calculus. -/
theorem ContDiff.scoreU_channelOf (U : Matrix κ ι ℂ)
    {f : E → Matrix (κ × ε) ι ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N (fun x => scoreU U (channelOf (f x))) := by
  have h : (fun x => scoreU U (channelOf (f x)))
      = fun x => ∑ e, Complex.normSq (NLQCLean.scoreVector U (f x) e) := by
    funext x; exact scoreU_eq_sum_normSq_scoreVector U (f x)
  rw [h]
  exact _root_.ContDiff.sum fun e _ =>
    NLQCLean.ContDiff.complexNormSq (NLQCLean.ContDiff.scoreVector U e hf)

omit [DecidableEq κ] [DecidableEq ε] in
/-- Continuity of the score in the forward blocks. -/
theorem continuous_scoreU_channelOf (U : Matrix κ ι ℂ)
    {f : E → Matrix (κ × ε) ι ℂ} (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) :
    Continuous (fun x => scoreU U (channelOf (f x))) :=
  (ContDiff.scoreU_channelOf U hf).continuous

end Smoothness

section MixedResources

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- The Choi matrix is real-affine in the channel. -/
theorem choiMatrix_sum_smul {n' : Type*} [Fintype n'] (w : n' → ℝ)
    (𝒩 : n' → Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (p q : κ × ι) :
    choiMatrix (∑ k, ((w k : ℂ)) • 𝒩 k) p q
      = ∑ k, ((w k : ℂ)) * choiMatrix (𝒩 k) p q := by
  simp only [choiMatrix_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq κ] in
/-- **The unitary score is real-affine in the channel**, the analogue of
`NLQCLean.scorePVM_sum_smul`. -/
theorem scoreU_sum_smul {n' : Type*} [Fintype n'] (U : Matrix κ ι ℂ) (w : n' → ℝ)
    (𝒩 : n' → Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    scoreU U (∑ k, ((w k : ℂ)) • 𝒩 k) = ∑ k, w k * scoreU U (𝒩 k) := by
  have hterm : ∀ p q : κ × ι,
      star (U p.1 p.2) * choiMatrix (∑ k, ((w k : ℂ)) • 𝒩 k) p q * U q.1 q.2
        = ∑ k, ((w k : ℂ)) *
            (star (U p.1 p.2) * choiMatrix (𝒩 k) p q * U q.1 q.2) := by
    intro p q
    rw [choiMatrix_sum_smul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hswap : ∑ p : κ × ι, ∑ q : κ × ι, ∑ k, ((w k : ℂ)) *
        (star (U p.1 p.2) * choiMatrix (𝒩 k) p q * U q.1 q.2)
      = ∑ k, ((w k : ℂ)) * ∑ p : κ × ι, ∑ q : κ × ι,
          star (U p.1 p.2) * choiMatrix (𝒩 k) p q * U q.1 q.2 := by
    calc ∑ p : κ × ι, ∑ q : κ × ι, ∑ k, ((w k : ℂ)) *
            (star (U p.1 p.2) * choiMatrix (𝒩 k) p q * U q.1 q.2)
        = ∑ p : κ × ι, ∑ k, ∑ q : κ × ι, ((w k : ℂ)) *
            (star (U p.1 p.2) * choiMatrix (𝒩 k) p q * U q.1 q.2) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ k, ∑ p : κ × ι, ∑ q : κ × ι, ((w k : ℂ)) *
            (star (U p.1 p.2) * choiMatrix (𝒩 k) p q * U q.1 q.2) := Finset.sum_comm
      _ = ∑ k, ((w k : ℂ)) * ∑ p : κ × ι, ∑ q : κ × ι,
            star (U p.1 p.2) * choiMatrix (𝒩 k) p q * U q.1 q.2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
  rw [scoreU]
  simp only [hterm]
  rw [hswap, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [scoreU, ← mul_assoc, mul_comm ((Fintype.card ι : ℂ)⁻¹) ((w k : ℂ)),
    mul_assoc, Complex.re_ofReal_mul]

omit [DecidableEq κ] in
/-- Some component of a convex combination scores at least as high as the
combination.  Mirrors `NLQCLean.exists_scorePVM_ge_of_convex`. -/
theorem exists_scoreU_ge_of_convex {n' : Type*} [Fintype n'] [Nonempty n']
    (U : Matrix κ ι ℂ) (w : n' → ℝ)
    (𝒩 : n' → Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    ∃ k, scoreU U (∑ j, ((w j : ℂ)) • 𝒩 j) ≤ scoreU U (𝒩 k) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
    (fun j => scoreU U (𝒩 j)) Finset.univ_nonempty
  refine ⟨k, ?_⟩
  rw [scoreU_sum_smul]
  calc
    ∑ j, w j * scoreU U (𝒩 j)
        ≤ ∑ j, w j * scoreU U (𝒩 k) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (hk j (Finset.mem_univ j)) (hw j)
    _ = scoreU U (𝒩 k) := by rw [← Finset.sum_mul, hsum, one_mul]

end MixedResources

section MixedProtocols

variable {ρA ρB ιA ιB ιA' ιB' κA κB μA μB εA εB : Type*} {n : ℕ}
variable [Fintype ρA] [Fintype ρB] [Fintype ιA] [Fintype ιB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq ιA] [DecidableEq ιB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq ιA'] [DecidableEq ιB'] in
/-- **The unitary score of a mixed-resource protocol is the weighted average of
the scores of its pure components**.  This specializes
`NLQCLean.scoreU_sum_smul` to the honest channel decomposition in
`NLQCLean.MixedResource.mixedChannel`. -/
theorem MixedResource.scoreU_mixedChannel
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) :
    scoreU U (m.mixedChannel VA VB DA DB) =
      ∑ k, m.weight k * scoreU U
        (operationalChannel (m.component k) VA VB DA DB) := by
  rw [MixedResource.mixedChannel, scoreU_sum_smul]

omit [DecidableEq ρA] [DecidableEq ρB] [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq ιA'] [DecidableEq ιB'] in
/-- **Component selection**: some pure component of a mixed-resource
protocol has unitary score at least that of the mixed protocol.  No
nonemptiness assumption on `Fin n` is needed; the convex weights summing to one
supply a positive-weight component. -/
theorem MixedResource.exists_component_scoreU_ge
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ)
    (U : Matrix (ιA' × ιB') (ιA × ιB) ℂ) :
    ∃ k, scoreU U (m.mixedChannel VA VB DA DB) ≤
      scoreU U (operationalChannel (m.component k) VA VB DA DB) := by
  have hpositive : ∃ k, 0 < m.weight k := by
    by_contra h
    push Not at h
    have hzero : ∀ k, m.weight k = 0 :=
      fun k => le_antisymm (h k) (m.weight_nonneg k)
    simpa [hzero] using m.weight_sum
  obtain ⟨k₀, _⟩ := hpositive
  let _ : Nonempty (Fin n) := ⟨k₀⟩
  rw [MixedResource.mixedChannel]
  exact exists_scoreU_ge_of_convex U m.weight
    (fun k => operationalChannel (m.component k) VA VB DA DB)
    m.weight_nonneg m.weight_sum

end MixedProtocols

end NLQCLean

import NLQCLean.Geometry.DirectVolume.Basic

/-!
# Direct image-volume route: outer perturbation of the source

A format with at most `c` constraints of degree at most `Δ` has source
`S = {x | ∀ t, 0 ≤ g_t(x)}` for `2c + 1` polynomials `g_t` of degree at most `Δ ≥ 2`: each
equation contributes `h` and `-h`, each inequality itself, then the ball constraint
`R² - ‖x‖²` and padding by the constant `1`. Lowering the levels to `b_t ∈ (-δ, 0]` gives
compact sets `S_b ⊇ S` inside the radius-`(R+1)` ball and inside any prescribed open
neighborhood of `S`. Roadmap step D3 (`D0-PROOF.md` §3–4).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Metric

variable {a c Δ : ℕ}

/-- **`def:format`.** A basic closed polynomial format: at most `c` polynomial equations and
weak inequalities, each of total degree at most `Δ`. -/
structure PolyFormat (a c Δ : ℕ) where
  numEquations : ℕ
  numInequalities : ℕ
  constraint_count : numEquations + numInequalities ≤ c
  equations : Fin numEquations → MvPolynomial (Fin a) ℝ
  inequalities : Fin numInequalities → MvPolynomial (Fin a) ℝ
  equations_degree : ∀ i, (equations i).totalDegree ≤ Δ
  inequalities_degree : ∀ i, (inequalities i).totalDegree ≤ Δ

/-- The set described by the format, with inequalities oriented as `g(x) ≥ 0`. -/
def PolyFormat.source (F : PolyFormat a c Δ) : Set (RealEuclidean a) :=
  {x | (∀ i, MvPolynomial.eval (fun j ↦ x j) (F.equations i) = 0) ∧
    (∀ i, 0 ≤ MvPolynomial.eval (fun j ↦ x j) (F.inequalities i))}

/-- The formats of the image-volume contract: twenty constraints of degree at most `100`. -/
def _root_.NLQCLean.PolynomialBasicClosedFormat.toPolyFormat (F : PolynomialBasicClosedFormat a) :
    PolyFormat a 20 100 :=
  ⟨F.numEquations, F.numInequalities, F.constraint_count, F.equations, F.inequalities,
    F.equations_degree, F.inequalities_degree⟩

@[simp] theorem _root_.NLQCLean.PolynomialBasicClosedFormat.toPolyFormat_source
    (F : PolynomialBasicClosedFormat a) : F.toPolyFormat.source = F.source := rfl

/-- Index of the ball constraint. -/
def ballIndex (F : PolyFormat a c Δ) : ℕ :=
  2 * F.numEquations + F.numInequalities

/-- The `2c + 1` level polynomials of a format, with ball radius `R`. -/
noncomputable def levelPolys (F : PolyFormat a c Δ) (R : ℝ) (t : Fin (2 * c + 1)) :
    MvPolynomial (Fin a) ℝ :=
  if h₁ : t.val < F.numEquations then F.equations ⟨t.val, h₁⟩
  else if h₂ : t.val < 2 * F.numEquations then
    -F.equations ⟨t.val - F.numEquations, by omega⟩
  else if h₃ : t.val < ballIndex F then
    F.inequalities ⟨t.val - 2 * F.numEquations, by unfold ballIndex at h₃; omega⟩
  else if t.val = ballIndex F then MvPolynomial.C (R ^ 2) - ∑ i, X i ^ 2
  else 1

theorem levelPolys_degree_le (hΔ : 2 ≤ Δ) (F : PolyFormat a c Δ) (R : ℝ) (t : Fin (2 * c + 1)) :
    (levelPolys F R t).totalDegree ≤ Δ := by
  unfold levelPolys
  split_ifs
  · exact F.equations_degree _
  · rw [totalDegree_neg]; exact F.equations_degree _
  · exact F.inequalities_degree _
  · refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; exact Nat.zero_le _) ?_)
    refine (totalDegree_finsetSum_le fun i _ => ?_)
    exact (totalDegree_pow _ 2).trans (by rw [totalDegree_X]; omega)
  · simp

theorem ballIndex_lt (F : PolyFormat a c Δ) : ballIndex F < 2 * c + 1 := by
  have := F.constraint_count; unfold ballIndex; omega

theorem evalE_levelPolys_ball (F : PolyFormat a c Δ) (R : ℝ) (x : RealEuclidean a) :
    evalE (levelPolys F R ⟨ballIndex F, ballIndex_lt F⟩) x = R ^ 2 - ‖x‖ ^ 2 := by
  have h1 : ¬ ballIndex F < F.numEquations := by unfold ballIndex; omega
  have h2 : ¬ ballIndex F < 2 * F.numEquations := by unfold ballIndex; omega
  simp only [levelPolys, h1, h2, lt_irrefl, dite_eq_right, not_false_eq_true, ite_true]
  simp [evalE, EuclideanSpace.real_norm_sq_eq]

variable {L : ℕ}

/-- The level source `S_b`. -/
def levelSource (g : Fin L → MvPolynomial (Fin a) ℝ) (b : Fin L → ℝ) :
    Set (RealEuclidean a) :=
  {x | ∀ t, b t ≤ evalE (g t) x}

theorem levelSource_antitone (g : Fin L → MvPolynomial (Fin a) ℝ) {b c : Fin L → ℝ}
    (h : ∀ t, c t ≤ b t) : levelSource g b ⊆ levelSource g c :=
  fun _ hx t => (h t).trans (hx t)

theorem isClosed_levelSource (g : Fin L → MvPolynomial (Fin a) ℝ) (b : Fin L → ℝ) :
    IsClosed (levelSource g b) := by
  have : levelSource g b = ⋂ t, {x | b t ≤ evalE (g t) x} := by ext; simp [levelSource]
  rw [this]
  exact isClosed_iInter fun t =>
    isClosed_le continuous_const (contDiff_evalE (g t)).continuous

/-- Nonnegativity of all level polynomials characterizes the source, given the
radius-`R` bound. -/
theorem source_eq_levelSource_zero (F : PolyFormat a c Δ) {R : ℝ}
    (h3 : F.source ⊆ closedBall 0 R) : F.source = levelSource (levelPolys F R) 0 := by
  ext x
  constructor
  · intro hx t
    simp only [Pi.zero_apply]
    unfold levelPolys
    split_ifs with h₁ h₂ h₃ h₄
    · exact (hx.1 _).ge
    · simp [evalE, hx.1 ⟨t.val - F.numEquations, by omega⟩]
    · exact hx.2 _
    · have hb : ‖x‖ ≤ R := by simpa using h3 hx
      have := evalE_levelPolys_ball F R x
      simp only [levelPolys] at this
      have h1 : ¬ ballIndex F < F.numEquations := by unfold ballIndex; omega
      have h2 : ¬ ballIndex F < 2 * F.numEquations := by unfold ballIndex; omega
      simp only [evalE] at this ⊢
      simp only [map_sub, map_sum, map_pow, eval_C, eval_X] at this ⊢
      have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hb 2
      rw [EuclideanSpace.real_norm_sq_eq] at hsq
      linarith
    · simp [evalE]
  · intro hx
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hp := hx ⟨i.val, by have := F.constraint_count; omega⟩
      have hn := hx ⟨F.numEquations + i.val, by have := F.constraint_count; omega⟩
      simp only [Pi.zero_apply, levelPolys] at hp hn
      rw [dite_eq_left i.isLt] at hp
      rw [dite_eq_right (by omega), dite_eq_left (by omega)] at hn
      simp only [Nat.add_sub_cancel_left, Fin.eta, evalE, map_neg] at hp hn
      linarith
    · have hj := hx ⟨2 * F.numEquations + j.val, by have := F.constraint_count; omega⟩
      simp only [Pi.zero_apply, levelPolys] at hj
      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by unfold ballIndex; omega)] at hj
      simpa [evalE] using hj

/-- **Outer perturbation (L1).** For every open `U ⊇ S` there is `δ ∈ (0, 1]` such
that for all levels `b_t ∈ (-δ, 0]` the level source contains `S`, lies in the
radius-`(R+1)` ball, is compact and lies in `U`. -/
theorem exists_levelFamily (F : PolyFormat a c Δ) {R : ℝ} (hR : 0 ≤ R)
    (h3 : F.source ⊆ closedBall 0 R) {U : Set (RealEuclidean a)} (hU : IsOpen U)
    (hSU : F.source ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ b : Fin (2 * c + 1) → ℝ, (∀ t, -δ < b t ∧ b t ≤ 0) →
      F.source ⊆ levelSource (levelPolys F R) b ∧
      levelSource (levelPolys F R) b ⊆ closedBall 0 (R + 1) ∧
      IsCompact (levelSource (levelPolys F R) b) ∧ levelSource (levelPolys F R) b ⊆ U := by
  set g := levelPolys F R with hg
  -- Levels `b_t ≥ -1` keep the source in the radius-`(R+1)` ball.
  have hball : ∀ b : Fin (2 * c + 1) → ℝ, (∀ t, -1 ≤ b t) →
      levelSource g b ⊆ closedBall 0 (R + 1) := by
    intro b hb x hx
    have h := hx ⟨ballIndex F, ballIndex_lt F⟩
    rw [hg, evalE_levelPolys_ball] at h
    have := hb ⟨ballIndex F, ballIndex_lt F⟩
    have hsq : ‖x‖ ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg x]
  have hcompact : ∀ b : Fin (2 * c + 1) → ℝ, (∀ t, -1 ≤ b t) → IsCompact (levelSource g b) :=
    fun b hb => (isCompact_closedBall 0 (R + 1)).of_isClosed_subset (isClosed_levelSource g b)
      (hball b hb)
  -- A level `-1/(n+1)` already maps into `U`.
  set K : ℕ → Set (RealEuclidean a) :=
    fun n => levelSource g (fun _ => -(1 / ((n : ℝ) + 1))) ∩ Uᶜ with hK
  have hKn : ∃ n, K n = ∅ := by
    by_contra hne
    push Not at hne
    have hdec : ∀ i, K (i + 1) ⊆ K i := by
      intro i x hx
      refine ⟨levelSource_antitone g (fun t => ?_) hx.1, hx.2⟩
      simp only [neg_le_neg_iff]
      gcongr
      linarith
    have hcl : ∀ i, IsClosed (K i) := fun i =>
      (isClosed_levelSource g _).inter hU.isClosed_compl
    have h0 : IsCompact (K 0) :=
      (hcompact _ fun _ => by norm_num).of_isClosed_subset (hcl 0) inter_subset_left
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hdec
      hne h0 hcl
    rw [mem_iInter] at hx
    have hxS : x ∈ F.source := by
      rw [source_eq_levelSource_zero F h3]
      intro t
      simp only [Pi.zero_apply]
      by_contra hneg
      push Not at hneg
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hneg)
      have := (hx n).1 t
      simp only at this
      linarith
    exact (hx 0).2 (hSU hxS)
  obtain ⟨n, hn⟩ := hKn
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, fun b hb => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  · rw [source_eq_levelSource_zero F h3]
    exact levelSource_antitone g fun t => (hb t).2
  · refine hball b fun t => ?_
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [(hb t).1]
  · refine hcompact b fun t => ?_
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [(hb t).1]
  · intro x hx
    by_contra hxU
    have : x ∈ K n := ⟨levelSource_antitone g (fun t => (hb t).1.le) hx, hxU⟩
    rw [hn] at this
    exact this

end NLQCLean.DirectVolume

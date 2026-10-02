import NLQCLean.Geometry.DirectVolume.Basic

/-!
# Direct image-volume route: outer perturbation of the source

The basic closed source `S` of a format is written as `{x | ∀ t, 0 ≤ g_t(x)}` for
41 polynomials `g_t` of degree at most 100: each equation contributes `h` and
`-h`, each inequality itself, then the ball constraint `9 - ‖x‖²` and padding by
the constant `1`. Lowering the levels to `b_t ∈ (-δ, 0]` gives compact sets
`S_b ⊇ S` inside the radius-4 ball and inside any prescribed open neighborhood
of `S`. Roadmap step D3 (`D0-PROOF.md` §3–4).
-/

namespace NLQCLean.DirectVolume

open MvPolynomial Set Metric

variable {a : ℕ}

/-- Index of the ball constraint. -/
def ballIndex (F : PolynomialBasicClosedFormat a) : ℕ :=
  2 * F.numEquations + F.numInequalities

/-- The 41 level polynomials of a format. -/
noncomputable def levelPolys (F : PolynomialBasicClosedFormat a) (t : Fin 41) :
    MvPolynomial (Fin a) ℝ :=
  if h₁ : t.val < F.numEquations then F.equations ⟨t.val, h₁⟩
  else if h₂ : t.val < 2 * F.numEquations then
    -F.equations ⟨t.val - F.numEquations, by omega⟩
  else if h₃ : t.val < ballIndex F then
    F.inequalities ⟨t.val - 2 * F.numEquations, by unfold ballIndex at h₃; omega⟩
  else if t.val = ballIndex F then C 9 - ∑ i, X i ^ 2
  else 1

theorem levelPolys_degree_le (F : PolynomialBasicClosedFormat a) (t : Fin 41) :
    (levelPolys F t).totalDegree ≤ 100 := by
  unfold levelPolys
  split_ifs
  · exact F.equations_degree _
  · rw [totalDegree_neg]; exact F.equations_degree _
  · exact F.inequalities_degree _
  · refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum_le fun i _ => ?_)
    exact (totalDegree_pow _ 2).trans (by rw [totalDegree_X]; norm_num)
  · simp

theorem ballIndex_lt (F : PolynomialBasicClosedFormat a) : ballIndex F < 41 := by
  have := F.constraint_count; unfold ballIndex; omega

theorem evalE_levelPolys_ball (F : PolynomialBasicClosedFormat a) (x : RealEuclidean a) :
    evalE (levelPolys F ⟨ballIndex F, ballIndex_lt F⟩) x = 9 - ‖x‖ ^ 2 := by
  have h1 : ¬ ballIndex F < F.numEquations := by unfold ballIndex; omega
  have h2 : ¬ ballIndex F < 2 * F.numEquations := by unfold ballIndex; omega
  simp only [levelPolys, h1, h2, lt_irrefl, dite_eq_right, not_false_eq_true, ite_true]
  simp [evalE, EuclideanSpace.real_norm_sq_eq]

/-- The level source `S_b`. -/
def levelSource (g : Fin 41 → MvPolynomial (Fin a) ℝ) (b : Fin 41 → ℝ) :
    Set (RealEuclidean a) :=
  {x | ∀ t, b t ≤ evalE (g t) x}

theorem levelSource_antitone (g : Fin 41 → MvPolynomial (Fin a) ℝ) {b c : Fin 41 → ℝ}
    (h : ∀ t, c t ≤ b t) : levelSource g b ⊆ levelSource g c :=
  fun _ hx t => (h t).trans (hx t)

theorem isClosed_levelSource (g : Fin 41 → MvPolynomial (Fin a) ℝ) (b : Fin 41 → ℝ) :
    IsClosed (levelSource g b) := by
  have : levelSource g b = ⋂ t, {x | b t ≤ evalE (g t) x} := by ext; simp [levelSource]
  rw [this]
  exact isClosed_iInter fun t =>
    isClosed_le continuous_const (contDiff_evalE (g t)).continuous

/-- Nonnegativity of all level polynomials characterizes the source, given the
radius-3 bound. -/
theorem source_eq_levelSource_zero (F : PolynomialBasicClosedFormat a)
    (h3 : F.source ⊆ closedBall 0 3) : F.source = levelSource (levelPolys F) 0 := by
  ext x
  constructor
  · intro hx t
    simp only [Pi.zero_apply]
    unfold levelPolys
    split_ifs with h₁ h₂ h₃ h₄
    · exact (hx.1 _).ge
    · simp [evalE, hx.1 ⟨t.val - F.numEquations, by omega⟩]
    · exact hx.2 _
    · have hb : ‖x‖ ≤ 3 := by simpa using h3 hx
      have := evalE_levelPolys_ball F x
      simp only [levelPolys] at this
      have h1 : ¬ ballIndex F < F.numEquations := by unfold ballIndex; omega
      have h2 : ¬ ballIndex F < 2 * F.numEquations := by unfold ballIndex; omega
      simp only [evalE] at this ⊢
      simp only [map_sub, map_sum, map_pow, eval_C, eval_X] at this ⊢
      have hsq : ‖x‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg x]
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
radius-4 ball, is compact and lies in `U`. -/
theorem exists_levelFamily (F : PolynomialBasicClosedFormat a)
    (h3 : F.source ⊆ closedBall 0 3) {U : Set (RealEuclidean a)} (hU : IsOpen U)
    (hSU : F.source ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ b : Fin 41 → ℝ, (∀ t, -δ < b t ∧ b t ≤ 0) →
      F.source ⊆ levelSource (levelPolys F) b ∧
      levelSource (levelPolys F) b ⊆ closedBall 0 4 ∧
      IsCompact (levelSource (levelPolys F) b) ∧ levelSource (levelPolys F) b ⊆ U := by
  set g := levelPolys F with hg
  -- Levels `b_t ≥ -1` keep the source in the radius-4 ball.
  have hball : ∀ b : Fin 41 → ℝ, (∀ t, -1 ≤ b t) → levelSource g b ⊆ closedBall 0 4 := by
    intro b hb x hx
    have h := hx ⟨ballIndex F, ballIndex_lt F⟩
    rw [hg, evalE_levelPolys_ball] at h
    have := hb ⟨ballIndex F, ballIndex_lt F⟩
    have hsq : ‖x‖ ^ 2 ≤ 16 := by linarith
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg x]
  have hcompact : ∀ b : Fin 41 → ℝ, (∀ t, -1 ≤ b t) → IsCompact (levelSource g b) :=
    fun b hb => (isCompact_closedBall 0 4).of_isClosed_subset (isClosed_levelSource g b)
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

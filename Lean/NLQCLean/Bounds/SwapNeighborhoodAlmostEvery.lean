import NLQCLean.Bounds.StrongHaarConditional
import NLQCLean.Bounds.AlmostEveryTargets
import NLQCLean.Semialgebraic.ProjectionTheorem

/-!
# Almost-every unitary resource rates in the SWAP neighbourhood

The restricted Haar estimate has prefactor `exp (C K²)` and exponent `d⁴/16`.
First Borel–Cantelli therefore applies at error `exp (-A K²/d⁴)`. For Haar-almost
every target in `swapNeighborhood d`, one target-dependent error threshold gives
`K ≥ c d² √log(1/e)` simultaneously for all budgets and pure/common-map finite-mixed
score or normalized diamond implementations. Haar is the full probability law.
The `d²` precision factor is restricted to the neighbourhood.

This is the unitary conclusion of the unlabeled consequences paragraph following
`thm:swap-haar` in the revised robust companion, `swap.tex`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal

/-- At the regional forbidden error, the strong Haar right side is at most
`exp (-K²)`, when `A ≥ 16(C+1)`. -/
theorem strong_haar_rhs_at_forbiddenError_le {C A : ℝ}
    (hA : 16 * (C + 1) ≤ A) {d K : ℕ} (hd : 0 < d) :
    Real.exp (C * (K : ℝ) ^ 2) *
        (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4))) ^ ((d : ℝ) ^ 4 / 16) ≤
      Real.exp (-((K : ℝ) ^ 2)) := by
  rw [← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcancel : -(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4) * ((d : ℝ) ^ 4 / 16) =
      -(A / 16 * (K : ℝ) ^ 2) := by field_simp
  rw [hcancel]
  have hcoef : C + 1 ≤ A / 16 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (K : ℝ))
  linarith

/-- The regional forbidden error is in the strong Haar range once `K ≥ d²`. -/
theorem strong_forbiddenError_side_conditions {A : ℝ} (hA : 1 ≤ A)
    {d K : ℕ} (hd : 2 ≤ d) (hK : d ^ 2 ≤ K) :
    (d : ℝ) ^ 2 / 2 ≤ K ∧
      0 < Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4)) ∧
      Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4)) ≤ 1 / 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hKR : (d : ℝ) ^ 2 ≤ K := by exact_mod_cast hK
  have hsq : (d : ℝ) ^ 4 ≤ (K : ℝ) ^ 2 := by
    calc (d : ℝ) ^ 4 = ((d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (K : ℝ) ^ 2 := by gcongr
  refine ⟨by nlinarith [sq_nonneg (d : ℝ)], Real.exp_pos _, exp_neg_le_half ?_⟩
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 4)]
  simpa only [one_mul] using hsq.trans (le_mul_of_one_le_left (sq_nonneg (K : ℝ)) hA)

/-- One universal forbidden-error exponent: almost every target in the SWAP
neighbourhood eventually avoids pure and common-map finite-mixed score reachability.
First Borel–Cantelli needs only upper measures of the restricted reachable sets. -/
theorem exists_ae_swapNeighborhood_forbidden_error_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ T ∂unitaryHaar (Fin d × Fin d), T ∈ swapNeighborhood d →
        ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
          T ∉ pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4))) ∧
          T ∉ mixedReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4))) := by
  obtain ⟨C, hC, hbound⟩ := exists_strongRestrictedHaarBound hGeom
  let A : ℝ := 16 * (C + 1)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  refine ⟨A, hA, fun d hd => ?_⟩
  have htail : ∀ᵐ T ∂unitaryHaar (Fin d × Fin d),
      ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
        T ∉ swapNeighborhood d ∩
          pureReachable d K (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4))) := by
    apply ae_exists_forall_notMem_of_le_exp_neg _ _ (d ^ 2)
    intro K hK
    obtain ⟨hq, he, hehalf⟩ := strong_forbiddenError_side_conditions hA hd hK
    refine (hbound d K hd hq _ he hehalf).1.trans ((min_le_right _ _).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    refine (strong_haar_rhs_at_forbiddenError_le le_rfl
      (show 0 < d by omega)).trans ?_
    simpa using exp_neg_sq_mul_le_exp_neg (d := 1) (K := K) (by omega)
  refine htail.mono fun T hT hswap => ?_
  obtain ⟨K₀, hK₀, hT⟩ := hT
  refine ⟨K₀, hK₀, fun K hK => ?_⟩
  have hp : T ∉ pureReachable d K
      (Real.exp (-(A * (K : ℝ) ^ 2 / (d : ℝ) ^ 4))) :=
    fun h => hT K hK ⟨hswap, h⟩
  exact ⟨hp, by rw [mixedReachable_eq_pureReachable]; exact hp⟩

/-- One universal constant and one target-dependent threshold serve every budget
and all four score/normalized-diamond pure/common-map mixed reachable sets. -/
theorem exists_ae_swapNeighborhood_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        T ∈ swapNeighborhood d →
        ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
          (T ∈ pureReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (T ∈ mixedReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨A, hA, hae⟩ := exists_ae_swapNeighborhood_forbidden_error_constant hGeom
  have hA0 : 0 < A := by linarith
  refine ⟨1 / Real.sqrt A, by positivity, fun d hd => ?_⟩
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  refine (hae d hd).mono fun T hT hswap => ?_
  obtain ⟨K₀, -, hT⟩ := hT hswap
  let K₁ := max K₀ (d ^ 4)
  have hK₀₁ : K₀ ≤ K₁ := le_max_left _ _
  have hK₁ : (d ^ 2) ^ 2 ≤ K₁ := by
    simp [K₁, ← pow_mul]
  obtain ⟨he₀, he₀half⟩ := forbiddenError_threshold_mem hA
    (show 1 ≤ d ^ 2 by nlinarith) hK₁
  have hpow : ((d ^ 2 : ℕ) : ℝ) ^ 2 = (d : ℝ) ^ 4 := by push_cast; ring
  rw [hpow] at he₀ he₀half
  refine ⟨_, he₀, he₀half, fun K e _he hee => ?_⟩
  have key : ∀ {R : ℕ → ℝ → Set (unitaryGroup (Fin d × Fin d) ℂ)},
      (∀ {K K' : ℕ} {e e' : ℝ}, K ≤ K' → e ≤ e' → R K e ⊆ R K' e') →
      (∀ K' : ℕ, K₁ ≤ K' → T ∉ R K'
        (Real.exp (-(A * (K' : ℝ) ^ 2 / (d : ℝ) ^ 4)))) →
      T ∈ R K e →
      1 / Real.sqrt A * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
    intro R hmono hf hx
    have hf' : ∀ K' : ℕ, K₁ ≤ K' → T ∉ R K'
        (Real.exp (-(A * (K' : ℝ) ^ 2 / ((d ^ 2 : ℕ) : ℝ) ^ 2))) := by
      simpa only [hpow] using hf
    have hee' : e ≤ Real.exp (-(A * (K₁ : ℝ) ^ 2 / ((d ^ 2 : ℕ) : ℝ) ^ 2)) := by
      simpa only [hpow] using hee
    simpa only [Nat.cast_pow] using resource_lower_of_forbiddenError hmono hA0
      (show 0 < d ^ 2 by positivity) hf' hee' hx
  have hp := key (R := pureReachable d) pureReachable_mono
    fun K' hK' => (hT K' (hK₀₁.trans hK')).1
  have hm := key (R := mixedReachable d) mixedReachable_mono
    fun K' hK' => (hT K' (hK₀₁.trans hK')).2
  exact ⟨hp, hm,
    fun h => hp (pureDiamondReachable_subset_pureReachable K e h),
    fun h => hm (mixedDiamondReachable_subset_mixedReachable K e h)⟩

/-- Regional rates on arbitrary finite original registers. The mixed resource
uses a component Schmidt-number bound and common local maps; both complete
message dimensions remain charged. -/
theorem exists_ae_swapNeighborhood_physical_resource_constant
    (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        T ∈ swapNeighborhood d →
        ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
            (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB,
              P.HasFootprint K →
              (1 - e ≤ scoreU (T : Matrix _ _ ℂ) P.operationalChannel ∨
                diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ)) ≤ e) →
              c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
            (∀ (n : ℕ) (m : MixedResource ρA ρB n)
              (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
              (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
              (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
              (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
              IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
              ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
              (1 - e ≤ scoreU (T : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ∨
                diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ)) ≤ e) →
              c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨c, hc, h⟩ := exists_ae_swapNeighborhood_resource_constant.{0, 0, 0, 0, 0, 0, 0, 0} hGeom
  refine ⟨c, hc, fun d hd => (h d hd).mono fun T hT hswap => ?_⟩
  obtain ⟨e₀, he₀, he₀half, hT⟩ := hT hswap
  have : NeZero d := ⟨by omega⟩
  have hU := Matrix.mem_unitaryGroup_iff'.mp T.2
  refine ⟨e₀, he₀, he₀half, fun K e he hee ρA ρB κA κB μA μB εA εB
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_⟩⟩
  · intro P hP hs
    exact (hT K e he hee).1
      (P.mem_pureReachable hP (hs.elim id (P.scoreU_ge_of_diamondError_le hU)))
  · intro n m VA VB DA DB hVA hVB hDA hDB R hR hK hs
    exact (hT K e he hee).2.1
      (m.mem_mixedReachable VA VB DA DB hVA hVB hDA hDB hR hK
        (hs.elim id (m.scoreU_ge_of_diamondError_le hVA hVB hDA hDB hU)))

/-- Regional rate with exactly three geometry inputs. Projection is supplied by
the checked semialgebraic projection theorem. -/
theorem exists_ae_swapNeighborhood_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        T ∈ swapNeighborhood d →
        ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
          (T ∈ pureReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (T ∈ mixedReachable d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
          (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
            c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_swapNeighborhood_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT semialgebraicProjectionTheorem
      hStratification hComponents)

/-- Regional physical rate with a single threshold before all budgets and
arbitrary finite original registers, under exactly three geometry premises. -/
theorem exists_ae_swapNeighborhood_physical_resource_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ᵐ (T : unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
        T ∈ swapNeighborhood d →
        ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (e : ℝ), 0 < e → e ≤ e₀ →
          ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
            (μA : Type u₅) (μB : Type u₆) (εA : Type u₇) (εB : Type u₈)
            [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
            [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
            [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
            [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB],
            (∀ P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d) (Fin d) εA εB,
              P.HasFootprint K →
              (1 - e ≤ scoreU (T : Matrix _ _ ℂ) P.operationalChannel ∨
                diamondError P.operationalChannel (adConj (T : Matrix _ _ ℂ)) ≤ e) →
              c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
            (∀ (n : ℕ) (m : MixedResource ρA ρB n)
              (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
              (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
              (DA : Matrix (Fin d × εA) (κA × μB) ℂ)
              (DB : Matrix (Fin d × εB) (κB × μA) ℂ),
              IsIsometry VA → IsIsometry VB → IsIsometry DA → IsIsometry DB →
              ∀ R : ℕ, m.schmidtNumberLE R → R * Fintype.card μA * Fintype.card μB ≤ K →
              (1 - e ≤ scoreU (T : Matrix _ _ ℂ) (m.mixedChannel VA VB DA DB) ∨
                diamondError (m.mixedChannel VA VB DA DB) (adConj (T : Matrix _ _ ℂ)) ≤ e) →
              c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) :=
  exists_ae_swapNeighborhood_physical_resource_constant.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈}
    (polynomialImageVolumeBound_of_external hLRT semialgebraicProjectionTheorem
      hStratification hComponents)

end NLQCLean

import NLQCLean.Exact.PathDerivatives
import NLQCLean.LinearAlgebra.LinearODE

/-!
# Integrating the measurement derivative (`lem:smoothsameorbit-pvm`)

If `Ṁ = -a M + M b` on an open interval with continuous local skew `a` and
diagonal skew `b`, then `M(t) = (L_A(t) ⊗ L_B(t)) M(t_*) Δ(t)` with continuous
unitary `L_A, L_B` and diagonal unitary `Δ`. The local generator is split
continuously by partial traces, `L_A, L_B` solve linear differential
equations (`fact:linear-ode`), `Δ` solves scalar equations, and
`L† M Δ†` has zero derivative.
-/

noncomputable section

namespace NLQCLean

open Matrix Filter
open scoped Matrix.Norms.Frobenius Kronecker Topology

section Constancy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- On an interval, zero derivative forces a constant function. -/
theorem eqOn_const_of_hasDerivAt_zero {J : Set ℝ} (hJ : J.OrdConnected)
    {f : ℝ → E} {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h : ∀ t ∈ J, HasDerivAt f 0 t) :
    _root_.Set.EqOn f (fun _ => f t₀) J := by
  have hf : IsLinearODESol (fun _ => (0 : E →L[ℝ] E)) J f := fun t ht => by
    simpa using (h t ht).hasDerivWithinAt
  have hc : IsLinearODESol (fun _ => (0 : E →L[ℝ] E)) J (fun _ => f t₀) := fun t _ => by
    simpa using (hasDerivAt_const t (f t₀)).hasDerivWithinAt
  exact hf.eqOn hJ continuousOn_const ht₀ hc rfl

end Constancy

section Split

variable {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- Alice's part of a local generator, `Tr_B a / d_B`. -/
def splitLeft (a : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Matrix ιA ιA ℂ :=
  ((Fintype.card ιB : ℂ)⁻¹) • ptraceB ιA ιB a

/-- Bob's part, `Tr_A a / d_A - Tr a / (d_A d_B)`. -/
def splitRight (a : Matrix (ιA × ιB) (ιA × ιB) ℂ) : Matrix ιB ιB ℂ :=
  ((Fintype.card ιA : ℂ)⁻¹) • ptraceA ιA ιB a -
    (((Fintype.card ιA : ℂ) * Fintype.card ιB)⁻¹ * a.trace) • (1 : Matrix ιB ιB ℂ)

theorem split_spec [Nonempty ιA] [Nonempty ιB] {a : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (ha : a ∈ localSkew ιA ιB) :
    a = splitLeft a ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ splitRight a ∧
      (splitLeft a)ᴴ = -splitLeft a ∧ (splitRight a)ᴴ = -splitRight a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_localSkew_iff.mp ha
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hL : splitLeft (x ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ y) =
      x + ((Fintype.card ιB : ℂ)⁻¹ * y.trace) • 1 := by
    rw [splitLeft, map_add, ptraceB_kronecker, ptraceB_kronecker, Matrix.trace_one, smul_add,
      smul_smul, smul_smul, inv_mul_cancel₀ hB, one_smul]
  have hR : splitRight (x ⊗ₖ (1 : Matrix ιB ιB ℂ) + (1 : Matrix ιA ιA ℂ) ⊗ₖ y) =
      y + (-((Fintype.card ιB : ℂ)⁻¹ * y.trace)) • 1 := by
    rw [splitRight, map_add, ptraceA_kronecker, ptraceA_kronecker, Matrix.trace_one,
      Matrix.trace_add, Matrix.trace_kronecker, Matrix.trace_kronecker, Matrix.trace_one,
      Matrix.trace_one, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hA, one_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring_nf
  have hxt : star x.trace = -x.trace := by
    rw [← Matrix.trace_conjTranspose, hx, Matrix.trace_neg]
  have hyt : star y.trace = -y.trace := by
    rw [← Matrix.trace_conjTranspose, hy, Matrix.trace_neg]
  have hc : star ((Fintype.card ιB : ℂ)⁻¹ * y.trace) = -((Fintype.card ιB : ℂ)⁻¹ * y.trace) := by
    rw [star_mul', hyt, star_inv₀, Complex.star_def, Complex.conj_natCast, mul_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [hL, hR, Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
      Matrix.kronecker_smul, neg_smul]
    abel
  · rw [hL, Matrix.conjTranspose_add, hx, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      hc, neg_smul, neg_add]
  · rw [hR, Matrix.conjTranspose_add, hy, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      star_neg, hc, neg_neg, neg_add, neg_smul, neg_neg]

omit [DecidableEq ιA] [DecidableEq ιB] in
/-- The splitting maps are real linear, hence continuous. -/
theorem continuous_splitLeft : Continuous (splitLeft (ιA := ιA) (ιB := ιB)) := by
  let L : Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℝ] Matrix ιA ιA ℂ :=
    (((Fintype.card ιB : ℂ)⁻¹) • ptraceB ιA ιB).restrictScalars ℝ
  exact L.continuous_of_finiteDimensional

omit [DecidableEq ιA] in
theorem continuous_splitRight : Continuous (splitRight (ιA := ιA) (ιB := ιB)) := by
  let L : Matrix (ιA × ιB) (ιA × ιB) ℂ →ₗ[ℝ] Matrix ιB ιB ℂ :=
    (((Fintype.card ιA : ℂ)⁻¹) • ptraceA ιA ιB -
      (LinearMap.smulRight (Matrix.traceLinearMap (ιA × ιB) ℂ ℂ)
        ((((Fintype.card ιA : ℂ) * Fintype.card ιB)⁻¹) • (1 : Matrix ιB ιB ℂ)))).restrictScalars ℝ
  have h : (splitRight (ιA := ιA) (ιB := ιB)) = L := by
    funext a
    simp only [L, splitRight, LinearMap.coe_restrictScalars, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, smul_smul]
    congr 1
    rw [mul_comm]
  rw [h]
  exact L.continuous_of_finiteDimensional

end Split

section Integration

variable {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- Solutions of `L' = -X(t) L` with skew `X` and `L(t₀) = 1` are unitary. -/
theorem exists_unitary_solution {n : Type*} [Fintype n] [DecidableEq n] {J : Set ℝ}
    (hJ : J.OrdConnected) (hJo : IsOpen J) {X : ℝ → Matrix n n ℂ} (hX : ContinuousOn X J)
    (hskew : ∀ t ∈ J, (X t)ᴴ = -X t) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ∃ L : ℝ → Matrix n n ℂ, L t₀ = 1 ∧ ContinuousOn L J ∧
      (∀ t ∈ J, HasDerivAt L (-X t * L t) t) ∧ ∀ t ∈ J, L t ∈ Matrix.unitaryGroup n ℂ := by
  have hA : ContinuousOn (fun t => mulCLM (𝕜 := ℂ) (l := n) (m := n) (n := n) (-X t)) J :=
    mulCLM.continuous.comp_continuousOn hX.neg
  obtain ⟨L, hL0, hL, -, -⟩ := linearODE_existsUnique hJ hA ht₀ (1 : Matrix n n ℂ)
  have hd : ∀ t ∈ J, HasDerivAt L (-X t * L t) t := fun t ht => by
    have h1 := (hL t ht).hasDerivAt (hJo.mem_nhds ht)
    beta_reduce at h1
    exact h1.congr_deriv (mulCLM_apply _ _)
  refine ⟨L, hL0, fun t ht => (hd t ht).continuousAt.continuousWithinAt, hd, ?_⟩
  have hc : ∀ t ∈ J, HasDerivAt (fun τ => (L τ)ᴴ * L τ) 0 t := by
    intro t ht
    have h := HasDerivAt.matrixMul (HasDerivAt.matrixConjTranspose (hd t ht)) (hd t ht)
    have h0 : (L t)ᴴ * (-X t * L t) + (-X t * L t)ᴴ * L t = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hskew t ht, neg_neg]
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_add_cancel]
    rw [h0] at h
    exact h
  have hconst := eqOn_const_of_hasDerivAt_zero hJ ht₀ hc
  intro t ht
  rw [Matrix.mem_unitaryGroup_iff']
  have := hconst ht
  simp only [hL0, Matrix.conjTranspose_one, Matrix.mul_one] at this
  exact this

/-- Scalar solutions of `z' = β(t) z` with imaginary `β` and `z(t₀) = 1` have unit
modulus. -/
theorem exists_phase_solution {J : Set ℝ} (hJ : J.OrdConnected) (hJo : IsOpen J)
    {β : ℝ → ℂ} (hβ : ContinuousOn β J) (him : ∀ t ∈ J, star (β t) = -β t) {t₀ : ℝ}
    (ht₀ : t₀ ∈ J) :
    ∃ z : ℝ → ℂ, z t₀ = 1 ∧ ContinuousOn z J ∧ (∀ t ∈ J, HasDerivAt z (β t * z t) t) ∧
      ∀ t ∈ J, ‖z t‖ = 1 := by
  have hA : ContinuousOn (fun t => ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ) (β t)) J :=
    (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)).continuous.comp_continuousOn hβ
  obtain ⟨z, hz0, hz, -, -⟩ := linearODE_existsUnique hJ hA ht₀ (1 : ℂ)
  have hd : ∀ t ∈ J, HasDerivAt z (β t * z t) t := fun t ht => by
    have := (hz t ht).hasDerivAt (hJo.mem_nhds ht)
    simpa using this
  refine ⟨z, hz0, fun t ht => (hd t ht).continuousAt.continuousWithinAt, hd, ?_⟩
  have hc : ∀ t ∈ J, HasDerivAt (fun τ => star (z τ) * z τ) 0 t := by
    intro t ht
    have h := ((hd t ht).star).mul (hd t ht)
    have hval : star (β t * z t) * z t + star (z t) * (β t * z t) = 0 := by
      rw [star_mul', him t ht]
      ring
    rw [hval] at h
    exact h
  have hconst := eqOn_const_of_hasDerivAt_zero hJ ht₀ hc
  intro t ht
  have h1 : star (z t) * z t = 1 := by
    have := hconst ht
    simpa [hz0] using this
  have h2 : Complex.normSq (z t) = 1 := by
    have h3 : (Complex.normSq (z t) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, h1]
    exact_mod_cast h3
  rw [Complex.normSq_eq_norm_sq] at h2
  nlinarith [norm_nonneg (z t)]

/-- **Integration of the measurement derivative.** If `Ṁ = -a M + M b` on an
open interval `J` with continuous local skew `a` and diagonal skew `b`, then
for `t₀ ∈ J` there are continuous unitary `L_A, L_B` and diagonal unitary `Δ`
on `J` with `M(t) = (L_A(t) ⊗ L_B(t)) M(t₀) Δ(t)`. -/
theorem exists_pvm_factorization [Nonempty ιA] [Nonempty ιB] {J : Set ℝ}
    (hJ : J.OrdConnected) (hJo : IsOpen J)
    {M a b : ℝ → Matrix (ιA × ιB) (ιA × ιB) ℂ}
    (ha : ContinuousOn a J) (hb : ContinuousOn b J)
    (hloc : ∀ t ∈ J, a t ∈ localSkew ιA ιB) (hdiag : ∀ t ∈ J, b t ∈ diagSkew (ιA × ιB))
    (hM : ∀ t ∈ J, HasDerivAt M (-a t * M t + M t * b t) t) {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ∃ LA : ℝ → Matrix ιA ιA ℂ, ∃ LB : ℝ → Matrix ιB ιB ℂ,
      ∃ Δ : ℝ → Matrix (ιA × ιB) (ιA × ιB) ℂ,
        ContinuousOn LA J ∧ ContinuousOn LB J ∧ ContinuousOn Δ J ∧
        ∀ t ∈ J, LA t ∈ Matrix.unitaryGroup ιA ℂ ∧ LB t ∈ Matrix.unitaryGroup ιB ℂ ∧
          Δ t ∈ phaseUnitaries (ιA × ιB) ∧ M t = (LA t ⊗ₖ LB t) * M t₀ * Δ t := by
  classical
  -- Local factors.
  obtain ⟨LA, hLA0, hLAc, hLAd, hLAu⟩ := exists_unitary_solution hJ hJo
    (continuous_splitLeft.comp_continuousOn ha) (fun t ht => (split_spec (hloc t ht)).2.1) ht₀
  obtain ⟨LB, hLB0, hLBc, hLBd, hLBu⟩ := exists_unitary_solution hJ hJo
    (continuous_splitRight.comp_continuousOn ha) (fun t ht => (split_spec (hloc t ht)).2.2) ht₀
  -- Diagonal phases.
  have hbskew : ∀ t ∈ J, (b t)ᴴ = -b t := fun t ht => (mem_diagSkew_iff.mp (hdiag t ht)).2
  have hbd : ∀ t ∈ J, b t = Matrix.diagonal (fun k => b t k k) := by
    intro t ht
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h, (mem_diagSkew_iff.mp (hdiag t ht)).1 i j h]
  have hphase : ∀ k : ιA × ιB, ∃ z : ℝ → ℂ, z t₀ = 1 ∧ ContinuousOn z J ∧
      (∀ t ∈ J, HasDerivAt z (b t k k * z t) t) ∧ ∀ t ∈ J, ‖z t‖ = 1 := by
    intro k
    refine exists_phase_solution hJ hJo ?_ (fun t ht => ?_) ht₀
    · exact (continuous_apply k).comp_continuousOn
        ((continuous_apply k).comp_continuousOn hb)
    · have := congrFun (congrFun (hbskew t ht) k) k
      simpa [Matrix.conjTranspose_apply] using this
  choose z hz0 hzc hzd hzn using hphase
  let Δ : ℝ → Matrix (ιA × ιB) (ιA × ιB) ℂ := fun t => Matrix.diagonal fun k => z k t
  have hΔc : ContinuousOn Δ J :=
    (LinearMap.continuous_of_finiteDimensional
      ((Matrix.diagonalLinearMap (ιA × ιB) ℂ ℂ).restrictScalars ℝ)).comp_continuousOn
      (continuousOn_pi.mpr hzc)
  have hΔd : ∀ t ∈ J, HasDerivAt Δ (Δ t * b t) t := by
    intro t ht
    have hv : HasDerivAt (fun τ => fun k => z k τ) (fun k => b t k k * z k t) t :=
      hasDerivAt_pi.mpr fun k => hzd k t ht
    have h := HasDerivAt.ofLinearMap ((Matrix.diagonalLinearMap (ιA × ιB) ℂ ℂ).restrictScalars ℝ) hv
    have hval : ((Matrix.diagonalLinearMap (ιA × ιB) ℂ ℂ).restrictScalars ℝ)
        (fun k => b t k k * z k t) = Δ t * b t := by
      conv_rhs => rw [hbd t ht]
      simp only [Δ, Matrix.diagonal_mul_diagonal, LinearMap.coe_restrictScalars,
        Matrix.diagonalLinearMap_apply]
      change Matrix.diagonal _ = _
      congr 1
      funext k
      ring
    rw [hval] at h
    exact h
  have hΔu : ∀ t ∈ J, Δ t ∈ phaseUnitaries (ιA × ιB) := fun t ht =>
    ⟨fun k => z k t, fun k => hzn k t ht, rfl⟩
  have hΔ0 : Δ t₀ = 1 := by
    simp only [Δ, hz0, Matrix.diagonal_one]
  refine ⟨LA, LB, Δ, hLAc, hLBc, hΔc, fun t ht => ⟨hLAu t ht, hLBu t ht, hΔu t ht, ?_⟩⟩
  -- The combined local factor solves `L' = -a L`.
  let L : ℝ → Matrix (ιA × ιB) (ιA × ιB) ℂ := fun τ => LA τ ⊗ₖ LB τ
  have hLd : ∀ τ ∈ J, HasDerivAt L (-a τ * L τ) τ := by
    intro τ hτ
    have h := HasDerivAt.matrixKronecker (hLAd τ hτ) (hLBd τ hτ)
    obtain ⟨hsplit, -, -⟩ := split_spec (hloc τ hτ)
    have hval : LA τ ⊗ₖ (-(splitRight ∘ a) τ * LB τ) + (-(splitLeft ∘ a) τ * LA τ) ⊗ₖ LB τ =
        -a τ * L τ := by
      conv_rhs => rw [hsplit]
      simp only [Function.comp_apply, L, Matrix.neg_mul]
      have e1 : LA τ ⊗ₖ (-(splitRight (a τ) * LB τ)) =
          -(((1 : Matrix ιA ιA ℂ) ⊗ₖ splitRight (a τ)) * (LA τ ⊗ₖ LB τ)) := by
        rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
        ext i j
        simp [Matrix.kroneckerMap_apply]
      have e2 : (-(splitLeft (a τ) * LA τ)) ⊗ₖ LB τ =
          -((splitLeft (a τ) ⊗ₖ (1 : Matrix ιB ιB ℂ)) * (LA τ ⊗ₖ LB τ)) := by
        rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
        ext i j
        simp [Matrix.kroneckerMap_apply]
      rw [e1, e2, Matrix.add_mul]
      abel
    rw [hval] at h
    exact h
  -- `N = L† M Δ†` is constant.
  have haskew : ∀ τ ∈ J, (a τ)ᴴ = -a τ := fun τ hτ =>
    mem_skewHermitian_iff.mp (localSkew_le_skewHermitian (hloc τ hτ))
  have hN : ∀ τ ∈ J, HasDerivAt (fun σ => (L σ)ᴴ * M σ * (Δ σ)ᴴ) 0 τ := by
    intro τ hτ
    have h := HasDerivAt.matrixMul (HasDerivAt.matrixMul
      (HasDerivAt.matrixConjTranspose (hLd τ hτ)) (hM τ hτ))
      (HasDerivAt.matrixConjTranspose (hΔd τ hτ))
    have hval : (L τ)ᴴ * M τ * (Δ τ * b τ)ᴴ + ((L τ)ᴴ * (-a τ * M τ + M τ * b τ) +
        (-a τ * L τ)ᴴ * M τ) * (Δ τ)ᴴ = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg,
        haskew τ hτ, hbskew τ hτ]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
        Matrix.mul_assoc]
      abel
    rw [hval] at h
    exact h
  have hNt := eqOn_const_of_hasDerivAt_zero hJ ht₀ hN ht
  have hL0 : L t₀ = 1 := by simp [L, hLA0, hLB0]
  simp only [hL0, hΔ0, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hNt
  have hLu : L t * (L t)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.kronecker_mem_unitary (hLAu t ht) (hLBu t ht))
  have hΔu' : (Δ t)ᴴ * Δ t = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (phaseUnitaries_subset_unitary (hΔu t ht))
  calc M t = (L t * (L t)ᴴ) * M t * ((Δ t)ᴴ * Δ t) := by rw [hLu, hΔu', Matrix.one_mul,
        Matrix.mul_one]
    _ = L t * ((L t)ᴴ * M t * (Δ t)ᴴ) * Δ t := by simp only [Matrix.mul_assoc]
    _ = (LA t ⊗ₖ LB t) * M t₀ * Δ t := by rw [hNt]

end Integration

section Measurement

variable {d : ℕ}

/-- **`lem:smoothsameorbit-pvm`.** Along a continuously differentiable family of
exact measurement strategies on an open interval `J`, for `t₀ ∈ J` there are
continuous unitary `L_A, L_B` and continuous diagonal unitary `Δ` with
`M(t) = (L_A(t) ⊗ L_B(t)) M(t₀) Δ(t)`; in particular `M(t) ∈ OrbM(M(t₀))`. -/
theorem pvm_path_factorization [NeZero d] (s : Fin 8 → ℕ) {J : Set ℝ} (hJ : J.OrdConnected)
    (hJo : IsOpen J)
    {γ : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ × PVMShapeBlocks d s}
    (hγ : ContDiffOn ℝ 1 γ J) (hmem : ∀ t ∈ J, γ t ∈ pvmTargetWitnessSet d s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) :
    ∃ LA LB : ℝ → Matrix (Fin d) (Fin d) ℂ, ∃ Δ : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      ContinuousOn LA J ∧ ContinuousOn LB J ∧ ContinuousOn Δ J ∧
      ∀ t ∈ J, LA t ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ LB t ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
        Δ t ∈ phaseUnitaries (Fin d × Fin d) ∧
        (γ t).1 = (LA t ⊗ₖ LB t) * (γ t₀).1 * Δ t ∧
        (γ t).1 ∈ pvmBasisOrbit (Fin d) (Fin d) (γ t₀).1 := by
  obtain ⟨a, b, ha, hb, hgen⟩ := exists_continuous_pvm_generators s hJo hγ hmem
  obtain ⟨LA, LB, Δ, hLA, hLB, hΔ, hfac⟩ := exists_pvm_factorization hJ hJo ha hb
    (fun t ht => (hgen t ht).1) (fun t ht => (hgen t ht).2.1)
    (M := fun τ => (γ τ).1) (fun t ht => (hgen t ht).2.2) ht₀
  refine ⟨LA, LB, Δ, hLA, hLB, hΔ, fun t ht => ?_⟩
  obtain ⟨hA, hB, hD, heq⟩ := hfac t ht
  exact ⟨hA, hB, hD, heq, ⟨_, ⟨LA t, hA, LB t, hB, rfl⟩, Δ t, hD, heq⟩⟩

end Measurement

end NLQCLean

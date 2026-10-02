/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.ImageVolume.BoxMonomialCount
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Separation.Hausdorff

/-!
# Nondegenerate zeros of square polynomial systems

A real zero of a square polynomial system is nondegenerate when the derivative of the
evaluation map there is injective. If every polynomial has total degree at most `D`,
there are at most `(D + 1) ^ card σ` nondegenerate zeros.

The proof perturbs the system to `G i + t X i ^ (D + 1)`. By the inverse function theorem
applied to `(w, t) ↦ (G w + t M w, t)`, each nondegenerate zero of `G` persists in a
prescribed neighborhood for all small `t`. For `t ≠ 0` the perturbed system has pure-power
leading terms, so `card_le_of_forall_eval_eq_zero` bounds the number of its zeros.
-/

namespace NLQCLean

open MvPolynomial Filter Set
open scoped Topology ContDiff

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Evaluation of a family of real polynomials as a map of coordinate vectors. -/
noncomputable def polyEvalMap (G : σ → MvPolynomial σ ℝ) (w : σ → ℝ) : σ → ℝ :=
  fun i => eval w (G i)

omit [DecidableEq σ] in
theorem contDiff_eval_pi {n : WithTop ℕ∞} (P : MvPolynomial σ ℝ) :
    ContDiff ℝ n (fun w : σ → ℝ => eval w P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ n (fun _ : σ → ℝ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℝ ℝ i)

omit [DecidableEq σ] in
theorem contDiff_polyEvalMap {n : WithTop ℕ∞} (G : σ → MvPolynomial σ ℝ) :
    ContDiff ℝ n (polyEvalMap G) :=
  contDiff_pi.mpr fun i => contDiff_eval_pi (G i)

/-- A zero at which the derivative of the evaluation map is injective. -/
def IsNondegenerateZero (G : σ → MvPolynomial σ ℝ) (w : σ → ℝ) : Prop :=
  (∀ i, eval w (G i) = 0) ∧ Function.Injective (fderiv ℝ (polyEvalMap G) w)

/-- The power map used to perturb the system. -/
noncomputable def coordinatePowerMap (e : ℕ) (w : σ → ℝ) : σ → ℝ := fun i => w i ^ e

omit [DecidableEq σ] in
theorem contDiff_coordinatePowerMap {n : WithTop ℕ∞} (e : ℕ) :
    ContDiff ℝ n (coordinatePowerMap (σ := σ) e) :=
  contDiff_pi.mpr fun i => (contDiff_apply ℝ ℝ i).pow e

omit [DecidableEq σ] in
/-- A nondegenerate zero persists in every neighborhood under all small perturbations
`G + t M`, for a smooth `M`. -/
theorem eventually_exists_zero_perturb {F M : (σ → ℝ) → (σ → ℝ)} {v : σ → ℝ}
    (hF : ContDiff ℝ 1 F) (hM : ContDiff ℝ 1 M) (hv : F v = 0)
    (hinj : Function.Injective (fderiv ℝ F v)) {U : Set (σ → ℝ)} (hU : U ∈ 𝓝 v) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ w ∈ U, F w + t • M w = 0 := by
  let Θ : (σ → ℝ) × ℝ → (σ → ℝ) × ℝ := fun p => (F p.1 + p.2 • M p.1, p.2)
  have hΘ : ContDiff ℝ 1 Θ := by
    refine ContDiff.prodMk ?_ contDiff_snd
    exact (hF.comp contDiff_fst).add (contDiff_snd.fun_smul (hM.comp contDiff_fst))
  let F' := fderiv ℝ F v
  let L : (σ → ℝ) × ℝ →L[ℝ] (σ → ℝ) × ℝ :=
    (F'.comp (ContinuousLinearMap.fst ℝ (σ → ℝ) ℝ) +
      (ContinuousLinearMap.snd ℝ (σ → ℝ) ℝ).smulRight (M v)).prod
      (ContinuousLinearMap.snd ℝ (σ → ℝ) ℝ)
  have hL : HasFDerivAt Θ L (v, 0) := by
    have h1 : HasFDerivAt (fun p : (σ → ℝ) × ℝ => F p.1)
        (F'.comp (ContinuousLinearMap.fst ℝ (σ → ℝ) ℝ)) (v, 0) :=
      ((hF.differentiable one_ne_zero) v).hasFDerivAt.comp (v, 0) hasFDerivAt_fst
    have h2 : HasFDerivAt (fun p : (σ → ℝ) × ℝ => M p.1)
        ((fderiv ℝ M v).comp (ContinuousLinearMap.fst ℝ (σ → ℝ) ℝ)) (v, 0) :=
      ((hM.differentiable one_ne_zero) v).hasFDerivAt.comp (v, 0) hasFDerivAt_fst
    have h3 := (hasFDerivAt_snd (p := ((v, 0) : (σ → ℝ) × ℝ))).fun_smul h2
    have h4 := (h1.fun_add h3).prodMk (hasFDerivAt_snd (p := ((v, 0) : (σ → ℝ) × ℝ)))
    refine h4.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [L]
  have hLinj : Function.Injective L := by
    intro p q hpq
    have h2 : p.2 = q.2 := by simpa [L] using congrArg Prod.snd hpq
    have h1 : F' p.1 + p.2 • M v = F' q.1 + q.2 • M v := by
      simpa [L] using congrArg Prod.fst hpq
    rw [h2] at h1
    exact Prod.ext (hinj (add_right_cancel h1)) h2
  let e : ((σ → ℝ) × ℝ) ≃L[ℝ] ((σ → ℝ) × ℝ) :=
    (LinearEquiv.ofInjectiveEndo (L : (σ → ℝ) × ℝ →ₗ[ℝ] (σ → ℝ) × ℝ) hLinj).toContinuousLinearEquiv
  have he : (e : (σ → ℝ) × ℝ →L[ℝ] (σ → ℝ) × ℝ) = L := by
    ext p <;> rfl
  have hstrict : HasStrictFDerivAt Θ (e : (σ → ℝ) × ℝ →L[ℝ] (σ → ℝ) × ℝ) (v, 0) := by
    rw [he]
    have hs := (hΘ.contDiffAt (x := ((v, 0) : (σ → ℝ) × ℝ))).hasStrictFDerivAt one_ne_zero
    rwa [hL.fderiv] at hs
  have hmap := hstrict.map_nhds_eq_of_equiv
  have hΘv : Θ (v, 0) = (0, 0) := by simp [Θ, hv]
  rw [hΘv] at hmap
  have himage : Θ '' (U ×ˢ univ) ∈ 𝓝 ((0 : σ → ℝ), (0 : ℝ)) := by
    rw [← hmap]
    exact image_mem_map (prod_mem_nhds hU univ_mem)
  have hcont : Continuous (fun t : ℝ => ((0 : σ → ℝ), t)) := continuous_const.prodMk continuous_id
  have ht := hcont.continuousAt.preimage_mem_nhds (x := (0 : ℝ)) himage
  filter_upwards [ht] with t ht
  obtain ⟨⟨w, s⟩, ⟨hw, -⟩, hΘw⟩ := ht
  simp only [Θ, Prod.mk.injEq] at hΘw
  obtain ⟨h1, rfl⟩ := hΘw
  exact ⟨w, hw, h1⟩

/-- Any finite set of nondegenerate zeros has at most `(D + 1) ^ card σ` points. -/
theorem card_le_of_isNondegenerateZero {D : ℕ} (G : σ → MvPolynomial σ ℝ)
    (hG : ∀ i, (G i).totalDegree ≤ D) (V : Finset (σ → ℝ))
    (hV : ∀ v ∈ V, IsNondegenerateZero G v) :
    V.card ≤ (D + 1) ^ Fintype.card σ := by
  classical
  obtain ⟨U, hU, hdisj⟩ := (V.finite_toSet).t2_separation
  have hev : ∀ v ∈ V, ∀ᶠ t in 𝓝 (0 : ℝ),
      ∃ w ∈ U v, polyEvalMap G w + t • coordinatePowerMap (D + 1) w = 0 := by
    intro v hv
    refine eventually_exists_zero_perturb (contDiff_polyEvalMap G)
      (contDiff_coordinatePowerMap (D + 1)) ?_ (hV v hv).2 ((hU v).2.mem_nhds (hU v).1)
    funext i
    exact (hV v hv).1 i
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v ∈ V,
      ∃ w ∈ U v, polyEvalMap G w + t • coordinatePowerMap (D + 1) w = 0 :=
    (Filter.eventually_all_finset V).mpr hev
  obtain ⟨t, ht, htne⟩ := ((hall.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ({0}ᶜ : Set ℝ) ∈ 𝓝[≠] (0 : ℝ))).exists
  choose! w hwU hw0 using ht
  have hinj : Set.InjOn w V := by
    intro v hv v' hv' hvv'
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hv hv' hne) (hwU v hv) (hvv' ▸ hwU v' hv')
  have htne' : t ≠ 0 := htne
  calc V.card = (V.image w).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (D + 1) ^ Fintype.card σ := by
      refine card_le_of_forall_eval_eq_zero (fun i => X i ^ (D + 1) + C t⁻¹ * G i)
        (fun i => C t⁻¹ * G i) (fun i => rfl) (fun i => ?_) _ ?_
      · calc (C t⁻¹ * G i).totalDegree ≤ (C t⁻¹ : MvPolynomial σ ℝ).totalDegree +
              (G i).totalDegree := totalDegree_mul _ _
          _ < D + 1 := by rw [totalDegree_C]; have := hG i; omega
      · intro u hu i
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
        have h := congrFun (hw0 v hv) i
        simp only [polyEvalMap, coordinatePowerMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at h
        simp only [map_add, map_mul, map_pow, eval_X, eval_C]
        field_simp
        linarith

end NLQCLean

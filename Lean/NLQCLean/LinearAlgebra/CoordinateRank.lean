/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.CoordinateMaps
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Invertible coordinate selections of injective linear maps

Coordinate functionals separate points of an injective
linear map. A basis extracted from these functionals supplies a square
invertible coordinate selection, without a dimension-theorem assumption.
-/

section

open Set

namespace NLQCLean

noncomputable def coordinateProjectionL {n k : ℕ} (I : Fin k → Fin n) :
    RealEuclidean n →L[ℝ] RealEuclidean k where
  toFun := coordinateProjection I
  map_add' x y := by ext j; rfl
  map_smul' a x := by ext j; rfl
  cont := continuous_coordinateProjection I

@[simp] theorem coordinateProjectionL_apply {n k : ℕ} (I : Fin k → Fin n)
    (x : RealEuclidean n) : coordinateProjectionL I x = coordinateProjection I x := rfl

/-- Every injective map into coordinate space has an invertible selection
of as many distinct output coordinates as the source dimension. -/
theorem exists_bijective_coordinateProjection_comp {n d : ℕ}
    (L : RealEuclidean d →L[ℝ] RealEuclidean n) (hL : Function.Injective L) :
    ∃ I : Fin d → Fin n, Function.Injective I ∧
      Function.Bijective ((coordinateProjectionL I).comp L) := by
  classical
  let v : Fin n → Module.Dual ℝ (RealEuclidean d) := fun i =>
    { toFun := fun x => L x i
      map_add' := by intro x y; simp
      map_smul' := by intro a x; simp }
  have hspan : Submodule.span ℝ (range v) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro x hx
    have hex : ∃ i, L x i ≠ 0 := by
      by_contra! h
      apply hx
      apply hL
      ext i
      simpa using h i
    obtain ⟨i, hi⟩ := hex
    exact ⟨v i, mem_range_self i, hi⟩
  have hr : Module.finrank ℝ (Submodule.span ℝ (range v)) = d := by
    rw [hspan]
    simp
  have hex : ∃ w : Fin d → Module.Dual ℝ (RealEuclidean d),
      (∀ i, w i ∈ range v) ∧ Submodule.span ℝ (range w) = ⊤ ∧
      LinearIndependent ℝ w := by
    obtain ⟨w, hw, hws, hwl⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (range v)
    let e := finCongr hr.symm
    refine ⟨w ∘ e, fun i => hw (e i), ?_, hwl.comp e e.injective⟩
    rw [e.surjective.range_comp, hws, hspan]
  obtain ⟨w, hw, hwspan, hwli⟩ := hex
  choose I hI using hw
  have hIinj : Function.Injective I := by
    intro i j hij
    apply hwli.injective
    rw [← hI i, ← hI j, hij]
  let A := (coordinateProjectionL I).comp L
  have hA : Function.Injective A := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply (Module.forall_dual_apply_eq_zero_iff ℝ x).mp
    intro f
    have hf : f ∈ Submodule.span ℝ (range w) := hwspan ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      rw [← hI i]
      exact congrArg (fun z : RealEuclidean d => z i) hx
    | zero => rfl
    | add f g _ _ hf hg => simp [hf, hg]
    | smul a f _ hf => simp [hf]
  exact ⟨I, hIinj, hA, LinearMap.injective_iff_surjective.mp hA⟩

theorem exists_equiv_coordinateProjection_comp {n d : ℕ}
    (L : RealEuclidean d →L[ℝ] RealEuclidean n) (hL : Function.Injective L) :
    ∃ I : Fin d → Fin n, Function.Injective I ∧
      ∃ e : RealEuclidean d ≃L[ℝ] RealEuclidean d,
        (e : RealEuclidean d →L[ℝ] RealEuclidean d) = (coordinateProjectionL I).comp L := by
  obtain ⟨I, hI, hA⟩ := exists_bijective_coordinateProjection_comp L hL
  let e := LinearEquiv.ofBijective ((coordinateProjectionL I).comp L).toLinearMap hA
  exact ⟨I, hI, e.toContinuousLinearEquiv, rfl⟩

end NLQCLean
end

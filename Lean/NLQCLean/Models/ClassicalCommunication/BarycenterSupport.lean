import NLQCLean.Models.ClassicalCommunication.HermitianMomentSupport
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite support for an attained-value barycenter

In finite-dimensional real spaces, the integral of an integrable function
under a probability measure lies in the actual convex hull of its values
on any full-measure good set. The proof uses dimension reduction along
supporting hyperplanes, not a replacement by the closed convex hull.
Consequently the barycenter has a finite representation by actual good
points, with at most `finrank + 1` terms.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Set Module

universe u v

variable {α : Type v} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem zero_mem_convexHull_image_of_submodule
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (G : Set α) (hf : Integrable f μ) (hf0 : (∫ a, f a ∂μ) = 0)
    (hG : ∀ᵐ a ∂μ, a ∈ G) (W : Submodule ℝ E) (hW : ∀ a ∈ G, f a ∈ W)
    (step : ∀ g : α → W, Integrable g μ → (∫ a, g a ∂μ) = 0 →
      (0 : W) ∈ convexHull ℝ (g '' G)) :
    (0 : E) ∈ convexHull ℝ (f '' G) := by
  classical
  let g : α → W := fun a => if ha : a ∈ G then ⟨f a, hW a ha⟩ else 0
  have hg : ∀ a ∈ G, (g a : E) = f a := by
    intro a ha
    simp only [g, dite_eq_left ha]
  have hgf : (fun a => (g a : E)) =ᵐ[μ] f := hG.mono fun a ha => hg a ha
  have hcomp : Integrable (W.subtypeₗᵢ ∘ g) μ := hf.congr hgf.symm
  have hgi : Integrable g μ :=
    (W.subtypeₗᵢ.lipschitz.integrable_comp_iff_of_antilipschitz
      W.subtypeₗᵢ.antilipschitz W.subtypeₗᵢ.map_zero).mp hcomp
  have hg0 : (∫ a, g a ∂μ) = 0 := by
    apply Subtype.ext
    change W.subtypeₗᵢ (∫ a, g a ∂μ) = 0
    rw [← W.subtypeₗᵢ.integral_comp_comm]
    exact (integral_congr_ae hgf).trans hf0
  have himage : W.subtype '' (g '' G) = f '' G := by
    ext x
    constructor
    · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, (hg a ha).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g a, ⟨a, ha, rfl⟩, hg a ha⟩
  have hmapped : (0 : E) ∈ W.subtype '' convexHull ℝ (g '' G) :=
    ⟨0, step g hgi hg0, rfl⟩
  rwa [W.subtype.image_convexHull, himage] at hmapped

private theorem zero_mem_convexHull_image_aux (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E = n → ∀ (f : α → E) (G : Set α),
        Integrable f μ → (∫ a, f a ∂μ) = 0 → (∀ᵐ a ∂μ, a ∈ G) →
          (0 : E) ∈ convexHull ℝ (f '' G) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ hn f G hf hf0 hG
    let S : Set E := f '' G
    let W : Submodule ℝ E := Submodule.span ℝ S
    by_cases hW : W = ⊤
    · have hzero : (0 : E) ∈ (affineSpan ℝ S : Set E) := by
        rw [← hf0]
        apply (affineSpan ℝ S).convex.integral_mem
          (affineSpan ℝ S).closed_of_finiteDimensional _ hf
        exact hG.mono fun a ha => subset_affineSpan ℝ S ⟨a, ha, rfl⟩
      have hspan : affineSpan ℝ S = ⊤ := by
        apply top_unique
        intro x _
        have hxW : x ∈ Submodule.span ℝ S := by
          change x ∈ W
          simp only [hW, Submodule.mem_top]
        have hxA : x ∈ affineSpan ℝ (insert 0 S) := by
          rwa [← SetLike.mem_coe, affineSpan_insert_zero]
        exact (affineSpan_le_of_subset_coe
          (insert_subset hzero (subset_affineSpan ℝ S))) hxA
      by_contra hzeroHull
      have hnotint : (0 : E) ∉ interior (convexHull ℝ S) :=
        fun h => hzeroHull (interior_subset h)
      obtain ⟨L, hL, hsupport⟩ :=
        geometric_hahn_banach_of_nonempty_interior_point (convex_convexHull ℝ S) hnotint
          (interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan)
      have hnonpos : ∀ᵐ a ∂μ, L (f a) ≤ 0 := by
        filter_upwards [hG] with a ha
        simpa only [map_zero] using hsupport (f a) (subset_convexHull ℝ S ⟨a, ha, rfl⟩)
      have hLi : Integrable (fun a => L (f a)) μ := L.integrable_comp hf
      have hLint : (∫ a, L (f a) ∂μ) = 0 := by
        rw [L.integral_comp_comm hf, hf0, map_zero]
      have hLeq : (fun a => L (f a)) =ᵐ[μ] 0 := by
        have hneg : (fun a => -L (f a)) =ᵐ[μ] 0 :=
          (integral_eq_zero_iff_of_nonneg_ae
            (hnonpos.mono fun a ha => neg_nonneg.mpr ha) hLi.neg).mp
              (by rw [integral_neg, hLint, neg_zero])
        exact hneg.mono fun a ha => neg_eq_zero.mp ha
      let H : Set α := {a | a ∈ G ∧ L (f a) = 0}
      have hH : ∀ᵐ a ∂μ, a ∈ H := hG.and hLeq
      let K : Submodule ℝ E := L.toLinearMap.ker
      have hK : K ≠ ⊤ := by
        intro htop
        apply hL
        apply ContinuousLinearMap.ext
        intro x
        exact LinearMap.congr_fun (LinearMap.ker_eq_top.mp htop) x
      have hdim : finrank ℝ K < n := (Submodule.finrank_lt hK).trans_eq hn
      have hm : (0 : E) ∈ convexHull ℝ (f '' H) :=
        zero_mem_convexHull_image_of_submodule f H hf hf0 hH K
          (fun a ha => ha.2)
          (fun g hgi hg0 => ih (finrank ℝ K) hdim rfl g H hgi hg0 hH)
      exact hzeroHull ((convexHull_mono (image_mono fun a ha => ha.1)) hm)
    · have hdim : finrank ℝ W < n := (Submodule.finrank_lt hW).trans_eq hn
      exact zero_mem_convexHull_image_of_submodule f G hf hf0 hG W
        (fun a ha => Submodule.subset_span ⟨a, ha, rfl⟩)
        (fun g hgi hg0 => ih (finrank ℝ W) hdim rfl g G hgi hg0 hG)

/-- An integrable finite-dimensional barycenter belongs to the actual convex
hull of values attained on any full-measure good set. -/
theorem integral_mem_convexHull_image
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (G : Set α) (hf : Integrable f μ) (hG : ∀ᵐ a ∂μ, a ∈ G) :
    (∫ a, f a ∂μ) ∈ convexHull ℝ (f '' G) := by
  let b : E := ∫ a, f a ∂μ
  let g : α → E := fun a => f a - b
  have hgi : Integrable g μ := hf.sub (integrable_const b)
  have hg0 : (∫ a, g a ∂μ) = 0 := by
    simp only [g, integral_sub hf (integrable_const b), integral_const,
      probReal_univ, one_smul, b, sub_self]
  have hm : (0 : E) ∈ convexHull ℝ (g '' G) :=
    zero_mem_convexHull_image_aux (finrank ℝ E) rfl g G hgi hg0 hG
  let A : E →ᵃ[ℝ] E := (AffineEquiv.constVAdd ℝ E b).toAffineMap
  have himage : A '' (g '' G) = f '' G := by
    ext x
    constructor
    · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by simp [A, g, vadd_eq_add]⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g a, ⟨a, ha, rfl⟩, by simp [A, g, vadd_eq_add]⟩
  have hmapped : b ∈ A '' convexHull ℝ (g '' G) := ⟨0, hm, by simp [A]⟩
  rwa [A.image_convexHull, himage] at hmapped

/-- The integral can be represented exactly by at most `finrank + 1`
actual points of a full-measure good set, with nonnegative probability
weights. No measurability of the good set itself is required. -/
theorem exists_finite_integral_support
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (G : Set α) (hf : Integrable f μ) (hG : ∀ᵐ a ∂μ, a ∈ G) :
    ∃ n : ℕ, n ≤ finrank ℝ E + 1 ∧
      ∃ (select : Fin n → α) (weight : Fin n → ℝ),
        (∀ j, select j ∈ G) ∧ (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
          (∑ j, weight j • f (select j)) = ∫ a, f a ∂μ := by
  have hm := integral_mem_convexHull_image f G hf hG
  have hrange : range (fun a : G => f a) = f '' G := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← hrange] at hm
  obtain ⟨n, hn, select, weight, hw, hsum, hmean⟩ :=
    exists_finite_moment_support (fun a : G => f a) hm
  exact ⟨n, hn, fun j => select j, weight, fun j => (select j).property, hw, hsum, hmean⟩

section Hermitian

open Matrix
open scoped Matrix.Norms.Frobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable local instance hermitianNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

noncomputable local instance : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (NormedSpace ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

noncomputable local instance hermitianTopologicalSpace :
    TopologicalSpace (selfAdjoint (Matrix ι ι ℂ)) :=
  (hermitianNormedAddCommGroup (ι := ι)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance : ContinuousENorm (selfAdjoint (Matrix ι ι ℂ)) :=
  @SeminormedAddGroup.toContinuousENorm (selfAdjoint (Matrix ι ι ℂ))
    (@SeminormedAddCommGroup.toSeminormedAddGroup (selfAdjoint (Matrix ι ι ℂ))
      (@NormedAddCommGroup.toSeminormedAddCommGroup (selfAdjoint (Matrix ι ι ℂ))
        (hermitianNormedAddCommGroup (ι := ι))))

local instance : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

/-- A constant-trace Hermitian marginal and a real score have an exact
integral representation by at most `card(input)² + 1` actual good points.
The trace constraint is required only on the full-measure good set. -/
theorem exists_hermitian_marginal_score_integral_support
    (marginal : α → selfAdjoint (Matrix ι ι ℂ)) (score : α → ℝ)
    (G : Set α) (M : selfAdjoint (Matrix ι ι ℂ)) (q : ℝ)
    (hmarginal : Integrable marginal μ) (hscore : Integrable score μ)
    (hM : (∫ a, marginal a ∂μ) = M) (hq : (∫ a, score a ∂μ) = q)
    (htrace : ∀ a ∈ G, (marginal a : Matrix ι ι ℂ).trace.re =
      (M : Matrix ι ι ℂ).trace.re) (hG : ∀ᵐ a ∂μ, a ∈ G) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 + 1 ∧
      ∃ (select : Fin n → α) (weight : Fin n → ℝ),
        (∀ j, select j ∈ G) ∧ (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
          (∑ j, weight j • marginal (select j)) = M ∧
          (∑ j, weight j * score (select j)) = q := by
  have hm := integral_mem_convexHull_image (fun a => (marginal a, score a)) G
    (hmarginal.prodMk hscore) hG
  rw [integral_pair hmarginal hscore, hM, hq] at hm
  have hrange : range (fun a : G => (marginal a, score a)) =
      (fun a => (marginal a, score a)) '' G := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← hrange] at hm
  obtain ⟨n, hn, select, weight, hw, hsum, hmarg, hsc⟩ :=
    exists_hermitian_marginal_score_support (fun a : G => marginal a)
      (fun a : G => score a) M q (fun a => htrace a a.property) hm
  exact ⟨n, hn, fun j => select j, weight, fun j => (select j).property,
    hw, hsum, hmarg, hsc⟩

/-- With normalized trace and integrated identity marginal, at most
`card(input)² + 1` actual good outcomes preserve normalization and score. -/
theorem exists_normalized_hermitian_marginal_score_integral_support
    (marginal : α → selfAdjoint (Matrix ι ι ℂ)) (score : α → ℝ)
    (G : Set α) (q : ℝ)
    (hmarginal : Integrable marginal μ) (hscore : Integrable score μ)
    (hM : (∫ a, marginal a ∂μ) = 1) (hq : (∫ a, score a ∂μ) = q)
    (htrace : ∀ a ∈ G, (marginal a : Matrix ι ι ℂ).trace.re = Fintype.card ι)
    (hG : ∀ᵐ a ∂μ, a ∈ G) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 + 1 ∧
      ∃ (select : Fin n → α) (weight : Fin n → ℝ),
        (∀ j, select j ∈ G) ∧ (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
          (∑ j, weight j • marginal (select j)) = 1 ∧
          (∑ j, weight j * score (select j)) = q := by
  apply exists_hermitian_marginal_score_integral_support marginal score G 1 q
    hmarginal hscore hM hq _ hG
  intro a ha
  simpa [Matrix.trace_one] using htrace a ha

end Hermitian

end NLQCLean.ClassicalCommunication

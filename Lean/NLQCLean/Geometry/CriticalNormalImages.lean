/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Geometry.UnitaryNormalVolume

/-!
# Critical normal images and Haar-null unitary sets

Let `f : E → V` be a map into a real coordinate space `V`, decoded into complex
square matrices by a real-linear equivalence `L`. Its right normal thickening is
the map `(x, Q) ↦ L (f x) (I + Q)` on `E × Herm`, written in the real Euclidean
matrix-entry coordinates that carry the normal-volume identity.

* The thickening is smooth whenever `f` is, on the whole product vector space.
* Its full ambient derivative at `(x, Q)` is `(v, R) ↦ L (df v) (I + Q) + L (f x) R`.
  Hence its rank is at most the rank of `df` plus the Hermitian dimension
  `(card n)²`, for every Hermitian `Q`; `I + Q` need not be invertible.
  When `rank df + (card n)² < 2 (card n)²` the full derivative is not surjective.
  This is a pointwise statement about the ambient derivative.
* If every unitary of a Borel set is reached by a decoded map on a
  witness set, the right normal image of the unitaries lies in the thickened
  image of the witness set. When those thickened images are volume-null,
  the normal-volume identity and positivity of the normal mass make the
  unitary set Haar-null.

No nullity of any image is assumed here: it is an explicit hypothesis of
the final Haar statements.
-/

namespace NLQCLean

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius _root_.ContDiff

variable {n : Type*} [Fintype n] [DecidableEq n]

section Definition

variable {E V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The right normal thickening `(x, Q) ↦ L (f x) (I + Q)` over Hermitian `Q`,
in real Euclidean matrix-entry coordinates. -/
noncomputable def normalThickening (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) :
    E × HermitianFrobenius n → EuclideanSpace ℝ ((n × n) × Fin 2) :=
  fun p => matrixFrobeniusCoordinates n n (L (f p.1) * (1 + (p.2 : Matrix n n ℂ)))

theorem normalThickening_apply (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) (x : E)
    (Q : HermitianFrobenius n) :
    normalThickening L f (x, Q) =
      matrixFrobeniusCoordinates n n (L (f x) * (1 + (Q : Matrix n n ℂ))) := rfl

end Definition

section Derivative

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [DecidableEq n] in
/-- The Hermitian matrices form a real space of dimension `(card n)²`. -/
theorem finrank_hermitianFrobenius :
    Module.finrank ℝ (HermitianFrobenius n) = Fintype.card n ^ 2 :=
  (finrank_adjoint_matrix_spaces n).1

/-- The normal thickening of a `C^k` map is `C^k` on the full product space. -/
theorem contDiff_normalThickening (L : V ≃ₗ[ℝ] Matrix n n ℂ) {k : WithTop ℕ∞} {f : E → V}
    (hf : ContDiff ℝ k f) : ContDiff ℝ k (normalThickening L f) := by
  have : FiniteDimensional ℝ V := L.symm.finiteDimensional
  have hL : ContDiff ℝ k (fun p : E × HermitianFrobenius n => L (f p.1)) :=
    (LinearMap.toContinuousLinearMap L.toLinearMap).contDiff.comp (hf.comp contDiff_fst)
  have hQ : ContDiff ℝ k (fun p : E × HermitianFrobenius n => 1 + (p.2 : Matrix n n ℂ)) :=
    contDiff_const.add
      ((selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL.contDiff.comp contDiff_snd)
  exact (matrixFrobeniusCoordinates n n).contDiff.comp (hL.mul hQ)

theorem differentiableAt_normalThickening (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V} {x : E}
    (hf : DifferentiableAt ℝ f x) (Q : HermitianFrobenius n) :
    DifferentiableAt ℝ (normalThickening L f) (x, Q) := by
  have : FiniteDimensional ℝ V := L.symm.finiteDimensional
  have hL : DifferentiableAt ℝ (fun p : E × HermitianFrobenius n => L (f p.1)) (x, Q) :=
    (LinearMap.toContinuousLinearMap L.toLinearMap).differentiableAt.comp _
      (hf.comp _ differentiableAt_fst)
  have hQ : DifferentiableAt ℝ (fun p : E × HermitianFrobenius n => 1 + (p.2 : Matrix n n ℂ))
      (x, Q) :=
    (differentiableAt_const _).add
      ((selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL.differentiableAt.comp _
        differentiableAt_snd)
  exact (matrixFrobeniusCoordinates n n).toContinuousLinearEquiv.differentiableAt.comp _
    (hL.mul hQ)

/-- The full ambient derivative of the normal thickening, in both directions at once. -/
theorem fderiv_normalThickening_apply (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V} {x : E}
    (hf : DifferentiableAt ℝ f x) (Q : HermitianFrobenius n) (v : E)
    (R : HermitianFrobenius n) :
    fderiv ℝ (normalThickening L f) (x, Q) (v, R) =
      matrixFrobeniusCoordinates n n
        (L (fderiv ℝ f x v) * (1 + (Q : Matrix n n ℂ)) + L (f x) * (R : Matrix n n ℂ)) := by
  have : FiniteDimensional ℝ V := L.symm.finiteDimensional
  set D := fderiv ℝ (normalThickening L f) (x, Q)
  have hG : HasFDerivAt (normalThickening L f) D (x, Q) :=
    (differentiableAt_normalThickening L hf Q).hasFDerivAt
  let C : V →L[ℝ] EuclideanSpace ℝ ((n × n) × Fin 2) := LinearMap.toContinuousLinearMap
    ((matrixFrobeniusCoordinates n n).toLinearEquiv.toLinearMap ∘ₗ
      LinearMap.mulRight ℝ (1 + (Q : Matrix n n ℂ)) ∘ₗ L.toLinearMap)
  have h1 : D.comp (ContinuousLinearMap.inl ℝ E (HermitianFrobenius n)) =
      C.comp (fderiv ℝ f x) := by
    have ha : HasFDerivAt (fun y => normalThickening L f (y, Q))
        (D.comp (ContinuousLinearMap.inl ℝ E (HermitianFrobenius n))) x :=
      hG.comp (f := fun y : E => (y, Q)) x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x Q)
    have hb : HasFDerivAt (fun y => C (f y)) (C.comp (fderiv ℝ f x)) x :=
      C.hasFDerivAt.comp x hf.hasFDerivAt
    exact ha.unique hb
  let K : HermitianFrobenius n →L[ℝ] EuclideanSpace ℝ ((n × n) × Fin 2) :=
    LinearMap.toContinuousLinearMap
      ((matrixFrobeniusCoordinates n n).toLinearEquiv.toLinearMap ∘ₗ
        LinearMap.mulLeft ℝ (L (f x)) ∘ₗ (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtype)
  have h2 : D.comp (ContinuousLinearMap.inr ℝ E (HermitianFrobenius n)) = K := by
    have ha : HasFDerivAt (fun S => normalThickening L f (x, S))
        (D.comp (ContinuousLinearMap.inr ℝ E (HermitianFrobenius n))) Q :=
      hG.comp (f := fun S : HermitianFrobenius n => (x, S)) Q
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) x Q)
    have hb : HasFDerivAt
        (fun S : HermitianFrobenius n => matrixFrobeniusCoordinates n n (L (f x)) + K S) K Q :=
      K.hasFDerivAt.const_add _
    refine ha.unique (hb.congr_of_eventuallyEq (Filter.Eventually.of_forall fun S => ?_))
    change matrixFrobeniusCoordinates n n (L (f x) * (1 + (S : Matrix n n ℂ))) =
      matrixFrobeniusCoordinates n n (L (f x)) +
        matrixFrobeniusCoordinates n n (L (f x) * (S : Matrix n n ℂ))
    rw [Matrix.mul_add, Matrix.mul_one, map_add]
  have hsplit : D (v, R) =
      D.comp (ContinuousLinearMap.inl ℝ E (HermitianFrobenius n)) v +
        D.comp (ContinuousLinearMap.inr ℝ E (HermitianFrobenius n)) R := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← map_add]
    simp
  rw [hsplit, h1, h2, map_add]
  rfl

/-- Rank of the full derivative: at most the rank of `df` plus the Hermitian dimension. -/
theorem finrank_range_fderiv_normalThickening_le (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V}
    {x : E} (hf : DifferentiableAt ℝ f x) (Q : HermitianFrobenius n) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (normalThickening L f) (x, Q)).toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) + Fintype.card n ^ 2 := by
  have : FiniteDimensional ℝ V := L.symm.finiteDimensional
  let C : V →ₗ[ℝ] EuclideanSpace ℝ ((n × n) × Fin 2) :=
    (matrixFrobeniusCoordinates n n).toLinearEquiv.toLinearMap ∘ₗ
      LinearMap.mulRight ℝ (1 + (Q : Matrix n n ℂ)) ∘ₗ L.toLinearMap
  let K : HermitianFrobenius n →ₗ[ℝ] EuclideanSpace ℝ ((n × n) × Fin 2) :=
    (matrixFrobeniusCoordinates n n).toLinearEquiv.toLinearMap ∘ₗ
      LinearMap.mulLeft ℝ (L (f x)) ∘ₗ (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtype
  have hle : LinearMap.range (fderiv ℝ (normalThickening L f) (x, Q)).toLinearMap ≤
      (LinearMap.range (fderiv ℝ f x).toLinearMap).map C ⊔ LinearMap.range K := by
    rintro _ ⟨⟨v, R⟩, rfl⟩
    rw [ContinuousLinearMap.coe_coe, fderiv_normalThickening_apply L hf Q v R, map_add]
    exact Submodule.add_mem_sup ⟨fderiv ℝ f x v, ⟨v, rfl⟩, rfl⟩ ⟨R, rfl⟩
  calc
    _ ≤ Module.finrank ℝ ((LinearMap.range (fderiv ℝ f x).toLinearMap).map C ⊔
        LinearMap.range K : Submodule ℝ (EuclideanSpace ℝ ((n × n) × Fin 2))) :=
      Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ ((LinearMap.range (fderiv ℝ f x).toLinearMap).map C) +
        Module.finrank ℝ (LinearMap.range K) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ _ := add_le_add (Submodule.finrank_map_le _ _)
        (K.finrank_range_le.trans finrank_hermitianFrobenius.le)

/-- A rank-deficient point of `f` gives a critical point of the full normal thickening,
for every Hermitian normal coordinate `Q`. -/
theorem not_surjective_fderiv_normalThickening (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V}
    {x : E} (hf : DifferentiableAt ℝ f x) {r : ℕ}
    (hrank : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hr : r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2) (Q : HermitianFrobenius n) :
    ¬ Function.Surjective (fderiv ℝ (normalThickening L f) (x, Q)) := by
  intro hsurj
  have h := finrank_range_fderiv_normalThickening_le L hf Q
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_euclideanSpace,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_fin] at h
  have hsq : Fintype.card n * Fintype.card n * 2 = 2 * Fintype.card n ^ 2 := by ring
  omega

/-- Pointwise critical-set form on an arbitrary witness set `T`: every point of
`T × Herm` is a critical point of the full normal thickening. -/
theorem not_surjective_fderiv_normalThickening_on (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V}
    {T : Set E} (hf : ∀ x ∈ T, DifferentiableAt ℝ f x) {r : ℕ}
    (hrank : ∀ x ∈ T, Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hr : r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2) :
    ∀ p ∈ T ×ˢ (Set.univ : Set (HermitianFrobenius n)),
      ¬ Function.Surjective (fderiv ℝ (normalThickening L f) p) := by
  rintro ⟨x, Q⟩ ⟨hx, -⟩
  exact not_surjective_fderiv_normalThickening L (hf x hx) (hrank x hx) hr Q

end Derivative

section Covering

/-- If each unitary of `S` is a decoded value of `f` on `T`, then the right normal
image of `S`, at every radius, lies in the thickened image of `T`. -/
theorem rightNormalImage_subset_image_normalThickening {E V : Type*} [AddCommGroup V]
    [Module ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) (T : Set E)
    {S : Set (Matrix.unitaryGroup n ℂ)}
    (hcover : ∀ U ∈ S, ∃ x ∈ T, L (f x) = (U : Matrix n n ℂ)) (s : ℝ) :
    {y | ∃ U ∈ S, ∃ Q : Matrix n n ℂ, Q.IsHermitian ∧ ‖Q‖ < s ∧
      matrixFrobeniusCoordinates n n ((U : Matrix n n ℂ) * (1 + Q)) = y} ⊆
      normalThickening L f '' (T ×ˢ Set.univ) := by
  rintro y ⟨U, hU, Q, hQ, -, rfl⟩
  obtain ⟨x, hx, hxU⟩ := hcover U hU
  exact ⟨(x, ⟨Q, hQ⟩), ⟨hx, Set.mem_univ _⟩, by rw [normalThickening_apply, hxU]⟩

/-- Family form: the right normal image lies in the union of the thickened images. -/
theorem rightNormalImage_subset_iUnion_image_normalThickening {ι : Type*} {E V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (L : ∀ i, V i ≃ₗ[ℝ] Matrix n n ℂ) (f : ∀ i, E i → V i) (T : ∀ i, Set (E i))
    {S : Set (Matrix.unitaryGroup n ℂ)}
    (hcover : ∀ U ∈ S, ∃ i, ∃ x ∈ T i, L i (f i x) = (U : Matrix n n ℂ)) (s : ℝ) :
    {y | ∃ U ∈ S, ∃ Q : Matrix n n ℂ, Q.IsHermitian ∧ ‖Q‖ < s ∧
      matrixFrobeniusCoordinates n n ((U : Matrix n n ℂ) * (1 + Q)) = y} ⊆
      ⋃ i, normalThickening (L i) (f i) '' (T i ×ˢ Set.univ) := by
  rintro y ⟨U, hU, Q, hQ, -, rfl⟩
  obtain ⟨i, x, hx, hxU⟩ := hcover U hU
  exact Set.mem_iUnion.mpr
    ⟨i, (x, ⟨Q, hQ⟩), ⟨hx, Set.mem_univ _⟩, by rw [normalThickening_apply, hxU]⟩

end Covering

section Haar

/-- A Borel unitary set whose right normal image of some radius `0 < s ≤ 1/2` lies in a
volume-null set is Haar-null. -/
theorem unitaryHaar_eq_zero_of_rightNormalImage_subset_null {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ 1 / 2) {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S)
    {N : Set (EuclideanSpace ℝ ((n × n) × Fin 2))} (hN : volume N = 0)
    (hsub : {y | ∃ U ∈ S, ∃ Q : Matrix n n ℂ, Q.IsHermitian ∧ ‖Q‖ < s ∧
      matrixFrobeniusCoordinates n n ((U : Matrix n n ℂ) * (1 + Q)) = y} ⊆ N) :
    unitaryHaar n S = 0 := by
  have hzero : unitaryNormalMeasure n s Set.univ * unitaryHaar n S = 0 := by
    rw [← normalVolume_eq_total_mul_haar n hs' hS]
    exact measure_mono_null hsub hN
  exact (mul_eq_zero.mp hzero).resolve_left (unitaryNormalMeasure_total_pos n hs hs').ne'

/-- A Borel unitary set covered by decoded values of countably many maps is Haar-null,
provided each thickened witness image is volume-null. -/
theorem unitaryHaar_eq_zero_of_normalThickening_cover {ι : Type*} [Countable ι]
    {E V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (L : ∀ i, V i ≃ₗ[ℝ] Matrix n n ℂ) (f : ∀ i, E i → V i) (T : ∀ i, Set (E i))
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ i, ∃ x ∈ T i, L i (f i x) = (U : Matrix n n ℂ))
    (hnull : ∀ i, volume (normalThickening (L i) (f i) '' (T i ×ˢ Set.univ)) = 0) :
    unitaryHaar n S = 0 :=
  unitaryHaar_eq_zero_of_rightNormalImage_subset_null (s := 1 / 4) (by norm_num) (by norm_num)
    hS (measure_iUnion_null hnull)
    (rightNormalImage_subset_iUnion_image_normalThickening L f T hcover _)

/-- Single-map form of `unitaryHaar_eq_zero_of_normalThickening_cover`. -/
theorem unitaryHaar_eq_zero_of_normalThickening_image {E V : Type*} [AddCommGroup V]
    [Module ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) (T : Set E)
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ x ∈ T, L (f x) = (U : Matrix n n ℂ))
    (hnull : volume (normalThickening L f '' (T ×ˢ Set.univ)) = 0) :
    unitaryHaar n S = 0 :=
  unitaryHaar_eq_zero_of_rightNormalImage_subset_null (s := 1 / 4) (by norm_num) (by norm_num)
    hS hnull (rightNormalImage_subset_image_normalThickening L f T hcover _)

end Haar

end NLQCLean

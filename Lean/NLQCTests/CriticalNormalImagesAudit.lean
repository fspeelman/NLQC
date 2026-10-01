/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NLQCLean.Geometry.CriticalNormalImages

/-!
# Audit of the critical normal-image lemmas

The full types of the normal-thickening API are frozen with `#guard_msgs`,
as are their axiom lists, which may contain only `propext`,
`Classical.choice` and `Quot.sound`. The examples check that

* the critical-point statement is pointwise on an arbitrary witness set,
  with no openness or measurability, and holds for a Hermitian coordinate
  with `I + Q = 0`;
* the rank hypothesis has the form produced by the existing ambient
  rank/error decompositions at zero error;
* the final Haar statement composes with a vector Sard theorem, supplied
  here only as an explicit local argument of an example, and with families
  of maps whose source and coordinate spaces do not depend on the index.
-/

set_option format.width 120

open NLQCLean
open scoped Matrix.Norms.Frobenius ContDiff

/-! ## Frozen full types -/

/--
info: @normalThickening : {n : Type u_1} →
  [inst : Fintype n] →
    [DecidableEq n] →
      {E : Type u_2} →
        {V : Type u_3} →
          [inst_2 : AddCommGroup V] →
            [inst_3 : Module ℝ V] →
              (V ≃ₗ[ℝ] Matrix n n ℂ) → (E → V) → E × HermitianFrobenius n → EuclideanSpace ℝ ((n × n) × Fin 2)
-/
#guard_msgs in
#check @normalThickening

/--
info: @normalThickening_apply : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2} {V : Type u_3}
  [inst_2 : AddCommGroup V] [inst_3 : Module ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) (x : E)
  (Q : HermitianFrobenius n), normalThickening L f (x, Q) = (matrixFrobeniusCoordinates n n) (L (f x) * (1 + ↑Q))
-/
#guard_msgs in
#check @normalThickening_apply

/--
info: @finrank_hermitianFrobenius : ∀ {n : Type u_1} [inst : Fintype n],
  Module.finrank ℝ (HermitianFrobenius n) = Fintype.card n ^ 2
-/
#guard_msgs in
#check @finrank_hermitianFrobenius

/--
info: @contDiff_normalThickening : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2} {V : Type u_3}
  [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [inst_4 : NormedAddCommGroup V] [inst_5 : NormedSpace ℝ V]
  (L : V ≃ₗ[ℝ] Matrix n n ℂ) {k : ℕ∞ω} {f : E → V}, ContDiff ℝ k f → ContDiff ℝ k (normalThickening L f)
-/
#guard_msgs in
#check @contDiff_normalThickening

/--
info: @differentiableAt_normalThickening : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2}
  {V : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [inst_4 : NormedAddCommGroup V]
  [inst_5 : NormedSpace ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V} {x : E},
  DifferentiableAt ℝ f x → ∀ (Q : HermitianFrobenius n), DifferentiableAt ℝ (normalThickening L f) (x, Q)
-/
#guard_msgs in
#check @differentiableAt_normalThickening

/--
info: @fderiv_normalThickening_apply : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2}
  {V : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [inst_4 : NormedAddCommGroup V]
  [inst_5 : NormedSpace ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V} {x : E},
  DifferentiableAt ℝ f x →
    ∀ (Q : HermitianFrobenius n) (v : E) (R : HermitianFrobenius n),
      (fderiv ℝ (normalThickening L f) (x, Q)) (v, R) =
        (matrixFrobeniusCoordinates n n) (L ((fderiv ℝ f x) v) * (1 + ↑Q) + L (f x) * ↑R)
-/
#guard_msgs in
#check @fderiv_normalThickening_apply

/--
info: @finrank_range_fderiv_normalThickening_le : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2}
  {V : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [inst_4 : NormedAddCommGroup V]
  [inst_5 : NormedSpace ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V} {x : E},
  DifferentiableAt ℝ f x →
    ∀ (Q : HermitianFrobenius n),
      Module.finrank ℝ ↥(↑(fderiv ℝ (normalThickening L f) (x, Q))).range ≤
        Module.finrank ℝ ↥(↑(fderiv ℝ f x)).range + Fintype.card n ^ 2
-/
#guard_msgs in
#check @finrank_range_fderiv_normalThickening_le

/--
info: @not_surjective_fderiv_normalThickening : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2}
  {V : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [inst_4 : NormedAddCommGroup V]
  [inst_5 : NormedSpace ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V} {x : E},
  DifferentiableAt ℝ f x →
    ∀ {r : ℕ},
      Module.finrank ℝ ↥(↑(fderiv ℝ f x)).range ≤ r →
        r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2 →
          ∀ (Q : HermitianFrobenius n), ¬Function.Surjective ⇑(fderiv ℝ (normalThickening L f) (x, Q))
-/
#guard_msgs in
#check @not_surjective_fderiv_normalThickening

/--
info: @not_surjective_fderiv_normalThickening_on : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {E : Type u_2}
  {V : Type u_3} [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace ℝ E] [inst_4 : NormedAddCommGroup V]
  [inst_5 : NormedSpace ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) {f : E → V} {T : Set E},
  (∀ x ∈ T, DifferentiableAt ℝ f x) →
    ∀ {r : ℕ},
      (∀ x ∈ T, Module.finrank ℝ ↥(↑(fderiv ℝ f x)).range ≤ r) →
        r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2 →
          ∀ p ∈ T ×ˢ Set.univ, ¬Function.Surjective ⇑(fderiv ℝ (normalThickening L f) p)
-/
#guard_msgs in
#check @not_surjective_fderiv_normalThickening_on

/--
info: @rightNormalImage_subset_image_normalThickening : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n]
  {E : Type u_2} {V : Type u_3} [inst_2 : AddCommGroup V] [inst_3 : Module ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V)
  (T : Set E) {S : Set ↥(Matrix.unitaryGroup n ℂ)},
  (∀ U ∈ S, ∃ x ∈ T, L (f x) = ↑U) →
    ∀ (s : ℝ),
      {y | ∃ U ∈ S, ∃ Q, Q.IsHermitian ∧ ‖Q‖ < s ∧ (matrixFrobeniusCoordinates n n) (↑U * (1 + Q)) = y} ⊆
        normalThickening L f '' T ×ˢ Set.univ
-/
#guard_msgs in
#check @rightNormalImage_subset_image_normalThickening

/--
info: @rightNormalImage_subset_iUnion_image_normalThickening : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n]
  {ι : Type u_2} {E : ι → Type u_3} {V : ι → Type u_4} [inst_2 : (i : ι) → AddCommGroup (V i)]
  [inst_3 : (i : ι) → Module ℝ (V i)] (L : (i : ι) → V i ≃ₗ[ℝ] Matrix n n ℂ) (f : (i : ι) → E i → V i)
  (T : (i : ι) → Set (E i)) {S : Set ↥(Matrix.unitaryGroup n ℂ)},
  (∀ U ∈ S, ∃ i, ∃ x ∈ T i, (L i) (f i x) = ↑U) →
    ∀ (s : ℝ),
      {y | ∃ U ∈ S, ∃ Q, Q.IsHermitian ∧ ‖Q‖ < s ∧ (matrixFrobeniusCoordinates n n) (↑U * (1 + Q)) = y} ⊆
        ⋃ i, normalThickening (L i) (f i) '' T i ×ˢ Set.univ
-/
#guard_msgs in
#check @rightNormalImage_subset_iUnion_image_normalThickening

/--
info: @unitaryHaar_eq_zero_of_rightNormalImage_subset_null : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n]
  {s : ℝ},
  0 < s →
    s ≤ 1 / 2 →
      ∀ {S : Set ↥(Matrix.unitaryGroup n ℂ)},
        MeasurableSet S →
          ∀ {N : Set (EuclideanSpace ℝ ((n × n) × Fin 2))},
            MeasureTheory.volume N = 0 →
              {y | ∃ U ∈ S, ∃ Q, Q.IsHermitian ∧ ‖Q‖ < s ∧ (matrixFrobeniusCoordinates n n) (↑U * (1 + Q)) = y} ⊆ N →
                (unitaryHaar n) S = 0
-/
#guard_msgs in
#check @unitaryHaar_eq_zero_of_rightNormalImage_subset_null

/--
info: @unitaryHaar_eq_zero_of_normalThickening_cover : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n]
  {ι : Type u_2} [Countable ι] {E : ι → Type u_3} {V : ι → Type u_4} [inst_3 : (i : ι) → AddCommGroup (V i)]
  [inst_4 : (i : ι) → Module ℝ (V i)] (L : (i : ι) → V i ≃ₗ[ℝ] Matrix n n ℂ) (f : (i : ι) → E i → V i)
  (T : (i : ι) → Set (E i)) {S : Set ↥(Matrix.unitaryGroup n ℂ)},
  MeasurableSet S →
    (∀ U ∈ S, ∃ i, ∃ x ∈ T i, (L i) (f i x) = ↑U) →
      (∀ (i : ι), MeasureTheory.volume (normalThickening (L i) (f i) '' T i ×ˢ Set.univ) = 0) → (unitaryHaar n) S = 0
-/
#guard_msgs in
#check @unitaryHaar_eq_zero_of_normalThickening_cover

/--
info: @unitaryHaar_eq_zero_of_normalThickening_image : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n]
  {E : Type u_2} {V : Type u_3} [inst_2 : AddCommGroup V] [inst_3 : Module ℝ V] (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V)
  (T : Set E) {S : Set ↥(Matrix.unitaryGroup n ℂ)},
  MeasurableSet S →
    (∀ U ∈ S, ∃ x ∈ T, L (f x) = ↑U) →
      MeasureTheory.volume (normalThickening L f '' T ×ˢ Set.univ) = 0 → (unitaryHaar n) S = 0
-/
#guard_msgs in
#check @unitaryHaar_eq_zero_of_normalThickening_image

/-! ## Guarded axiom lists -/

/--
info: 'NLQCLean.normalThickening' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms normalThickening

/--
info: 'NLQCLean.normalThickening_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms normalThickening_apply

/--
info: 'NLQCLean.finrank_hermitianFrobenius' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finrank_hermitianFrobenius

/--
info: 'NLQCLean.contDiff_normalThickening' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms contDiff_normalThickening

/--
info: 'NLQCLean.differentiableAt_normalThickening' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms differentiableAt_normalThickening

/--
info: 'NLQCLean.fderiv_normalThickening_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fderiv_normalThickening_apply

/--
info: 'NLQCLean.finrank_range_fderiv_normalThickening_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finrank_range_fderiv_normalThickening_le

/--
info: 'NLQCLean.not_surjective_fderiv_normalThickening' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_surjective_fderiv_normalThickening

/--
info: 'NLQCLean.not_surjective_fderiv_normalThickening_on' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_surjective_fderiv_normalThickening_on

/--
info: 'NLQCLean.rightNormalImage_subset_image_normalThickening' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rightNormalImage_subset_image_normalThickening

/--
info: 'NLQCLean.rightNormalImage_subset_iUnion_image_normalThickening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rightNormalImage_subset_iUnion_image_normalThickening

/--
info: 'NLQCLean.unitaryHaar_eq_zero_of_rightNormalImage_subset_null' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unitaryHaar_eq_zero_of_rightNormalImage_subset_null

/--
info: 'NLQCLean.unitaryHaar_eq_zero_of_normalThickening_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unitaryHaar_eq_zero_of_normalThickening_cover

/--
info: 'NLQCLean.unitaryHaar_eq_zero_of_normalThickening_image' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unitaryHaar_eq_zero_of_normalThickening_image

/-! ## Regression examples -/

namespace NLQCTests.CriticalNormalImages

open MeasureTheory

section Pointwise

variable {n E V : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The critical-point conclusion needs hypotheses only at the points of an
arbitrary witness set `T`; no openness, measurability or smoothness off `T`. -/
example (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) (T : Set E) {r : ℕ}
    (hf : ∀ x ∈ T, DifferentiableAt ℝ f x)
    (hrank : ∀ x ∈ T, Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hr : r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2) :
    ∀ p ∈ T ×ˢ (Set.univ : Set (HermitianFrobenius n)),
      ¬ Function.Surjective (fderiv ℝ (normalThickening L f) p) :=
  not_surjective_fderiv_normalThickening_on L hf hrank hr

/-- The Hermitian coordinate `Q = -I` makes `I + Q = 0`; no invertibility is needed. -/
example (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) (x : E) {r : ℕ}
    (hf : DifferentiableAt ℝ f x)
    (hrank : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hr : r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2) :
    ¬ Function.Surjective
      (fderiv ℝ (normalThickening L f) (x, ⟨-1, Matrix.isHermitian_one.neg⟩)) :=
  not_surjective_fderiv_normalThickening L hf hrank hr _

/-- At zero error an ambient rank/error decomposition `df = A + R` with `‖R‖ ≤ 0`
supplies the rank hypothesis in exactly the required form. -/
example (f : E → V) (x : E) (A R : E →L[ℝ] V) {r : ℕ} (hdec : fderiv ℝ f x = A + R)
    (hR : ‖R‖ ≤ 0) (hA : Module.finrank ℝ (LinearMap.range A.toLinearMap) ≤ r) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r := by
  rw [hdec, norm_le_zero_iff.mp hR, add_zero]
  exact hA

/-- A concrete critical witness set: a constant map on an arbitrary subset of `ℝ`. -/
example (T : Set ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ p ∈ T ×ˢ (Set.univ : Set (HermitianFrobenius (Fin 2))),
      ¬ Function.Surjective
        (fderiv ℝ (normalThickening (LinearEquiv.refl ℝ (Matrix (Fin 2) (Fin 2) ℂ))
          (fun _ : ℝ => M)) p) := by
  refine not_surjective_fderiv_normalThickening_on (r := 0) _
    (fun x _ => differentiableAt_const M) (fun x _ => ?_) (by simp)
  simp

end Pointwise

section Composition

/-- The final Haar statement composes with a vector Sard theorem for the full
normal thickenings. Sard is an explicit argument of this example only. The
family has fixed source and coordinate spaces, as the witness applications do. -/
example {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Countable ι]
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (sard : ∀ (g : E × HermitianFrobenius n → EuclideanSpace ℝ ((n × n) × Fin 2))
      (s : Set (E × HermitianFrobenius n)), ContDiff ℝ ∞ g →
        (∀ p ∈ s, ¬ Function.Surjective (fderiv ℝ g p)) → volume (g '' s) = 0)
    (L : ι → V ≃ₗ[ℝ] Matrix n n ℂ) (f : ι → E → V) (T : ι → Set E)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) {r : ℕ}
    (hrank : ∀ i, ∀ x ∈ T i,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (f i) x).toLinearMap) ≤ r)
    (hr : r + Fintype.card n ^ 2 < 2 * Fintype.card n ^ 2)
    {S : Set (Matrix.unitaryGroup n ℂ)} (hS : MeasurableSet S)
    (hcover : ∀ U ∈ S, ∃ i, ∃ x ∈ T i, L i (f i x) = (U : Matrix n n ℂ)) :
    unitaryHaar n S = 0 :=
  unitaryHaar_eq_zero_of_normalThickening_cover L f T hS hcover fun i =>
    sard _ _ (contDiff_normalThickening (L i) (hf i))
      (not_surjective_fderiv_normalThickening_on (L i)
        (fun x _ => ((hf i).differentiable (by simp)).differentiableAt) (hrank i) hr)

/-- The covering set is literally the left side of the normal-volume identity. -/
example {n : Type*} [Fintype n] [DecidableEq n] {S : Set (Matrix.unitaryGroup n ℂ)}
    (hS : MeasurableSet S) {E V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V ≃ₗ[ℝ] Matrix n n ℂ) (f : E → V) (T : Set E)
    (hcover : ∀ U ∈ S, ∃ x ∈ T, L (f x) = (U : Matrix n n ℂ)) :
    unitaryNormalMeasure n (1 / 4) Set.univ * unitaryHaar n S ≤
      volume (normalThickening L f '' (T ×ˢ Set.univ)) := by
  rw [← normalVolume_eq_total_mul_haar n (by norm_num) hS]
  exact measure_mono (rightNormalImage_subset_image_normalThickening L f T hcover _)

end Composition

end NLQCTests.CriticalNormalImages

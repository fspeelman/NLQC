import NLQCLean.Approx.PVMSharpFreezing
import NLQCLean.LinearAlgebra.CrossedSinglet
import NLQCLean.LinearAlgebra.FlatGroupedTail

/-!
# Corrected reference projections and near-Bell freezing

The reference correction contracts the normalized Choi-vector distance.
This supplies the actual reference-state comparison used to bound both
messages. Flat column spectra also permit a smaller total garbage allocation.
The source is `lem:bell-compression` in the revised robust companion.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- Contract both Choi-reference indices after a correction controlled by
Bob's output label. Alice's output and both environments remain present. -/
def nearBellReferenceProjection {d : ℕ} {δ εA εB : Type*}
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (F : Matrix ((δ × εA) × (δ × εB)) (Fin d × Fin d) ℂ) :
    Matrix (δ × εA) (δ × εB) ℂ :=
  fun x y => ∑ a, ∑ b, C y.1 a b * F (x, y) (a, b)

theorem nearBellReferenceProjection_sub {d : ℕ} {δ εA εB : Type*}
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (F G : Matrix ((δ × εA) × (δ × εB)) (Fin d × Fin d) ℂ) :
    nearBellReferenceProjection C (F - G) =
      nearBellReferenceProjection C F - nearBellReferenceProjection C G := by
  ext x y
  simp only [nearBellReferenceProjection, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The unnormalized reference contraction has operator norm at most
`sqrt d`; after Choi and reference-pair normalization it is a contraction. -/
theorem nearBellReferenceProjection_norm_sq_le
    {d : ℕ} {δ εA εB : Type*} [Fintype δ] [Fintype εA] [Fintype εB]
    (C : δ → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ i, ‖C i‖ ^ 2 ≤ (d : ℝ))
    (F : Matrix ((δ × εA) × (δ × εB)) (Fin d × Fin d) ℂ) :
    ‖nearBellReferenceProjection C F‖ ^ 2 ≤ (d : ℝ) * ‖F‖ ^ 2 := by
  have hrow (x : δ × εA) (y : δ × εB) :
      Complex.normSq (nearBellReferenceProjection C F x y) ≤
        (d : ℝ) * ∑ q : Fin d × Fin d, Complex.normSq (F (x, y) q) := by
    have h1 : ‖∑ q : Fin d × Fin d, C y.1 q.1 q.2 * F (x, y) q‖ ≤
        ∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ * ‖F (x, y) q‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun q : Fin d × Fin d => ‖C y.1 q.1 q.2‖)
      (fun q : Fin d × Fin d => ‖F (x, y) q‖)
    have hnorm : (∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ ^ 2) = ‖C y.1‖ ^ 2 := by
      simp only [frobNorm_sq, Fintype.sum_prod_type]
    calc
      _ = ‖∑ q : Fin d × Fin d, C y.1 q.1 q.2 * F (x, y) q‖ ^ 2 := by
        simp only [nearBellReferenceProjection, Complex.normSq_eq_norm_sq, Fintype.sum_prod_type]
      _ ≤ (∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ * ‖F (x, y) q‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ q : Fin d × Fin d, ‖C y.1 q.1 q.2‖ ^ 2) *
          ∑ q : Fin d × Fin d, ‖F (x, y) q‖ ^ 2 := h2
      _ ≤ _ := by
        rw [hnorm]
        simp only [Complex.normSq_eq_norm_sq]
        exact mul_le_mul_of_nonneg_right (hC y.1) (Finset.sum_nonneg fun q _ => sq_nonneg _)
  calc
    _ = ∑ x, ∑ y, Complex.normSq (nearBellReferenceProjection C F x y) := by
      simp only [← frobNormSq_eq_norm_sq, frobNormSq_eq_sum_normSq, Fintype.sum_prod_type]
    _ ≤ ∑ x, ∑ y, (d : ℝ) * ∑ q : Fin d × Fin d, Complex.normSq (F (x, y) q) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hrow x y
    _ = _ := by
      simp only [← frobNormSq_eq_norm_sq, frobNormSq_eq_sum_normSq,
        Fintype.sum_prod_type, Finset.mul_sum]


section Flat

variable {ιA ιB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq εA] [DecidableEq εB]
variable [Nonempty ιA] [Nonempty ιB]

omit [DecidableEq εB] in
/-- **Freezing with flat target columns.** If every column Schmidt weight of
the target basis is at least `β`, so that `c = β |ιA|` is positive, the frozen
environments can be chosen with total Schmidt rank at most `m + D` whenever
`K ≤ m |ιA|`, at normalized distance `√(2ε(1 + c)/c)`. The retained top-`m`
mass is at least `(1 - ε)(1 - ε/c)` because the weights sum to the score. -/
theorem exists_pvm_frozen_of_choi_rank_flat
    {M : Matrix (ιA × ιB) (ιA × ιB) ℂ}
    {F : Matrix (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) (ιA × ιB) ℂ}
    (hM : IsIsometry M) (hF : IsIsometry F)
    {K m : ℕ} (hK : (tensorChoiMatrix F).rank ≤ K) (hKm : K ≤ m * Fintype.card ιA)
    {β : ℝ} (hβ0 : 0 ≤ β) (hc0 : 0 < β * Fintype.card ιA)
    (hflat : ∀ i j, β ≤ schmidtWeights (pvmConjugateColumnMatrix M i) j)
    {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / 2)
    (hq : 1 - ε ≤ scorePVM M (channelOf
      (F.submatrix (outputRegroup (ιA × ιB) (ιA × ιB) εA εB) id))) :
    ∃ u : (ιA × ιB) → εA × εB → ℂ, (∀ i, IsUnitVector (u i)) ∧
      (∑ i, schmidtRank (u i)) ≤ m + Fintype.card (ιA × ιB) ∧
      ‖F - flagIsometry u * Mᴴ‖ / Real.sqrt (Fintype.card (ιA × ιB) : ℝ) ≤
        Real.sqrt (2 * ε * (1 + β * Fintype.card ιA) / (β * Fintype.card ιA)) := by
  classical
  have hout : Nonempty (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) := by
    rcases isEmpty_or_nonempty (((ιA × ιB) × εA) × ((ιA × ιB) × εB)) with he | hn
    · let := he
      let i : ιA × ιB := Classical.choice inferInstance
      have hi := congrArg (fun X : Matrix (ιA × ιB) (ιA × ιB) ℂ => X i i) hF
      simp [Matrix.mul_apply] at hi
    · exact hn
  obtain ⟨⟨⟨_, eA⟩, ⟨_, eB⟩⟩⟩ := hout
  let : Nonempty εA := ⟨eA⟩
  let : Nonempty εB := ⟨eB⟩
  set c := β * Fintype.card ιA with hc
  let A : (ιA × ιB) → Matrix εA εB ℂ := fun i => resourceMatrix (pvmEnvironment M F i)
  have hA : ∀ i, ‖A i‖ ≤ 1 := fun i => norm_resourceMatrix_pvmEnvironment_le_one hF hM i
  let t : ℝ := (Fintype.card (ιA × ιB) : ℝ)⁻¹
  have hD : (0 : ℝ) < Fintype.card (ιA × ιB) := by exact_mod_cast Fintype.card_pos
  have ht0 : 0 ≤ t := inv_nonneg.mpr hD.le
  let aw : (ιA × ιB) × εA → ℝ := fun pc => t * schmidtWeights (A pc.1) pc.2
  have haw : ∀ pc, 0 ≤ aw pc := fun pc => mul_nonneg ht0 (schmidtWeights_nonneg _ _)
  -- the selected support and the normalized blocks
  obtain ⟨S, hScard, hSmass⟩ := exists_topWeightMass_support m aw
  let s : (ιA × ιB) → Finset εA := fun i => Finset.univ.filter fun c => (i, c) ∈ S
  have hsS : ∑ i, (s i).card = S.card := by
    have h1 : ∀ i, (s i).card = (S.filter fun q => q.1 = i).card := by
      intro i
      refine Finset.card_bij (fun c _ => (i, c)) ?_ ?_ ?_
      · intro c hc'
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        simp [hc']
      · intro c₁ _ c₂ _ h
        simpa using h
      · intro q hq
        simp only [Finset.mem_filter] at hq
        refine ⟨q.2, ?_, ?_⟩
        · simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hq.2]
          exact hq.1
        · ext <;> simp [hq.2]
    simp only [h1]
    exact (Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_univ q.1)).symm
  choose V hV _ hgram using fun i => exists_schmidt_coordinates (A i)
  choose U hU hUrank _ hinner hupper using fun i =>
    exists_normalized_spectral_support (A i) (V i) (s i) (hA i) (hV i) (hgram i)
  let u : (ιA × ιB) → εA × εB → ℂ := fun i e => U i e.1 e.2
  have hu (i : ιA × ιB) : IsUnitVector (u i) :=
    (isUnitVector_iff_norm_resourceMatrix (u i)).mpr (hU i)
  have hM' : IsIsometry Mᴴ := by
    rw [IsIsometry, Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hM
  have hCu : IsIsometry (flagIsometry u * Mᴴ) :=
    (isIsometry_flagIsometry u hu).mul hM'
  -- retained mass
  have hle (i : ιA × ιB) : (∑ c ∈ s i, schmidtWeights (A i) c) ≤ (frobInner (U i) (A i)).re := by
    have hnonneg : 0 ≤ ∑ c ∈ s i, schmidtWeights (A i) c :=
      Finset.sum_nonneg fun c _ => schmidtWeights_nonneg _ _
    have hsqrt := Real.sq_sqrt hnonneg
    have hroot0 := Real.sqrt_nonneg (∑ c ∈ s i, schmidtWeights (A i) c)
    have hroot1 := (hinner i).trans (hupper i)
    nlinarith [hinner i, mul_nonneg hroot0 (sub_nonneg.mpr hroot1)]
  have hLam : topWeightMass m aw ≤ t * ∑ i, (frobInner (U i) (A i)).re := by
    rw [hSmass]
    have hsplit : ∑ q ∈ S, aw q = ∑ i, ∑ c ∈ s i, aw (i, c) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Finset.univ)
        (fun q _ => Finset.mem_univ q.1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_bij (fun q _ => q.2) ?_ ?_ ?_ ?_
      · intro q hq
        simp only [Finset.mem_filter] at hq
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hq.2]
        exact hq.1
      · intro q₁ h₁ q₂ h₂ h
        simp only [Finset.mem_filter] at h₁ h₂
        exact Prod.ext (h₁.2.trans h₂.2.symm) h
      · intro c hc'
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        exact ⟨(i, c), by simp [hc'], rfl⟩
      · intro q hq
        simp only [Finset.mem_filter] at hq
        rw [← hq.2]
    rw [hsplit, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      simp only [aw, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hle i) ht0
  -- the score bound through the flat grouped tail
  let b : (ιA × ιB) × εA → ιA → ℝ := fun pc j => schmidtWeights (pvmConjugateColumnMatrix M pc.1) j
  have hb1 : ∀ pc, ∑ j, b pc j = 1 := fun pc => by
    simp only [b]
    rw [sum_schmidtWeights, norm_conjugate_pvmColumnMatrix hM pc.1, one_pow]
  have hgrouped := topWeightMass_grouped_le_of_flat aw b haw hβ0 (fun pc j => hflat pc.1 j) hb1 hKm
  have hreindex : schmidtMass K (tensorChoiMatrix (pvmProjectedDilation M F)) =
      topWeightMass K (fun q : ((ιA × ιB) × εA) × ιA => aw q.1 * b q.1 q.2) := by
    rw [pvmProjectedDilation, schmidtMass_tensorChoiMatrix_flag_mul_adjoint]
    let e : ((ιA × ιB) × εA) × ιA ≃ (εA × ιA) × (ιA × ιB) :=
      { toFun := fun q => ((q.1.2, q.2), q.1.1)
        invFun := fun p => ((p.2, p.1.1), p.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← topWeightMass_reindex e K]
    congr 1
    funext q
    simp only [aw, b, e, Equiv.coe_fn_mk, A, mul_assoc]
    rfl
  have hscore := scorePVM_sq_le_schmidtMass_pvmProjected M hF hK
  set q := scorePVM M (channelOf (F.submatrix (outputRegroup (ιA × ιB) (ιA × ιB) εA εB) id))
  have hq0 : 0 ≤ q := scorePVM_channelOf_regrouped_nonneg F M
  have hsum_aw : ∑ pc, aw pc = t * ∑ i, ‖A i‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [aw, ← Finset.mul_sum]
      rw [sum_schmidtWeights]
  -- the weights sum to the score
  have hqsum : ∑ pc, aw pc = q := by
    have h := frobInner_tensorChoiMatrix_pvmProjected M F
    rw [frobInner_tensorChoiMatrix, frobInner_pvmProjectedDilation] at h
    rw [hsum_aw]
    have hA2 : ∀ i, ‖A i‖ ^ 2 = ∑ e, Complex.normSq (pvmEnvironment M F i e) :=
      fun i => norm_sq_resourceMatrix _
    simp only [hA2, t]
    push_cast at h
    exact Complex.ofReal_injective (by push_cast; exact h)
  have hlow : (1 - ε) * (c - ε) ≤ c * topWeightMass m aw := by
    have h1 := hscore.trans (hreindex ▸ hgrouped)
    rw [hqsum] at h1
    have hfac : 0 ≤ (q - (1 - ε)) * (q - ε + c) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  -- overlap with the frozen dilation
  have hinnerC : (frobInner (tensorChoiMatrix (flagIsometry u * Mᴴ))
      (tensorChoiMatrix F)).re = t * ∑ i, (frobInner (U i) (A i)).re := by
    rw [frobInner_tensorChoiMatrix, frobInner_flag_mul_adjoint]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul, Complex.re_sum]
    simp only [t, frobInner, A, u, resourceMatrix_apply, Fintype.sum_prod_type, Complex.re_sum]
  have hres : ‖tensorChoiMatrix F - tensorChoiMatrix (flagIsometry u * Mᴴ)‖ ^ 2 ≤
      2 * ε * (1 + c) / c := by
    rw [frobNorm_sub_sq, norm_tensorChoiMatrix_of_isometry hF,
      norm_tensorChoiMatrix_of_isometry hCu, hinnerC]
    have hΛ : (1 - ε) * (c - ε) / c ≤ topWeightMass m aw := by
      rw [div_le_iff₀ hc0]; linarith
    have hexp : 2 * ε * (1 + c) / c = 2 - 2 * ((1 - ε) * (c - ε) / c) + 2 * ε ^ 2 / c := by
      field_simp
      ring
    have hε2 : 0 ≤ 2 * ε ^ 2 / c := by positivity
    rw [hexp]
    nlinarith [hLam, hΛ]
  refine ⟨u, hu, ?_, ?_⟩
  · calc ∑ i, schmidtRank (u i) ≤ ∑ i, ((s i).card + 1) := Finset.sum_le_sum fun i _ => by
          exact hUrank i
      _ = (∑ i, (s i).card) + Fintype.card (ιA × ιB) := by simp [Finset.sum_add_distrib]
      _ ≤ m + Fintype.card (ιA × ιB) := by rw [hsS]; omega
  · rw [← norm_tensorChoiMatrix, tensorChoiMatrix_sub]
    exact Real.le_sqrt_of_sq_le hres

end Flat

end NLQCLean

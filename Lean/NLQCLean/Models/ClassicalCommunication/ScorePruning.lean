import NLQCLean.Models.ClassicalCommunication.InstrumentCompression

/-!
# Score-nondecreasing pruning of instrument outcomes

If more weights are positive than the dimension of a real vector space containing the
moment vectors, the vectors are linearly dependent. When a linear functional is positive on
every vector, a dependence has coefficients of both signs; choosing its sign so that a real
score does not decrease and moving the weights along it until one vanishes removes an
outcome. Iterating leaves at most `dim` positive weights
(`lem:free-classical-compression`, the pruning step).

For a finite Kraus instrument on an `s`-dimensional input this selects at most `s²` actual
outcomes, realized by square-root rescaling of the original Kraus matrices, without
decreasing any outcome-dependent real-linear score. Exact score preservation needs `s² + 1`
outcomes (`FiniteKrausInstrument.exists_score_preserving_compression`).
-/

namespace NLQCLean.ClassicalCommunication

open Matrix Module

/-- **Pruning.** Nonnegative weights on vectors with positive values under a linear
functional can be replaced by nonnegative weights with at most `finrank` nonzero entries,
the same weighted sum and a weighted score that is not smaller. -/
theorem exists_pruned_weights {α V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (tr : V →ₗ[ℝ] ℝ) (c : α → V) (hc : ∀ j, 0 < tr (c j)) (f : α → ℝ)
    (p : α → ℝ) (hp : ∀ j, 0 ≤ p j) :
    ∃ q : α → ℝ, (∀ j, 0 ≤ q j) ∧
      (Finset.univ.filter fun j => q j ≠ 0).card ≤ finrank ℝ V ∧
      (∑ j, q j • c j) = (∑ j, p j • c j) ∧ (∑ j, p j * f j) ≤ ∑ j, q j * f j := by
  suffices H : ∀ n : ℕ, ∀ p : α → ℝ, (∀ j, 0 ≤ p j) →
      (Finset.univ.filter fun j => p j ≠ 0).card = n →
      ∃ q : α → ℝ, (∀ j, 0 ≤ q j) ∧
        (Finset.univ.filter fun j => q j ≠ 0).card ≤ finrank ℝ V ∧
        (∑ j, q j • c j) = (∑ j, p j • c j) ∧ (∑ j, p j * f j) ≤ ∑ j, q j * f j from
    H _ p hp rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp hn
  by_cases hsmall : n ≤ finrank ℝ V
  · exact ⟨p, hp, hn ▸ hsmall, rfl, le_rfl⟩
  have hsmall' : finrank ℝ V < n := lt_of_not_ge hsmall
  set s := Finset.univ.filter fun j => p j ≠ 0 with hs
  have hdep : ¬ LinearIndependent ℝ (fun j : s => c j) := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, hn] at h
    omega
  obtain ⟨g, hg0, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let z : α → ℝ := fun j => if h : j ∈ s then g ⟨j, h⟩ else 0
  have hzoff : ∀ j, j ∉ s → z j = 0 := fun j hj => by simp [z, hj]
  have hzc : (∑ j, z j • c j) = 0 := by
    rw [← hg0, ← Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by
      rw [hzoff j hj, zero_smul]), ← Finset.sum_attach s]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [z, j.property]
  have hzi : z i ≠ 0 := by simpa [z, i.property] using hi
  -- choose the sign so that the score does not decrease
  obtain ⟨w, hwc, hwf, hwoff, hwne⟩ : ∃ w : α → ℝ, (∑ j, w j • c j) = 0 ∧
      0 ≤ (∑ j, w j * f j) ∧ (∀ j, j ∉ s → w j = 0) ∧ w i ≠ 0 := by
    by_cases h : 0 ≤ ∑ j, z j * f j
    · exact ⟨z, hzc, h, hzoff, hzi⟩
    · refine ⟨fun j => -z j, ?_, ?_, fun j hj => by simp [hzoff j hj], by simpa using hzi⟩
      · simp only [neg_smul, Finset.sum_neg_distrib, hzc, neg_zero]
      · simp only [neg_mul, Finset.sum_neg_distrib]; linarith
  have hwtr : (∑ j, w j * tr (c j)) = 0 := by
    have h := congrArg tr hwc
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using h
  have hneg : ∃ j, w j < 0 := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < ∑ j, w j * tr (c j) :=
      Finset.sum_pos' (fun j _ => mul_nonneg (hcon j) (hc j).le)
        ⟨i, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hcon i) (Ne.symm hwne)) (hc i)⟩
    linarith
  set N := Finset.univ.filter fun j => w j < 0 with hN
  have hNne : N.Nonempty := by
    obtain ⟨j, hj⟩ := hneg
    exact ⟨j, by simp [hN, hj]⟩
  obtain ⟨j₀, hj₀N, hmin⟩ := N.exists_min_image (fun j => p j / (-w j)) hNne
  have hj₀ : w j₀ < 0 := by simpa [hN] using hj₀N
  set t := p j₀ / (-w j₀) with ht
  have ht0 : 0 ≤ t := div_nonneg (hp j₀) (neg_pos.mpr hj₀).le
  let q : α → ℝ := fun j => p j + t * w j
  have hq : ∀ j, 0 ≤ q j := by
    intro j
    by_cases hj : w j < 0
    · have h := hmin j (by simp [hN, hj])
      rw [le_div_iff₀ (neg_pos.mpr hj)] at h
      change 0 ≤ p j + t * w j
      linarith
    · push Not at hj
      exact add_nonneg (hp j) (mul_nonneg ht0 hj)
  have hqj₀ : q j₀ = 0 := by
    have hw : -w j₀ ≠ 0 := (neg_pos.mpr hj₀).ne'
    change p j₀ + p j₀ / (-w j₀) * w j₀ = 0
    calc p j₀ + p j₀ / (-w j₀) * w j₀ = p j₀ - p j₀ / (-w j₀) * (-w j₀) := by ring
      _ = 0 := by rw [div_mul_cancel₀ _ hw, sub_self]
  have hsub : (Finset.univ.filter fun j => q j ≠ 0) ⊂ s := by
    refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨j₀, ?_, ?_⟩
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, fun hpj => hj.2 ?_⟩
      have hjs : j ∉ s := by simp [hs, hpj]
      change p j + t * w j = 0
      rw [hpj, hwoff j hjs, mul_zero, add_zero]
    · by_contra hj₀s
      exact hj₀.ne (hwoff j₀ hj₀s)
    · simp [hqj₀]
  obtain ⟨q', hq'0, hq'card, hq'c, hq'f⟩ :=
    ih _ (hn ▸ Finset.card_lt_card hsub) q hq rfl
  refine ⟨q', hq'0, hq'card, hq'c.trans ?_, le_trans ?_ hq'f⟩
  · simp only [q, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hwc,
      smul_zero, add_zero]
  · simp only [q, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    nlinarith

/-- Sums over an enumeration of the support of `q` of terms that vanish off the support. -/
theorem sum_enum_support_eq_sum {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    (q : α → ℝ) (F : α → M) (hF : ∀ a, q a = 0 → F a = 0)
    (e : Fin (Finset.univ.filter fun a => q a ≠ 0).card ≃
      (Finset.univ.filter fun a => q a ≠ 0)) :
    (∑ j, F (e j)) = ∑ a, F a := by
  rw [e.sum_comp (fun a => F a), Finset.sum_coe_sort _ F]
  exact Finset.sum_subset (Finset.subset_univ _) fun a _ ha => hF a (by simpa using ha)

section Hermitian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

/-- At most `s²` actual outcomes keep the normalized identity marginal without decreasing a
real score. -/
theorem exists_normalized_hermitian_marginal_score_pruning {α : Type*} [Fintype α]
    (marginal : α → selfAdjoint (Matrix ι ι ℂ)) (score : α → ℝ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a)
    (htrace : ∀ a, (marginal a : Matrix ι ι ℂ).trace.re = Fintype.card ι)
    (hm : (∑ a, p a • marginal a) = 1) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 ∧
      ∃ (select : Fin n → α) (weight : Fin n → ℝ),
        (∀ j, 0 ≤ weight j) ∧
          (∑ j, weight j • marginal (select j)) = 1 ∧
          (∑ a, p a * score a) ≤ ∑ j, weight j * score (select j) := by
  classical
  have hc : ∀ a, 0 < hermitianRealTrace ι (marginal a) := fun a => by
    change 0 < (marginal a : Matrix ι ι ℂ).trace.re
    rw [htrace a]
    exact Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨q, hq0, hqcard, hqc, hqf⟩ :=
    exists_pruned_weights (hermitianRealTrace ι) marginal hc score p hp
  rw [(finrank_adjoint_matrix_spaces ι).1] at hqcard
  let e := (Fintype.equivFinOfCardEq
    (Fintype.card_coe (Finset.univ.filter fun a => q a ≠ 0))).symm
  refine ⟨_, hqcard, fun j => e j, fun j => q (e j), fun j => hq0 _, ?_, ?_⟩
  · show ∑ j, q (e j) • marginal (e j) = 1
    rw [sum_enum_support_eq_sum q (fun a => q a • marginal a)
      (fun a ha => by rw [ha, zero_smul]) e, hqc, hm]
  · show _ ≤ ∑ j, q (e j) * score (e j)
    rw [sum_enum_support_eq_sum q (fun a => q a * score a) (fun a ha => by rw [ha, zero_mul]) e]
    exact hqf

end Hermitian

namespace FiniteKrausInstrument

variable {ι κ σ ε : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [Fintype ε]
variable [DecidableEq ι]

/-- **Score-nondecreasing compression.** At most `s²` selected actual outcomes, realized by
square-root rescaling, do not decrease any outcome-dependent real-linear target score. -/
theorem exists_score_nondecreasing_compression [Nonempty ι]
    (I : FiniteKrausInstrument ι κ σ ε)
    (L : σ → ((Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ)) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 ∧
      ∃ (select : Fin n → σ) (scale : Fin n → ℝ)
        (J : FiniteKrausInstrument ι κ (Fin n) ε),
        (∀ j, 0 ≤ scale j) ∧
        (∀ j e, J.operator j e = (Real.sqrt (scale j) : ℂ) • I.operator (select j) e) ∧
        (∀ j, J.branch j = scale j • I.branch (select j)) ∧
        (∑ x, L x (I.branch x)) ≤ ∑ j, L (select j) (J.branch j) := by
  classical
  let p : I.PositiveOutcome → ℝ := fun a => I.traceProbability a.val
  let f : I.PositiveOutcome → ℝ := fun a => (p a)⁻¹ * L a.val (I.branch a.val)
  have hm : (∑ a, p a • I.normalizedMarginal a) = 1 := by
    calc
      _ = ∑ a : I.PositiveOutcome, I.inputMarginal a.val := by
        refine Finset.sum_congr rfl fun a _ => ?_
        change p a • ((p a)⁻¹ • I.inputMarginal a.val) = _
        rw [smul_smul, mul_inv_cancel₀ (I.traceProbability_pos a).ne', one_smul]
      _ = ∑ x, I.inputMarginal x :=
        I.sum_positiveOutcome_eq_sum _ fun x hx => I.inputMarginal_eq_zero_of_traceMass_eq_zero hx
      _ = 1 := I.sum_inputMarginal
  have hf : (∑ a, p a * f a) = ∑ x, L x (I.branch x) := by
    calc
      _ = ∑ a : I.PositiveOutcome, L a.val (I.branch a.val) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        change p a * ((p a)⁻¹ * _) = _
        rw [← mul_assoc, mul_inv_cancel₀ (I.traceProbability_pos a).ne', one_mul]
      _ = _ := I.sum_positiveOutcome_eq_sum (fun x => L x (I.branch x)) fun x hx => by
        rw [I.branch_eq_zero_of_traceMass_eq_zero hx, map_zero]
  obtain ⟨n, hn, chooseOutcome, weight, hweight, hmarg, hscore⟩ :=
    exists_normalized_hermitian_marginal_score_pruning I.normalizedMarginal f p
      (fun a => (I.traceProbability_pos a).le) I.trace_normalizedMarginal hm
  let select : Fin n → σ := fun j => (chooseOutcome j).val
  let scale : Fin n → ℝ := fun j => weight j * (I.traceProbability (select j))⁻¹
  have hscale : ∀ j, 0 ≤ scale j := fun j =>
    mul_nonneg (hweight j) (inv_nonneg.mpr (I.traceProbability_nonneg _))
  have hnormalized : (∑ j, scale j • I.inputMarginal (select j)) = 1 := by
    simpa only [normalizedMarginal, select, scale, smul_smul] using hmarg
  let J := I.rescaleSelected select scale hscale hnormalized
  refine ⟨n, hn, select, scale, J, hscale, (fun _ _ => rfl),
    I.branch_rescaleSelected select scale hscale hnormalized, ?_⟩
  rw [← hf]
  refine hscore.trans_eq ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [I.branch_rescaleSelected select scale hscale hnormalized, map_smul, smul_eq_mul]
  simp only [f, p, scale, select, mul_assoc]

end FiniteKrausInstrument

end NLQCLean.ClassicalCommunication
